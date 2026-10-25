"""Compare whole output buffers and carries against native code and a byte reference."""
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MASK = (1 << 64) - 1


def run(args):
    result = subprocess.run(args, cwd=ROOT, text=True, capture_output=True, timeout=60)
    if result.returncode:
        raise RuntimeError(result.stdout + result.stderr)
    return result.stdout


def initial_buffer(seed):
    mem = bytearray((i * 37 + 11) & 255 for i in range(96))
    # General values, zero, carry into the high limb, and carry beyond 128 bits.
    limbs = [None, (0, 0, 0, 0), (MASK, 0, 1, 0), (MASK, MASK, 1, 0)][seed]
    if limbs is not None:
        for offset, value in zip([0, 8, 32, 40], limbs):
            mem[offset:offset + 8] = value.to_bytes(8, "little")
    return mem


def check_writes():
    cases = [("add", offset, seed) for offset in [0, 32, 64, 1, 31, 40]
             for seed in range(4)]
    cases += [("fill", n, value) for n in range(9) for value in [0, 1, MASK]]
    c = ['#include <stdint.h>\n#include <stdio.h>',
         'extern uint64_t addmem(void*,void*,void*);',
         'extern void fill64(void*,uint64_t,uint64_t);', 'int main(void){']
    lean = ['import Examples.Generated.AddMem', 'import Examples.Generated.Fill',
            'open PcodeLean', 'def main : IO Unit := do']
    expected = []
    for kind, a, b in cases:
        mem = initial_buffer(b if kind == "add" else 0)
        c.append(' { unsigned char m[96]={' + ','.join(map(str, mem)) + '};')
        c.append(f' uint64_t carry=addmem(m+{a},m,m+32);' if kind == "add" else
                 f' fill64(m+16,{a},{b}ULL); uint64_t carry=0;')
        c.append(' printf("%llu ",(unsigned long long)carry);'
                 ' for(unsigned i=0;i<96;i++)printf("%u ",m[i]);puts("");}')
        lean += ['  do', '    let bytes : Array Nat := #[' + ','.join(map(str, mem)) + ']',
                 '    let mem : Memory := fun p ↦',
                 '      BitVec.ofNat 8 (bytes[(p-0x6000).toNat]?.getD 165)',
                 '    let s : X86State := {', '      rsp := 0x8000',
                 '      mem := writeLE mem 0x8000 8 0x9000']
        lean += ([f'      rdi := {0x6000 + a}', '      rsi := 0x6000', '      rdx := 0x6020 }']
                 if kind == "add" else
                 ['      rdi := 0x6010', f'      rsi := {a}', f'      rdx := {b} }}'])
        model = "AddMem" if kind == "add" else "Fill"
        lean += [f'    let some out := {model}.execute 100 s | throw (IO.userError "fuel")',
                 '    if out.rsp != 0x8008 || out.rip != 0x9000 then',
                 '      throw (IO.userError "return")',
                 '    IO.print s!"{out.rax.toNat} "' if kind == "add" else '    IO.print "0 "',
                 '    for i in List.range 96 do',
                 '      IO.print s!"{(out.mem (0x6000 + BitVec.ofNat 64 i)).toNat} "',
                 '    IO.println ""']
        carry = 0
        if kind == "fill":
            mem[16:16 + 8*a] = b.to_bytes(8, 'little') * a
        else:
            low = int.from_bytes(mem[0:8], 'little') + int.from_bytes(mem[32:40], 'little')
            mem[a:a + 8] = (low & MASK).to_bytes(8, 'little')
            # The machine reads high inputs AFTER the low store, also for unsafe overlaps.
            high = (int.from_bytes(mem[8:16], 'little') +
                    int.from_bytes(mem[40:48], 'little') + (low >> 64))
            mem[a + 8:a + 16] = (high & MASK).to_bytes(8, 'little')
            carry = high >> 64
        expected.append([carry, *mem])
    c.append('return 0;}')
    (ROOT / 'build/write-native.c').write_text('\n'.join(c) + '\n')
    (ROOT / 'build/WriteCases.lean').write_text('\n'.join(lean) + '\n')
    run(['cc', '-O2', 'build/write-native.c', 'examples/routines.S', '-o', 'build/write-native'])
    native = [[int(x) for x in row.split()] for row in run(['build/write-native']).splitlines()]
    model = [[int(x) for x in row.split()] for row in
             run(['lake', 'env', 'lean', '--run', 'build/WriteCases.lean']).splitlines()]
    assert native == model == expected, 'carry, output, or surrounding-byte mismatch'
    print(f'{len(cases)} native/model/reference whole-buffer comparisons pass (96 bytes each).')
    check_stack()


def check_stack():
    values = [0, 1, (1 << 63), MASK, 0x123456789ABCDEF0]
    c = ['#include <stdint.h>\n#include <stdio.h>',
         'extern uint64_t probe_stack32(uint64_t);', 'int main(void){']
    lean = ['import Examples.Generated.Stack32', 'open PcodeLean',
            'def main : IO Unit := do']
    for value in values:
        c.append(f'printf("%llu\\n",(unsigned long long)probe_stack32({value}ULL));')
        lean += [f'  let s : X86State := {{ rdi := {value}, rsp := 0x8000, mem := writeLE (fun _ ↦ 0xa5) 0x8000 8 0x9000 }}',
                 '  let some out := Stack32.execute 4 s | throw (IO.userError "fuel")',
                 '  if out.rsp != 0x8008 || out.rip != 0x9000 then',
                 '    throw (IO.userError "stack return")',
                 '  IO.println (readLE out.mem 0x7fe0 8).toNat']
    c.append('return 0;}')
    (ROOT / 'build/stack-native.c').write_text('\n'.join(c) + '\n')
    (ROOT / 'build/StackCases.lean').write_text('\n'.join(lean) + '\n')
    run(['cc', '-O2', 'build/stack-native.c', 'examples/routines.S',
         'tests/stack_probe.S', '-o', 'build/stack-native'])
    native = list(map(int, run(['build/stack-native']).splitlines()))
    model = list(map(int, run(['lake', 'env', 'lean', '--run', 'build/StackCases.lean']).splitlines()))
    assert native == model == values, 'stack spill mismatch'
    print(f'{len(values)} native/model stack-spill comparisons pass.')


if __name__ == '__main__':
    check_writes()
