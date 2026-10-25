import Examples.Generated.Increment
import Examples.Generated.Maximum
import Examples.Generated.Count
import Examples.Generated.AFGap

open PcodeLean

private def flags (s : X86State) : Nat :=
  s.cf.toNat + 4 * s.pf.toNat + 16 * s.af.toNat + 64 * s.zf.toNat +
    128 * s.sf.toNat + 1024 * s.df.toNat + 2048 * s.of.toNat

def main (args : List String) : IO UInt32 := do
  let [routine, first, second, budget] := args
    | IO.eprintln "usage: pcode-run (inc|max|count|afgap) ARG1 ARG2 FUEL"; return 2
  let some a := first.toNat? | IO.eprintln "invalid first argument"; return 2
  let some b := second.toNat? | IO.eprintln "invalid second argument"; return 2
  let some fuel := budget.toNat? | IO.eprintln "invalid fuel"; return 2
  let s : X86State := {
    rdi := BitVec.ofNat 64 a
    rsi := BitVec.ofNat 64 b
    rsp := 0x8000
    mem := writeLE (fun _ ↦ 0) 0x8000 8 0x9000 }
  let result ← match routine with
    | "inc" => pure (Increment.execute fuel s)
    | "max" => pure (Maximum.execute fuel s)
    | "count" => pure (Count.execute fuel s)
    | "afgap" => pure (AFGap.execute fuel s)
    | _ => IO.eprintln "unknown routine"; return 2
  match result with
  | none => IO.eprintln "fuel exhausted"; return 1
  | some out =>
    IO.println s!"{out.rax.toNat} {out.rsp.toNat} {out.rip.toNat} {flags out}"
    return 0
