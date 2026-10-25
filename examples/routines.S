/* Original examples for pcode-lean. Each section is one self-contained raw-code region. */
.section .text.inc64,"ax",@progbits
.globl inc64
.type inc64,@function
inc64:
  lea 1(%rdi), %rax
  ret
.size inc64,.-inc64

.section .text.umax64,"ax",@progbits
.globl umax64
.type umax64,@function
umax64:
  mov %rdi, %rax
  cmp %rsi, %rdi
  cmovb %rsi, %rax
  ret
.size umax64,.-umax64

.section .text.count64,"ax",@progbits
.globl count64
.type count64,@function
count64:
  xor %eax, %eax
  test %rdi, %rdi
  jz .Ldone
.Lloop:
  inc %rax
  dec %rdi
  jnz .Lloop
.Ldone:
  ret
.size count64,.-count64

/* Deliberate witness for the known SLEIGH auxiliary-carry gap, not a verified routine. */
.section .text.afgap64,"ax",@progbits
.globl afgap64
.type afgap64,@function
afgap64:
  xor %eax, %eax
  mov $15, %al
  add $1, %al
  lahf
  movzbl %ah, %eax
  ret
.size afgap64,.-afgap64
.section .text.scan64,"ax",@progbits
.globl scan64
.type scan64,@function
scan64:
  xor %rax, %rax
  test %rdi, %rdi
  jz .Lscan_done
.Lscan_loop:
  or (%rsi), %rax
  lea 8(%rsi), %rsi
  dec %rdi
  jnz .Lscan_loop
.Lscan_done:
  ret
.size scan64,.-scan64

/* Add (RSI:RDI) and (RCX:RDX), returning (RDX:RAX) with carry in CF. */
.section .text.add128,"ax",@progbits
.globl add128
.type add128,@function
add128:
  mov %rdi, %rax
  add %rdx, %rax
  mov %rsi, %rdx
  adc %rcx, %rdx
  ret
.size add128,.-add128
.section .note.GNU-stack,"",@progbits
/* Original scalar examples, following ASMC challenges and stack fixtures. */
.section .text.addmem,"ax",@progbits
.globl addmem
.type addmem,@function
addmem:
 mov (%rsi),%rax
 add (%rdx),%rax
 mov %rax,(%rdi)
 mov 8(%rsi),%rax
 adc 8(%rdx),%rax
 mov %rax,8(%rdi)
 mov $0,%eax
 setc %al
 ret
.size addmem,.-addmem
.section .text.fill64,"ax",@progbits
.globl fill64
.type fill64,@function
fill64:
 test %rsi,%rsi
 jz .Lfill_done
.Lfill_loop:
 mov %rdx,(%rdi)
 lea 8(%rdi),%rdi
 dec %rsi
 jnz .Lfill_loop
.Lfill_done:
 ret
.size fill64,.-fill64
.section .text.stack32,"ax",@progbits
.globl stack32
.type stack32,@function
stack32:
 sub $32,%rsp
 mov %rdi,(%rsp)
 add $32,%rsp
 ret
.size stack32,.-stack32
.section .text.reserve256,"ax",@progbits
.globl reserve256
.type reserve256,@function
reserve256:
 sub $256,%rsp
 add $256,%rsp
 ret
.size reserve256,.-reserve256
