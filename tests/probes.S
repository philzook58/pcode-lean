/* Extra native regressions exercise aliases, memory, and x86 shift-count masking. */
.section .text.alias64,"ax",@progbits
.globl alias64
.type alias64,@function
alias64:
  mov %rdi, %rax
  mov $0x5a, %al
  mov $0x12, %ah
  mov %eax, %eax
  ret
.size alias64,.-alias64

.section .text.stack64,"ax",@progbits
.globl stack64
.type stack64,@function
stack64:
  push %rdi
  add %rsi, (%rsp)
  pop %rax
  ret
.size stack64,.-stack64

.section .text.shift64,"ax",@progbits
.globl shift64
.type shift64,@function
shift64:
  mov %rdi, %rax
  mov %rsi, %rcx
  shl %cl, %rax
  ret
.size shift64,.-shift64
.section .note.GNU-stack,"",@progbits
