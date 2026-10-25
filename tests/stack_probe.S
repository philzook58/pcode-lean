/* Read back stack32's scratch store after it restores RSP. */
.section .text.probe_stack32,"ax",@progbits
.globl probe_stack32
.type probe_stack32,@function
probe_stack32:
  sub $40, %rsp
  call stack32
  mov -40(%rsp), %rax
  add $40, %rsp
  ret
.size probe_stack32,.-probe_stack32

.section .note.GNU-stack,"",@progbits
