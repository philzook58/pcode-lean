import Init.Data.BitVec

/-! RV32 user-mode state: the 32 integer registers under their ABI names, as in the
SLEIGH `riscv.ilp32d` spec, plus `pc` and flat little-endian memory. There is no CSR,
FPU, trap or MMIO model. SLEIGH reads `zero` as a register: proofs assume it is 0. -/
namespace PcodeLean

structure RV32State where
  zero : BitVec 32 := 0
  ra : BitVec 32 := 0
  sp : BitVec 32 := 0
  gp : BitVec 32 := 0
  tp : BitVec 32 := 0
  t0 : BitVec 32 := 0
  t1 : BitVec 32 := 0
  t2 : BitVec 32 := 0
  s0 : BitVec 32 := 0
  s1 : BitVec 32 := 0
  a0 : BitVec 32 := 0
  a1 : BitVec 32 := 0
  a2 : BitVec 32 := 0
  a3 : BitVec 32 := 0
  a4 : BitVec 32 := 0
  a5 : BitVec 32 := 0
  a6 : BitVec 32 := 0
  a7 : BitVec 32 := 0
  s2 : BitVec 32 := 0
  s3 : BitVec 32 := 0
  s4 : BitVec 32 := 0
  s5 : BitVec 32 := 0
  s6 : BitVec 32 := 0
  s7 : BitVec 32 := 0
  s8 : BitVec 32 := 0
  s9 : BitVec 32 := 0
  s10 : BitVec 32 := 0
  s11 : BitVec 32 := 0
  t3 : BitVec 32 := 0
  t4 : BitVec 32 := 0
  t5 : BitVec 32 := 0
  t6 : BitVec 32 := 0
  pc : BitVec 32 := 0
  mem : BitVec 32 → BitVec 8 := fun _ ↦ 0

end PcodeLean
