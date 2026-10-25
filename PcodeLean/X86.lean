import Init.Data.BitVec

/-! Flat, little-endian user-mode state. There are no permissions, MMIO, faults, or concurrency.
These are p-code flag cells, not a claim that SLEIGH models every architectural flag faithfully. -/
namespace PcodeLean

abbrev Memory := BitVec 64 → BitVec 8

/-- Register aliases in raw p-code refer to slices of these canonical register cells. -/
structure X86State where
  rax : BitVec 64 := 0
  rcx : BitVec 64 := 0
  rdx : BitVec 64 := 0
  rbx : BitVec 64 := 0
  rsp : BitVec 64 := 0
  rbp : BitVec 64 := 0
  rsi : BitVec 64 := 0
  rdi : BitVec 64 := 0
  r8 : BitVec 64 := 0
  r9 : BitVec 64 := 0
  r10 : BitVec 64 := 0
  r11 : BitVec 64 := 0
  r12 : BitVec 64 := 0
  r13 : BitVec 64 := 0
  r14 : BitVec 64 := 0
  r15 : BitVec 64 := 0
  rip : BitVec 64 := 0
  cf : BitVec 8 := 0
  pf : BitVec 8 := 0
  af : BitVec 8 := 0
  zf : BitVec 8 := 0
  sf : BitVec 8 := 0
  df : BitVec 8 := 0
  of : BitVec 8 := 0
  mem : Memory := fun _ ↦ 0

def boolByte (b : Bool) : BitVec 8 := if b then 1 else 0

def readLE (mem : Memory) (address : BitVec 64) : (bytes : Nat) → BitVec (bytes * 8)
  | 0 => 0
  | n + 1 => ((readLE mem (address + 1) n).setWidth ((n + 1) * 8) <<< 8) |||
      (mem address).setWidth ((n + 1) * 8)

def writeLE (mem : Memory) (address : BitVec 64) (bytes : Nat)
    (value : BitVec (bytes * 8)) : Memory :=
  fun p ↦ if (p - address).toNat < bytes
    then (value >>> ((p - address).toNat * 8)).setWidth 8 else mem p

def insertBits (old : BitVec w) (offset : Nat) (value : BitVec n) : BitVec w :=
  let mask := ((BitVec.ofNat w (2 ^ n - 1)) <<< offset)
  (old &&& ~~~mask) ||| (value.setWidth w <<< offset)

def shiftLeft (x : BitVec w) (n : Nat) : BitVec w := if n < w then x <<< n else 0

def popcount (x : BitVec w) : Nat :=
  (List.range w).foldl (fun n i ↦ n + if x.getLsbD i then 1 else 0) 0

end PcodeLean
