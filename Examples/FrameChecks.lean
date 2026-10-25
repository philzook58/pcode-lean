import PcodeLean

open PcodeLean
namespace Examples.FrameChecks

-- A byte written at a wrapped address still belongs to the declared footprint.
example : ByteRegion (0xffffffffffffffff : BitVec 64) 2 0 := by decide
example : ¬ByteRegion (0xffffffffffffffff : BitVec 64) 2 1 := by decide

example : readLE (writeLE (fun _ ↦ 0) 0xffffffffffffffff 2 0xabcd)
    0xffffffffffffffff 2 = 0xabcd := by decide

-- Writing into the return cell cannot satisfy the disjointness premise.
example : ¬(∀ p, ReadRegion 0x8000 8 p → ¬ByteRegion 0x8000 1 p) := by
  intro h
  exact h 0x8000 (Or.inl rfl) (by decide)

-- A callee-saved register cannot be hidden by permitting all caller-saved registers.
example : ¬MayChange (sysVFootprint (fun _ ↦ False)) {} { rbx := 1 } := by
  intro h
  have hr := h.1 .rbx (by simp [sysVFootprint, callerSaved])
  change (1 : BitVec 64) = 0 at hr
  contradiction

-- A successful stack frame must account for RET's eight-byte adjustment.
example : ¬StackReturn ({} : X86State) {} := by
  intro h
  have hr := h.1
  change (0 : BitVec 64) = 8 at hr
  contradiction

-- Even a single out-of-range memory change violates the frame.
example : ¬MayChange ⟨[], [], ByteRegion 0x1000 16⟩ {}
    { mem := fun p ↦ if p == 0x2000 then 1 else 0 } := by
  intro h
  have hm := h.2.2 0x2000 (by decide)
  change (1 : BitVec 8) = 0 at hm
  contradiction

/-- A store changes exactly its declared byte representation and preserves everything outside. -/
theorem store_contract (s : X86State) (base : BitVec 64) (bytes : Nat)
    (v : BitVec (bytes * 8)) :
    let out := { s with mem := writeLE s.mem base bytes v }
    MayChange ⟨[], [], ByteRegion base bytes⟩ s out ∧
      ∀ p, ByteRegion base bytes p →
        out.mem p = (v >>> ((p - base).toNat * 8)).setWidth 8 :=
  ⟨writeLE_mayChange s base bytes v, fun p hp ↦ writeLE_inside s.mem base bytes v p hp⟩

/-- The frame alone suffices to preserve the caller's return cell when stores are disjoint. -/
theorem return_cell_preserved (before after : X86State) (allowed : Footprint)
    (frame : MayChange allowed before after)
    (disjoint : ∀ p, ReadRegion before.rsp 8 p → ¬allowed.memory p) :
    readLE after.mem before.rsp 8 = readLE before.mem before.rsp 8 :=
  readLE_frame allowed.memory before.mem after.mem frame.2.2 before.rsp 8 disjoint

end Examples.FrameChecks
