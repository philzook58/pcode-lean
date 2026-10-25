import Examples.Contracts

open PcodeLean
namespace Examples.Tutorial

/-- A caller can extract an individual register and any caller-owned stack byte. -/
theorem increment_caller (s : X86State) : (Increment.run s).wp (fun out ↦
    out.rax = s.rdi + 1 ∧ out.rbx = s.rbx ∧ out.mem (s.rsp + 8) = s.mem (s.rsp + 8)) := by
  apply (Increment.run s).mono (fun out h ↦ ?_) (Contracts.increment s)
  exact ⟨h.1.1, h.2.1 .rbx (by simp [Frames.IncrementFrame.footprint]),
    h.2.2.2 (s.rsp + 8) (by simp [Frames.IncrementFrame.footprint])⟩

/-- A concrete store summary combines exact contents, a frame, and return-cell preservation. -/
theorem store_and_keep_return (s : X86State) (dst : BitVec 64) (n : Nat)
    (v : BitVec (n * 8))
    (disjoint : ∀ p, ReadRegion s.rsp 8 p → ¬ByteRegion dst n p) :
    let out := { s with mem := writeLE s.mem dst n v }
    MayChange ⟨[], [], ByteRegion dst n⟩ s out ∧
      readLE out.mem s.rsp 8 = readLE s.mem s.rsp 8 := by
  refine ⟨writeLE_mayChange s dst n v, ?_⟩
  exact readLE_frame (ByteRegion dst n) s.mem _
    (fun p hp ↦ writeLE_outside s.mem dst n v p hp) s.rsp 8 disjoint

/-- The two permissions can describe an output buffer and reserved stack scratch separately. -/
def bufferAndScratch (dst sp : BitVec 64) (bytes scratch : Nat) : Footprint :=
  sysVFootprint (fun p ↦ ByteRegion dst bytes p ∨ StackScratch sp scratch p)

end Examples.Tutorial
