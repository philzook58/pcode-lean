import Examples.Proofs
import Examples.Frames
import Examples.ScanProofs
import Examples.Add128Proofs

open PcodeLean Std.WP
namespace Examples.Contracts

theorem increment (s : X86State) : (Increment.run s).wp (fun out ↦
    Returns s out (s.rdi + 1) ∧ MayChange Frames.IncrementFrame.footprint s out) :=
  run_and Increment.step (Increment.initial s) ((IncrementProof.correct s).le_wp trivial)
    (Frames.IncrementFrame.correct s)

theorem maximum (s : X86State) : (Maximum.run s).wp (fun out ↦
    Returns s out (MaximumProof.result s) ∧ MayChange Frames.MaximumFrame.footprint s out) :=
  run_and Maximum.step (Maximum.initial s) ((MaximumProof.correct s).le_wp trivial)
    (Frames.MaximumFrame.correct s)

theorem count (s : X86State) : (Count.run s).wp (fun out ↦
    Returns s out s.rdi ∧ MayChange Frames.CountFrame.footprint s out) :=
  run_and Count.step (Count.initial s) ((CountProof.correct s).le_wp trivial)
    (Frames.CountFrame.correct s)

theorem scan (s : X86State) : (Scan.run s).wp (fun out ↦
    ScanProof.Post s out ∧ MayChange Frames.ScanFrame.footprint s out) :=
  run_and Scan.step (Scan.initial s) ((ScanProof.correct s).le_wp trivial)
    (Frames.ScanFrame.correct s)

theorem add128 (s : X86State) : (Add128.run s).wp (fun out ↦
    Add128Proof.Post s out ∧ MayChange Frames.Add128Frame.footprint s out) :=
  run_and Add128.step (Add128.initial s) (Add128Proof.correct s)
    (Frames.Add128Frame.correct s)

theorem scan_terminates (s : X86State) : ∃ out,
    Scan.execute (4 * s.rdi.toNat + 5) s = some out ∧
      ScanProof.Post s out ∧ MayChange Frames.ScanFrame.footprint s out := by
  obtain ⟨out, he, _⟩ := ScanProof.terminates s
  exact ⟨out, he, execute_correct Scan.step (Scan.initial s) _ (scan s) he⟩

theorem add128_terminates (s : X86State) : ∃ out, Add128.execute 5 s = some out ∧
    Add128Proof.Post s out ∧ MayChange Frames.Add128Frame.footprint s out := by
  obtain ⟨out, he, _⟩ := Add128Proof.terminates s
  exact ⟨out, he, execute_correct Add128.step (Add128.initial s) _ (add128 s) he⟩

theorem add128_value (s out : X86State) (h : Add128Proof.Post s out) :
    out.rax.toNat + 2^64 * out.rdx.toNat + 2^128 * out.cf.toNat =
      (s.rdi.toNat + 2^64 * s.rsi.toNat) + (s.rdx.toNat + 2^64 * s.rcx.toNat) := by
  rw [h.1, h.2.1, h.2.2.1]
  exact Add128Proof.arithmetic s

end Examples.Contracts
