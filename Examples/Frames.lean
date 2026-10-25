import Examples.Generated.Increment
import Examples.Generated.Maximum
import Examples.Generated.Count
import Examples.Generated.Scan
import Examples.Generated.Add128

open PcodeLean Std.WP Lean.Order
set_option experimental.vcgen true
namespace Examples.Frames

private theorem run_frame (step : Step (PC × X86State) X86State) (allowed : Footprint)
    (effect : ∀ f, MayChange allowed f.2 (Sum.elim Prod.snd id (step f)))
    (pc : PC) (s before : X86State) (initial : MayChange allowed before s) :
    (PcodeLean.run step (pc, s)).wp (MayChange allowed before) := by
  apply (run_spec step (pc, s) (fun f ↦ MayChange allowed before f.2) _ ?_).le_wp
  · exact initial
  intro f
  constructor
  intro h
  have he := MayChange.trans h (effect f)
  change Sum.elim (fun f ↦ MayChange allowed before f.2) (MayChange allowed before) (step f)
  cases hn : step f <;> simpa [hn] using he

namespace IncrementFrame

def footprint : Footprint :=
  ⟨[.rax, .rsp, .rip], arithmeticFlags, fun _ ↦ False⟩

private theorem step_effect (f : Increment.Frame) :
    MayChange footprint f.2 (Sum.elim Prod.snd id (Increment.step f)) := by
  rcases f with ⟨pc, s⟩
  cases pc <;> simp [MayChange, footprint, Register.forall_iff,
    Register.read, Flag.read, arithmeticFlags, Increment.step, Sum.elim, pure]
  all_goals split <;> simp_all

theorem correct (s : X86State) : (Increment.run s).wp (MayChange footprint s) := by
  apply run_frame Increment.step footprint step_effect Increment.PC.p0
    { s with rip := 0x1000 } s
  simp [MayChange, footprint, Register.forall_iff,
    Register.read, Flag.read, arithmeticFlags]

theorem sysV (s : X86State) : (Increment.run s).wp
    (MayChange (sysVFootprint (fun _ ↦ False)) s) := by
  apply (Increment.run s).mono (fun out h ↦ h.weaken ?_ ?_ ?_) (correct s)
  all_goals simp [footprint, sysVFootprint, callerSaved, arithmeticFlags]

end IncrementFrame

namespace MaximumFrame

def footprint : Footprint :=
  ⟨[.rax, .rsp, .rip], arithmeticFlags, fun _ ↦ False⟩

private theorem step_effect (f : Maximum.Frame) :
    MayChange footprint f.2 (Sum.elim Prod.snd id (Maximum.step f)) := by
  rcases f with ⟨pc, s⟩
  cases pc <;> simp [MayChange, footprint, Register.forall_iff, Flag.forall_iff,
    Register.read, Flag.read, arithmeticFlags, Maximum.step, Sum.elim, pure, boolByte]
  all_goals split <;> simp_all

theorem correct (s : X86State) : (Maximum.run s).wp (MayChange footprint s) := by
  apply run_frame Maximum.step footprint step_effect Maximum.PC.p0
    { s with rip := 0x1000 } s
  simp [MayChange, footprint, Register.forall_iff,
    Register.read, Flag.read, arithmeticFlags]

theorem sysV (s : X86State) : (Maximum.run s).wp
    (MayChange (sysVFootprint (fun _ ↦ False)) s) := by
  apply (Maximum.run s).mono (fun out h ↦ h.weaken ?_ ?_ ?_) (correct s)
  all_goals simp [footprint, sysVFootprint, callerSaved, arithmeticFlags]

end MaximumFrame

namespace CountFrame

def footprint : Footprint :=
  ⟨[.rax, .rdi, .rsp, .rip], arithmeticFlags, fun _ ↦ False⟩

private theorem step_effect (f : Count.Frame) :
    MayChange footprint f.2 (Sum.elim Prod.snd id (Count.step f)) := by
  rcases f with ⟨pc, s⟩
  cases pc <;> simp [MayChange, footprint, Register.forall_iff, Flag.forall_iff,
    Register.read, Flag.read, arithmeticFlags, Count.step, Sum.elim, pure, boolByte]
  all_goals split <;> simp_all

theorem correct (s : X86State) : (Count.run s).wp (MayChange footprint s) := by
  apply run_frame Count.step footprint step_effect Count.PC.p0
    { s with rip := 0x1000 } s
  simp [MayChange, footprint, Register.forall_iff,
    Register.read, Flag.read, arithmeticFlags]

theorem sysV (s : X86State) : (Count.run s).wp
    (MayChange (sysVFootprint (fun _ ↦ False)) s) := by
  apply (Count.run s).mono (fun out h ↦ h.weaken ?_ ?_ ?_) (correct s)
  all_goals simp [footprint, sysVFootprint, callerSaved, arithmeticFlags]

end CountFrame

namespace ScanFrame

def footprint : Footprint :=
  ⟨[.rax, .rdi, .rsi, .rsp, .rip], arithmeticFlags, fun _ ↦ False⟩

private theorem step_effect (f : Scan.Frame) :
    MayChange footprint f.2 (Sum.elim Prod.snd id (Scan.step f)) := by
  rcases f with ⟨pc, s⟩
  cases pc <;> simp [MayChange, footprint, Register.forall_iff, Flag.forall_iff,
    Register.read, Flag.read, arithmeticFlags, Scan.step, Sum.elim, pure, boolByte]
  all_goals split <;> simp_all

theorem correct (s : X86State) : (Scan.run s).wp (MayChange footprint s) := by
  apply run_frame Scan.step footprint step_effect Scan.PC.p0
    { s with rip := 0x1000 } s
  simp [MayChange, footprint, Register.forall_iff,
    Register.read, Flag.read, arithmeticFlags]

theorem sysV (s : X86State) : (Scan.run s).wp
    (MayChange (sysVFootprint (fun _ ↦ False)) s) := by
  apply (Scan.run s).mono (fun out h ↦ h.weaken ?_ ?_ ?_) (correct s)
  all_goals simp [footprint, sysVFootprint, callerSaved, arithmeticFlags]

end ScanFrame

namespace Add128Frame

def footprint : Footprint :=
  ⟨[.rax, .rdx, .rsp, .rip], arithmeticFlags, fun _ ↦ False⟩

private theorem step_effect (f : Add128.Frame) :
    MayChange footprint f.2 (Sum.elim Prod.snd id (Add128.step f)) := by
  rcases f with ⟨pc, s⟩
  cases pc <;> simp [MayChange, footprint, Register.forall_iff, Flag.forall_iff,
    Register.read, Flag.read, arithmeticFlags, Add128.step, Sum.elim, pure, boolByte]
  all_goals split <;> simp_all

theorem correct (s : X86State) : (Add128.run s).wp (MayChange footprint s) := by
  apply run_frame Add128.step footprint step_effect Add128.PC.p0
    { s with rip := 0x1000 } s
  simp [MayChange, footprint, Register.forall_iff,
    Register.read, Flag.read, arithmeticFlags]

theorem sysV (s : X86State) : (Add128.run s).wp
    (MayChange (sysVFootprint (fun _ ↦ False)) s) := by
  apply (Add128.run s).mono (fun out h ↦ h.weaken ?_ ?_ ?_) (correct s)
  all_goals simp [footprint, sysVFootprint, callerSaved, arithmeticFlags]

end Add128Frame

end Examples.Frames
