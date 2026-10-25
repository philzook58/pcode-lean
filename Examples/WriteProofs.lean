import Examples.Generated.AddMem
import Examples.Generated.Stack32
import Examples.Generated.Reserve256
import Examples.Add128Proofs

open PcodeLean
namespace Examples.WriteProof

def inputs (s : X86State) : X86State := {
  rdi := readLE s.mem s.rsi 8
  rsi := readLE s.mem (s.rsi + 8) 8
  rdx := readLE s.mem s.rdx 8
  rcx := readLE s.mem (s.rdx + 8) 8 }

def lowMemory (s : X86State) := writeLE s.mem s.rdi 8 (Add128Proof.low (inputs s))
def resultMemory (s : X86State) :=
  writeLE (lowMemory s) (s.rdi + 8) 8 (Add128Proof.high (inputs s))

/-- Only the first store can precede the loads of the high input limbs. -/
def InputsStable (s : X86State) : Prop :=
  (∀ p, ReadRegion (s.rsi + 8) 8 p → ¬ByteRegion s.rdi 8 p) ∧
  (∀ p, ReadRegion (s.rdx + 8) 8 p → ¬ByteRegion s.rdi 8 p)

def ReturnStable (s : X86State) : Prop :=
  ∀ p, ReadRegion s.rsp 8 p →
    ¬ByteRegion s.rdi 8 p ∧ ¬ByteRegion (s.rdi + 8) 8 p

def addFootprint (s : X86State) : Footprint :=
  ⟨[.rax, .rsp, .rip], arithmeticFlags,
    fun p ↦ ByteRegion s.rdi 8 p ∨ ByteRegion (s.rdi + 8) 8 p⟩

def AddPost (s out : X86State) : Prop :=
  out.mem = resultMemory s ∧ out.rax = (Add128Proof.overflow (inputs s)).setWidth 64 ∧
    StackReturn s out ∧ MayChange (addFootprint s) s out

theorem add_completion (s : X86State) (hi : InputsStable s) (hr : ReturnStable s) :
    finishes AddMem.step 9 (AddMem.initial s) (AddPost s) := by
  have hx := readLE_frame (ByteRegion s.rdi 8) s.mem (lowMemory s)
    (fun p hp ↦ writeLE_outside s.mem s.rdi 8 _ p hp) (s.rsi + 8) 8 hi.1
  have hy := readLE_frame (ByteRegion s.rdi 8) s.mem (lowMemory s)
    (fun p hp ↦ writeLE_outside s.mem s.rdi 8 _ p hp) (s.rdx + 8) 8 hi.2
  have hm : ∀ p, ¬(addFootprint s).memory p → resultMemory s p = s.mem p := by
    intro p hp
    have h1 : ¬ByteRegion s.rdi 8 p := fun h ↦ hp (Or.inl h)
    have h2 : ¬ByteRegion (s.rdi + 8) 8 p := fun h ↦ hp (Or.inr h)
    simp only [resultMemory, lowMemory, writeLE_outside _ _ _ _ _ h2,
      writeLE_outside _ _ _ _ _ h1]
  have ret := readLE_frame (addFootprint s).memory s.mem (resultMemory s) hm s.rsp 8
    (fun p hp h ↦ h.elim (hr p hp).1 (hr p hp).2)
  simp only [finishes, AddMem.step, AddMem.initial, AddPost, StackReturn,
    MayChange, Register.forall_iff, Flag.forall_iff, addFootprint, arithmeticFlags,
    Register.read, Flag.read, pure, Sum.elim]
  simp [resultMemory, lowMemory, inputs, Add128Proof.low, Add128Proof.high,
    Add128Proof.overflow, Add128Proof.carry] at hx hy ret hm ⊢
  simp [hx, hy, ret, insertBits]
  simpa [addFootprint] using hm

def stackMemory (s : X86State) := writeLE s.mem (s.rsp - 32) 8 s.rdi
def stackFootprint (s : X86State) : Footprint :=
  ⟨[.rsp, .rip], arithmeticFlags, ByteRegion (s.rsp - 32) 8⟩

def StackPost (s out : X86State) : Prop :=
  out.mem = stackMemory s ∧ StackReturn s out ∧ MayChange (stackFootprint s) s out

theorem stack_completion (s : X86State)
    (hr : ∀ p, ReadRegion s.rsp 8 p → ¬ByteRegion (s.rsp - 32) 8 p) :
    finishes Stack32.step 4 (Stack32.initial s) (StackPost s) := by
  have hm := writeLE_mayChange s (s.rsp - 32) 8 s.rdi
  have ret := readLE_frame (ByteRegion (s.rsp - 32) 8) s.mem (stackMemory s)
    hm.2.2 s.rsp 8 hr
  simp [finishes, Stack32.step, Stack32.initial, StackPost, StackReturn, stackMemory,
    MayChange, stackFootprint, Register.forall_iff, Flag.forall_iff, Register.read,
    Flag.read, arithmeticFlags, pure, Sum.elim, BitVec.sub_add_cancel] at ret ⊢
  exact ⟨ret, hm.2.2⟩

theorem add_correct (s : X86State) (hi : InputsStable s) (hr : ReturnStable s) :
    (AddMem.run s).wp (AddPost s) := finishes_run _ _ _ (add_completion s hi hr)

theorem stack_correct (s : X86State)
    (hr : ∀ p, ReadRegion s.rsp 8 p → ¬ByteRegion (s.rsp - 32) 8 p) :
    (Stack32.run s).wp (StackPost s) :=
  finishes_run _ _ _ (stack_completion s hr)

/-- A large temporary reservation still satisfies the ordinary exit frame. -/
theorem reserve_completion (s : X86State) :
    finishes Reserve256.step 3 (Reserve256.initial s) (fun out ↦
      StackReturn s out ∧ MayChange ⟨[.rsp, .rip], arithmeticFlags, fun _ ↦ False⟩ s out) := by
  simp [finishes, Reserve256.step, Reserve256.initial, StackReturn, MayChange,
    Register.forall_iff, Flag.forall_iff, Register.read, Flag.read, arithmeticFlags,
    pure, Sum.elim, BitVec.sub_add_cancel]

-- Entry/exit agreement alone cannot establish a stack high-water bound.
theorem reserve_depth : (Sum.elim Prod.snd id (Reserve256.step
    (.p0, { rsp := 0x8000 }))).rsp = 0x7f00 := by decide

end Examples.WriteProof
