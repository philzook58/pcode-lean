import PcodeLean.X86

namespace PcodeLean

inductive Register where
  | rax | rcx | rdx | rbx | rsp | rbp | rsi | rdi
  | r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15 | rip
  deriving DecidableEq, Repr

def Register.read (s : X86State) : Register → BitVec 64
  | .rax => s.rax
  | .rcx => s.rcx
  | .rdx => s.rdx
  | .rbx => s.rbx
  | .rsp => s.rsp
  | .rbp => s.rbp
  | .rsi => s.rsi
  | .rdi => s.rdi
  | .r8 => s.r8
  | .r9 => s.r9
  | .r10 => s.r10
  | .r11 => s.r11
  | .r12 => s.r12
  | .r13 => s.r13
  | .r14 => s.r14
  | .r15 => s.r15
  | .rip => s.rip

inductive Flag where
  | cf | pf | af | zf | sf | df | of
  deriving DecidableEq, Repr

def Flag.read (s : X86State) : Flag → BitVec 8
  | .cf => s.cf
  | .pf => s.pf
  | .af => s.af
  | .zf => s.zf
  | .sf => s.sf
  | .df => s.df
  | .of => s.of

theorem Register.forall_iff (P : Register → Prop) : (∀ x, P x) ↔
    P .rax ∧ P .rcx ∧ P .rdx ∧ P .rbx ∧ P .rsp ∧ P .rbp ∧ P .rsi ∧ P .rdi ∧
      P .r8 ∧ P .r9 ∧ P .r10 ∧ P .r11 ∧ P .r12 ∧ P .r13 ∧ P .r14 ∧ P .r15 ∧ P .rip := by
  constructor
  · intro h
    exact ⟨h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _, h _⟩
  · intro h x; cases x <;> simp_all

theorem Flag.forall_iff (P : Flag → Prop) : (∀ x, P x) ↔
  P .cf ∧ P .pf ∧ P .af ∧ P .zf ∧ P .sf ∧ P .df ∧ P .of := by
  constructor
  · intro h; exact ⟨h _, h _, h _, h _, h _, h _, h _⟩
  · intro h x; cases x <;> simp_all

/-- Modular byte interval; addresses may wrap around the 64-bit address space. -/
def ByteRegion (base : BitVec 64) (size : Nat) (p : BitVec 64) : Prop :=
  (p - base).toNat < size

instance (base : BitVec 64) (size : Nat) (p : BitVec 64) :
    Decidable (ByteRegion base size p) := inferInstanceAs (Decidable ((p - base).toNat < size))

/-- A final-state frame. Permission to change is not a claim that a change occurred. -/
structure Footprint where
  registers : List Register := []
  flags : List Flag := []
  memory : BitVec 64 → Prop := fun _ ↦ False

def MayChange (allowed : Footprint) (before after : X86State) : Prop :=
  (∀ r, r ∉ allowed.registers → r.read after = r.read before) ∧
  (∀ f, f ∉ allowed.flags → f.read after = f.read before) ∧
  (∀ p, ¬allowed.memory p → after.mem p = before.mem p)

@[simp] theorem MayChange.refl (allowed : Footprint) (s : X86State) :
    MayChange allowed s s := ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem MayChange.trans (ab : MayChange allowed a b) (bc : MayChange allowed b c) :
    MayChange allowed a c :=
  ⟨fun r h ↦ (bc.1 r h).trans (ab.1 r h),
   fun f h ↦ (bc.2.1 f h).trans (ab.2.1 f h),
   fun p h ↦ (bc.2.2 p h).trans (ab.2.2 p h)⟩

/-- System V AMD64 volatile registers; RSP is handled separately at return. -/
def callerSaved : List Register := [.rax, .rcx, .rdx, .rsi, .rdi, .r8, .r9, .r10, .r11]
def arithmeticFlags : List Flag := [.cf, .pf, .af, .zf, .sf, .of]

def sysVFootprint (memory : BitVec 64 → Prop) : Footprint :=
  ⟨.rip :: .rsp :: callerSaved, arithmeticFlags, memory⟩

/-- The caller's return cell is read before RSP advances by eight bytes. -/
def StackReturn (before after : X86State) : Prop :=
  after.rsp = before.rsp + 8 ∧ after.rip = readLE before.mem before.rsp 8

/-- Candidate scratch space below entry RSP; the caller establishes required disjointness. -/
def StackScratch (sp : BitVec 64) (bytes : Nat) : BitVec 64 → Prop :=
  ByteRegion (sp - BitVec.ofNat 64 bytes) bytes

/-- An instruction-boundary stack pointer lies at most `bytes` below entry, without wraparound. -/
def StackWithin (entry : BitVec 64) (bytes : Nat) (sp : BitVec 64) : Prop :=
  sp.toNat ≤ entry.toNat ∧ entry.toNat ≤ sp.toNat + bytes

instance (entry sp : BitVec 64) (bytes : Nat) : Decidable (StackWithin entry bytes sp) :=
  inferInstanceAs (Decidable (sp.toNat ≤ entry.toNat ∧ entry.toNat ≤ sp.toNat + bytes))

theorem writeLE_outside (mem : Memory) (base : BitVec 64) (n : Nat)
    (value : BitVec (n * 8)) (p : BitVec 64) (h : ¬ByteRegion base n p) :
    writeLE mem base n value p = mem p := by
  exact ite_eq_right h

theorem writeLE_inside (mem : Memory) (base : BitVec 64) (n : Nat)
    (value : BitVec (n * 8)) (p : BitVec 64) (h : ByteRegion base n p) :
    writeLE mem base n value p = (value >>> ((p - base).toNat * 8)).setWidth 8 :=
  ite_eq_left h

theorem writeLE_mayChange (s : X86State) (base : BitVec 64) (n : Nat)
    (value : BitVec (n * 8)) :
    MayChange ⟨[], [], ByteRegion base n⟩ s { s with mem := writeLE s.mem base n value } :=
  ⟨fun _ _ ↦ rfl, fun _ _ ↦ rfl, fun p hp ↦ writeLE_outside s.mem base n value p hp⟩

/-- The actual byte addresses used by `readLE`, including modular address wraparound. -/
def ReadRegion (base : BitVec 64) : Nat → BitVec 64 → Prop
  | 0, _ => False
  | n + 1, p => p = base ∨ ReadRegion (base + 1) n p

theorem readLE_frame (allowed : BitVec 64 → Prop) (before after : Memory)
    (hmem : ∀ p, ¬allowed p → after p = before p) (base : BitVec 64) (n : Nat)
    (disjoint : ∀ p, ReadRegion base n p → ¬allowed p) :
    readLE after base n = readLE before base n := by
  induction n generalizing base with
  | zero => rfl
  | succ n ih =>
    simp only [readLE]
    rw [ih (base + 1) (fun p hp ↦ disjoint p (Or.inr hp)),
      hmem base (disjoint base (Or.inl rfl))]

theorem MayChange.weaken (h : MayChange small before after)
    (regs : ∀ r, r ∈ small.registers → r ∈ large.registers)
    (flags : ∀ f, f ∈ small.flags → f ∈ large.flags)
    (mem : ∀ p, small.memory p → large.memory p) : MayChange large before after :=
  ⟨fun r hr ↦ h.1 r (fun hs ↦ hr (regs r hs)),
   fun f hf ↦ h.2.1 f (fun hs ↦ hf (flags f hs)),
   fun p hp ↦ h.2.2 p (fun hs ↦ hp (mem p hs))⟩

def Footprint.union (a b : Footprint) : Footprint :=
  ⟨a.registers ++ b.registers, a.flags ++ b.flags, fun p ↦ a.memory p ∨ b.memory p⟩

theorem MayChange.compose (ab : MayChange first a b) (bc : MayChange second b c) :
    MayChange (first.union second) a c := by
  apply MayChange.trans (ab.weaken ?_ ?_ ?_) (bc.weaken ?_ ?_ ?_)
  all_goals simp only [Footprint.union, List.mem_append]
  · exact fun _ h ↦ Or.inl h
  · exact fun _ h ↦ Or.inl h
  · exact fun _ h ↦ Or.inl h
  · exact fun _ h ↦ Or.inr h
  · exact fun _ h ↦ Or.inr h
  · exact fun _ h ↦ Or.inr h

end PcodeLean
