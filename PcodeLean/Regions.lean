import PcodeLean.Frame
import PcodeLean.Basic

namespace PcodeLean

/-- The half-open byte range ends at or before the end of the address space. -/
def NoWrap (base : BitVec 64) (bytes : Nat) : Prop := base.toNat + bytes ≤ 2^64

instance (base : BitVec 64) (bytes : Nat) : Decidable (NoWrap base bytes) :=
  inferInstanceAs (Decidable (base.toNat + bytes ≤ 2^64))

/-- Nonwrapping buffers separated by their endpoints; adjacency and empty ranges are allowed. -/
def Separated (a : BitVec 64) (n : Nat) (b : BitVec 64) (m : Nat) : Prop :=
  NoWrap a n ∧ NoWrap b m ∧
    (n = 0 ∨ m = 0 ∨ a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat)

instance (a b : BitVec 64) (n m : Nat) : Decidable (Separated a n b m) :=
  inferInstanceAs (Decidable (NoWrap a n ∧ NoWrap b m ∧
    (n = 0 ∨ m = 0 ∨ a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat)))

theorem Separated.symm (h : Separated a n b m) : Separated b m a n := by
  refine ⟨h.2.1, h.1, ?_⟩
  rcases h.2.2 with h | h | h | h <;> simp_all

theorem ByteRegion.bounds (hw : NoWrap base n) (hp : ByteRegion base n p) :
    base.toNat ≤ p.toNat ∧ p.toNat < base.toNat + n := by
  unfold NoWrap at hw
  unfold ByteRegion at hp
  by_cases h : base ≤ p
  · rw [BitVec.toNat_sub_of_le h] at hp
    have := (BitVec.le_def.mp h)
    omega
  · have hlt : p < base := by
      change p.toNat < base.toNat
      change ¬base.toNat ≤ p.toNat at h
      omega
    rw [BitVec.toNat_sub_of_lt hlt] at hp
    have := base.isLt
    omega

theorem ByteRegion.of_bounds (hp : base.toNat ≤ p.toNat ∧ p.toNat < base.toNat + n) :
    ByteRegion base n p := by
  unfold ByteRegion
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr hp.1)]
  omega

/-- A nonempty slice of a nonwrapping buffer has its expected natural-number address. -/
theorem NoWrap.offset (hw : NoWrap base n) (hs : off + bytes ≤ n) (hn : 0 < bytes) :
    (base + BitVec.ofNat 64 off).toNat = base.toNat + off ∧
      NoWrap (base + BitVec.ofNat 64 off) bytes := by
  unfold NoWrap at *
  have hb := base.isLt
  have ho : off < 2^64 := by omega
  have ha : (base + BitVec.ofNat 64 off).toNat = base.toNat + off := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho]
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨ha, by omega⟩

/-- A byte store into a slice is contained in the whole caller-owned buffer. -/
theorem ByteRegion.slice (hw : NoWrap base n) (hs : off + bytes ≤ n)
    (hp : ByteRegion (base + BitVec.ofNat 64 off) bytes p) : ByteRegion base n p := by
  have hn : 0 < bytes := by have := hp; unfold ByteRegion at this; omega
  obtain ⟨ha, hw'⟩ := hw.offset hs hn
  have hb := ByteRegion.bounds hw' hp
  apply ByteRegion.of_bounds
  omega

theorem ReadRegion.bounds (hw : NoWrap base n) (hp : ReadRegion base n p) :
    base.toNat ≤ p.toNat ∧ p.toNat < base.toNat + n := by
  induction n generalizing base with
  | zero => exact False.elim hp
  | succ n ih =>
    rcases hp with rfl | hp
    · unfold NoWrap at hw
      omega
    · by_cases hn : n = 0
      · subst n; exact False.elim hp
      · have ha : (base + 1).toNat = base.toNat + 1 := by
          apply BitVec.toNat_add_of_lt
          change base.toNat + 1 < 2^64
          unfold NoWrap at hw
          omega
        have ht := ih (base := base + 1) (by unfold NoWrap at *; omega) hp
        omega

/-- A read from a slice is contained in the whole caller-owned buffer. -/
theorem ReadRegion.slice (hw : NoWrap base n) (hs : off + bytes ≤ n)
    (hp : ReadRegion (base + BitVec.ofNat 64 off) bytes p) : ByteRegion base n p := by
  have hn : 0 < bytes := by cases bytes <;> simp_all [ReadRegion]
  obtain ⟨ha, hw'⟩ := hw.offset hs hn
  have hb := ReadRegion.bounds hw' hp
  apply ByteRegion.of_bounds
  omega

/-- Discharge the bytewise premise of `readLE_frame` from buffer endpoints. -/
theorem Separated.read_write (h : Separated readBase n writeBase m) :
    ∀ p, ReadRegion readBase n p → ¬ByteRegion writeBase m p := by
  intro p hr hw
  have := ReadRegion.bounds h.1 hr
  have := ByteRegion.bounds h.2.1 hw
  rcases h.2.2 with h | h | h | h <;> omega

theorem Separated.byte_disjoint (h : Separated a n b m) :
    ∀ p, ByteRegion a n p → ¬ByteRegion b m p := by
  intro p ha hb
  have := ByteRegion.bounds h.1 ha
  have := ByteRegion.bounds h.2.1 hb
  rcases h.2.2 with h | h | h | h <;> omega

/-- The next limb's read never touches the preceding limb, even across address wraparound. -/
theorem ReadRegion.high_limb (base p : BitVec 64) (hp : ReadRegion (base + 8) 8 p) :
    ¬ByteRegion base 8 p := by
  simp only [ReadRegion, or_false] at hp
  rcases hp with h | h | h | h | h | h | h | h
  all_goals subst p; unfold ByteRegion; bv_omega

/-- Scratch below a nonwrapping return cell is separated using only the reservation size. -/
theorem stack_scratch_separated (hw : NoWrap sp 8) (hs : bytes ≤ sp.toNat) :
    Separated (sp - BitVec.ofNat 64 bytes) bytes sp 8 := by
  have hb := sp.isLt
  have hn : bytes < 2^64 := by omega
  have ht : (sp - BitVec.ofNat 64 bytes).toNat = sp.toNat - bytes := by
    rw [BitVec.toNat_sub_of_le (by
      rw [BitVec.le_def]
      simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn] using hs)]
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]
  exact ⟨by unfold NoWrap; omega, hw, Or.inr (Or.inr (Or.inl (by omega)))⟩

end PcodeLean
