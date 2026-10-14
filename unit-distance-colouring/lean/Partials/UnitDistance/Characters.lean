import Partials.UnitDistance.Quotient
import Mathlib.LinearAlgebra.Basis.Defs

/-! R6 blind source. The two-character addition/cancellation argument adapts
the retained historical-drafts/AdditiveColoring.lean (frozen SHA-256
5eafd5576efeae46673d838be23814b35ed78cb016133e14735f2354d63a3121).
This module adds the common-rho whole-line detection and character sums.
No finite table, Fourier basis, or proof has been evaluated. -/
namespace Partials.UnitDistance

variable {V : Type*} [AddCommGroup V]

def twoCharacterColor (h k : V →+ ZMod 2) (v : V) : BinaryPalette := (h v, k v)

theorem twoCharacterColor_add (h k : V →+ ZMod 2) (v d : V) :
    twoCharacterColor h k (v + d) =
      twoCharacterColor h k v + twoCharacterColor h k d := by
  simp [twoCharacterColor, map_add]

theorem twoCharacterColor_proper (h k : V →+ ZMod 2) (D : Finset V)
    (hdetect : ∀ d ∈ D, twoCharacterColor h k d ≠ 0) :
    ∀ v d, d ∈ D → twoCharacterColor h k (v + d) ≠ twoCharacterColor h k v := by
  intro v d hd he
  have he' : twoCharacterColor h k v + twoCharacterColor h k d =
      twoCharacterColor h k v + 0 := by
    simpa [twoCharacterColor_add] using he
  exact hdetect d hd (add_left_cancel he')

def lineAt [DecidableEq V] (F : CommonBinaryLineFamily V) (i : Fin 21) : Finset V :=
  {F.head i, F.R (F.head i), F.head i + F.R (F.head i)}

def lineDirections [DecidableEq V] (F : CommonBinaryLineFamily V)
    (S : Finset (Fin 21)) : Finset V := S.biUnion (lineAt F)

def AnnihilatesLine (F : CommonBinaryLineFamily V) (h : V →+ ZMod 2)
    (i : Fin 21) : Prop := h (F.head i) = 0 ∧ h (F.R (F.head i)) = 0

instance annihilatesLineDecidable (F : CommonBinaryLineFamily V)
    (h : V →+ ZMod 2) (i : Fin 21) : Decidable (AnnihilatesLine F h i) := by
  unfold AnnihilatesLine
  infer_instance

def LineHit (F : CommonBinaryLineFamily V) (S : Finset (Fin 21)) : Prop :=
  ∀ h : V →+ ZMod 2, h ≠ 0 → ∃ i ∈ S, AnnihilatesLine F h i

theorem annihilates_line_iff [DecidableEq V] (F : CommonBinaryLineFamily V)
    (h : V →+ ZMod 2) (i : Fin 21) :
    AnnihilatesLine F h i ↔ ∀ d ∈ lineAt F i, h d = 0 := by
  constructor
  · rintro ⟨hh, hr⟩ d hd
    simp only [lineAt, Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl | rfl
    · exact hh
    · exact hr
    · simp only [map_add, hh, hr, add_zero]
  · intro hz
    exact ⟨hz _ (by simp [lineAt]), hz _ (by simp [lineAt])⟩

theorem pair_zero_forces_line_annihilation [DecidableEq V]
    (F : CommonBinaryLineFamily V) (h : V →+ ZMod 2)
    (i : Fin 21) (d : V) (hd : d ∈ lineAt F i)
    (hz : twoCharacterColor h (h.comp F.R) d = 0) : AnnihilatesLine F h i := by
  have h0 : h d = 0 := congrArg Prod.fst hz
  have hR0 : h (F.R d) = 0 := congrArg Prod.snd hz
  simp only [lineAt, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl
  · exact ⟨h0, hR0⟩
  · have hsum : h (F.head i) + h (F.R (F.head i)) = 0 := by
      simpa only [F.square, map_add] using hR0
    exact ⟨by simpa only [h0, add_zero] using hsum, h0⟩
  · have hh : h (F.head i) = 0 := by
      simpa only [common_rotation_sum] using hR0
    have hsum : h (F.head i) + h (F.R (F.head i)) = 0 := by
      simpa only [map_add] using h0
    exact ⟨hh, by simpa only [hh, zero_add] using hsum⟩

theorem missed_whole_lines_give_detection [DecidableEq V]
    (F : CommonBinaryLineFamily V) (h : V →+ ZMod 2) (S : Finset (Fin 21))
    (hmiss : ∀ i ∈ S, ¬ AnnihilatesLine F h i) :
    ∀ d ∈ lineDirections F S, twoCharacterColor h (h.comp F.R) d ≠ 0 := by
  intro d hd hz
  obtain ⟨i, hi, hdi⟩ := Finset.mem_biUnion.mp hd
  exact hmiss i hi (pair_zero_forces_line_annihilation F h i d hdi hz)

def ProperCayley [DecidableEq V] {C : Type*}
    (F : CommonBinaryLineFamily V) (S : Finset (Fin 21)) (c : V → C) : Prop :=
  ∀ a b, a + b ∈ lineDirections F S → c a ≠ c b

theorem paired_colour_proper_when_missed [DecidableEq V]
    (F : CommonBinaryLineFamily V) (h : V →+ ZMod 2) (S : Finset (Fin 21))
    (hmiss : ∀ i ∈ S, ¬ AnnihilatesLine F h i) :
    ProperCayley F S (twoCharacterColor h (h.comp F.R)) := by
  intro a b hab he
  have htranslation := twoCharacterColor_proper h (h.comp F.R)
    (lineDirections F S) (missed_whole_lines_give_detection F h S hmiss)
    a (a + b) hab
  have hadd : a + (a + b) = b := by
    rw [← add_assoc, F.two_torsion, zero_add]
  exact htranslation (by simpa only [hadd] using he.symm)

def binarySign (x : ZMod 2) : ℤ := if x = 0 then 1 else -1
def additiveCharacter (h : V →+ ZMod 2) (v : V) : ℤ := binarySign (h v)

theorem binary_sign_add (a b : ZMod 2) :
    binarySign (a + b) = binarySign a * binarySign b := by
  fin_cases a <;> fin_cases b <;> unfold binarySign <;> decide

theorem additiveCharacter_add (h : V →+ ZMod 2) (a b : V) :
    additiveCharacter h (a + b) = additiveCharacter h a * additiveCharacter h b := by
  simp only [additiveCharacter, map_add, binary_sign_add]

theorem cayley_character_sum (h : V →+ ZMod 2) (D : Finset V) (v : V) :
    (∑ d ∈ D, additiveCharacter h (v + d)) =
      additiveCharacter h v * (∑ d ∈ D, additiveCharacter h d) := by
  simp only [additiveCharacter_add, Finset.mul_sum]

/-- Ordered three-vector sum. Distinctness/nonzero and disjoint whole-line
admission are separate duties needed to identify it with the actual adjacency
sum over a Finset of directions. -/
theorem three_character_sum (a b : ZMod 2) :
    binarySign a + binarySign b + binarySign (a + b) =
      if a = 0 ∧ b = 0 then 3 else -1 := by
  fin_cases a <;> fin_cases b <;> unfold binarySign <;> decide

theorem whole_line_character_sum (F : CommonBinaryLineFamily V)
    (h : V →+ ZMod 2) (i : Fin 21) :
    additiveCharacter h (F.head i) + additiveCharacter h (F.R (F.head i)) +
      additiveCharacter h (F.head i + F.R (F.head i)) =
      if AnnihilatesLine F h i then 3 else -1 := by
  simpa only [additiveCharacter, map_add, AnnihilatesLine] using
    three_character_sum (h (F.head i)) (h (F.R (F.head i)))

noncomputable def annihilatedCount (F : CommonBinaryLineFamily V)
    (S : Finset (Fin 21)) (h : V →+ ZMod 2) : ℕ := by
  classical
  exact (S.filter (AnnihilatesLine F h)).card

noncomputable def lineEigenvalue (F : CommonBinaryLineFamily V)
    (S : Finset (Fin 21)) (h : V →+ ZMod 2) : ℤ :=
  4 * (annihilatedCount F S h : ℤ) - S.card

theorem lineEigenvalue_zero (F : CommonBinaryLineFamily V)
    (S : Finset (Fin 21)) : lineEigenvalue F S 0 = 3 * (S.card : ℤ) := by
  classical
  have hz : ∀ i, AnnihilatesLine F (0 : V →+ ZMod 2) i := by
    intro i
    exact ⟨rfl, rfl⟩
  simp [lineEigenvalue, annihilatedCount, hz]
  omega

theorem actual_character_eigenvector [DecidableEq V]
    (F : CommonBinaryLineFamily V) (S : Finset (Fin 21))
    (h : V →+ ZMod 2)
    (hsum : (∑ d ∈ lineDirections F S, additiveCharacter h d) =
      lineEigenvalue F S h) (v : V) :
    (∑ d ∈ lineDirections F S, additiveCharacter h (v + d)) =
      lineEigenvalue F S h * additiveCharacter h v := by
  rw [cayley_character_sum, hsum]
  ring

theorem line_sum_eigenvalue (F : CommonBinaryLineFamily V)
    (S : Finset (Fin 21)) (h : V →+ ZMod 2) :
    (∑ i ∈ S, if AnnihilatesLine F h i then (3 : ℤ) else -1) =
      lineEigenvalue F S h := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [lineEigenvalue, annihilatedCount]
  | @insert i S hi ih =>
      by_cases ha : AnnihilatesLine F h i
      · simp [Finset.sum_insert, Finset.filter_insert, hi, ha, lineEigenvalue, annihilatedCount] at *
        omega
      · simp [Finset.sum_insert, Finset.filter_insert, hi, ha, lineEigenvalue, annihilatedCount] at *
        omega

theorem hit_eigenvalue_lower (F : CommonBinaryLineFamily V)
    (S : Finset (Fin 21)) (hhit : LineHit F S) (h : V →+ ZMod 2) (h0 : h ≠ 0) :
    4 - (S.card : ℤ) ≤ lineEigenvalue F S h := by
  classical
  obtain ⟨i, hi, hai⟩ := hhit h h0
  have hpos : 0 < annihilatedCount F S h := by
    exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hai⟩⟩
  unfold lineEigenvalue
  omega

/-- Primitive Fourier and physical direction correspondence remain duties.
The columns give actual characters, not an arbitrary asserted spectrum. -/
structure QuotientFourierDuty [Fintype V] [DecidableEq V]
    (F : CommonBinaryLineFamily V) (S : Finset (Fin 21)) where
  A : Type
  finiteA : Fintype A
  functional : A → (V →+ ZMod 2)
  exhaustive : Function.Bijective functional
  basis : Module.Basis A ℝ (V → ℝ)
  basis_character : ∀ a v, basis a v = (additiveCharacter (functional a) v : ℝ)
  degree : (lineDirections F S).card = 3 * S.card
  eigenvector : ∀ a v,
    (∑ d ∈ lineDirections F S, basis a (v + d)) =
      (lineEigenvalue F S (functional a) : ℝ) * basis a v

end Partials.UnitDistance
