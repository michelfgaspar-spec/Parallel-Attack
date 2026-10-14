import Partials.UnitDistance.Model

/-! R6 BLIND SOURCE / UNCOMPILED. Main `lem:kernel` and (5.2)--(5.3).
The primitive duty below is a degree-12 rational basis fact, not an assumption
that integral representations already have the desired common-shift kernel.
No field structure on the binary quotient is involved. -/
namespace Partials.UnitDistance.Words

open Partials.UnitDistance

def hexStep (h : Fin 6) : ℤ × ℤ :=
  ![(1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1)] h

def shiftSeven (p : SevenPairs) (A B : ℤ) : SevenPairs :=
  fun k => ((p k).1 + A, (p k).2 + B)

def subtractSeven (q p : SevenPairs) : SevenPairs :=
  fun k => ((q k).1 - (p k).1, (q k).2 - (p k).2)

noncomputable def pairEmbedding (v : ℤ × ℤ) : ℂ :=
  (v.1 : ℂ) + (v.2 : ℂ) * rho

theorem pairEmbedding_add (u v : ℤ × ℤ) :
    pairEmbedding (u + v) = pairEmbedding u + pairEmbedding v := by
  simp only [pairEmbedding, Prod.fst_add, Prod.snd_add, Int.cast_add]
  ring

theorem sevenPairValue_sub (q p : SevenPairs) :
    sevenPairValue (subtractSeven q p) = sevenPairValue q - sevenPairValue p := by
  simp only [sevenPairValue, subtractSeven, Int.cast_sub]
  simp_rw [show ∀ k : Fin 7,
    (((q k).1 : ℂ) - (p k).1 + (((q k).2 : ℂ) - (p k).2) * rho) *
      zeta ^ k.val =
    (((q k).1 : ℂ) + (q k).2 * rho) * zeta ^ k.val -
      (((p k).1 : ℂ) + (p k).2 * rho) * zeta ^ k.val by intro k; ring]
  rw [Finset.sum_sub_distrib]

theorem sevenPairValue_shift (p : SevenPairs) (A B : ℤ) :
    sevenPairValue (shiftSeven p A B) =
      sevenPairValue p + ((A : ℂ) + (B : ℂ) * rho) *
        ∑ k : Fin 7, zeta ^ k.val := by
  simp only [sevenPairValue, shiftSeven, Int.cast_add]
  simp_rw [show ∀ k : Fin 7,
    (((p k).1 : ℂ) + A + (((p k).2 : ℂ) + B) * rho) * zeta ^ k.val =
      ((p k).1 + (p k).2 * rho) * zeta ^ k.val +
      ((A : ℂ) + (B : ℂ) * rho) * zeta ^ k.val by intro k; ring]
  rw [Finset.sum_add_distrib, Finset.mul_sum]

/-- Exact primitive algebraic obligations: Phi7 annihilation and independence
of its first six powers over Q(rho), expressed without silently introducing
an abstract field or assuming integral coefficient uniqueness. They follow
from the cited minimal-polynomial/degree argument, which remains unverified.
The rational independence, including the rho coordinate, is essential. -/
structure SevenBasisDuty : Prop where
  phiSeven : (∑ k : Fin 7, zeta ^ k.val) = 0
  sixPairIndependent : ∀ a b : Fin 6 → ℚ,
    (∑ k : Fin 6, ((a k : ℂ) + (b k : ℂ) * rho) * zeta ^ k.val) = 0 →
    ∀ k, a k = 0 ∧ b k = 0

theorem shift_preserves_value (d : SevenBasisDuty) (p : SevenPairs) (A B : ℤ) :
    sevenPairValue (shiftSeven p A B) = sevenPairValue p := by
  rw [sevenPairValue_shift, d.phiSeven]
  simp

/-- Separate last coefficient, so the primitive six-power independence
applies to an integral seven-pair vector whose last coefficient is zero. -/
theorem seven_zero_of_last_zero (d : SevenBasisDuty) (p : SevenPairs)
    (hz : sevenPairValue p = 0) (hlast : p 6 = (0, 0)) :
    ∀ k, p k = (0, 0) := by
  have hsix : (∑ k : Fin 6,
      ((((p k.castSucc).1 : ℚ) : ℂ) +
        (((p k.castSucc).2 : ℚ) : ℂ) * rho) * zeta ^ k.val) = 0 := by
    rw [sevenPairValue, Fin.sum_univ_castSucc] at hz
    simpa [hlast] using hz
  have hcoords := d.sixPairIndependent
    (fun k => ((p k.castSucc).1 : ℚ))
    (fun k => ((p k.castSucc).2 : ℚ)) hsix
  intro k
  by_cases hlastk : k = 6
  · simpa [hlastk] using hlast
  · have hlt : k.val < 6 := by
      have hk : k.val < 7 := k.isLt
      have hne : k.val ≠ 6 := by
        intro he
        apply hlastk
        exact Fin.ext he
      omega
    let j : Fin 6 := ⟨k.val, hlt⟩
    have hj : j.castSucc = k := Fin.ext rfl
    have h := hcoords j
    apply Prod.ext
    · have hzero : (p j.castSucc).1 = 0 := by exact_mod_cast h.1
      simpa [hj] using hzero
    · have hzero : (p j.castSucc).2 = 0 := by exact_mod_cast h.2
      simpa [hj] using hzero

/-- Main Lemma `lem:kernel`: common shifts are derived from rational basis
independence, then their integrality comes from the actual last coefficients. -/
theorem same_value_iff_common_shift (d : SevenBasisDuty) (p q : SevenPairs) :
    sevenPairValue q = sevenPairValue p ↔
      ∃ A B : ℤ, q = shiftSeven p A B := by
  constructor
  · intro hvalue
    let A : ℤ := (q 6).1 - (p 6).1
    let B : ℤ := (q 6).2 - (p 6).2
    let difference := shiftSeven (subtractSeven q p) (-A) (-B)
    have hdvalue : sevenPairValue difference = 0 := by
      rw [show difference = shiftSeven (subtractSeven q p) (-A) (-B) from rfl,
        shift_preserves_value d, sevenPairValue_sub, hvalue]
      ring
    have hdlast : difference 6 = (0, 0) := by
      simp [difference, shiftSeven, subtractSeven, A, B]
    have hzero := seven_zero_of_last_zero d difference hdvalue hdlast
    refine ⟨A, B, ?_⟩
    funext k
    apply Prod.ext
    · have h := congrArg Prod.fst (hzero k)
      simp only [difference, shiftSeven, subtractSeven, Prod.fst] at h ⊢
      omega
    · have h := congrArg Prod.snd (hzero k)
      simp only [difference, shiftSeven, subtractSeven, Prod.snd] at h ⊢
      omega
  · rintro ⟨A, B, rfl⟩
    exact shift_preserves_value d p A B

/-- Root exponent 6k+7h modulo42. Its inverse is k=-r modulo7, h=r modulo6. -/
def rootIndex (k : Fin 7) (h : Fin 6) : Fin 42 :=
  ⟨(6 * k.val + 7 * h.val) % 42, Nat.mod_lt _ (by decide)⟩

def rootClass (r : Fin 42) : Fin 7 × Fin 6 :=
  (⟨(6 * r.val) % 7, Nat.mod_lt _ (by decide)⟩,
   ⟨r.val % 6, Nat.mod_lt _ (by decide)⟩)

/-- Finite case proofs are authored, never evaluated in R6. -/
def rootClassEquiv : (Fin 7 × Fin 6) ≃ Fin 42 where
  toFun kh := rootIndex kh.1 kh.2
  invFun := rootClass
  left_inv := by
    rintro ⟨k, h⟩
    fin_cases k <;> fin_cases h <;> norm_num [rootClass, rootIndex]
  right_inv := by
    intro r
    fin_cases r <;> norm_num [rootClass, rootIndex]

/-- Exact finite cyclotomic applicability duty. No word optimality or kernel
conclusion occurs here. Proving it uses order42 and rho^2-rho+1=0, together
with the definitions of rho,zeta and the six listed integer coordinates. -/
structure RootClassEvaluationDuty : Prop where
  root_evaluation : ∀ k : Fin 7, ∀ h : Fin 6,
    w ^ (rootIndex k h).val = pairEmbedding (hexStep h) * zeta ^ k.val

theorem root_class_evaluation (d : RootClassEvaluationDuty) (r : Fin 42) :
    w ^ r.val = pairEmbedding (hexStep (rootClass r).2) *
      zeta ^ (rootClass r).1.val := by
  have h := d.root_evaluation (rootClass r).1 (rootClass r).2
  have he : rootIndex (rootClass r).1 (rootClass r).2 = r := rootClassEquiv.right_inv r
  simpa only [he] using h

end Partials.UnitDistance.Words
