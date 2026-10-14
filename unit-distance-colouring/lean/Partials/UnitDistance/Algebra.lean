import Partials.UnitDistance.Model

/-! BLIND source. Primitive cyclotomic facts remain in CyclotomicBasisDuty
and IntegralOrderDuty. No seed, quotient or final graph conclusion is assumed. -/
namespace Partials.UnitDistance.Algebra

theorem evalInteger_zero : evalInteger 0 = 0 := by
  simp [evalInteger]

theorem evalInteger_add (a b : IntegerCode) :
    evalInteger (a + b) = evalInteger a + evalInteger b := by
  simp [evalInteger, add_mul, Finset.sum_add_distrib]

theorem evalInteger_neg (a : IntegerCode) : evalInteger (-a) = -evalInteger a := by
  simp [evalInteger, Finset.sum_neg_distrib]

theorem zero_mem_O : (0 : ℂ) ∈ O := by
  exact ⟨0, evalInteger_zero⟩

theorem add_mem_O {a b : ℂ} (ha : a ∈ O) (hb : b ∈ O) : a + b ∈ O := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x + y, evalInteger_add x y⟩

theorem neg_mem_O {a : ℂ} (ha : a ∈ O) : -a ∈ O := by
  obtain ⟨x, rfl⟩ := ha
  exact ⟨-x, evalInteger_neg x⟩

theorem O_subset_M1 : O ⊆ M1 := by
  intro a ha
  exact ⟨a, ha, 0, zero_mem_O, by simp⟩

theorem M1_subset_M2 : M1 ⊆ M2 := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  exact ⟨a, ha, b, hb, 0, zero_mem_O, by simp⟩

theorem O_subset_M2 : O ⊆ M2 := Set.Subset.trans O_subset_M1 M1_subset_M2

structure IntegralOrderDuty : Prop where
  one_mem : (1 : ℂ) ∈ O
  multiplication : ∀ a ∈ O, ∀ b ∈ O, a * b ∈ O
  conjugation : ∀ a ∈ O, star a ∈ O
  roots : ∀ r : Fin 42, w ^ r.val ∈ O

theorem reflected_M1_in_M2 (d : IntegralOrderDuty) (ht : star t * t = 1)
    {z : ℂ} (hz : z ∈ M1) : t ^ 2 * star z ∈ M2 := by
  obtain ⟨a, ha, b, hb, rfl⟩ := hz
  have htb : t ^ 2 * star t = t := by
    calc
      t ^ 2 * star t = t * (star t * t) := by ring
      _ = t := by rw [ht]; ring
  refine ⟨0, zero_mem_O, star b, d.conjugation b hb,
    star a, d.conjugation a ha, ?_⟩
  simp only [star_add, star_mul']
  rw [mul_add]
  calc
    t ^ 2 * star a + t ^ 2 * (star t * star b)
        = t ^ 2 * star a + (t ^ 2 * star t) * star b := by ring
    _ = 0 + t * star b + t ^ 2 * star a := by rw [htb]; ring

theorem delta_rotation_identities (h : rho ^ 2 - rho + 1 = 0) :
    delta * (1 - rho) = 1 + rho ∧ -delta * rho = 2 - rho := by
  constructor <;> dsimp [delta] <;> linear_combination -2 * h

/-- Uniform shell covariance must include the reflection case; it is an
identity of the actual transport, not a statement about quotient labels. -/
theorem seedTransport_rotation (j : Fin 3) (r : Fin 42) (z : ℂ) :
    seedTransport (j, r) z = w ^ r.val * seedTransport (j, (0 : Fin 42)) z := by
  unfold seedTransport indexedUnit
  split_ifs <;> simp only [Fin.val_zero, pow_zero, mul_one] <;> ring

end Partials.UnitDistance.Algebra
