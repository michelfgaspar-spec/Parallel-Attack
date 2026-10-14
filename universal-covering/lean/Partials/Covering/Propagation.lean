import Partials.Covering.Model
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section

/-! R4 BLIND / UNCHECKED SOURCE.
The pointwise argument is adapted from historical-drafts/ConditionalPropagation.lean,
SHA-256 0e6744407e93a87196d3abc5b1b8012f7ce87cbb2e27cfd7d3d4fd3047cea018.
It formalizes main.tex cor:gluing / eq:propagate, conditional on the clipped
angular modulus and a genuine all-translation regional premise. No numerical
geometry is admitted by these adapters. `closedIntervalDist` has an explicit
nearest point and minimality proof. Its correspondence to Mathlib's infDist is
separately exposed as MetricIntervalDistanceDuty, not silently assumed proved.
-/
namespace Partials.Covering

/-- Historical pointwise logical core, with its source attribution above. -/
theorem conditional_propagation_pointwise
    (g : ℝ → ℝ) (cap L c : ℝ) (I : Set ℝ)
    (hLip : ∀ φ ψ : ℝ,
      |min cap (g φ) - min cap (g ψ)| ≤ c * |φ - ψ|)
    (hsource : ∀ ψ ∈ I, L ≤ g ψ)
    (φ ψ : ℝ) (hψ : ψ ∈ I) :
    min L cap - c * |φ - ψ| ≤ g φ := by
  have hs : min L cap ≤ min cap (g ψ) := by
    apply le_min
    · exact min_le_right L cap
    · exact (min_le_left L cap).trans (hsource ψ hψ)
  have hlower := (abs_le.mp (hLip φ ψ)).1
  have hupper : min cap (g φ) ≤ g φ := min_le_right cap (g φ)
  linarith

def intervalClamp (lo hi x : ℝ) : ℝ := max lo (min hi x)

def closedIntervalDist (lo hi x : ℝ) : ℝ := |x - intervalClamp lo hi x|

theorem intervalClamp_mem (lo hi x : ℝ) (h : lo ≤ hi) :
    intervalClamp lo hi x ∈ Set.Icc lo hi := by
  constructor
  · exact le_max_left _ _
  · exact max_le h (min_le_left _ _)

theorem intervalClamp_of_le_left (lo hi x : ℝ)
    (h : lo ≤ hi) (hx : x ≤ lo) : intervalClamp lo hi x = lo := by
  simp [intervalClamp, min_eq_right (hx.trans h), max_eq_left hx]

theorem intervalClamp_of_mem (lo hi x : ℝ) (hx : x ∈ Set.Icc lo hi) :
    intervalClamp lo hi x = x := by
  simp [intervalClamp, min_eq_right hx.2, max_eq_right hx.1]

theorem intervalClamp_of_right_le (lo hi x : ℝ)
    (h : lo ≤ hi) (hx : hi ≤ x) : intervalClamp lo hi x = hi := by
  simp [intervalClamp, min_eq_left hx, max_eq_right h]

theorem closedIntervalDist_nonnegative (lo hi x : ℝ) :
    0 ≤ closedIntervalDist lo hi x := abs_nonneg _

theorem closedIntervalDist_of_le_left (lo hi x : ℝ)
    (h : lo ≤ hi) (hx : x ≤ lo) : closedIntervalDist lo hi x = lo - x := by
  rw [closedIntervalDist, intervalClamp_of_le_left lo hi x h hx,
    abs_of_nonpos (sub_nonpos.mpr hx)]
  ring

theorem closedIntervalDist_of_mem (lo hi x : ℝ) (hx : x ∈ Set.Icc lo hi) :
    closedIntervalDist lo hi x = 0 := by
  simp [closedIntervalDist, intervalClamp_of_mem lo hi x hx]

theorem closedIntervalDist_of_right_le (lo hi x : ℝ)
    (h : lo ≤ hi) (hx : hi ≤ x) : closedIntervalDist lo hi x = x - hi := by
  rw [closedIntervalDist, intervalClamp_of_right_le lo hi x h hx,
    abs_of_nonneg (sub_nonneg.mpr hx)]

/-- The chosen point is actually closest, rather than an arbitrary source point. -/
theorem closedIntervalDist_minimal (lo hi x y : ℝ)
    (h : lo ≤ hi) (hy : y ∈ Set.Icc lo hi) :
    closedIntervalDist lo hi x ≤ |x - y| := by
  by_cases hx : x ≤ lo
  · rw [closedIntervalDist_of_le_left lo hi x h hx]
    have ha : y - x ≤ |x - y| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    linarith [hy.1]
  · by_cases hx' : hi ≤ x
    · rw [closedIntervalDist_of_right_le lo hi x h hx']
      have ha : x - y ≤ |x - y| := le_abs_self _
      linarith [hy.2]
    · rw [closedIntervalDist_of_mem lo hi x ⟨le_of_lt (lt_of_not_ge hx),
        le_of_lt (lt_of_not_ge hx')⟩]
      exact abs_nonneg _

theorem nearest_closedInterval (lo hi x : ℝ) (h : lo ≤ hi) :
    ∃ y ∈ Set.Icc lo hi, |x - y| = closedIntervalDist lo hi x ∧
      ∀ z ∈ Set.Icc lo hi, |x - y| ≤ |x - z| := by
  refine ⟨intervalClamp lo hi x, intervalClamp_mem lo hi x h, rfl, ?_⟩
  intro z hz
  exact closedIntervalDist_minimal lo hi x z h hz

/-- OPEN library correspondence duty only. The scalar closest-point result above
is independent of this duty; no infDist equation is claimed unconditionally. -/
def MetricIntervalDistanceDuty : Prop :=
  ∀ lo hi : ℝ, lo ≤ hi → ∀ x : ℝ,
    Metric.infDist x (Set.Icc lo hi) = closedIntervalDist lo hi x

/-- P1 identifies the exact closed-interval clamp distance with Mathlib's
nonempty-set infimum distance. -/
theorem metricIntervalDistance_verified : MetricIntervalDistanceDuty := by
  intro lo hi h x
  apply le_antisymm
  · simpa only [Real.dist_eq, closedIntervalDist] using
      Metric.infDist_le_dist_of_mem (intervalClamp_mem lo hi x h)
  · apply (Metric.le_infDist (show (Set.Icc lo hi).Nonempty from
      ⟨lo, le_rfl, h⟩)).mpr
    intro y hy
    simpa only [Real.dist_eq] using closedIntervalDist_minimal lo hi x y h hy

theorem closedIntervalDist_le_iff (lo hi x r : ℝ)
    (h : lo ≤ hi) (hr : 0 ≤ r) :
    closedIntervalDist lo hi x ≤ r ↔ lo - r ≤ x ∧ x ≤ hi + r := by
  by_cases hx : x ≤ lo
  · rw [closedIntervalDist_of_le_left lo hi x h hx]
    constructor
    · intro hd; constructor <;> linarith
    · intro hd; linarith [hd.1]
  · by_cases hx' : hi ≤ x
    · rw [closedIntervalDist_of_right_le lo hi x h hx']
      constructor
      · intro hd; constructor <;> linarith
      · intro hd; linarith [hd.2]
    · rw [closedIntervalDist_of_mem lo hi x ⟨le_of_lt (lt_of_not_ge hx),
        le_of_lt (lt_of_not_ge hx')⟩]
      constructor
      · intro hd; constructor <;> linarith
      · intro hd; exact hr

theorem closedIntervalDist_lt_iff (lo hi x r : ℝ)
    (h : lo ≤ hi) (hr : 0 < r) :
    closedIntervalDist lo hi x < r ↔ lo - r < x ∧ x < hi + r := by
  by_cases hx : x ≤ lo
  · rw [closedIntervalDist_of_le_left lo hi x h hx]
    constructor
    · intro hd; constructor <;> linarith
    · intro hd; linarith [hd.1]
  · by_cases hx' : hi ≤ x
    · rw [closedIntervalDist_of_right_le lo hi x h hx']
      constructor
      · intro hd; constructor <;> linarith
      · intro hd; linarith [hd.2]
    · rw [closedIntervalDist_of_mem lo hi x ⟨le_of_lt (lt_of_not_ge hx),
        le_of_lt (lt_of_not_ge hx')⟩]
      constructor
      · intro hd; constructor <;> linarith
      · intro hd; exact hr

/-- Nonemptiness is witnessed by the zero translation pair. -/
theorem propagation_areaRange_nonempty (φ : ℝ) :
    (Set.range (fun t : Translations => placementArea t φ)).Nonempty := by
  exact ⟨placementArea (0, 0) φ, ⟨(0, 0), rfl⟩⟩

/-- Real-area nonnegativity supplies the honest bounded-below hypothesis. -/
theorem propagation_areaRange_bddBelow (φ : ℝ) :
    BddBelow (Set.range (fun t : Translations => placementArea t φ)) := by
  refine ⟨0, ?_⟩
  rintro y ⟨t, rfl⟩
  exact H_nonnegative t.1 t.2 φ

/-- An all-translation pointwise bound is a lower bound of the nonempty range.
`le_csInf` uses nonemptiness; the threshold itself is a lower-bound witness. -/
theorem regionalPremise_implies_G (lo hi L : ℝ)
    (hsource : RegionalPremise lo hi L) (ψ : ℝ) (hψ : ψ ∈ Set.Icc lo hi) :
    L ≤ G ψ := by
  apply le_csInf (propagation_areaRange_nonempty ψ)
  rintro y ⟨t, rfl⟩
  exact (regionalPremise_iff lo hi L).mp hsource t.1 t.2 ψ hψ

theorem propagation_G_le_H (t3 t5 : Plane) (φ : ℝ) : G φ ≤ H t3 t5 φ := by
  exact csInf_le (propagation_areaRange_bddBelow φ) ⟨(t3, t5), rfl⟩

/-- This is the concrete nearest-closed-interval form of cor:gluing. -/
theorem conditional_propagation_closedInterval (lo hi L : ℝ) (h : lo ≤ hi)
    (hLip : ∀ φ ψ : ℝ, |min L3 (G φ) - min L3 (G ψ)| ≤ C * |φ - ψ|)
    (hsource : RegionalPremise lo hi L) (φ : ℝ) :
    min L L3 - C * closedIntervalDist lo hi φ ≤ G φ := by
  exact conditional_propagation_pointwise G L3 L C (Set.Icc lo hi) hLip
    (regionalPremise_implies_G lo hi L hsource) φ (intervalClamp lo hi φ)
    (intervalClamp_mem lo hi φ h)

/-- The paper's infDist spelling is conditional on the stated library bridge. -/
theorem conditional_propagation_metric (hmetric : MetricIntervalDistanceDuty)
    (lo hi L : ℝ) (h : lo ≤ hi)
    (hLip : ∀ φ ψ : ℝ, |min L3 (G φ) - min L3 (G ψ)| ≤ C * |φ - ψ|)
    (hsource : RegionalPremise lo hi L) (φ : ℝ) :
    min L L3 - C * Metric.infDist φ (Set.Icc lo hi) ≤ G φ := by
  rw [hmetric lo hi h φ]
  exact conditional_propagation_closedInterval lo hi L h hLip hsource φ

theorem halo_radius_balance (L : ℝ) : C * ((L - tau) / C) = L - tau := by
  have hC : C ≠ 0 := ne_of_gt constants_order.2.2.2
  field_simp [hC]

theorem conditional_closed_halo (lo hi L : ℝ) (h : lo ≤ hi) (hcap : L ≤ L3)
    (hLip : ∀ φ ψ : ℝ, |min L3 (G φ) - min L3 (G ψ)| ≤ C * |φ - ψ|)
    (hsource : RegionalPremise lo hi L) (φ : ℝ)
    (hd : closedIntervalDist lo hi φ ≤ (L - tau) / C) : tau ≤ G φ := by
  have hp := conditional_propagation_closedInterval lo hi L h hLip hsource φ
  rw [min_eq_left hcap] at hp
  have hc := mul_le_mul_of_nonneg_left hd (le_of_lt constants_order.2.2.2)
  rw [halo_radius_balance] at hc
  linarith

theorem conditional_strict_halo (lo hi L : ℝ) (h : lo ≤ hi) (hcap : L ≤ L3)
    (hLip : ∀ φ ψ : ℝ, |min L3 (G φ) - min L3 (G ψ)| ≤ C * |φ - ψ|)
    (hsource : RegionalPremise lo hi L) (φ : ℝ)
    (hd : closedIntervalDist lo hi φ < (L - tau) / C) : tau < G φ := by
  have hp := conditional_propagation_closedInterval lo hi L h hLip hsource φ
  rw [min_eq_left hcap] at hp
  have hc := mul_lt_mul_of_pos_left hd constants_order.2.2.2
  rw [halo_radius_balance] at hc
  linarith

/-- Equality belongs to the conservative envelope, never to actual G or H. -/
theorem halo_envelope_at_radius (L : ℝ) :
    L - C * ((L - tau) / C) = tau := by
  rw [halo_radius_balance]
  ring

theorem halo_envelope_threshold_iff (L d : ℝ) :
    tau ≤ L - C * d ↔ d ≤ (L - tau) / C := by
  constructor
  · intro h
    have hm : C * d ≤ C * ((L - tau) / C) := by
      rw [halo_radius_balance]
      linarith
    exact (mul_le_mul_iff_right₀ constants_order.2.2.2).mp (by simpa only [mul_comm C] using hm)
  · intro h
    have hm := mul_le_mul_of_nonneg_left h (le_of_lt constants_order.2.2.2)
    rw [halo_radius_balance] at hm
    linarith

theorem halo_envelope_strict_iff (L d : ℝ) :
    tau < L - C * d ↔ d < (L - tau) / C := by
  constructor
  · intro h
    have hm : C * d < C * ((L - tau) / C) := by
      rw [halo_radius_balance]
      linarith
    exact (mul_lt_mul_iff_right₀ constants_order.2.2.2).mp (by simpa only [mul_comm C] using hm)
  · intro h
    have hm := mul_lt_mul_of_pos_left h constants_order.2.2.2
    rw [halo_radius_balance] at hm
    linarith

end Partials.Covering
end
