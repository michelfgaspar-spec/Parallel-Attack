import Partials.Covering.Geometry

open scoped ENNReal

noncomputable section

namespace Partials.Covering

/-- OPEN analytic inputs, independently stated from all placement bounds.
π lower is the Lucas enclosure; arcsin lower is its elementary integral
inequality. No requested area/confinement conclusion occurs here. -/
structure RationalAnalyticDuty : Prop where
  pi_lower : (333 : ℝ) / 106 < Real.pi
  arcsin_lower : ∀ z : ℝ, 0 ≤ z → z < 1 → z ≤ Real.arcsin z

/-- P1 discharges the exact analytic enclosure and arcsine inequality from
checked scalar library results; it establishes no disk-hull area formula. -/
theorem rationalAnalytic_verified : RationalAnalyticDuty := by
  constructor
  · linarith [Real.pi_gt_d6]
  · intro z hz hz1
    have h := Real.sin_le (Real.arcsin_nonneg.mpr hz)
    rwa [Real.sin_arcsin (by linarith) (le_of_lt hz1)] at h

/-- OPEN rotation/area bridge for arbitrary two centered disks. -/
def DiskPairRadialAreaDuty : Prop :=
  ∀ R r : ℝ, ∀ t : Plane,
    setArea (convexHull ℝ (disk 0 R ∪ disk t r)) = diskHullArea R r ‖t‖

/-- OPEN compact-disk-hull finiteness, independently of the area formula. -/
def DiskHullFiniteDuty : Prop :=
  ∀ R r d : ℝ, MeasureTheory.volume (diskHull R r d) ≠ ∞

theorem cutoff_radicands :
    d3 ^ 2 - ((1 / 2 : ℝ) - r3) ^ 2 = 4879 / 250000 ∧
    d5 ^ 2 - ((1 / 2 : ℝ) - r5) ^ 2 = 1856 / 250000 := by
  norm_num [d3, d5, r3, r5]

theorem rational_cutoff_sums :
    (35637993 : ℝ) / 53000000 + 701181 / 20000000 + 160889 / 1250000 = L3 ∧
    (39516777 : ℝ) / 53000000 + 82303 / 11250000 + 20941 / 250000 = L5 := by
  norm_num [L3, L5]

theorem exact_confinement_margins :
    L3 - tau = 71453 / 42400000 ∧
    L5 - tau = 5197841 / 2385000000 ∧
    L5 - L3 = 4714439 / 9540000000 := by
  norm_num [L3, L5, tau]

theorem sqrt_cutoff3_strict :
    (349 : ℝ) / 2500 < Real.sqrt (d3 ^ 2 - ((1 / 2 : ℝ) - r3) ^ 2) := by
  have h0 : (0 : ℝ) ≤ d3 ^ 2 - ((1 / 2 : ℝ) - r3) ^ 2 := by
    norm_num [d3, r3]
  have hs := Real.sq_sqrt h0
  have hn := Real.sqrt_nonneg (d3 ^ 2 - ((1 / 2 : ℝ) - r3) ^ 2)
  norm_num [d3, r3] at hs hn ⊢
  nlinarith

theorem sqrt_cutoff5_strict :
    (43 : ℝ) / 500 < Real.sqrt (d5 ^ 2 - ((1 / 2 : ℝ) - r5) ^ 2) := by
  have h0 : (0 : ℝ) ≤ d5 ^ 2 - ((1 / 2 : ℝ) - r5) ^ 2 := by
    norm_num [d5, r5]
  have hs := Real.sq_sqrt h0
  have hn := Real.sqrt_nonneg (d5 ^ 2 - ((1 / 2 : ℝ) - r5) ^ 2)
  norm_num [d5, r5] at hs hn ⊢
  nlinarith

theorem cutoff3_expression_strict (ha : RationalAnalyticDuty) :
    L3 < diskAreaExpression (1 / 2) r3 d3 := by
  have hp := ha.pi_lower
  have hi := ha.arcsin_lower ((39 : ℝ) / 80) (by norm_num) (by norm_num)
  have hs := sqrt_cutoff3_strict
  norm_num [L3, diskAreaExpression, r3, d3] at hs ⊢
  nlinarith

theorem cutoff5_expression_strict (ha : RationalAnalyticDuty) :
    L5 < diskAreaExpression (1 / 2) r5 d5 := by
  have hp := ha.pi_lower
  have hi := ha.arcsin_lower ((13 : ℝ) / 45) (by norm_num) (by norm_num)
  have hs := sqrt_cutoff5_strict
  norm_num [L5, diskAreaExpression, r5, d5] at hs ⊢
  nlinarith

theorem cutoff3_area_strict (ha : RationalAnalyticDuty)
    (hf : DiskHullAreaFormulaDuty) : L3 < diskHullArea (1 / 2) r3 d3 := by
  have he := (hf (1 / 2) r3 d3 (by norm_num [r3])
    (by norm_num [r3]) (by norm_num [d3])).2 (by norm_num [d3, r3])
  rw [he]
  exact cutoff3_expression_strict ha

theorem cutoff5_area_strict (ha : RationalAnalyticDuty)
    (hf : DiskHullAreaFormulaDuty) : L5 < diskHullArea (1 / 2) r5 d5 := by
  have he := (hf (1 / 2) r5 d5 (by norm_num [r5])
    (by norm_num [r5]) (by norm_num [d5])).2 (by norm_num [d5, r5])
  rw [he]
  exact cutoff5_expression_strict ha

theorem disk_pair_subset_triangle (hi : disk 0 r3 ⊆ B3)
    (t3 t5 : Plane) (φ : ℝ) :
    convexHull ℝ (disk 0 (1 / 2) ∪ disk t3 r3) ⊆ K t3 t5 φ := by
  apply convexHull_mono
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (Or.inl hx)
  · apply Or.inl
    apply Or.inr
    apply hi
    simpa [Partials.Interface.ClosedDisk, Partials.Interface.Translate] using hx

theorem disk_pair_subset_pentagon (he : EuclideanCoordinateDuty)
    (hi : disk 0 r5 ⊆ B5) (t3 t5 : Plane) (φ : ℝ) :
    convexHull ℝ (disk 0 (1 / 2) ∪ disk t5 r5) ⊆ K t3 t5 φ := by
  have hrot : disk 0 r5 ⊆ rotate φ '' B5 := by
    intro x hx
    have himg : x ∈ rotate φ '' disk 0 r5 := by
      rw [rotate_disk he]
      exact hx
    rcases himg with ⟨y, hy, hxy⟩
    exact ⟨y, hi hy, hxy⟩
  apply convexHull_mono
  intro x hx
  rcases hx with hx | hx
  · exact Or.inl (Or.inl hx)
  · apply Or.inr
    apply hrot
    simpa [Partials.Interface.ClosedDisk, Partials.Interface.Translate] using hx

/-- The two exact strict cutoff conclusions, derived from named geometric
and analytic duties. None of those duties assumes either cutoff conclusion. -/
theorem confinement_cutoffs (he : EuclideanCoordinateDuty)
    (ht : RadiusTrigonometryDuty) (ha : RationalAnalyticDuty)
    (hformula : DiskHullAreaFormulaDuty) (hradial : DiskPairRadialAreaDuty)
    (hregular : HullRegularityDuty) (hfinite : DiskHullFiniteDuty)
    (t3 t5 : Plane) (φ : ℝ) :
    (d3 ≤ ‖t3‖ → L3 < H t3 t5 φ) ∧ (d5 ≤ ‖t5‖ → L5 < H t3 t5 φ) := by
  obtain ⟨hi3, hi5⟩ := concrete_inner_disks he ht
  have hfK := (hregular t3 t5 φ).2.2
  constructor
  · intro hcut
    have hmono := diskHullArea_mono (by norm_num [r3] : (0 : ℝ) < r3)
      (by norm_num [r3] : r3 ≤ (1 / 2 : ℝ))
      (by norm_num [d3] : (0 : ℝ) ≤ d3) hcut (hfinite (1 / 2) r3 ‖t3‖)
    have hpair := setArea_mono (disk_pair_subset_triangle hi3 t3 t5 φ) hfK
    rw [hradial (1 / 2) r3 t3] at hpair
    exact lt_of_lt_of_le (cutoff3_area_strict ha hformula) (le_trans hmono hpair)
  · intro hcut
    have hmono := diskHullArea_mono (by norm_num [r5] : (0 : ℝ) < r5)
      (by norm_num [r5] : r5 ≤ (1 / 2 : ℝ))
      (by norm_num [d5] : (0 : ℝ) ≤ d5) hcut (hfinite (1 / 2) r5 ‖t5‖)
    have hpair := setArea_mono (disk_pair_subset_pentagon he hi5 t3 t5 φ) hfK
    rw [hradial (1 / 2) r5 t5] at hpair
    exact lt_of_lt_of_le (cutoff5_area_strict ha hformula) (le_trans hmono hpair)

/-- Public downstream API: strict exterior bounds remain an explicit supplied
premise here; confinement_cutoffs above is their conditional construction. -/
theorem low_area_strictQ
    (hc : ∀ t3 t5 φ, (d3 ≤ ‖t3‖ → L3 < H t3 t5 φ) ∧
      (d5 ≤ ‖t5‖ → L5 < H t3 t5 φ))
    {t : Translations} {φ : ℝ} (harea : placementArea t φ ≤ L3) : t ∈ strictQ := by
  constructor
  · by_contra h
    have hgt := (hc t.1 t.2 φ).1 (le_of_not_gt h)
    exact (not_lt_of_ge harea) hgt
  · by_contra h
    have hgt := (hc t.1 t.2 φ).2 (le_of_not_gt h)
    have horder : L3 < L5 := constants_order.2.2.1
    exact (not_lt_of_ge harea) (lt_trans horder hgt)

theorem exterior_of_not_Q
    (hc : ∀ t3 t5 φ, (d3 ≤ ‖t3‖ → L3 < H t3 t5 φ) ∧
      (d5 ≤ ‖t5‖ → L5 < H t3 t5 φ))
    {t : Translations} {φ : ℝ} (ht : t ∉ Q) : L3 < placementArea t φ := by
  by_cases h3 : ‖t.1‖ ≤ d3
  · have h5 : ¬ ‖t.2‖ ≤ d5 := fun h5 => ht ⟨h3, h5⟩
    have hgt := (hc t.1 t.2 φ).2 (le_of_lt (lt_of_not_ge h5))
    exact lt_trans constants_order.2.2.1 hgt
  · exact (hc t.1 t.2 φ).1 (le_of_lt (lt_of_not_ge h3))

theorem radial_all_translation_reduction
    (hc : ∀ t3 t5 φ, (d3 ≤ ‖t3‖ → L3 < H t3 t5 φ) ∧
      (d5 ≤ ‖t5‖ → L5 < H t3 t5 φ))
    (I : Set ℝ) (κ : ℝ) (hκ : κ ≤ L3)
    (hQ : ∀ t ∈ Q, ∀ φ ∈ I, κ ≤ placementArea t φ) :
    ∀ t : Translations, ∀ φ ∈ I, κ ≤ placementArea t φ := by
  intro t φ hφ
  by_cases ht : t ∈ Q
  · exact hQ t ht φ hφ
  · exact le_trans hκ (le_of_lt (exterior_of_not_Q hc ht))

theorem vertical_all_translation_reduction (he : EuclideanCoordinateDuty)
    (hc : ∀ t3 t5 φ, (d3 ≤ ‖t3‖ → L3 < H t3 t5 φ) ∧
      (d5 ≤ ‖t5‖ → L5 < H t3 t5 φ))
    (I : Set ℝ) (κ : ℝ) (hκ : κ ≤ L3)
    (hV : ∀ t ∈ verticalRectangle, ∀ φ ∈ I, κ ≤ placementArea t φ) :
    ∀ t : Translations, ∀ φ ∈ I, κ ≤ placementArea t φ := by
  apply radial_all_translation_reduction hc I κ hκ
  intro t ht φ hφ
  have hv : t ∈ verticalRectangle :=
    ⟨le_trans (coordinate_abs_le_norm he t.1) ht.1,
      le_trans (coordinate_abs_le_norm he t.2) ht.2⟩
  exact hV t hv φ hφ

theorem vertical_rectangle_domain_ratio :
    (((8 : ℝ) / 25) * (9 / 50)) / ((7 / 5) ^ 2) = 36 / 1225 := by norm_num

end Partials.Covering

end
