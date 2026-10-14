import Partials.Covering.Propagation
import Partials.Covering.RegionalData

noncomputable section

/-! R4 BLIND / UNCHECKED SOURCE. This is the conditional application of
main.tex prop:halos, eq:halo-union, eq:strict-halos, eq:gap-widths and
eq:covered-lengths. The clipped modulus and inherited numerical geometry are
arguments. The exact three-halo union fails to cover the fundamental interval.
Neither complement below asserts failure of the area threshold in a gap.
-/
namespace Partials.Covering

def closedHalos : Set ℝ :=
  Set.Icc 0 aZero ∪ Set.Icc aTen bTen ∪ Set.Icc aEnd fundamentalEnd

def strictHalos : Set ℝ :=
  Set.Ico 0 aZero ∪ Set.Ioo aTen bTen ∪ Set.Ioc aEnd fundamentalEnd

theorem closedHalos_isClosed : IsClosed closedHalos := by
  exact (isClosed_Icc.union isClosed_Icc).union isClosed_Icc

theorem closedHalos_distance_iff (φ : ℝ) :
    φ ∈ closedHalos ↔ φ ∈ fundamentalInterval ∧
      (closedIntervalDist 0 (3 / 1250) φ ≤ etaZero ∨
        closedIntervalDist (99 / 10000) (101 / 10000) φ ≤ etaTen ∨
        closedIntervalDist (fundamentalEnd - 1 / 125) fundamentalEnd φ ≤ etaEnd) := by
  rcases regional_intervals_nonempty with ⟨hi0, hi10, hie⟩
  rcases eta_positive_and_small with ⟨h0, h10, he⟩
  rcases halo_endpoints_order with ⟨ho0, ho1, ho10, ho2, hoe⟩
  constructor
  · intro hφ
    simp only [closedHalos, Set.mem_union, Set.mem_Icc] at hφ
    rcases hφ with (hφ0 | hφ10) | hφe
    · refine ⟨⟨hφ0.1, ?_⟩, Or.inl ?_⟩
      · linarith [hφ0.2]
      · apply (closedIntervalDist_le_iff 0 (3 / 1250) φ etaZero hi0
          (le_of_lt h0.1)).mpr
        dsimp [aZero] at hφ0
        constructor <;> linarith [hφ0.1, hφ0.2]
    · refine ⟨⟨?_, ?_⟩, Or.inr (Or.inl ?_)⟩
      · linarith [hφ10.1]
      · linarith [hφ10.2]
      · apply (closedIntervalDist_le_iff (99 / 10000) (101 / 10000) φ etaTen
          hi10 (le_of_lt h10.1)).mpr
        dsimp [aTen, bTen] at hφ10
        exact hφ10
    · refine ⟨⟨?_, hφe.2⟩, Or.inr (Or.inr ?_)⟩
      · linarith [hφe.1]
      · apply (closedIntervalDist_le_iff (fundamentalEnd - 1 / 125)
          fundamentalEnd φ etaEnd hie (le_of_lt he.1)).mpr
        dsimp [aEnd] at hφe
        constructor <;> linarith [hφe.1, hφe.2]
  · rintro ⟨hdom, hd0 | hd10 | hde⟩
    · have hx := (closedIntervalDist_le_iff 0 (3 / 1250) φ etaZero hi0
        (le_of_lt h0.1)).mp hd0
      exact Or.inl (Or.inl ⟨hdom.1, hx.2⟩)
    · have hx := (closedIntervalDist_le_iff (99 / 10000) (101 / 10000) φ etaTen
        hi10 (le_of_lt h10.1)).mp hd10
      exact Or.inl (Or.inr hx)
    · have hx := (closedIntervalDist_le_iff (fundamentalEnd - 1 / 125)
        fundamentalEnd φ etaEnd hie (le_of_lt he.1)).mp hde
      exact Or.inr ⟨hx.1, hdom.2⟩

theorem strictHalos_distance_iff (φ : ℝ) :
    φ ∈ strictHalos ↔ φ ∈ fundamentalInterval ∧
      (closedIntervalDist 0 (3 / 1250) φ < etaZero ∨
        closedIntervalDist (99 / 10000) (101 / 10000) φ < etaTen ∨
        closedIntervalDist (fundamentalEnd - 1 / 125) fundamentalEnd φ < etaEnd) := by
  rcases regional_intervals_nonempty with ⟨hi0, hi10, hie⟩
  rcases eta_positive_and_small with ⟨h0, h10, he⟩
  rcases halo_endpoints_order with ⟨ho0, ho1, ho10, ho2, hoe⟩
  constructor
  · intro hφ
    simp only [strictHalos, Set.mem_union, Set.mem_Ico, Set.mem_Ioo, Set.mem_Ioc] at hφ
    rcases hφ with (hφ0 | hφ10) | hφe
    · refine ⟨⟨hφ0.1, ?_⟩, Or.inl ?_⟩
      · linarith [hφ0.2]
      · apply (closedIntervalDist_lt_iff 0 (3 / 1250) φ etaZero hi0 h0.1).mpr
        dsimp [aZero] at hφ0
        constructor <;> linarith [hφ0.1, hφ0.2]
    · refine ⟨⟨?_, ?_⟩, Or.inr (Or.inl ?_)⟩
      · linarith [hφ10.1]
      · linarith [hφ10.2]
      · apply (closedIntervalDist_lt_iff (99 / 10000) (101 / 10000) φ etaTen
          hi10 h10.1).mpr
        dsimp [aTen, bTen] at hφ10
        exact hφ10
    · refine ⟨⟨?_, hφe.2⟩, Or.inr (Or.inr ?_)⟩
      · linarith [hφe.1]
      · apply (closedIntervalDist_lt_iff (fundamentalEnd - 1 / 125)
          fundamentalEnd φ etaEnd hie he.1).mpr
        dsimp [aEnd] at hφe
        constructor <;> linarith [hφe.1, hφe.2]
  · rintro ⟨hdom, hd0 | hd10 | hde⟩
    · have hx := (closedIntervalDist_lt_iff 0 (3 / 1250) φ etaZero hi0 h0.1).mp hd0
      exact Or.inl (Or.inl ⟨hdom.1, hx.2⟩)
    · have hx := (closedIntervalDist_lt_iff (99 / 10000) (101 / 10000) φ etaTen
        hi10 h10.1).mp hd10
      exact Or.inl (Or.inr hx)
    · have hx := (closedIntervalDist_lt_iff (fundamentalEnd - 1 / 125)
        fundamentalEnd φ etaEnd hie he.1).mp hde
      exact Or.inr ⟨hx.1, hdom.2⟩

theorem conditional_regional_closedHalos_G
    (hLip : ∀ φ ψ : ℝ, |min L3 (G φ) - min L3 (G ψ)| ≤ C * |φ - ψ|)
    (hp : InheritedRegionalPremises) (φ : ℝ) (hφ : φ ∈ closedHalos) :
    tau ≤ G φ := by
  rcases regional_intervals_nonempty with ⟨hi0, hi10, hie⟩
  rcases regional_constant_order with ⟨h0, h10, he⟩
  rcases (closedHalos_distance_iff φ).mp hφ with ⟨hdom, hd0 | hd10 | hde⟩
  · exact conditional_closed_halo 0 (3 / 1250) Lzero hi0 (le_of_lt h0.2)
      hLip hp.1 φ hd0
  · exact conditional_closed_halo (99 / 10000) (101 / 10000) Lten hi10
      (le_of_lt h10.2) hLip hp.2.1 φ hd10
  · exact conditional_closed_halo (fundamentalEnd - 1 / 125) fundamentalEnd Lend
      hie (le_of_lt he.2) hLip hp.2.2 φ hde

theorem conditional_regional_strictHalos_G
    (hLip : ∀ φ ψ : ℝ, |min L3 (G φ) - min L3 (G ψ)| ≤ C * |φ - ψ|)
    (hp : InheritedRegionalPremises) (φ : ℝ) (hφ : φ ∈ strictHalos) :
    tau < G φ := by
  rcases regional_intervals_nonempty with ⟨hi0, hi10, hie⟩
  rcases regional_constant_order with ⟨h0, h10, he⟩
  rcases (strictHalos_distance_iff φ).mp hφ with ⟨hdom, hd0 | hd10 | hde⟩
  · exact conditional_strict_halo 0 (3 / 1250) Lzero hi0 (le_of_lt h0.2)
      hLip hp.1 φ hd0
  · exact conditional_strict_halo (99 / 10000) (101 / 10000) Lten hi10
      (le_of_lt h10.2) hLip hp.2.1 φ hd10
  · exact conditional_strict_halo (fundamentalEnd - 1 / 125) fundamentalEnd Lend
      hie (le_of_lt he.2) hLip hp.2.2 φ hde

theorem conditional_regional_closedHalos_H
    (hLip : ∀ φ ψ : ℝ, |min L3 (G φ) - min L3 (G ψ)| ≤ C * |φ - ψ|)
    (hp : InheritedRegionalPremises) (t3 t5 : Plane) (φ : ℝ)
    (hφ : φ ∈ closedHalos) : tau ≤ H t3 t5 φ :=
  (conditional_regional_closedHalos_G hLip hp φ hφ).trans (propagation_G_le_H t3 t5 φ)

theorem conditional_regional_strictHalos_H
    (hLip : ∀ φ ψ : ℝ, |min L3 (G φ) - min L3 (G ψ)| ≤ C * |φ - ψ|)
    (hp : InheritedRegionalPremises) (t3 t5 : Plane) (φ : ℝ)
    (hφ : φ ∈ strictHalos) : tau < H t3 t5 φ :=
  (conditional_regional_strictHalos_G hLip hp φ hφ).trans_le (propagation_G_le_H t3 t5 φ)

/-- Fundamental endpoints are included in the strict guarantee. -/
theorem fundamental_endpoints_in_strictHalos :
    (0 : ℝ) ∈ strictHalos ∧ fundamentalEnd ∈ strictHalos := by
  rcases halo_endpoints_order with ⟨ho0, ho1, ho10, ho2, hoe⟩
  constructor
  · exact Or.inl (Or.inl ⟨le_rfl, ho0⟩)
  · exact Or.inr ⟨hoe, le_rfl⟩

/-- These four faces are excluded only from the conservative strict guarantee;
there is no assertion of equality for actual G or H at any face. -/
theorem halo_outer_faces :
    (aZero ∈ closedHalos ∧ aZero ∉ strictHalos) ∧
    (aTen ∈ closedHalos ∧ aTen ∉ strictHalos) ∧
    (bTen ∈ closedHalos ∧ bTen ∉ strictHalos) ∧
    (aEnd ∈ closedHalos ∧ aEnd ∉ strictHalos) := by
  rcases halo_endpoints_order with ⟨ho0, ho1, ho10, ho2, hoe⟩
  simp only [closedHalos, strictHalos, Set.mem_union, Set.mem_Icc,
    Set.mem_Ico, Set.mem_Ioo, Set.mem_Ioc]
  constructor
  · constructor
    · exact Or.inl (Or.inl ⟨le_of_lt ho0, le_rfl⟩)
    · rintro ((h | h) | h) <;> linarith [h.1, h.2]
  constructor
  · constructor
    · exact Or.inl (Or.inr ⟨le_rfl, le_of_lt ho10⟩)
    · rintro ((h | h) | h) <;> linarith [h.1, h.2]
  constructor
  · constructor
    · exact Or.inl (Or.inr ⟨le_of_lt ho10, le_rfl⟩)
    · rintro ((h | h) | h) <;> linarith [h.1, h.2]
  · constructor
    · exact Or.inr ⟨le_rfl, le_of_lt hoe⟩
    · rintro ((h | h) | h) <;> linarith [h.1, h.2]

theorem closedHalos_complement :
    fundamentalInterval \ closedHalos = Set.Ioo aZero aTen ∪ Set.Ioo bTen aEnd := by
  rcases halo_endpoints_order with ⟨ho0, ho1, ho10, ho2, hoe⟩
  ext φ
  simp only [fundamentalInterval, closedHalos, Set.mem_diff, Set.mem_union,
    Set.mem_Icc, Set.mem_Ioo]
  constructor
  · rintro ⟨hdom, hn⟩
    have hleft : aZero < φ := by
      by_contra hx
      exact hn (Or.inl (Or.inl ⟨hdom.1, le_of_not_gt hx⟩))
    by_cases hx : φ < aTen
    · exact Or.inl ⟨hleft, hx⟩
    · have hmid : bTen < φ := by
        by_contra hx'
        exact hn (Or.inl (Or.inr ⟨le_of_not_gt hx, le_of_not_gt hx'⟩))
      have hright : φ < aEnd := by
        by_contra hx'
        exact hn (Or.inr ⟨le_of_not_gt hx', hdom.2⟩)
      exact Or.inr ⟨hmid, hright⟩
  · rintro (hgap | hgap)
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · linarith [hgap.1]
      · linarith [hgap.2]
      · rintro ((h | h) | h) <;> linarith [hgap.1, hgap.2, h.1, h.2]
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · linarith [hgap.1]
      · linarith [hgap.2]
      · rintro ((h | h) | h) <;> linarith [hgap.1, hgap.2, h.1, h.2]

theorem strictHalos_complement :
    fundamentalInterval \ strictHalos = Set.Icc aZero aTen ∪ Set.Icc bTen aEnd := by
  rcases halo_endpoints_order with ⟨ho0, ho1, ho10, ho2, hoe⟩
  ext φ
  simp only [fundamentalInterval, strictHalos, Set.mem_diff, Set.mem_union,
    Set.mem_Icc, Set.mem_Ico, Set.mem_Ioo, Set.mem_Ioc]
  constructor
  · rintro ⟨hdom, hn⟩
    have hleft : aZero ≤ φ := by
      by_contra hx
      exact hn (Or.inl (Or.inl ⟨hdom.1, lt_of_not_ge hx⟩))
    by_cases hx : φ ≤ aTen
    · exact Or.inl ⟨hleft, hx⟩
    · have hmid : bTen ≤ φ := by
        by_contra hx'
        exact hn (Or.inl (Or.inr ⟨lt_of_not_ge hx, lt_of_not_ge hx'⟩))
      have hright : φ ≤ aEnd := by
        by_contra hx'
        exact hn (Or.inr ⟨lt_of_not_ge hx', hdom.2⟩)
      exact Or.inr ⟨hmid, hright⟩
  · rintro (hgap | hgap)
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · linarith [hgap.1]
      · linarith [hgap.2]
      · rintro ((h | h) | h) <;> linarith [hgap.1, hgap.2, h.1, h.2]
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · linarith [hgap.1]
      · linarith [hgap.2]
      · rintro ((h | h) | h) <;> linarith [hgap.1, hgap.2, h.1, h.2]

/-- A witness in a positive gap establishes only missing coverage. -/
theorem closedHalos_do_not_cover : ¬ fundamentalInterval ⊆ closedHalos := by
  intro hcover
  have hgap : (aZero + aTen) / 2 ∈ Set.Ioo aZero aTen := by
    constructor <;> linarith [halo_endpoints_order.2.1]
  have hmissing : (aZero + aTen) / 2 ∈ fundamentalInterval \ closedHalos := by
    rw [closedHalos_complement]
    exact Or.inl hgap
  exact hmissing.2 (hcover hmissing.1)

/-- Lebesgue measure, beyond endpoint bookkeeping. The disjointness follows
from the strictly positive gap widths, and every interval is measurable. -/
theorem closedHalos_volume :
    MeasureTheory.volume closedHalos =
      ENNReal.ofReal (aZero - 0) + ENNReal.ofReal (bTen - aTen) +
        ENNReal.ofReal (fundamentalEnd - aEnd) := by
  rcases halo_endpoints_order with ⟨ho0, ho1, ho10, ho2, hoe⟩
  have h01 : Disjoint (Set.Icc (0 : ℝ) aZero) (Set.Icc aTen bTen) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    linarith [hx.2, hy.1]
  have h02 : Disjoint (Set.Icc (0 : ℝ) aZero ∪ Set.Icc aTen bTen)
      (Set.Icc aEnd fundamentalEnd) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    rcases hx with hx | hx <;> linarith [hx.2, hy.1]
  rw [closedHalos, MeasureTheory.measure_union h02 measurableSet_Icc,
    MeasureTheory.measure_union h01 measurableSet_Icc,
    Real.volume_Icc, Real.volume_Icc, Real.volume_Icc]

theorem closedHalos_real_length :
    (MeasureTheory.volume closedHalos).toReal = coveredLength := by
  rcases halo_endpoints_order with ⟨ho0, ho1, ho10, ho2, hoe⟩
  rw [closedHalos_volume,
    ENNReal.toReal_add (by simp) (by simp),
    ENNReal.toReal_add (by simp) (by simp),
    ENNReal.toReal_ofReal (by linarith : 0 ≤ aZero - 0),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (le_of_lt ho10)),
    ENNReal.toReal_ofReal (sub_nonneg.mpr (le_of_lt hoe))]
  exact covered_component_lengths

/-- A finite family would close the global bound only if it actually covers
the fundamental interval and the independent geometric angle reduction holds.
This theorem is not instantiated by the three noncovering halos above. -/
theorem conditional_finite_full_coverage_M {ι : Type*} [Fintype ι]
    (lo hi lower : ι → ℝ) (hn : ∀ i, lo i ≤ hi i)
    (hsource : ∀ i, RegionalPremise (lo i) (hi i) (lower i))
    (hLip : ∀ φ ψ : ℝ, |min L3 (G φ) - min L3 (G ψ)| ≤ C * |φ - ψ|)
    (hcover : ∀ φ ∈ fundamentalInterval, ∃ i,
      closedIntervalDist (lo i) (hi i) φ ≤ (min (lower i) L3 - tau) / C)
    (hreduction : ∀ φ : ℝ, ∃ ψ ∈ fundamentalInterval, G φ = G ψ) :
    tau ≤ M := by
  have hfund : ∀ φ ∈ fundamentalInterval, tau ≤ G φ := by
    intro φ hφ
    rcases hcover φ hφ with ⟨i, hiφ⟩
    have hsrc : RegionalPremise (lo i) (hi i) (min (lower i) L3) := by
      apply (regionalPremise_iff _ _ _).mpr
      intro t3 t5 ψ hψ
      exact (min_le_left _ _).trans
        ((regionalPremise_iff _ _ _).mp (hsource i) t3 t5 ψ hψ)
    exact conditional_closed_halo (lo i) (hi i) (min (lower i) L3) (hn i)
      (min_le_right _ _) hLip hsrc φ hiφ
  apply le_csInf (show (Set.range G).Nonempty from ⟨G 0, ⟨0, rfl⟩⟩)
  rintro y ⟨φ, rfl⟩
  rcases hreduction φ with ⟨ψ, hψ, hEq⟩
  rw [hEq]
  exact hfund ψ hψ

/-- This scalar adapter requires a nonempty cover family and the independently
derived universal-cover comparison. It imports no desired threshold conclusion. -/
theorem conditional_M_lower_to_aLeb
    (hM : tau ≤ M)
    (hne : (setArea '' {U : Set Plane | UniversalCover U}).Nonempty)
    (hcomparison : ∀ U : Set Plane, UniversalCover U → M ≤ setArea U) :
    tau ≤ aLeb := by
  apply le_csInf hne
  rintro y ⟨U, hU, rfl⟩
  exact hM.trans (hcomparison U hU)

theorem conditional_finite_full_coverage {ι : Type*} [Fintype ι]
    (lo hi lower : ι → ℝ) (hn : ∀ i, lo i ≤ hi i)
    (hsource : ∀ i, RegionalPremise (lo i) (hi i) (lower i))
    (hLip : ∀ φ ψ : ℝ, |min L3 (G φ) - min L3 (G ψ)| ≤ C * |φ - ψ|)
    (hcover : ∀ φ ∈ fundamentalInterval, ∃ i,
      closedIntervalDist (lo i) (hi i) φ ≤ (min (lower i) L3 - tau) / C)
    (hreduction : ∀ φ : ℝ, ∃ ψ ∈ fundamentalInterval, G φ = G ψ)
    (hne : (setArea '' {U : Set Plane | UniversalCover U}).Nonempty)
    (hcomparison : ∀ U : Set Plane, UniversalCover U → M ≤ setArea U) :
    tau ≤ M ∧ tau ≤ aLeb := by
  have hM := conditional_finite_full_coverage_M lo hi lower hn hsource hLip hcover hreduction
  exact ⟨hM, conditional_M_lower_to_aLeb hM hne hcomparison⟩

end Partials.Covering
end
