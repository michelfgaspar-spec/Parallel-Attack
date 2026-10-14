import Partials.Covering.Regularity

noncomputable section

/-! Uncompiled R4 source. Scalar/order consequences are proved here; each
missing geometric hypothesis is an explicitly named argument. In particular,
no theorem asserts the exact body's attainment merely from a record label. -/
namespace Partials.Covering

theorem placementArea_nonnegative (t : Translations) (φ : ℝ) :
    0 ≤ placementArea t φ := H_nonnegative t.1 t.2 φ

theorem placement_range_bddBelow (φ : ℝ) :
    BddBelow (Set.range (fun t : Translations => placementArea t φ)) := by
  refine ⟨0, ?_⟩
  rintro y ⟨t, rfl⟩
  exact placementArea_nonnegative t φ

theorem G_nonnegative (φ : ℝ) : 0 ≤ G φ := by
  apply le_csInf (Set.range_nonempty _)
  rintro y ⟨t, rfl⟩
  exact placementArea_nonnegative t φ

theorem G_le_placementArea (t : Translations) (φ : ℝ) :
    G φ ≤ placementArea t φ :=
  csInf_le (placement_range_bddBelow φ) (Set.mem_range_self t)

theorem G_le_H (t3 t5 : Plane) (φ : ℝ) : G φ ≤ H t3 t5 φ :=
  G_le_placementArea (t3, t5) φ

theorem G_range_bddBelow : BddBelow (Set.range G) := by
  refine ⟨0, ?_⟩
  rintro y ⟨φ, rfl⟩
  exact G_nonnegative φ

theorem M_nonnegative : 0 ≤ M := by
  apply le_csInf (Set.range_nonempty _)
  rintro y ⟨φ, rfl⟩
  exact G_nonnegative φ

theorem M_le_G (φ : ℝ) : M ≤ G φ :=
  csInf_le G_range_bddBelow (Set.mem_range_self φ)

theorem M_le_H (t3 t5 : Plane) (φ : ℝ) : M ≤ H t3 t5 φ :=
  le_trans (M_le_G φ) (G_le_H t3 t5 φ)

theorem Q_image_nonempty (φ : ℝ) :
    ((fun t : Translations => placementArea t φ) '' Q).Nonempty :=
  ⟨placementArea (0, 0) φ, ⟨(0, 0), zero_in_Q, rfl⟩⟩

theorem Q_image_bddBelow (φ : ℝ) :
    BddBelow ((fun t : Translations => placementArea t φ) '' Q) := by
  refine ⟨0, ?_⟩
  rintro y ⟨t, ht, rfl⟩
  exact placementArea_nonnegative t φ

theorem F_nonnegative (φ : ℝ) : 0 ≤ F φ := by
  apply le_csInf (Q_image_nonempty φ)
  rintro y ⟨t, ht, rfl⟩
  exact placementArea_nonnegative t φ

theorem F_le_placementArea {t : Translations} (ht : t ∈ Q) (φ : ℝ) :
    F φ ≤ placementArea t φ :=
  csInf_le (Q_image_bddBelow φ) ⟨t, ht, rfl⟩

theorem G_le_F (φ : ℝ) : G φ ≤ F φ := by
  apply le_csInf (Q_image_nonempty φ)
  rintro y ⟨t, ht, rfl⟩
  exact G_le_placementArea t φ

theorem T_eq_product_closedBalls :
    T = Metric.closedBall (0 : Plane) 3 ×ˢ Metric.closedBall (0 : Plane) 3 := by
  ext t
  simp [T, Metric.mem_closedBall, dist_eq_norm]

theorem Q_eq_product_closedBalls :
    Q = Metric.closedBall (0 : Plane) d3 ×ˢ Metric.closedBall (0 : Plane) d5 := by
  ext t
  simp [Q, Metric.mem_closedBall, dist_eq_norm]

theorem T_compact : IsCompact T := by
  rw [T_eq_product_closedBalls]
  exact (isCompact_closedBall (0 : Plane) 3).prod (isCompact_closedBall (0 : Plane) 3)

theorem Q_compact : IsCompact Q := by
  rw [Q_eq_product_closedBalls]
  exact (isCompact_closedBall (0 : Plane) d3).prod (isCompact_closedBall (0 : Plane) d5)

theorem fundamentalInterval_nonempty : fundamentalInterval.Nonempty := by
  refine ⟨0, ?_⟩
  constructor
  · exact le_refl _
  · unfold fundamentalEnd
    positivity

theorem fundamentalInterval_compact : IsCompact fundamentalInterval := isCompact_Icc

theorem pi_thirds_lt_three_halves : Real.pi / 3 < (3 / 2 : ℝ) := by
  have hpi := Real.pi_lt_four
  linarith

theorem exterior_T_large (hc : CoercivityDuty) {t : Translations}
    (ht : t ∉ T) (φ : ℝ) : (3 / 2 : ℝ) < placementArea t φ := by
  have hn : 3 < ‖t.1‖ ∨ 3 < ‖t.2‖ := by
    simpa only [T, Set.mem_setOf_eq, not_and_or, not_le] using ht
  have hm : 3 < max ‖t.1‖ ‖t.2‖ := by
    rcases hn with h | h
    · exact lt_of_lt_of_le h (le_max_left _ _)
    · exact lt_of_lt_of_le h (le_max_right _ _)
  have hl := hc t.1 t.2 φ
  change (3 / 2 : ℝ) < H t.1 t.2 φ
  linarith

/-- Generic compact minimization plus an exterior comparison. The premises
supply continuity, a compact nonempty set and a better anchor, not a minimizer
or an infimum equality. -/
theorem compact_minimum_global {α : Type*} [TopologicalSpace α]
    (f : α → ℝ) (S : Set α) (hS : IsCompact S) (hSne : S.Nonempty)
    (hf : ContinuousOn f S) (a : α) (ha : a ∈ S)
    (hexterior : ∀ x, x ∉ S → f a ≤ f x) :
    ∃ x ∈ S, ∀ y, f x ≤ f y := by
  rcases hS.exists_isMinOn hSne hf with ⟨x, hx, hmin⟩
  refine ⟨x, hx, ?_⟩
  intro y
  by_cases hy : y ∈ S
  · exact hmin hy
  · exact le_trans (hmin ha) (hexterior y hy)

theorem sInf_range_eq_of_global_minimum {α : Type*} (f : α → ℝ)
    (x : α) (hmin : ∀ y, f x ≤ f y) : sInf (Set.range f) = f x := by
  apply le_antisymm
  · apply csInf_le
    · refine ⟨f x, ?_⟩
      rintro z ⟨y, rfl⟩
      exact hmin y
    · exact Set.mem_range_self x
  · apply le_csInf ⟨f x, Set.mem_range_self x⟩
    rintro z ⟨y, rfl⟩
    exact hmin y

theorem G_attained_on_T (hcont : PlacementContinuityDuty)
    (hc : CoercivityDuty) (hz : ZeroPlacementBoundDuty) (φ : ℝ) :
    ∃ t ∈ T, placementArea t φ = G φ ∧
      ∀ u : Translations, placementArea t φ ≤ placementArea u φ := by
  have hslice : Continuous (fun t : Translations => placementArea t φ) := by
    change Continuous ((fun z : Translations × ℝ => placementArea z.1 z.2) ∘
      (fun t : Translations => (t, φ)))
    exact Continuous.comp hcont
      (show Continuous (fun t : Translations => (t, φ)) from
        continuous_id.prodMk continuous_const)
  have hext : ∀ t : Translations, t ∉ T →
      placementArea (0, 0) φ ≤ placementArea t φ := by
    intro t ht
    exact le_of_lt (lt_of_le_of_lt (hz φ)
      (lt_trans pi_thirds_lt_three_halves (exterior_T_large hc ht φ)))
  rcases compact_minimum_global (fun t : Translations => placementArea t φ) T T_compact ⟨(0, 0), zero_in_T⟩
    hslice.continuousOn (0, 0) zero_in_T hext with ⟨t, ht, hmin⟩
  refine ⟨t, ht, ?_, hmin⟩
  exact (sInf_range_eq_of_global_minimum (fun t : Translations => placementArea t φ) t hmin).symm

theorem F_attained_on_Q (hcont : PlacementContinuityDuty) (φ : ℝ) :
    ∃ t ∈ Q, placementArea t φ = F φ ∧
      ∀ u ∈ Q, placementArea t φ ≤ placementArea u φ := by
  have hslice : Continuous (fun t : Translations => placementArea t φ) := by
    change Continuous ((fun z : Translations × ℝ => placementArea z.1 z.2) ∘
      (fun t : Translations => (t, φ)))
    exact Continuous.comp hcont
      (show Continuous (fun t : Translations => (t, φ)) from
        continuous_id.prodMk continuous_const)
  rcases Q_compact.exists_isMinOn ⟨(0, 0), zero_in_Q⟩
      hslice.continuousOn with ⟨t, ht, hmin⟩
  refine ⟨t, ht, ?_, ?_⟩
  · apply le_antisymm
    · apply le_csInf (Q_image_nonempty φ)
      rintro y ⟨u, hu, rfl⟩
      exact hmin hu
    · exact F_le_placementArea ht φ
  · intro u hu
    exact hmin hu

/-- Exact value-preserving angular reduction. Geometry/symmetry author must
derive this from evenness and period 2π/15; it is not an assumption that M is
attained or that its infimum already equals the restricted infimum. -/
def FundamentalRepresentativeDuty : Prop :=
  ∀ φ : ℝ, ∃ ψ ∈ fundamentalInterval, G ψ = G φ

theorem M_eq_fundamental_infimum (hr : FundamentalRepresentativeDuty) :
    M = sInf (G '' fundamentalInterval) := by
  have hsets : Set.range G = G '' fundamentalInterval := by
    ext v
    constructor
    · rintro ⟨φ, rfl⟩
      rcases hr φ with ⟨ψ, hψ, hval⟩
      exact ⟨ψ, hψ, hval⟩
    · rintro ⟨ψ, hψ, rfl⟩
      exact Set.mem_range_self ψ
  exact congrArg sInf hsets

theorem M_attained_on_T_fundamental (hcont : PlacementContinuityDuty)
    (hc : CoercivityDuty) (hz : ZeroPlacementBoundDuty)
    (hr : FundamentalRepresentativeDuty) :
    ∃ t ∈ T, ∃ φ ∈ fundamentalInterval,
      placementArea t φ = M ∧ G φ = M := by
  let S : Set (Translations × ℝ) := T ×ˢ fundamentalInterval
  have hS : IsCompact S := T_compact.prod fundamentalInterval_compact
  have h0I : (0 : ℝ) ∈ fundamentalInterval := by
    constructor
    · exact le_rfl
    · unfold fundamentalEnd
      positivity
  have hSne : S.Nonempty := ⟨((0, 0), 0), zero_in_T, h0I⟩
  have hf : ContinuousOn (fun z : Translations × ℝ => placementArea z.1 z.2) S :=
    hcont.continuousOn
  rcases hS.exists_isMinOn (f := fun z : Translations × ℝ => placementArea z.1 z.2)
      hSne hf with ⟨z, hzS, hmin⟩
  have hmin_explicit : ∀ w : Translations × ℝ, w ∈ S →
      placementArea z.1 z.2 ≤ placementArea w.1 w.2 := by
    intro w hw
    exact hmin hw
  have hzT : z.1 ∈ T := hzS.1
  have hzI : z.2 ∈ fundamentalInterval := hzS.2
  have hminzero : placementArea z.1 z.2 ≤ placementArea (0, 0) z.2 :=
    hmin_explicit (((0 : Plane), (0 : Plane)), z.2) ⟨zero_in_T, hzI⟩
  have hglobalI : ∀ u : Translations, ∀ ψ ∈ fundamentalInterval,
      placementArea z.1 z.2 ≤ placementArea u ψ := by
    intro u ψ hψ
    by_cases hu : u ∈ T
    · exact hmin_explicit (u, ψ) ⟨hu, hψ⟩
    · have hsmall : placementArea z.1 z.2 < (3 / 2 : ℝ) :=
        lt_of_le_of_lt (le_trans hminzero (hz z.2)) pi_thirds_lt_three_halves
      exact le_of_lt (lt_trans hsmall (exterior_T_large hc hu ψ))
  have hG : ∀ ψ ∈ fundamentalInterval, placementArea z.1 z.2 ≤ G ψ := by
    intro ψ hψ
    apply le_csInf (Set.range_nonempty (fun u : Translations => placementArea u ψ))
    rintro v ⟨u, rfl⟩
    exact hglobalI u ψ hψ
  have hzG : placementArea z.1 z.2 = G z.2 :=
    le_antisymm (hG z.2 hzI) (G_le_placementArea z.1 z.2)
  have hminG : ∀ ψ : ℝ, G z.2 ≤ G ψ := by
    intro ψ
    rcases hr ψ with ⟨χ, hχ, hval⟩
    exact hzG.symm.le.trans ((hG χ hχ).trans_eq hval)
  have hM : M = G z.2 := sInf_range_eq_of_global_minimum G z.2 hminG
  exact ⟨z.1, hzT, z.2, hzI, hzG.trans hM.symm, hM.symm⟩

/-- Exterior lower bound only. Strict confinement supplies this after taking
the disjunction outside Q; an approached exterior infimum may equal L3. -/
def ExteriorQCutoffDuty : Prop :=
  ∀ t : Translations, t ∉ Q → ∀ φ, L3 ≤ placementArea t φ

theorem clipped_infimum_identity (hext : ExteriorQCutoffDuty) (φ : ℝ) :
    clippedG φ = min L3 (F φ) := by
  change min L3 (G φ) = min L3 (F φ)
  apply le_antisymm
  · exact min_le_min (le_refl L3) (G_le_F φ)
  · apply le_min (min_le_left _ _)
    apply le_csInf (Set.range_nonempty _)
    rintro v ⟨t, rfl⟩
    by_cases ht : t ∈ Q
    · exact le_trans (min_le_right _ _) (F_le_placementArea ht φ)
    · exact le_trans (min_le_left _ _) (hext t ht φ)

theorem low_global_minimizer_in_Q (hext : ExteriorQCutoffDuty)
    {t : Translations} {φ : ℝ} (hsmall : placementArea t φ < L3) : t ∈ Q := by
  by_contra ht
  exact (not_lt_of_ge (hext t ht φ)) hsmall

end Partials.Covering
end
