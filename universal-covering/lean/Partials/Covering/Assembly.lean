import Partials.Covering.Symmetry
import Partials.Covering.Confinement
import Partials.Covering.Modulus
import Partials.Covering.Halos
import Partials.Covering.RestrictedData
import Partials.Covering.ClassicalTargets

noncomputable section
namespace Partials.Covering

/-! Manuscript-facing source assembly. This proves only the displayed
implication from named, explicitly unfinished geometric imports. It asserts
no inhabitant of those inputs and no unconditional headline theorem. -/

def MainAnalyticTarget : Prop :=
  (∀ t3 t5 φ, (d3 ≤ ‖t3‖ → L3 < H t3 t5 φ) ∧
    (d5 ≤ ‖t5‖ → L5 < H t3 t5 φ)) ∧
  (∀ φ, ∃ t ∈ T, placementArea t φ = G φ ∧
    ∀ u : Translations, placementArea t φ ≤ placementArea u φ) ∧
  (∃ t ∈ T, ∃ φ ∈ fundamentalInterval, placementArea t φ = M ∧ G φ = M) ∧
  (∀ φ, clippedG φ = min L3 (F φ)) ∧ ClippedAngularModulus ∧
  (∀ t φ, placementArea t φ ≤ L3 → t ∈ strictQ) ∧
  tau < L3 ∧ L3 < L5

theorem exterior_cutoff_from_primitive_imports (he : EuclideanCoordinateDuty)
    (ht : RadiusTrigonometryDuty) (ha : RationalAnalyticDuty)
    (hf : DiskHullAreaFormulaDuty) (hr : DiskPairRadialAreaDuty)
    (c : CompactPlanarImports) (hrot : RotationContinuityDuty)
    (hfinite : DiskHullFiniteDuty) : ExteriorQCutoffDuty := by
  intro t hnot φ
  have hreg := hullRegularity_of_imports c hrot
  have hc := confinement_cutoffs he ht ha hf hr hreg hfinite
  exact le_of_lt (exterior_of_not_Q hc hnot)

theorem fundamental_representative_from_symmetry (he : EuclideanCoordinateDuty)
    (hb : CenteredBodySymmetryDuty) (hh : RigidHullTransportDuty)
    (ha : RigidAreaDuty) (hr : RealPeriodRepresentativeDuty) :
    FundamentalRepresentativeDuty :=
  G_fundamental_representative he hb hh ha hr

theorem universal_comparison_of_named_bridges (hn : UniversalNormalizationDuty)
    (hf : UniversalImageFiniteDuty) : M ≤ aLeb :=
  M_le_aLeb hn hf universal_cover_family_nonempty

theorem main_from_explicit_geometric_imports
    (he : EuclideanCoordinateDuty) (ht : RadiusTrigonometryDuty)
    (han : RationalAnalyticDuty) (hformula : DiskHullAreaFormulaDuty)
    (hradial : DiskPairRadialAreaDuty) (hfinite : DiskHullFiniteDuty)
    (c : CompactPlanarImports) (hrot : RotationContinuityDuty)
    (i : ClassicalAreaImports)
    (hcenters : CenterContainmentInputs) (hpoint : DiskPointAreaDuty)
    (hzero : ZeroHullInputs) (hdisk : EuclideanDiskAreaDuty)
    (b : QHullInputs) (hd : DiskInteriorDuty) (hpi : PiUpperDuty)
    (hb : CenteredBodySymmetryDuty) (hh : RigidHullTransportDuty)
    (har : RigidAreaDuty) (hr : RealPeriodRepresentativeDuty) : MainAnalyticTarget := by
  have hreg := hullRegularity_of_imports c hrot
  have hcut := confinement_cutoffs he ht han hformula hradial hreg hfinite
  have hcont := placement_continuity_of_body_inputs c hrot i b hd
  have hcoerc := coercivity_of_diskPoint c hrot hcenters hpoint
  have hzeroBound := zeroPlacementBound_of_inputs c hzero hdisk
  have hfund := fundamental_representative_from_symmetry he hb hh har hr
  have hext := exterior_cutoff_from_primitive_imports he ht han hformula hradial c hrot hfinite
  have hmod := clipped_modulus_of_geometric_imports c hrot i b hd hpi hext
  exact ⟨hcut, G_attained_on_T hcont hcoerc hzeroBound,
    M_attained_on_T_fundamental hcont hcoerc hzeroBound hfund,
    clipped_infimum_identity hext, hmod,
    fun t φ h => low_area_strictQ hcut h,
    constants_order.2.1, constants_order.2.2.1⟩

/-- P1 supplies seven checked scalar/topological primitive witnesses to the
original conditional assembly. The remaining geometric and area inputs are
still quantified hypotheses; no inhabitants or numerical coverage follow. -/
theorem main_from_remaining_geometric_imports
    (hformula : DiskHullAreaFormulaDuty) (hradial : DiskPairRadialAreaDuty)
    (hfinite : DiskHullFiniteDuty) (c : CompactPlanarImports)
    (i : ClassicalAreaImports) (hcenters : CenterContainmentInputs)
    (hpoint : DiskPointAreaDuty) (hzero : ZeroHullInputs)
    (hdisk : EuclideanDiskAreaDuty) (b : QHullInputs)
    (hb : CenteredBodySymmetryDuty) (hh : RigidHullTransportDuty)
    (har : RigidAreaDuty) : MainAnalyticTarget :=
  main_from_explicit_geometric_imports euclideanCoordinate_verified
    radiusTrigonometry_verified rationalAnalytic_verified hformula hradial hfinite
    c rotationContinuity_verified i hcenters hpoint hzero hdisk b
    diskInterior_verified piUpper_verified hb hh har realPeriodRepresentative_verified

/-- Conditional numerical application; these independent geometry and
inherited regional inputs do not supply a full angle cover. -/
theorem regional_application_from_main_source (hm : MainAnalyticTarget)
    (hp : InheritedRegionalPremises) (t3 t5 : Plane) (φ : ℝ) :
    (φ ∈ closedHalos → tau ≤ H t3 t5 φ) ∧
      (φ ∈ strictHalos → tau < H t3 t5 φ) := by
  have hmod := hm.2.2.2.2.1
  have hLip : ∀ φ ψ, |min L3 (G φ) - min L3 (G ψ)| ≤ C * |φ - ψ| := hmod
  exact ⟨conditional_regional_closedHalos_H hLip hp t3 t5 φ,
    conditional_regional_strictHalos_H hLip hp t3 t5 φ⟩

end Partials.Covering
end
