import Partials.Cap.Characters
import Partials.Cap.DataAdmissions
import Partials.Cap.TwoCosets
import Partials.Cap.LinkCertificate
import Partials.Cap.Targets

/-! Integrated conditional restricted conclusions. ExactH41AssemblyDuty and
ExactD82AssemblyDuty are unproved targets, never inputs to this assembly. -/
namespace Partials.Cap.Assembly

noncomputable section
open Partials.Cap
variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

theorem same_H_pair_safety {z : K} (hE : Order41SubgroupDuty (H41 z))
    (he : EulerCriterionDuty K) (hm : MinusOneSquareDuty K) : PairSafety (H41 z) := by
  intro a ha b hb hab
  exact same_order41_pair_cap hE he frobenius81_from_characteristic_three hm ha hb hab

theorem concrete_cap_reduction {z : K} (ha : ExponentActionDuty z)
    (hE : Order41SubgroupDuty (H41 z)) (he : EulerCriterionDuty K)
    (hm : MinusOneSquareDuty K) (T : Finset Vertex) :
    Cap (P (ExponentCoefficients z T)) ↔ Independent (discriminantHypergraph z) T :=
  cap_iff_hypergraph_independent z ha.coefficient_injective (order41_nonantipodal hE)
    (fun _ hx => order41_nonzero hE hx) (same_H_pair_safety hE he hm) T

theorem independent_upper_from_certificate {z : K} (ho : ThreeOrderDuty)
    (ha : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (hc : Certificate.RootedCertificate (discriminantHypergraph z) Admission.familyResidue)
    (hb : ∀ T ∈ Admission.familyResidue, T.card ≤ 5)
    (T : Finset Vertex) (hT : Independent (discriminantHypergraph z) T) : T.card ≤ 5 := by
  by_cases hne : T.Nonempty
  · obtain ⟨U, hroot, hcard, hind⟩ := nonempty_independent_root_normalization ho ha hf hne hT
    have hmem := (Certificate.residue_certificate_iff _ _ hc U).mpr ⟨hroot, hind⟩
    have hu := hb U hmem
    simpa [hcard] using hu
  · have hempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    simp [hempty]

theorem classification_data_from_certificate {z : K}
    (hc : Certificate.RootedCertificate (discriminantHypergraph z) Admission.familyResidue)
    (hs : Admission.RootedStatistics) : FiveClassificationDataDuty z := by
  have hsets : rootedFiveFamily (discriminantHypergraph z) 0 =
      Admission.familyResidue.filter (fun T => T.card = 5) := by
    ext T
    simp only [rootedFiveFamily, Finset.mem_filter, mem_fiveFamily]
    have hcriterion := Certificate.residue_certificate_iff
      (discriminantHypergraph z) Admission.familyResidue hc T
    constructor
    · rintro ⟨⟨hind, hcard⟩, hroot⟩
      exact ⟨hcriterion.mpr ⟨hroot, hind⟩, hcard⟩
    · rintro ⟨hmem, hcard⟩
      obtain ⟨hroot, hind⟩ := hcriterion.mp hmem
      exact ⟨⟨hind, hcard⟩, hroot⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [hsets]
    exact hs.2.2
  · exact ((Certificate.residue_certificate_iff _ _ hc witnessExponents).mp hs.2.1).2
  · decide

theorem maximum_five_H_from_named_inputs {z : K} (ho : ThreeOrderDuty)
    (ha : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (hE : Order41SubgroupDuty (H41 z)) (he : EulerCriterionDuty K)
    (hm : MinusOneSquareDuty K)
    (hc : Certificate.RootedCertificate (discriminantHypergraph z) Admission.familyResidue)
    (hs : Admission.RootedStatistics) : MaximumFive (H41 z) := by
  have hd := classification_data_from_certificate hc hs
  constructor
  · intro S hS
    let T := coefficientPreimage z S
    have hrec : ExponentCoefficients z T = S := coefficientPreimage_recovers_H_set z S hS.1
    have hind : Independent (discriminantHypergraph z) T :=
      (concrete_cap_reduction ha hE he hm T).mp (by simpa [hrec] using hS.2)
    have hbound := independent_upper_from_certificate ho ha hf hc hs.1 T hind
    have hcard : S.card = T.card := by simpa [hrec] using exponentCoefficient_image_card ha T
    simpa [hcard] using hbound
  · refine ⟨witnessCoefficients z, ⟨exponentCoefficients_subset_H z witnessExponents,
      (concrete_cap_reduction ha hE he hm _).mpr hd.witness_independent⟩, ?_⟩
    rw [witnessCoefficients, exponentCoefficient_image_card ha, hd.witness_card]

theorem hImages_eq_coefficientOrbit {z : K} (ha : ExponentActionDuty z) :
    Targets.hImages z = coefficientOrbit z := by
  simp only [Targets.hImages, coefficientOrbit, witnessOrbit, Finset.image_image]
  congr 1
  funext p
  exact (coefficient_action_formula ha p.1 p.2).symm

/-- Only library representation conversions; no point-count conclusion. -/
def CardinalRepresentationDuty (K : Type*) [Field K] [CharP K 3] [DecidableEq K] : Prop :=
  ∀ S : Finset K, Nat.card (↑S : Set K) = S.card ∧ (P S).ncard = Nat.card (P S)

theorem cardinal_representation_from_library : CardinalRepresentationDuty K := by
  intro S
  exact ⟨Nat.card_eq_finsetCard S, (Nat.card_coe_set_eq (P S)).symm⟩

theorem point_count_for_five [Fintype K] (hrep : CardinalRepresentationDuty K)
    (hfibre : NonzeroFibreCardDuty K) (hfield : Nat.card K = 6561)
    (S : Finset K) (hS : S.card = 5) : (P S).ncard = 32800 := by
  rw [(hrep S).2]
  change Nat.card (PSet (↑S : Set K)) = 32800
  rw [parabola_point_count hfibre (↑S : Set K), hfield, (hrep S).1, hS]

theorem H41_conclusion_from_named_inputs [Fintype K] {z : K}
    (ho : ThreeOrderDuty) (ha : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (hcycle : PrimeTranslationCycleDuty) (hhalf : AffineHalfPowerDuty) (hcomp : AffineCompositionDuty)
    (hE : Order41SubgroupDuty (H41 z)) (he : EulerCriterionDuty K) (hm : MinusOneSquareDuty K)
    (hc : Certificate.RootedCertificate (discriminantHypergraph z) Admission.familyResidue)
    (hs : Admission.RootedStatistics) (hrep : CardinalRepresentationDuty K)
    (hfibre : NonzeroFibreCardDuty K) (hfield : Nat.card K = 6561) : Targets.H41Conclusion z := by
  have hd := classification_data_from_certificate hc hs
  have hmax := maximum_five_H_from_named_inputs ho ha hf hE he hm hc hs
  have hwcard : (witnessCoefficients z).card = 5 := by
    rw [witnessCoefficients, exponentCoefficient_image_card ha, hd.witness_card]
  have hclass : ∀ S : Finset K, S ∈ Targets.hImages z ↔
      CapCoefficientSet (H41 z) S ∧ S.card = 5 := by
    intro S
    change S ∈ (↑(Targets.hImages z) : Set (Finset K)) ↔ _
    rw [hImages_eq_coefficientOrbit ha,
      coefficientOrbit_eq_maximizers_H ho ha hf hcycle hhalf hcomp hd (concrete_cap_reduction ha hE he hm)]
    rfl
  have hcount : (Targets.hImages z).card = 328 := by
    rw [hImages_eq_coefficientOrbit ha]
    exact coefficientOrbit_card ho ha hcomp hcycle hhalf hd
  have hparam : Function.Injective (Targets.hImage z) := by
    have h := displayed_coefficient_sets_distinct ho ha hcomp hcycle hhalf hd
    intro p q hpq
    apply h
    simpa [coefficient_action_formula ha, Targets.hImage] using hpq
  exact ⟨hmax, ⟨exponentCoefficients_subset_H z _,
      (concrete_cap_reduction ha hE he hm _).mpr hd.witness_independent⟩,
    hwcard, point_count_for_five hrep hfibre hfield _ hwcard, hclass, hcount, hparam⟩

theorem mixed_pair_bridge_from_algebra {z : K} (hE : Order41SubgroupDuty (H41 z))
    (he : EulerCriterionDuty K) (hm : MinusOneSquareDuty K) (hg : ¬ Square (primitive z)) :
    MixedPairBridge z := by
  intro a ha b hb
  simpa [P, PSet, oppositeCoset, scaledCoefficientSet] using mixed_pair_not_cap hE he hm hg ha hb

theorem D82_conclusion_from_H [Fintype K] {z : K} (hg : primitive z ≠ 0)
    (hdis : Disjoint (H41 z) (oppositeCoset z)) (hmix : MixedPairBridge z)
    (hH : Targets.H41Conclusion z) (hrep : CardinalRepresentationDuty K)
    (hfibre : NonzeroFibreCardDuty K) (hfield : Nat.card K = 6561) : Targets.D82Conclusion z := by
  rcases hH with ⟨hmax, hw, hwcard, hwpoints, hclass, hcount, hdistinct⟩
  have hF : (↑(Targets.hImages z) : Set (Finset K)) = Maximizers (H41 z) := by
    ext S
    exact hclass S
  obtain ⟨hmaxD, hclassD, hcountD⟩ := two_coset_classification_transfer hg hmix hdis hmax _ hF hcount
  have hdFamily : Targets.dImages z = coefficientTwoClassFamily z (Targets.hImages z) := by rfl
  have hopp : (Targets.oppositeImages z).card = 328 := by
    rw [Targets.oppositeImages]
    change ((Targets.hImages z).image (scaleCoefficients (primitive z))).card = 328
    rw [Finset.card_image_of_injective _ (scaleCoefficients_injective hg), hcount]
  have hclasses : Disjoint (Targets.hImages z) (Targets.oppositeImages z) := by
    apply Finset.disjoint_left.mpr
    intro S hS hSG
    obtain ⟨T, hT, hTS⟩ := Finset.mem_image.mp hSG
    exact Set.disjoint_left.mp (maximizing_classes_disjoint hg hdis)
      ((hclass S).mp hS) ⟨T, (hclass T).mp hT, hTS⟩
  have hclassification : ∀ S : Finset K, S ∈ Targets.dImages z ↔
      CapCoefficientSet (domainD z) S ∧ S.card = 5 := by
    intro S
    change S ∈ (↑(Targets.dImages z) : Set (Finset K)) ↔ _
    rw [hdFamily, hclassD]
    rfl
  refine ⟨hmaxD, hclassification, hcount, hopp, hclasses, ?_, ?_⟩
  · simpa [hdFamily] using hcountD
  · intro S hS
    exact point_count_for_five hrep hfibre hfield S ((hclassification S).mp hS).2

theorem full_restricted_conclusions_from_explicit_imports [Fintype K] {z : K}
    (ho : ThreeOrderDuty) (ha : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (hcycle : PrimeTranslationCycleDuty) (hhalf : AffineHalfPowerDuty) (hcomp : AffineCompositionDuty)
    (hE : Order41SubgroupDuty (H41 z)) (he : EulerCriterionDuty K) (hm : MinusOneSquareDuty K)
    (hg : ¬ Square (primitive z)) (hd : Admission.ExactDataAcceptanceDuty z)
    (hrep : CardinalRepresentationDuty K) (hfibre : NonzeroFibreCardDuty K)
    (hfield : Nat.card K = 6561) : Targets.H41Conclusion z ∧ Targets.D82Conclusion z := by
  rcases hd with ⟨hShape, hArith, hRaw, hNatural, hResidue, hStats, hRow, hTable⟩
  have hc := Admission.rooted_certificate_from_actual_acceptance z hTable hResidue
  have hs := Admission.rooted_statistics_from_acceptance hStats
  have hH := H41_conclusion_from_named_inputs ho ha hf hcycle hhalf hcomp hE he hm hc hs hrep hfibre hfield
  have hcosets : Disjoint (H41 z) (oppositeCoset z) := by
    simpa [oppositeCoset, scaledCoefficientSet] using cosets_disjoint hE hg
  exact ⟨hH, D82_conclusion_from_H (nonsquare_ne_zero hg) hcosets
    (mixed_pair_bridge_from_algebra hE he hm hg) hH hrep hfibre hfield⟩

/-- The same headline conclusions with the proved finite multiplier and generic
cardinality primitives supplied. Eleven field/action/data imports remain explicit. -/
theorem full_restricted_conclusions_from_remaining_imports [Fintype K] {z : K}
    (ha : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (hcycle : PrimeTranslationCycleDuty) (hhalf : AffineHalfPowerDuty) (hcomp : AffineCompositionDuty)
    (hE : Order41SubgroupDuty (H41 z)) (he : EulerCriterionDuty K) (hm : MinusOneSquareDuty K)
    (hg : ¬ Square (primitive z)) (hd : Admission.ExactDataAcceptanceDuty z)
    (hfield : Nat.card K = 6561) : Targets.H41Conclusion z ∧ Targets.D82Conclusion z :=
  full_restricted_conclusions_from_explicit_imports three_order_from_finite_arithmetic ha hf
    hcycle hhalf hcomp hE he hm hg hd cardinal_representation_from_library
    nonzero_fibre_card_from_fintype hfield

end
end Partials.Cap.Assembly
