import Partials.Cap.Freeness

/-! Blind source for main.tex classification and eq:count. Incidence,
cardinality saturation and orbit distinctness are derived below. Exact
rooted count, witness membership and elementary action coordinates remain
explicit numerical/algebraic duties; no classification is taken as input. -/
namespace Partials.Cap

noncomputable section

def fiveFamily (graph : Hypergraph Vertex) : Finset (Finset Vertex) := by
  classical
  exact Finset.univ.filter (fun T => Independent graph T ∧ T.card = 5)

theorem mem_fiveFamily (graph : Hypergraph Vertex) (T : Finset Vertex) :
    T ∈ fiveFamily graph ↔ Independent graph T ∧ T.card = 5 := by
  simp [fiveFamily]

def rootedFiveFamily (graph : Hypergraph Vertex) (v : Vertex) : Finset (Finset Vertex) :=
  (fiveFamily graph).filter (fun T => v ∈ T)

/-- Generic finite double counting, with all vertex/set incidences present. -/
theorem incidence_double_count {α : Type*} [Fintype α] [DecidableEq α]
    (F : Finset (Finset α)) :
    (∑ T ∈ F, T.card) = ∑ v : α, (F.filter (fun T => v ∈ T)).card := by
  classical
  have hcard : ∀ T : Finset α, T.card = ∑ v : α, if v ∈ T then (1 : ℕ) else 0 := by
    intro T
    rw [← Finset.sum_filter]
    simp
  calc
    (∑ T ∈ F, T.card) = ∑ T ∈ F, ∑ v : α, if v ∈ T then (1 : ℕ) else 0 := by
      simp_rw [hcard]
    _ = ∑ v : α, ∑ T ∈ F, if v ∈ T then (1 : ℕ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ v : α, (F.filter (fun T => v ∈ T)).card := by
      congr 1
      ext v
      rw [← Finset.sum_filter]
      simp

theorem fiveFamily_translation_root_count (graph : Hypergraph Vertex)
    (htr : ∀ t T, Independent graph (translateImage t T) ↔ Independent graph T)
    (v : Vertex) : (rootedFiveFamily graph v).card = (rootedFiveFamily graph 0).card := by
  classical
  apply Finset.card_bij (fun T _ => translateImage (-v) T)
  · intro T hT
    obtain ⟨hTfive, hv⟩ := Finset.mem_filter.mp hT
    obtain ⟨hind, hc⟩ := (mem_fiveFamily graph T).1 hTfive
    apply Finset.mem_filter.mpr
    refine ⟨(mem_fiveFamily graph _).2 ⟨(htr _ _).2 hind, ?_⟩, translated_root hv⟩
    simpa [translateImage_card] using hc
  · intro T hT U hU hTU
    exact finset_image_injective (fun _ _ h => add_right_cancel h) hTU
  · intro U hU
    obtain ⟨hUfive, hzero⟩ := Finset.mem_filter.mp hU
    obtain ⟨hind, hc⟩ := (mem_fiveFamily graph U).1 hUfive
    refine ⟨translateImage v U, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨(mem_fiveFamily graph _).2 ⟨(htr _ _).2 hind, ?_⟩, ?_⟩
      · simpa [translateImage_card] using hc
      · exact Finset.mem_image.mpr ⟨0, hzero, by simp⟩
    · exact translateImage_inverse v U

theorem five_incidence_equation (graph : Hypergraph Vertex)
    (hroot : ∀ v : Vertex, (rootedFiveFamily graph v).card = 40) :
    5 * (fiveFamily graph).card = 41 * 40 := by
  have hsum : (∑ T ∈ fiveFamily graph, T.card) = (fiveFamily graph).card * 5 := by
    calc
      (∑ T ∈ fiveFamily graph, T.card) = ∑ T ∈ fiveFamily graph, (5 : ℕ) := by
        apply Finset.sum_congr rfl
        intro T hT
        exact ((mem_fiveFamily graph T).1 hT).2
      _ = (fiveFamily graph).card * 5 := by simp
  have htotal := incidence_double_count (fiveFamily graph)
  have hvertices : (Finset.univ : Finset Vertex).card = 41 := by simp [Vertex]
  change (∑ T ∈ fiveFamily graph, T.card) =
    ∑ v : Vertex, (rootedFiveFamily graph v).card at htotal
  simp_rw [hroot] at htotal
  rw [hsum] at htotal
  simpa [hvertices, Nat.mul_comm] using htotal

theorem five_count_from_rooted_count (graph : Hypergraph Vertex)
    (htr : ∀ t T, Independent graph (translateImage t T) ↔ Independent graph T)
    (hroot : (rootedFiveFamily graph 0).card = 40) : (fiveFamily graph).card = 328 := by
  have hrootall : ∀ v, (rootedFiveFamily graph v).card = 40 := by
    intro v
    rw [fiveFamily_translation_root_count graph htr v, hroot]
  have hcount := five_incidence_equation graph hrootall
  omega

/-- Unfinished elementary closure/inverse coordinate facts for the eight
multiplier affine maps. These are pointwise map identities, not stabilizer,
orbit-cardinality or classification premises. -/
structure AffineCompositionDuty : Prop where
  inverse_coordinate : ∀ q : Vertex × Fin 8, ∃ r : Vertex × Fin 8,
    ∀ v : Vertex, affine r.1 r.2 (affine q.1 q.2 v) = v
  composition_coordinate : ∀ r p : Vertex × Fin 8, ∃ s : Vertex × Fin 8,
    ∀ v : Vertex, affine s.1 s.2 v = affine r.1 r.2 (affine p.1 p.2 v)

theorem affineImage_identity (T : Finset Vertex) : affineImage 0 0 T = T := by
  rw [affine_zero_is_translation, translateImage_zero]

theorem affine_orbit_parameter_injective (ho : ThreeOrderDuty)
    (hc : AffineCompositionDuty) (T : Finset Vertex)
    (hfree : ∀ t j, affineImage t j T = T → t = 0 ∧ j = 0) :
    Function.Injective (fun p : Vertex × Fin 8 => affineImage p.1 p.2 T) := by
  intro p q hpq
  change affineImage p.1 p.2 T = affineImage q.1 q.2 T at hpq
  obtain ⟨r, hr⟩ := hc.inverse_coordinate q
  obtain ⟨s, hs⟩ := hc.composition_coordinate r p
  have hsT : affineImage s.1 s.2 T = T := by
    calc
      affineImage s.1 s.2 T = affineImage r.1 r.2 (affineImage p.1 p.2 T) := by
        simp only [affineImage, Finset.image_image]
        congr 1
        funext v
        exact hs v
      _ = affineImage r.1 r.2 (affineImage q.1 q.2 T) := by rw [hpq]
      _ = T := by
        simp only [affineImage, Finset.image_image]
        have hfun : affine r.1 r.2 ∘ affine q.1 q.2 = id := funext hr
        rw [hfun]
        simp
  obtain ⟨hszero, hsjzero⟩ := hfree s.1 s.2 hsT
  apply affine_parameter_injective ho
  funext v
  apply affine_injective ho r.1 r.2
  calc
    affine r.1 r.2 (affine p.1 p.2 v) = affine s.1 s.2 v := (hs v).symm
    _ = v := by simp [hszero, hsjzero, affine]
    _ = affine r.1 r.2 (affine q.1 q.2 v) := (hr v).symm

theorem parameter_card : (Finset.univ : Finset (Vertex × Fin 8)).card = 328 := by
  simp [Vertex]

theorem witnessOrbit_card_from_free (ho : ThreeOrderDuty) (hc : AffineCompositionDuty)
    (hfree : ∀ t j, affineImage t j witnessExponents = witnessExponents → t = 0 ∧ j = 0) :
    witnessOrbit.card = 328 := by
  rw [witnessOrbit, Finset.card_image_of_injective _ (affine_orbit_parameter_injective ho hc _ hfree)]
  exact parameter_card

theorem orbit_saturation (F O : Finset (Finset Vertex)) (hsub : O ⊆ F)
    (hF : F.card = 328) (hO : O.card = 328) : O = F := by
  apply Finset.eq_of_subset_of_card_le hsub
  omega

section Field
variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

/-- Exact finite datum admissions: only the root count and witness validity.
This is uninstantiated; its count must be obtained from the full increasing-
extension certificate, not a search maximum or a list of valid examples. -/
structure FiveClassificationDataDuty (z : K) : Prop where
  rooted_count : (rootedFiveFamily (discriminantHypergraph z) 0).card = 40
  witness_independent : Independent (discriminantHypergraph z) witnessExponents
  witness_card : witnessExponents.card = 5

theorem witnessOrbit_eq_all_five {z : K} (ho : ThreeOrderDuty)
    (ha : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (hcycle : PrimeTranslationCycleDuty) (hhalf : AffineHalfPowerDuty)
    (hcomp : AffineCompositionDuty) (hd : FiveClassificationDataDuty z) :
    witnessOrbit = fiveFamily (discriminantHypergraph z) := by
  have hF : (fiveFamily (discriminantHypergraph z)).card = 328 :=
    five_count_from_rooted_count _ (independent_translate_iff ho ha hf) hd.rooted_count
  have hfree : ∀ t j, affineImage t j witnessExponents = witnessExponents → t = 0 ∧ j = 0 :=
    independent_five_action_free ha hcycle hhalf _ hd.witness_independent hd.witness_card
  have hO : witnessOrbit.card = 328 := witnessOrbit_card_from_free ho hcomp hfree
  apply orbit_saturation _ _ ?_ hF hO
  intro U hU
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hU
  exact (mem_fiveFamily _ _).2
    ⟨(independent_affine_iff ho ha hf _ _ _).2 hd.witness_independent,
      by rw [affineImage_card ho]; exact hd.witness_card⟩

theorem independent_five_iff_displayed_orbit {z : K} (ho : ThreeOrderDuty)
    (ha : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (hcycle : PrimeTranslationCycleDuty) (hhalf : AffineHalfPowerDuty)
    (hcomp : AffineCompositionDuty) (hd : FiveClassificationDataDuty z) (T : Finset Vertex) :
    (Independent (discriminantHypergraph z) T ∧ T.card = 5) ↔
      ∃ t : Vertex, ∃ j : Fin 8, T = affineImage t j witnessExponents := by
  rw [← mem_fiveFamily, ← witnessOrbit_eq_all_five ho ha hf hcycle hhalf hcomp hd]
  simp only [witnessOrbit, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨t, j⟩, h⟩
    exact ⟨t, j, h.symm⟩
  · rintro ⟨t, j, h⟩
    exact ⟨(t, j), h.symm⟩

theorem exponentCoefficient_image_card {z : K} (ha : ExponentActionDuty z)
    (T : Finset Vertex) : (ExponentCoefficients z T).card = T.card := by
  exact Finset.card_image_of_injective T ha.coefficient_injective

theorem exponentCoefficient_set_injective {z : K} (ha : ExponentActionDuty z) :
    Function.Injective (ExponentCoefficients z) := finset_image_injective ha.coefficient_injective

theorem displayed_coefficient_sets_distinct {z : K} (ho : ThreeOrderDuty)
    (ha : ExponentActionDuty z) (hcomp : AffineCompositionDuty)
    (hcycle : PrimeTranslationCycleDuty) (hhalf : AffineHalfPowerDuty)
    (hd : FiveClassificationDataDuty z) :
    Function.Injective (fun p : Vertex × Fin 8 =>
      ExponentCoefficients z (affineImage p.1 p.2 witnessExponents)) := by
  apply Function.Injective.comp (exponentCoefficient_set_injective ha)
  exact affine_orbit_parameter_injective ho hcomp _
    (independent_five_action_free ha hcycle hhalf _ hd.witness_independent hd.witness_card)

theorem coefficient_action_formula {z : K} (ha : ExponentActionDuty z)
    (t : Vertex) (j : Fin 8) :
    ExponentCoefficients z (affineImage t j witnessExponents) =
      (witnessCoefficients z).image (fun c => coefficient z t * c ^ (3 ^ j.val)) := by
  simp only [ExponentCoefficients, affineImage, witnessCoefficients, Finset.image_image]
  congr 1
  funext v
  exact ha.coefficient_affine t j v

def coefficientPreimage (z : K) (S : Finset K) : Finset Vertex :=
  Finset.univ.filter (fun i => coefficient z i ∈ S)

theorem exponentCoefficients_subset_H (z : K) (T : Finset Vertex) :
    (↑(ExponentCoefficients z T) : Set K) ⊆ H41 z := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨i, rfl⟩

theorem coefficientPreimage_recovers_H_set (z : K) (S : Finset K)
    (hS : (↑S : Set K) ⊆ H41 z) : ExponentCoefficients z (coefficientPreimage z S) = S := by
  ext a
  constructor
  · intro ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp hi).2
  · intro ha
    obtain ⟨i, rfl⟩ := hS ha
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩, rfl⟩

def coefficientOrbit (z : K) : Finset (Finset K) := witnessOrbit.image (ExponentCoefficients z)

theorem coefficientOrbit_card {z : K} (ho : ThreeOrderDuty)
    (ha : ExponentActionDuty z) (hcomp : AffineCompositionDuty)
    (hcycle : PrimeTranslationCycleDuty) (hhalf : AffineHalfPowerDuty)
    (hd : FiveClassificationDataDuty z) : (coefficientOrbit z).card = 328 := by
  rw [coefficientOrbit,
    Finset.card_image_of_injective witnessOrbit (exponentCoefficient_set_injective ha)]
  exact witnessOrbit_card_from_free ho hcomp
    (independent_five_action_free ha hcycle hhalf _ hd.witness_independent hd.witness_card)

/-- The cap/hypergraph correspondence is an explicit hypothesis for this
module boundary, to be supplied by the separate normalization/reduction
source. It is not a maximum or orbit-classification premise. -/
theorem coefficientOrbit_eq_maximizers_H {z : K} (ho : ThreeOrderDuty)
    (ha : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (hcycle : PrimeTranslationCycleDuty) (hhalf : AffineHalfPowerDuty)
    (hcomp : AffineCompositionDuty) (hd : FiveClassificationDataDuty z)
    (hreduce : ∀ T : Finset Vertex,
      Cap (P (ExponentCoefficients z T)) ↔ Independent (discriminantHypergraph z) T) :
    (↑(coefficientOrbit z) : Set (Finset K)) = Maximizers (H41 z) := by
  have hclass := witnessOrbit_eq_all_five ho ha hf hcycle hhalf hcomp hd
  ext S
  constructor
  · intro hS
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    rw [hclass] at hT
    obtain ⟨hind, hc⟩ := (mem_fiveFamily _ T).1 hT
    exact ⟨⟨exponentCoefficients_subset_H z T, (hreduce T).2 hind⟩,
      by rw [exponentCoefficient_image_card ha, hc]⟩
  · rintro ⟨hS, hc⟩
    let T := coefficientPreimage z S
    have heq : ExponentCoefficients z T = S := coefficientPreimage_recovers_H_set z S hS.1
    have hind : Independent (discriminantHypergraph z) T := (hreduce T).1 (heq.symm ▸ hS.2)
    have hTcard : T.card = 5 := by
      rw [← exponentCoefficient_image_card ha T, heq, hc]
    have hT : T ∈ witnessOrbit := by rw [hclass]; exact (mem_fiveFamily _ T).2 ⟨hind, hTcard⟩
    exact Finset.mem_image.mpr ⟨T, hT, heq⟩

theorem maximizer_H_iff_displayed_coefficients {z : K} (ho : ThreeOrderDuty)
    (ha : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (hcycle : PrimeTranslationCycleDuty) (hhalf : AffineHalfPowerDuty)
    (hcomp : AffineCompositionDuty) (hd : FiveClassificationDataDuty z)
    (hreduce : ∀ T : Finset Vertex,
      Cap (P (ExponentCoefficients z T)) ↔ Independent (discriminantHypergraph z) T)
    (S : Finset K) :
    S ∈ Maximizers (H41 z) ↔ ∃ u ∈ H41 z, ∃ j : Fin 8,
      S = (witnessCoefficients z).image (fun c => u * c ^ (3 ^ j.val)) := by
  rw [← coefficientOrbit_eq_maximizers_H ho ha hf hcycle hhalf hcomp hd hreduce]
  constructor
  · intro hS
    obtain ⟨T, hT, hTS⟩ := Finset.mem_image.mp hS
    obtain ⟨⟨t, j⟩, hp, hpt⟩ := Finset.mem_image.mp hT
    refine ⟨coefficient z t, ⟨t, rfl⟩, j, ?_⟩
    rw [← hTS, ← hpt]
    exact coefficient_action_formula ha t j
  · rintro ⟨u, ⟨t, rfl⟩, j, hS⟩
    apply Finset.mem_image.mpr
    refine ⟨affineImage t j witnessExponents, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨(t, j), Finset.mem_univ _, rfl⟩
    · rw [coefficient_action_formula ha]
      exact hS.symm

end Field
end
end Partials.Cap
