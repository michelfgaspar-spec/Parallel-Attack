import Partials.Cap.Quadratic

/-! Actual normalized-equation to finite-hypergraph reduction. All concrete
subgroup/nonantipodal/character and encoding inputs remain explicit. -/
namespace Partials.Cap

noncomputable section
variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

def DistinctCoefficientSafety (S : Set K) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S,
    a ≠ b → a ≠ c → b ≠ c → ¬ Square (delta a b c)
def PairSafety (S : Set K) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, a ≠ b → Cap (PSet ({a, b} : Set K))

theorem cap_iff_distinct_coefficient_safety (S : Set K)
    (hn : NonAntipodal S) (hz : NonzeroCoefficients S) (hp : PairSafety S) :
    Cap (PSet S) ↔ DistinctCoefficientSafety S := by
  constructor
  · intro hcap a ha b hb c hc hab hac hbc hd
    exact square_delta_obstructs_cap hn ha hb hc (by tauto) hd hcap
  · intro hs
    apply (Cap_iff_normalized_root_safety S).mpr
    intro a ha b hb c hc t ht hroot
    by_cases hab : a = b
    · by_cases hbc : b = c
      · have hquad : quadratic a a a t = 0 := by simpa [← hab, ← hbc] using hroot
        exact ⟨hab, hbc, (all_equal_root_iff (hz a ha)).mp hquad⟩
      · have hac : a ≠ c := by intro h; exact hbc (hab.symm.trans h)
        have hsafe := (Cap_iff_normalized_root_safety ({a, c} : Set K)).mp (hp a ha c hc hac)
        exact hsafe a (by simp) b (by simp [← hab]) c (by simp) t ht hroot
    · by_cases hac : a = c
      · have hsafe := (Cap_iff_normalized_root_safety ({a, b} : Set K)).mp (hp a ha b hb hab)
        exact hsafe a (by simp) b (by simp) c (by simp [← hac]) t ht hroot
      · by_cases hbc : b = c
        · have hsafe := (Cap_iff_normalized_root_safety ({a, b} : Set K)).mp (hp a ha b hb hab)
          exact hsafe a (by simp) b (by simp) c (by simp [← hbc]) t ht hroot
        · have hd : Square (delta a b c) :=
            (root_iff_square_delta a b c (hn a ha c hc)).mp ⟨t, hroot⟩
          exact False.elim (hs a ha b hb c hc hab hac hbc hd)

theorem mem_discriminantHypergraph_iff (z : K) (e : Finset Vertex) :
    e ∈ discriminantHypergraph z ↔ DiscriminantEdge z e := by
  classical
  simp [discriminantHypergraph]

theorem distinct_triple_card {i j k : Vertex} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ({i, j, k} : Finset Vertex).card = 3 := by simp [hij, hik, hjk]

theorem independent_discriminant_iff (z : K) (T : Finset Vertex) :
    Independent (discriminantHypergraph z) T ↔
      ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T, i ≠ j → i ≠ k → j ≠ k →
        ¬ Square (delta (coefficient z i) (coefficient z j) (coefficient z k)) := by
  constructor
  · intro h i hi j hj k hk hij hik hjk hd
    let e : Finset Vertex := {i, j, k}
    have he : e ∈ discriminantHypergraph z := by
      apply (mem_discriminantHypergraph_iff z e).mpr
      exact ⟨distinct_triple_card hij hik hjk, i, by simp [e], j, by simp [e],
        k, by simp [e], hij, hik, hjk, hd⟩
    apply h e he
    intro v hv
    simp only [e, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact hi
    · exact hj
    · exact hk
  · intro h e he hsub
    obtain ⟨hcard, i, hi, j, hj, k, hk, hij, hik, hjk, hd⟩ :=
      (mem_discriminantHypergraph_iff z e).mp he
    exact h i (hsub hi) j (hsub hj) k (hsub hk) hij hik hjk hd

theorem exponent_coefficients_subset_H (z : K) (T : Finset Vertex) :
    (↑(ExponentCoefficients z T) : Set K) ⊆ H41 z := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  exact ⟨i, rfl⟩

theorem exponent_card_of_injective (z : K) (hi : Function.Injective (coefficient z))
    (T : Finset Vertex) : (ExponentCoefficients z T).card = T.card :=
  Finset.card_image_of_injective T hi

theorem coefficient_safety_iff_vertex_safety (z : K)
    (hinj : Function.Injective (coefficient z)) (T : Finset Vertex) :
    DistinctCoefficientSafety (↑(ExponentCoefficients z T) : Set K) ↔
      ∀ i ∈ T, ∀ j ∈ T, ∀ k ∈ T, i ≠ j → i ≠ k → j ≠ k →
        ¬ Square (delta (coefficient z i) (coefficient z j) (coefficient z k)) := by
  constructor
  · intro h i hi j hj k hk hij hik hjk
    exact h _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
      _ (Finset.mem_image.mpr ⟨k, hk, rfl⟩)
      (by intro he; exact hij (hinj he))
      (by intro he; exact hik (hinj he))
      (by intro he; exact hjk (hinj he))
  · intro h a ha b hb c hc hab hac hbc
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
    exact h i hi j hj k hk (by intro he; exact hab (congrArg _ he))
      (by intro he; exact hac (congrArg _ he)) (by intro he; exact hbc (congrArg _ he))

theorem cap_iff_hypergraph_independent (z : K)
    (hinj : Function.Injective (coefficient z)) (hn : NonAntipodal (H41 z))
    (hz : NonzeroCoefficients (H41 z)) (hp : PairSafety (H41 z)) (T : Finset Vertex) :
    Cap (P (ExponentCoefficients z T)) ↔ Independent (discriminantHypergraph z) T := by
  let S : Set K := ↑(ExponentCoefficients z T)
  have hsub : S ⊆ H41 z := exponent_coefficients_subset_H z T
  have hnS : NonAntipodal S := fun a ha b hb => hn a (hsub ha) b (hsub hb)
  have hzS : NonzeroCoefficients S := fun a ha => hz a (hsub ha)
  have hpS : PairSafety S := fun a ha b hb => hp a (hsub ha) b (hsub hb)
  exact (cap_iff_distinct_coefficient_safety S hnS hzS hpS).trans
    ((coefficient_safety_iff_vertex_safety z hinj T).trans
      (independent_discriminant_iff z T).symm)

end
end Partials.Cap
