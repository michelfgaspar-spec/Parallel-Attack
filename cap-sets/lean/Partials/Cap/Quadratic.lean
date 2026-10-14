import Partials.Cap.Normalization

/-! Exact discriminant converse and repeated-POINT criterion. Square includes
zero. Grace--Voloch Lemma 2.4 supplies the construction's antecedent; the
stronger converse used here is the frozen paper's explicit specialization.
All proof text is authored blind and remains uncompiled. -/
namespace Partials.Cap

noncomputable section
variable {K : Type*} [Field K] [CharP K 3]

theorem square_zero : Square (0 : K) := ⟨0, by ring⟩
theorem square_one : Square (1 : K) := ⟨1, by ring⟩

theorem square_mul {a b : K} (ha : Square a) (hb : Square b) : Square (a * b) := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  refine ⟨x * y, ?_⟩
  rw [mul_pow, hx, hy]

theorem square_inv {a : K} (ha : Square a) : Square a⁻¹ := by
  obtain ⟨x, hx⟩ := ha
  refine ⟨x⁻¹, ?_⟩
  rw [inv_pow, hx]

theorem square_div {a b : K} (ha : Square a) (hb : Square b) : Square (a / b) := by
  simpa [div_eq_mul_inv] using square_mul ha (square_inv hb)

theorem square_scaled_iff (u : K) (hu : u ≠ 0) (a : K) :
    Square (u ^ 2 * a) ↔ Square a := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x / u, ?_⟩
    field_simp [hu]
    linear_combination hx
  · rintro ⟨x, hx⟩
    refine ⟨u * x, ?_⟩
    rw [mul_pow, hx]

/-- Completing the square avoids importing a quadratic-root headline as a
premise. Only a+c≠0 is needed to recover t from the square root. -/
theorem completed_square_identity (a b c t : K) :
    ((a + c) * t + c) ^ 2 = delta a b c + (a + c) * quadratic a b c t := by
  dsimp [delta, quadratic]
  ring

theorem root_iff_square_delta (a b c : K) (hac : a + c ≠ 0) :
    (∃ t : K, quadratic a b c t = 0) ↔ Square (delta a b c) := by
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨(a + c) * t + c, ?_⟩
    rw [completed_square_identity, ht, mul_zero, add_zero]
  · rintro ⟨d, hd⟩
    let t := (d - c) / (a + c)
    refine ⟨t, ?_⟩
    have hlin : (a + c) * t + c = d := by
      dsimp [t]
      field_simp [hac]
      <;> ring
    have hi := completed_square_identity a b c t
    rw [hlin, hd] at hi
    have hz : (a + c) * quadratic a b c t = 0 := by linear_combination -hi
    exact (mul_eq_zero.mp hz).resolve_left hac

theorem quadratic_at_zero (a b c : K) : quadratic a b c 0 = b + c := by
  simp [quadratic]

theorem quadratic_at_neg_one (a b c : K) : quadratic a b c (-1) = a + b := by
  dsimp [quadratic]
  ring

theorem root_admissible {a b c t : K} (hab : a + b ≠ 0) (hbc : b + c ≠ 0)
    (ht : quadratic a b c t = 0) : ratioAdmissible t := by
  constructor
  · intro hz
    subst t
    exact hbc (by simpa [quadratic_at_zero] using ht)
  · intro hm
    subst t
    exact hab (by simpa [quadratic_at_neg_one] using ht)

theorem admissible_root_iff_square_delta (a b c : K)
    (hab : a + b ≠ 0) (hac : a + c ≠ 0) (hbc : b + c ≠ 0) :
    (∃ t : K, ratioAdmissible t ∧ quadratic a b c t = 0) ↔ Square (delta a b c) := by
  constructor
  · rintro ⟨t, had, ht⟩
    exact (root_iff_square_delta a b c hac).mp ⟨t, ht⟩
  · intro hd
    obtain ⟨t, ht⟩ := (root_iff_square_delta a b c hac).mpr hd
    exact ⟨t, root_admissible hab hbc ht, ht⟩

theorem minus_two_eq_one : -(1 : K) - 1 = 1 := by
  linear_combination -(three_eq_zero (K := K))

theorem quadratic_all_equal (a t : K) :
    quadratic a a a t = 2 * a * (t - 1) ^ 2 := by
  calc
    quadratic a a a t = 2 * a * (t - 1) ^ 2 + (3 : K) * (2 * a * t) := by
      dsimp [quadratic]
      ring
    _ = 2 * a * (t - 1) ^ 2 := by rw [three_eq_zero]; ring

theorem all_equal_root_iff {a t : K} (ha : a ≠ 0) :
    quadratic a a a t = 0 ↔ t = 1 := by
  rw [quadratic_all_equal]
  constructor
  · intro h
    have hz : (t - 1) ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left (mul_ne_zero two_ne_zero ha)
    exact sub_eq_zero.mp ((sq_eq_zero_iff).mp hz)
  · intro ht
    subst t
    ring

theorem point_triple_self_sum (p : Point K) : p + p + p = 0 := by
  ext
  · dsimp
    linear_combination p.1 * (three_eq_zero (K := K))
  · dsimp
    linear_combination p.2 * (three_eq_zero (K := K))

theorem zero_sum_two_equal_forces_all {p q r : Point K}
    (hs : p + q + r = 0) (hpq : p = q) : p = r := by
  subst q
  have heq : p + p + r = p + p + p := hs.trans (point_triple_self_sum p).symm
  exact (add_left_cancel heq).symm

theorem zero_sum_repeated_forces_all {p q r : Point K}
    (hs : p + q + r = 0) (hr : p = q ∨ p = r ∨ q = r) : p = q ∧ p = r := by
  rcases hr with hpq | hpr | hqr
  · exact ⟨hpq, zero_sum_two_equal_forces_all hs hpq⟩
  · have hpq := zero_sum_two_equal_forces_all
      (p := p) (q := r) (r := q)
      (by simpa [add_comm, add_left_comm, add_assoc] using hs) hpr
    exact ⟨hpq, hpr⟩
  · have hqp := zero_sum_two_equal_forces_all
      (p := q) (q := r) (r := p)
      (by simpa [add_comm, add_left_comm, add_assoc] using hs) hqr
    exact ⟨hqp.symm, hqp.symm.trans hqr⟩

theorem normalized_all_points_equal_iff (a b c t : K) :
    (normA a t = normB b ∧ normA a t = normC c t) ↔
      (a = b ∧ b = c ∧ t = 1) := by
  constructor
  · rintro ⟨hAB, hAC⟩
    have ht := congrArg Prod.fst hAB
    dsimp [normA, normB, parabolaPoint] at ht
    subst t
    have hab := congrArg Prod.snd hAB
    have hac := congrArg Prod.snd hAC
    dsimp [normA, normB, normC, parabolaPoint] at hab hac
    simp only [minus_two_eq_one, one_pow, mul_one] at hab hac
    exact ⟨hab, hab.symm.trans hac, rfl⟩
  · rintro ⟨hab, hbc, ht⟩
    subst b
    subst c
    subst t
    simp [normA, normB, normC, parabolaPoint, minus_two_eq_one]

/-- Coefficient repetitions alone are not repeated POINTS. This equivalence
requires the zero-sum root equation and covers any of the three point pairs. -/
theorem normalized_repeated_iff {a b c t : K} (ht : quadratic a b c t = 0) :
    (normA a t = normB b ∨ normA a t = normC c t ∨ normB b = normC c t) ↔
      (a = b ∧ b = c ∧ t = 1) := by
  constructor
  · intro hr
    exact (normalized_all_points_equal_iff a b c t).mp
      (zero_sum_repeated_forces_all ((normalized_zero_sum_iff a b c t).mpr ht) hr)
  · intro h
    exact Or.inl ((normalized_all_points_equal_iff a b c t).mpr h).1

theorem normalized_root_pairwise_distinct {a b c t : K}
    (ht : quadratic a b c t = 0) (hne : ¬ (a = b ∧ b = c)) :
    normA a t ≠ normB b ∧ normA a t ≠ normC c t ∧ normB b ≠ normC c t := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hr := (normalized_repeated_iff ht).mp (Or.inl h)
    exact hne ⟨hr.1, hr.2.1⟩
  · intro h
    have hr := (normalized_repeated_iff ht).mp (Or.inr (Or.inl h))
    exact hne ⟨hr.1, hr.2.1⟩
  · intro h
    have hr := (normalized_repeated_iff ht).mp (Or.inr (Or.inr h))
    exact hne ⟨hr.1, hr.2.1⟩

def NormalizedRootSafety (S : Set K) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ t : K,
    ratioAdmissible t → quadratic a b c t = 0 → a = b ∧ b = c ∧ t = 1

/-- The complete punctured-parabola correspondence, over every field of
characteristic three. No field-size, coset, hypergraph or finite-search premise. -/
theorem Cap_iff_normalized_root_safety (S : Set K) :
    Cap (PSet S) ↔ NormalizedRootSafety S := by
  classical
  constructor
  · intro hcap a ha b hb c hc t ht hquad
    obtain ⟨hA, hB, hC⟩ := normalized_points_mem ha hb hc ht
    have hsum := (normalized_zero_sum_iff a b c t).mpr hquad
    apply (normalized_repeated_iff hquad).mp
    by_cases hAB : normA a t = normB b
    · exact Or.inl hAB
    by_cases hAC : normA a t = normC c t
    · exact Or.inr (Or.inl hAC)
    by_cases hBC : normB b = normC c t
    · exact Or.inr (Or.inr hBC)
    exact False.elim (hcap _ hA _ hB _ hC hAB hAC hBC hsum)
  · intro hsafe p hp q hq r hr hpq hpr hqr hsum
    rcases hp with ⟨a, ha, x, hx, rfl⟩
    rcases hq with ⟨b, hb, y, hy, rfl⟩
    rcases hr with ⟨c, hc, z, hz, rfl⟩
    obtain ⟨had, hquad⟩ := parabola_triple_normalization hx hy hz hsum
    obtain ⟨hab, hbc, ht⟩ := hsafe a ha b hb c hc (x / y) had hquad
    have hxy : x = y := by
      field_simp [hy] at ht
      exact ht
    apply hpq
    rw [hab, hxy]

theorem normalized_root_obstructs_cap {S : Set K} {a b c t : K}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (ht : ratioAdmissible t) (hquad : quadratic a b c t = 0)
    (hne : ¬ (a = b ∧ b = c)) : ¬ Cap (PSet S) := by
  intro hcap
  have hr := (Cap_iff_normalized_root_safety S).mp hcap a ha b hb c hc t ht hquad
  exact hne ⟨hr.1, hr.2.1⟩

theorem square_delta_obstructs_cap_of_sums {S : Set K}
    {a b c : K} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hab : a + b ≠ 0) (hac : a + c ≠ 0) (hbc : b + c ≠ 0)
    (hne : ¬ (a = b ∧ b = c)) (hd : Square (delta a b c)) : ¬ Cap (PSet S) := by
  obtain ⟨t, had, hquad⟩ :=
    (admissible_root_iff_square_delta a b c hab hac hbc).mpr hd
  exact normalized_root_obstructs_cap ha hb hc had hquad hne

theorem square_delta_obstructs_cap {S : Set K} (hn : NonAntipodal S)
    {a b c : K} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hne : ¬ (a = b ∧ b = c)) (hd : Square (delta a b c)) : ¬ Cap (PSet S) := by
  exact square_delta_obstructs_cap_of_sums ha hb hc
    (hn a ha b hb) (hn a ha c hc) (hn b hb c hc) hne hd

/-- Two labels exhaust six nonconstant ordered multiplicity patterns. The
discriminant is symmetric, so only aab and abb need be excluded. -/
theorem delta_perm_swap_ab (a b c : K) : delta a b c = delta b a c := by
  dsimp [delta]
  ring

theorem delta_perm_swap_bc (a b c : K) : delta a b c = delta a c b := by
  dsimp [delta]
  ring

theorem delta_perm_cycle (a b c : K) : delta a b c = delta b c a := by
  dsimp [delta]
  ring

theorem pair_cap_of_repeated_discriminants {a b : K} (ha : a ≠ 0) (hb : b ≠ 0)
    (hnsA : ¬ Square (delta a a b)) (hnsB : ¬ Square (delta a b b)) :
    Cap (PSet ({a, b} : Set K)) := by
  apply (Cap_iff_normalized_root_safety _).mpr
  intro u hu v hv w hw t had hroot
  have hs : Square (delta u v w) :=
    ⟨(u + w) * t + w, by rw [completed_square_identity, hroot]; ring⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv hw
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;>
    rcases hw with rfl | rfl
  · exact ⟨rfl, rfl, (all_equal_root_iff ha).mp hroot⟩
  · exact False.elim (hnsA hs)
  · exact False.elim (hnsA (by convert hs using 1 <;> unfold delta <;> ring))
  · exact False.elim (hnsB hs)
  · exact False.elim (hnsA (by convert hs using 1 <;> unfold delta <;> ring))
  · exact False.elim (hnsB (by convert hs using 1 <;> unfold delta <;> ring))
  · exact False.elim (hnsB (by convert hs using 1 <;> unfold delta <;> ring))
  · exact ⟨rfl, rfl, (all_equal_root_iff hb).mp hroot⟩

end
end Partials.Cap
