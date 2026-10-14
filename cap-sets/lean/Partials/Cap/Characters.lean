import Partials.Cap.Quadratic

/-! Character-theoretic source for the two order-41 coefficient cosets.
The proof text specializes the frozen paper's algebra; concrete field,
cyclicity, Frobenius/Euler and coset witnesses are not supplied by source hashes.
The two classes remain distinct coefficient domains, with no ambient optimum. -/
namespace Partials.Cap

noncomputable section
variable {K : Type*} [Field K] [CharP K 3]

/-- Elementary subgroup properties and the order-divisibility relation.
No cap, hypergraph, maximum or classification conclusion is a field here. -/
structure Order41SubgroupDuty (E : Set K) : Prop where
  one_mem : (1 : K) ∈ E
  mul_mem : ∀ a ∈ E, ∀ b ∈ E, a * b ∈ E
  inv_mem : ∀ a ∈ E, a⁻¹ ∈ E
  pow41 : ∀ a ∈ E, a ^ 41 = 1

/-- Classical finite-field inputs still uninhabited for the exact quotient.
They concern every nonzero element of the proposed F₃⁸ field, not a stored
edge flag, normalized root or any desired cap conclusion. -/
structure EulerCriterionDuty (K : Type*) [Field K] [CharP K 3] : Prop where
  square_iff : ∀ a : K, a ≠ 0 → (Square a ↔ a ^ 3280 = 1)
  power_dichotomy : ∀ a : K, a ≠ 0 → a ^ 3280 = 1 ∨ a ^ 3280 = -1

def Frobenius81Duty (K : Type*) [Field K] [CharP K 3] : Prop :=
  ∀ r : K, (r - 1) ^ 81 = r ^ 81 - 1

def MinusOneSquareDuty (K : Type*) [Field K] [CharP K 3] : Prop := Square (-1 : K)

theorem char_three_cube_sub_one (r : K) : (r - 1) ^ 3 = r ^ 3 - 1 := by
  calc
    (r - 1) ^ 3 = r ^ 3 - 1 - (3 : K) * r * (r - 1) := by ring
    _ = r ^ 3 - 1 := by rw [three_eq_zero]; ring

theorem char_three_frobenius_sub_one (r : K) (n : ℕ) :
    (r - 1) ^ (3 ^ n) = r ^ (3 ^ n) - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        (r - 1) ^ (3 ^ (n + 1)) = ((r - 1) ^ (3 ^ n)) ^ 3 := by
          rw [← pow_mul, ← pow_succ]
        _ = (r ^ (3 ^ n) - 1) ^ 3 := by rw [ih]
        _ = (r ^ (3 ^ n)) ^ 3 - 1 := char_three_cube_sub_one _
        _ = r ^ (3 ^ (n + 1)) - 1 := by rw [← pow_mul, ← pow_succ]

/-- This generic duty has actual characteristic-three proof source here.
It is not a finite-field experiment or a supplied numerical witness. -/
theorem frobenius81_from_characteristic_three : Frobenius81Duty K := by
  intro r
  convert char_three_frobenius_sub_one r 4 using 1 <;> norm_num

theorem order41_nonzero {E : Set K} (hE : Order41SubgroupDuty E)
    {r : K} (hr : r ∈ E) : r ≠ 0 := by
  intro hz
  have h := hE.pow41 r hr
  rw [hz] at h
  norm_num at h

theorem order41_square {E : Set K} (hE : Order41SubgroupDuty E)
    {r : K} (hr : r ∈ E) : Square r := by
  refine ⟨r ^ 21, ?_⟩
  rw [← pow_mul]
  change r ^ 42 = r
  rw [pow_succ, hE.pow41 r hr, one_mul]

theorem order41_neg_one_not_mem {E : Set K} (hE : Order41SubgroupDuty E) :
    (-1 : K) ∉ E := by
  intro hminus
  have h := hE.pow41 (-1) hminus
  have hneg : (-1 : K) ^ 41 = -1 := by norm_num
  rw [hneg] at h
  exact one_ne_neg_one h.symm

theorem order41_nonantipodal {E : Set K} (hE : Order41SubgroupDuty E) :
    NonAntipodal E := by
  intro a ha b hb hsum
  have ha0 := order41_nonzero hE ha
  have hbneg : b = -a := by linear_combination hsum
  have hratio : b * a⁻¹ = -1 := by
    rw [hbneg]
    field_simp [ha0]
  apply order41_neg_one_not_mem hE
  rw [← hratio]
  exact hE.mul_mem b hb a⁻¹ (hE.inv_mem a ha)

theorem order41_pow81_inverse {E : Set K} (hE : Order41SubgroupDuty E)
    {r : K} (hr : r ∈ E) : r ^ 81 = r⁻¹ := by
  have hr0 := order41_nonzero hE hr
  have hp : r ^ 81 * r = 1 := by
    rw [← pow_succ]
    change r ^ (41 * 2) = 1
    rw [pow_mul, hE.pow41 r hr]
    simp
  field_simp [hr0]
  simpa only [pow_succ] using hp

theorem order41_minus_one_pow80 {E : Set K} (hE : Order41SubgroupDuty E)
    (hf : Frobenius81Duty K) {r : K} (hr : r ∈ E) (hr1 : r ≠ 1) :
    (r - 1) ^ 80 = -r⁻¹ := by
  have hr0 := order41_nonzero hE hr
  have hm0 : r - 1 ≠ 0 := sub_ne_zero.mpr hr1
  have hp : (r - 1) ^ 80 * (r - 1) = r⁻¹ - 1 := by
    rw [← pow_succ, hf r, order41_pow81_inverse hE hr]
  have heq : r⁻¹ - 1 = -r⁻¹ * (r - 1) := by
    field_simp [hr0]
    <;> ring
  rw [heq] at hp
  exact mul_right_cancel₀ hm0 hp

theorem order41_minus_one_pow3280 {E : Set K} (hE : Order41SubgroupDuty E)
    (hf : Frobenius81Duty K) {r : K} (hr : r ∈ E) (hr1 : r ≠ 1) :
    (r - 1) ^ 3280 = -1 := by
  calc
    (r - 1) ^ 3280 = ((r - 1) ^ 80) ^ 41 := by rw [← pow_mul]
    _ = (-r⁻¹) ^ 41 := by rw [order41_minus_one_pow80 hE hf hr hr1]
    _ = -1 := by
      have hi : (r⁻¹) ^ 41 = 1 := by rw [inv_pow, hE.pow41 r hr]; simp
      rw [neg_pow, hi]
      norm_num

theorem order41_difference_nonsquare {E : Set K} (hE : Order41SubgroupDuty E)
    (he : EulerCriterionDuty K) (hf : Frobenius81Duty K)
    {r : K} (hr : r ∈ E) (hr1 : r ≠ 1) : ¬ Square (r - 1) := by
  intro hs
  have hp := (he.square_iff (r - 1) (sub_ne_zero.mpr hr1)).mp hs
  rw [order41_minus_one_pow3280 hE hf hr hr1] at hp
  exact one_ne_neg_one hp.symm

theorem square_mul_iff_of_square_nonzero {u : K} (hu0 : u ≠ 0)
    (hu : Square u) (d : K) : Square (u * d) ↔ Square d := by
  constructor
  · intro h
    have hs := square_mul (square_inv hu) h
    have heq : u⁻¹ * (u * d) = d := by field_simp [hu0]
    rwa [heq] at hs
  · exact square_mul hu

theorem nonsquare_power_eq_neg_one (he : EulerCriterionDuty K)
    {d : K} (hd0 : d ≠ 0) (hd : ¬ Square d) : d ^ 3280 = -1 := by
  rcases he.power_dichotomy d hd0 with hp | hp
  · exact False.elim (hd ((he.square_iff d hd0).mpr hp))
  · exact hp

/-- A nonsquare factor interchanges the two nonzero square classes. This
argument derives the status toggle from the explicitly named Euler import. -/
theorem nonsquare_product_toggles (he : EulerCriterionDuty K)
    {m d : K} (hm0 : m ≠ 0) (hd0 : d ≠ 0) (hm : ¬ Square m) :
    Square (m * d) ↔ ¬ Square d := by
  have hmp := nonsquare_power_eq_neg_one he hm0 hm
  constructor
  · intro hprod hd
    have hp := (he.square_iff (m * d) (mul_ne_zero hm0 hd0)).mp hprod
    have hdp := (he.square_iff d hd0).mp hd
    rw [mul_pow, hmp, hdp, mul_one] at hp
    exact one_ne_neg_one hp.symm
  · intro hd
    have hdp := nonsquare_power_eq_neg_one he hd0 hd
    apply (he.square_iff (m * d) (mul_ne_zero hm0 hd0)).mpr
    rw [mul_pow, hmp, hdp]
    ring

theorem delta_aab (a b : K) : delta a a b = a * (b - a) := by
  calc
    delta a a b = a * (b - a) - (3 : K) * a * b := by dsimp [delta]; ring
    _ = a * (b - a) := by rw [three_eq_zero]; ring

theorem delta_abb (a b : K) : delta a b b = b * (a - b) := by
  calc
    delta a b b = b * (a - b) - (3 : K) * a * b := by dsimp [delta]; ring
    _ = b * (a - b) := by rw [three_eq_zero]; ring

theorem delta_aab_ratio (a b : K) (ha : a ≠ 0) :
    delta a a b = a ^ 2 * (b / a - 1) := by
  rw [delta_aab]
  field_simp [ha]
  <;> ring

theorem delta_abb_ratio (a b : K) (ha : a ≠ 0) :
    delta a b b = a ^ 2 * ((-(b / a)) * (b / a - 1)) := by
  rw [delta_abb]
  field_simp [ha]
  <;> ring

theorem same_order41_pair_discriminants_nonsquare {E : Set K}
    (hE : Order41SubgroupDuty E) (he : EulerCriterionDuty K)
    (hf : Frobenius81Duty K) (hm : MinusOneSquareDuty K)
    {a b : K} (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) :
    ¬ Square (delta a a b) ∧ ¬ Square (delta a b b) := by
  have ha0 := order41_nonzero hE ha
  have hb0 := order41_nonzero hE hb
  have hrE : b / a ∈ E := by
    simpa [div_eq_mul_inv] using hE.mul_mem b hb a⁻¹ (hE.inv_mem a ha)
  have hr1 : b / a ≠ 1 := by
    intro h
    have hba : b = a := by field_simp [ha0] at h; exact h
    exact hab hba.symm
  have hn := order41_difference_nonsquare hE he hf hrE hr1
  have hr0 : b / a ≠ 0 := div_ne_zero hb0 ha0
  have hmr : Square (-(b / a)) := by
    simpa only [neg_one_mul] using square_mul hm (order41_square hE hrE)
  constructor
  · rw [delta_aab_ratio a b ha0]
    intro hd
    exact hn ((square_scaled_iff a ha0 _).mp hd)
  · rw [delta_abb_ratio a b ha0]
    intro hd
    have hs := (square_scaled_iff a ha0 _).mp hd
    exact hn ((square_mul_iff_of_square_nonzero (neg_ne_zero.mpr hr0) hmr _).mp hs)

theorem same_order41_pair_cap {E : Set K} (hE : Order41SubgroupDuty E)
    (he : EulerCriterionDuty K) (hf : Frobenius81Duty K) (hm : MinusOneSquareDuty K)
    {a b : K} (ha : a ∈ E) (hb : b ∈ E) (hab : a ≠ b) :
    Cap (PSet ({a, b} : Set K)) := by
  obtain ⟨hA, hB⟩ := same_order41_pair_discriminants_nonsquare hE he hf hm ha hb hab
  exact pair_cap_of_repeated_discriminants (order41_nonzero hE ha)
    (order41_nonzero hE hb) hA hB

def scaledCoefficientSet (u : K) (E : Set K) : Set K :=
  {b | ∃ a ∈ E, b = u * a}

theorem quadratic_coefficient_scale (u a b c t : K) :
    quadratic (u * a) (u * b) (u * c) t = u * quadratic a b c t := by
  dsimp [quadratic]
  ring

theorem delta_scale (u a b c : K) :
    delta (u * a) (u * b) (u * c) = u ^ 2 * delta a b c := by
  dsimp [delta]
  ring

/-- Scaling coefficients is the invertible vertical point map (x,y)↦(x,uy).
The proof uses the exact normalized criterion and its scalar identity. -/
theorem Cap_coefficient_scale_iff (u : K) (hu : u ≠ 0) (E : Set K) :
    Cap (PSet (scaledCoefficientSet u E)) ↔ Cap (PSet E) := by
  rw [Cap_iff_normalized_root_safety, Cap_iff_normalized_root_safety]
  constructor
  · intro hs a ha b hb c hc t had hroot
    have hr : quadratic (u * a) (u * b) (u * c) t = 0 := by
      rw [quadratic_coefficient_scale, hroot, mul_zero]
    obtain ⟨hab, hbc, ht⟩ := hs _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨c, hc, rfl⟩ t had hr
    exact ⟨mul_left_cancel₀ hu hab, mul_left_cancel₀ hu hbc, ht⟩
  · intro hs a ha b hb c hc t had hroot
    rcases ha with ⟨a', ha', rfl⟩
    rcases hb with ⟨b', hb', rfl⟩
    rcases hc with ⟨c', hc', rfl⟩
    rw [quadratic_coefficient_scale] at hroot
    have hr := (mul_eq_zero.mp hroot).resolve_left hu
    obtain ⟨hab, hbc, ht⟩ := hs a' ha' b' hb' c' hc' t had hr
    exact ⟨congrArg (u * ·) hab, congrArg (u * ·) hbc, ht⟩

theorem scaled_pair_set (g a b : K) :
    scaledCoefficientSet g ({a, b} : Set K) = ({g * a, g * b} : Set K) := by
  ext c
  constructor
  · rintro ⟨d, hd, rfl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd ⊢
    rcases hd with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact ⟨a, by simp, rfl⟩
    · exact ⟨b, by simp, rfl⟩

theorem same_scaled_order41_pair_cap {E : Set K} (hE : Order41SubgroupDuty E)
    (he : EulerCriterionDuty K) (hf : Frobenius81Duty K) (hm : MinusOneSquareDuty K)
    {g a b : K} (hg : g ≠ 0) (ha : a ∈ scaledCoefficientSet g E)
    (hb : b ∈ scaledCoefficientSet g E) (hab : a ≠ b) :
    Cap (PSet ({a, b} : Set K)) := by
  rcases ha with ⟨a', ha', rfl⟩
  rcases hb with ⟨b', hb', rfl⟩
  have hab' : a' ≠ b' := by intro h; exact hab (congrArg (g * ·) h)
  have hs := (Cap_coefficient_scale_iff g hg ({a', b'} : Set K)).mpr
    (same_order41_pair_cap hE he hf hm ha' hb' hab')
  rwa [scaled_pair_set] at hs

theorem nonsquare_ne_zero {g : K} (hg : ¬ Square g) : g ≠ 0 := by
  intro h
  subst g
  exact hg square_zero

theorem opposite_coset_nonsquare {E : Set K} (hE : Order41SubgroupDuty E)
    {g b : K} (hg : ¬ Square g) (hb : b ∈ scaledCoefficientSet g E) : ¬ Square b := by
  rcases hb with ⟨a, ha, rfl⟩
  intro hs
  have ha0 := order41_nonzero hE ha
  have heq : g * a = a * g := mul_comm _ _
  rw [heq] at hs
  exact hg ((square_mul_iff_of_square_nonzero ha0 (order41_square hE ha) g).mp hs)

theorem opposite_coset_nonzero {E : Set K} (hE : Order41SubgroupDuty E)
    {g b : K} (hg : ¬ Square g) (hb : b ∈ scaledCoefficientSet g E) : b ≠ 0 :=
  nonsquare_ne_zero (opposite_coset_nonsquare hE hg hb)

theorem cosets_disjoint {E : Set K} (hE : Order41SubgroupDuty E)
    {g : K} (hg : ¬ Square g) : Disjoint E (scaledCoefficientSet g E) := by
  apply Set.disjoint_left.mpr
  intro a ha hb
  exact opposite_coset_nonsquare hE hg hb (order41_square hE ha)

theorem two_cosets_nonantipodal {E : Set K} (hE : Order41SubgroupDuty E)
    (hm : MinusOneSquareDuty K) {g : K} (hg : ¬ Square g) :
    NonAntipodal (E ∪ scaledCoefficientSet g E) := by
  intro a ha b hb hsum
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact order41_nonantipodal hE a ha b hb hsum
  · have hbneg : b = -a := by linear_combination hsum
    have hsq : Square b := by
      rw [hbneg]
      simpa only [neg_one_mul] using square_mul hm (order41_square hE ha)
    exact opposite_coset_nonsquare hE hg hb hsq
  · have haneg : a = -b := by linear_combination hsum
    have hsq : Square a := by
      rw [haneg]
      simpa only [neg_one_mul] using square_mul hm (order41_square hE hb)
    exact opposite_coset_nonsquare hE hg ha hsq
  · rcases ha with ⟨a', ha', rfl⟩
    rcases hb with ⟨b', hb', rfl⟩
    have hz : g * (a' + b') = 0 := by linear_combination hsum
    have hab := (mul_eq_zero.mp hz).resolve_left (nonsquare_ne_zero hg)
    exact order41_nonantipodal hE a' ha' b' hb' hab

theorem mixed_ratio_nonsquare {E : Set K} (hE : Order41SubgroupDuty E)
    {g a b : K} (hg : ¬ Square g) (ha : a ∈ E)
    (hb : b ∈ scaledCoefficientSet g E) : ¬ Square (b / a) := by
  intro hratio
  have hs := square_mul (order41_square hE ha) hratio
  have heq : a * (b / a) = b := by field_simp [order41_nonzero hE ha]
  rw [heq] at hs
  exact opposite_coset_nonsquare hE hg hb hs

/-- Both repeated-label discriminants are nonzero and exactly one is square.
The status toggle is derived; no stored mixed-pair Boolean is a premise. -/
theorem mixed_discriminant_square_status {E : Set K} (hE : Order41SubgroupDuty E)
    (he : EulerCriterionDuty K) (hm : MinusOneSquareDuty K)
    {g a b : K} (hg : ¬ Square g) (ha : a ∈ E)
    (hb : b ∈ scaledCoefficientSet g E) :
    delta a a b ≠ 0 ∧ delta a b b ≠ 0 ∧
      (Square (delta a b b) ↔ ¬ Square (delta a a b)) := by
  have ha0 := order41_nonzero hE ha
  have hb0 := opposite_coset_nonzero hE hg hb
  have hr0 : b / a ≠ 0 := div_ne_zero hb0 ha0
  have hrns := mixed_ratio_nonsquare hE hg ha hb
  have hr1 : b / a ≠ 1 := by intro h; rw [h] at hrns; exact hrns square_one
  have hd0 : b / a - 1 ≠ 0 := sub_ne_zero.mpr hr1
  have hmns : ¬ Square (-(b / a)) := by
    intro hs
    have hi := (square_mul_iff_of_square_nonzero (neg_ne_zero.mpr one_ne_zero) hm
      (b / a)).mp (by simpa only [neg_one_mul] using hs)
    exact hrns hi
  rw [delta_aab_ratio a b ha0, delta_abb_ratio a b ha0]
  refine ⟨mul_ne_zero (pow_ne_zero 2 ha0) hd0,
    mul_ne_zero (pow_ne_zero 2 ha0) (mul_ne_zero (neg_ne_zero.mpr hr0) hd0), ?_⟩
  rw [square_scaled_iff a ha0, square_scaled_iff a ha0]
  exact nonsquare_product_toggles he (neg_ne_zero.mpr hr0) hd0 hmns

theorem mixed_pair_not_cap {E : Set K} (hE : Order41SubgroupDuty E)
    (he : EulerCriterionDuty K) (hm : MinusOneSquareDuty K)
    {g a b : K} (hg : ¬ Square g) (ha : a ∈ E)
    (hb : b ∈ scaledCoefficientSet g E) : ¬ Cap (PSet ({a, b} : Set K)) := by
  classical
  have hna := two_cosets_nonantipodal hE hm hg
  have hsub : ({a, b} : Set K) ⊆ E ∪ scaledCoefficientSet g E := by
    intro c hc
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
    rcases hc with rfl | rfl
    · exact Or.inl ha
    · exact Or.inr hb
  have hn : NonAntipodal ({a, b} : Set K) :=
    fun c hc d hd => hna c (hsub hc) d (hsub hd)
  have hab : a ≠ b := by
    intro h
    exact opposite_coset_nonsquare hE hg hb (h ▸ order41_square hE ha)
  obtain ⟨hA0, hB0, htoggle⟩ := mixed_discriminant_square_status hE he hm hg ha hb
  have ham : a ∈ ({a, b} : Set K) := by simp
  have hbm : b ∈ ({a, b} : Set K) := by simp
  by_cases hA : Square (delta a a b)
  · exact square_delta_obstructs_cap hn ham ham hbm (by tauto) hA
  · exact square_delta_obstructs_cap hn ham hbm hbm (by tauto) (htoggle.mpr hA)

/-- The pair obstruction applies to arbitrary coefficient supersets. -/
theorem mixed_pair_obstructs_larger_set {E S : Set K} (hE : Order41SubgroupDuty E)
    (he : EulerCriterionDuty K) (hm : MinusOneSquareDuty K)
    {g a b : K} (hg : ¬ Square g) (ha : a ∈ E)
    (hb : b ∈ scaledCoefficientSet g E) (haS : a ∈ S) (hbS : b ∈ S) :
    ¬ Cap (PSet S) := by
  intro hcap
  apply mixed_pair_not_cap hE he hm hg ha hb
  apply Cap_mono (PSet_mono ?_) hcap
  intro c hc
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc
  rcases hc with rfl | rfl
  · exact haS
  · exact hbS

theorem cap_subset_one_coset {E S : Set K} (hE : Order41SubgroupDuty E)
    (he : EulerCriterionDuty K) (hm : MinusOneSquareDuty K)
    {g : K} (hg : ¬ Square g) (hS : S ⊆ E ∪ scaledCoefficientSet g E)
    (hcap : Cap (PSet S)) : S ⊆ E ∨ S ⊆ scaledCoefficientSet g E := by
  classical
  by_cases hmeet : ∃ a ∈ S, a ∈ E
  · obtain ⟨a, haS, haE⟩ := hmeet
    left
    intro b hbS
    rcases hS hbS with hbE | hbG
    · exact hbE
    · exact False.elim (mixed_pair_obstructs_larger_set hE he hm hg haE hbG haS hbS hcap)
  · right
    intro b hbS
    rcases hS hbS with hbE | hbG
    · exact False.elim (hmeet ⟨b, hbS, hbE⟩)
    · exact hbG

theorem two_cosets_origin_cap_iff {E S : Set K} (hE : Order41SubgroupDuty E)
    (hm : MinusOneSquareDuty K) {g : K} (hg : ¬ Square g)
    (hS : S ⊆ E ∪ scaledCoefficientSet g E) :
    Cap (insert (0 : Point K) (PSet S)) ↔ Cap (PSet S) := by
  apply origin_insertion_cap_iff
  intro a ha b hb
  exact two_cosets_nonantipodal hE hm hg a (hS ha) b (hS hb)

theorem character_reciprocal_delta_identity (r : K) (hr : r ≠ 0) :
    delta 1 r r⁻¹ = -((r - 1) ^ 2 / r) := by
  calc
    delta 1 r r⁻¹ = -((r - 1) ^ 2 / r) - (3 : K) := by
      dsimp [delta]
      field_simp [hr]
      <;> ring
    _ = -((r - 1) ^ 2 / r) := by rw [three_eq_zero]; ring

theorem character_reciprocal_delta_nonzero {r : K} (hr0 : r ≠ 0) (hr1 : r ≠ 1) :
    delta 1 r r⁻¹ ≠ 0 := by
  rw [character_reciprocal_delta_identity r hr0]
  exact neg_ne_zero.mpr (div_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hr1)) hr0)

theorem character_reciprocal_delta_square {E : Set K} (hE : Order41SubgroupDuty E)
    (hm : MinusOneSquareDuty K) {r : K} (hr : r ∈ E) : Square (delta 1 r r⁻¹) := by
  rw [character_reciprocal_delta_identity r (order41_nonzero hE hr)]
  have hs : Square ((r - 1) ^ 2 / r) :=
    square_div ⟨r - 1, rfl⟩ (order41_square hE hr)
  simpa only [neg_one_mul] using square_mul hm hs

theorem order41_reciprocal_distinct {E : Set K} (hE : Order41SubgroupDuty E)
    {r : K} (hr : r ∈ E) (hr1 : r ≠ 1) : 1 ≠ r ∧ 1 ≠ r⁻¹ ∧ r ≠ r⁻¹ := by
  have hr0 := order41_nonzero hE hr
  refine ⟨hr1.symm, ?_, ?_⟩
  · intro h
    have hi := congrArg Inv.inv h
    have hrone : r = 1 := by simpa using hi.symm
    exact hr1 hrone
  · intro h
    have hs : r * r = 1 := by
      calc
        r * r = r⁻¹ * r := by rw [← h]
        _ = 1 := inv_mul_cancel₀ hr0
    have hz : (r - 1) * (r + 1) = 0 := by linear_combination hs
    rcases mul_eq_zero.mp hz with hminus | hplus
    · exact hr1 (sub_eq_zero.mp hminus)
    · have heq : r = -1 := by linear_combination hplus
      apply order41_neg_one_not_mem hE
      rwa [heq] at hr

theorem reciprocal_coefficients_distinct {E : Set K} (hE : Order41SubgroupDuty E)
    {u r : K} (hu : u ∈ E) (hr : r ∈ E) (hr1 : r ≠ 1) :
    u * r⁻¹ ≠ u ∧ u * r⁻¹ ≠ u * r ∧ u ≠ u * r := by
  obtain ⟨h1r, h1ri, hrri⟩ := order41_reciprocal_distinct hE hr hr1
  have hu0 := order41_nonzero hE hu
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hi : r⁻¹ = 1 := mul_left_cancel₀ hu0 (by simpa only [mul_one] using h)
    exact h1ri hi.symm
  · intro h
    exact hrri (mul_left_cancel₀ hu0 h).symm
  · intro h
    have hi : 1 = r := mul_left_cancel₀ hu0 (by simpa only [mul_one] using h)
    exact h1r hi

/-- Actual zero-sum obstruction for a coefficient superset. The three
nonantipodal sums follow from E, independently of the rest of that superset. -/
theorem reciprocal_obstruction {E S : Set K} (hE : Order41SubgroupDuty E)
    (hm : MinusOneSquareDuty K) {u r : K}
    (hu : u ∈ E) (hr : r ∈ E) (hr1 : r ≠ 1)
    (hleft : u * r⁻¹ ∈ S) (hmid : u ∈ S) (hright : u * r ∈ S) :
    ¬ Cap (PSet S) := by
  have hleftE := hE.mul_mem u hu r⁻¹ (hE.inv_mem r hr)
  have hrightE := hE.mul_mem u hu r hr
  have hn := order41_nonantipodal hE
  have hdist := reciprocal_coefficients_distinct hE hu hr hr1
  have hs0 := character_reciprocal_delta_square hE hm hr
  have hs : Square (delta (u * r⁻¹) u (u * r)) := by
    have hscaled := square_mul ⟨u, rfl⟩ hs0
    have hperm : delta (u * r⁻¹) u (u * r) = u ^ 2 * delta 1 r r⁻¹ := by
      dsimp [delta]
      ring
    rwa [← hperm] at hscaled
  exact square_delta_obstructs_cap_of_sums hleft hmid hright
    (hn _ hleftE _ hu) (hn _ hleftE _ hrightE) (hn _ hu _ hrightE)
    (by intro h; exact hdist.1 h.1) hs

end
end Partials.Cap
