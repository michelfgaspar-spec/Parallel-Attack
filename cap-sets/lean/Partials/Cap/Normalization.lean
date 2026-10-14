import Partials.Cap.Model
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-! R5 source-only specialization of the punctured-parabola construction.
The construction and normalization antecedents are Grace--Voloch, Algebraic
Capsets, §2; the frozen manuscript gives the required converse explicitly.
No concrete F₃⁸ instance or finite certificate is admitted by this file. -/
namespace Partials.Cap

noncomputable section
variable {K : Type*} [Field K] [CharP K 3]

theorem three_eq_zero : (3 : K) = 0 := CharP.cast_eq_zero K 3

theorem two_eq_neg_one : (2 : K) = -1 := by
  linear_combination (three_eq_zero (K := K))

theorem two_ne_zero : (2 : K) ≠ 0 := by
  rw [two_eq_neg_one]
  exact neg_ne_zero.mpr one_ne_zero

theorem one_ne_neg_one : (1 : K) ≠ -1 := by
  intro h
  have htwo : (2 : K) = 0 := by linear_combination h
  exact two_ne_zero htwo

theorem parabola_fst (a x : K) : (parabolaPoint a x).1 = x := rfl
theorem parabola_snd (a x : K) : (parabolaPoint a x).2 = a * x ^ 2 := rfl

theorem parabolaPoint_injective_coeff {a b x : K} (hx : x ≠ 0)
    (h : parabolaPoint a x = parabolaPoint b x) : a = b := by
  have hs := congrArg Prod.snd h
  dsimp [parabolaPoint] at hs
  exact mul_right_cancel₀ (pow_ne_zero 2 hx) hs

theorem parabolaPoint_injective_parameters {a b x y : K} (hx : x ≠ 0)
    (h : parabolaPoint a x = parabolaPoint b y) : a = b ∧ x = y := by
  have hxy := congrArg Prod.fst h
  dsimp [parabolaPoint] at hxy
  subst y
  exact ⟨parabolaPoint_injective_coeff hx h, rfl⟩

theorem parabola_membership {S : Set K} {a x : K}
    (ha : a ∈ S) (hx : x ≠ 0) : parabolaPoint a x ∈ PSet S :=
  ⟨a, ha, x, hx, rfl⟩

theorem punctured_first_ne_zero {S : Set K} {p : Point K}
    (hp : p ∈ PSet S) : p.1 ≠ 0 := by
  rcases hp with ⟨a, ha, x, hx, rfl⟩
  exact hx

theorem origin_not_mem (S : Set K) : (0 : Point K) ∉ PSet S := by
  intro h
  exact punctured_first_ne_zero h rfl

theorem distinct_fibres_disjoint {a b : K} (hab : a ≠ b) :
    Disjoint (Partials.Interface.PuncturedParabola a)
      (Partials.Interface.PuncturedParabola b) := by
  apply Set.disjoint_left.mpr
  intro p hp hq
  rcases hp with ⟨x, hx, rfl⟩
  rcases hq with ⟨y, hy, hxy⟩
  exact hab (parabolaPoint_injective_parameters hx hxy).1

/-- The two coordinates scale with different powers. This is field scaling,
not a permutation or ordinary multiplication of the stored integer labels. -/
def normalizeAt (u : K) (p : Point K) : Point K := (p.1 / u, p.2 / u ^ 2)
def denormalizeAt (u : K) (p : Point K) : Point K := (u * p.1, u ^ 2 * p.2)

theorem denormalize_normalize (u : K) (hu : u ≠ 0) (p : Point K) :
    denormalizeAt u (normalizeAt u p) = p := by
  ext <;> dsimp [normalizeAt, denormalizeAt] <;> field_simp [hu]

theorem normalize_denormalize (u : K) (hu : u ≠ 0) (p : Point K) :
    normalizeAt u (denormalizeAt u p) = p := by
  ext <;> dsimp [normalizeAt, denormalizeAt] <;> field_simp [hu]

theorem normalizeAt_injective (u : K) (hu : u ≠ 0) :
    Function.Injective (normalizeAt u : Point K → Point K) := by
  intro p q hpq
  have h := congrArg (denormalizeAt u) hpq
  simpa [denormalize_normalize u hu] using h

theorem normalizeAt_add (u : K) (p q : Point K) :
    normalizeAt u (p + q) = normalizeAt u p + normalizeAt u q := by
  ext <;> dsimp [normalizeAt] <;> simp only [add_div]

theorem normalizeAt_zero (u : K) : normalizeAt u (0 : Point K) = 0 := by
  ext <;> simp [normalizeAt]

theorem normalizeAt_sum_zero_iff (u : K) (hu : u ≠ 0) (p q r : Point K) :
    normalizeAt u p + normalizeAt u q + normalizeAt u r = 0 ↔ p + q + r = 0 := by
  rw [← normalizeAt_add, ← normalizeAt_add]
  simpa only [normalizeAt_zero] using
    (normalizeAt_injective u hu).eq_iff (a := p + q + r) (b := 0)

theorem normalize_parabola (a x u : K) (hu : u ≠ 0) :
    normalizeAt u (parabolaPoint a x) = parabolaPoint a (x / u) := by
  apply Prod.ext <;> simp [normalizeAt, parabolaPoint, div_pow, mul_div_assoc]

theorem normalizeAt_preserves_union (S : Set K) (u : K) (hu : u ≠ 0) :
    normalizeAt u '' PSet S = PSet S := by
  apply Set.Subset.antisymm
  · rintro p ⟨q, ⟨a, ha, x, hx, rfl⟩, rfl⟩
    change normalizeAt u (parabolaPoint a x) ∈ PSet S
    rw [normalize_parabola a x u hu]
    exact parabola_membership ha (div_ne_zero hx hu)
  · rintro p ⟨a, ha, x, hx, rfl⟩
    refine ⟨parabolaPoint a (u * x), parabola_membership ha (mul_ne_zero hu hx), ?_⟩
    rw [normalize_parabola a (u * x) u hu]
    congr 1
    field_simp [hu]

theorem normalized_zero_sum_iff (a b c t : K) :
    normA a t + normB b + normC c t = 0 ↔ quadratic a b c t = 0 := by
  constructor
  · intro h
    have hs := congrArg Prod.snd h
    dsimp [normA, normB, normC, parabolaPoint, quadratic] at *
    linear_combination hs
  · intro h
    apply Prod.ext
    · dsimp [normA, normB, normC, parabolaPoint]
      ring
    · dsimp [normA, normB, normC, parabolaPoint, quadratic] at *
      linear_combination h

/-- Exact first-coordinate normalization. The third nonzero coordinate is
what excludes t=-1; that endpoint is not discarded by convention. -/
theorem normalized_coordinates {x y z : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hz : z ≠ 0) (hxyz : x + y + z = 0) :
    ratioAdmissible (x / y) ∧ z / y = -(x / y) - 1 := by
  have hthird : z / y = -(x / y) - 1 := by
    field_simp [hy]
    linear_combination hxyz
  refine ⟨⟨div_ne_zero hx hy, ?_⟩, hthird⟩
  intro ht
  have hzy : z / y = 0 := by rw [hthird, ht]; ring
  exact (div_ne_zero hz hy) hzy

theorem parabola_triple_normalization {a b c x y z : K}
    (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (h : parabolaPoint a x + parabolaPoint b y + parabolaPoint c z = 0) :
    ratioAdmissible (x / y) ∧ quadratic a b c (x / y) = 0 := by
  have hf := congrArg Prod.fst h
  dsimp [parabolaPoint] at hf
  obtain ⟨had, hthird⟩ := normalized_coordinates hx hy hz hf
  refine ⟨had, (normalized_zero_sum_iff a b c (x / y)).mp ?_⟩
  have hs := (normalizeAt_sum_zero_iff y hy
    (parabolaPoint a x) (parabolaPoint b y) (parabolaPoint c z)).mpr h
  rw [normalize_parabola a x y hy, normalize_parabola b y y hy,
    normalize_parabola c z y hy, div_self hy, hthird] at hs
  exact hs

theorem normalized_points_mem {S : Set K} {a b c t : K}
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (ht : ratioAdmissible t) :
    normA a t ∈ PSet S ∧ normB b ∈ PSet S ∧ normC c t ∈ PSet S := by
  refine ⟨parabola_membership ha ht.1, parabola_membership hb one_ne_zero,
    parabola_membership hc ?_⟩
  intro hz
  apply ht.2
  linear_combination -hz

theorem Cap_mono {U V : Set (Point K)} (hUV : U ⊆ V) (hV : Cap V) : Cap U := by
  intro a ha b hb c hc hab hac hbc
  exact hV a (hUV ha) b (hUV hb) c (hUV hc) hab hac hbc

theorem PSet_mono {S T : Set K} (hST : S ⊆ T) : PSet S ⊆ PSet T := by
  rintro p ⟨a, ha, hp⟩
  exact ⟨a, hST ha, hp⟩

theorem origin_punctured_sum_ne_zero {S : Set K} (hn : NonAntipodal S)
    {p q : Point K} (hp : p ∈ PSet S) (hq : q ∈ PSet S) :
    (0 : Point K) + p + q ≠ 0 := by
  rcases hp with ⟨a, ha, x, hx, rfl⟩
  rcases hq with ⟨b, hb, y, hy, rfl⟩
  intro h
  have hf := congrArg Prod.fst h
  have hs := congrArg Prod.snd h
  dsimp at hf hs
  have hxy : y = -x := by linear_combination hf
  rw [hxy] at hs
  have hab : (a + b) * x ^ 2 = 0 := by linear_combination hs
  exact (mul_ne_zero (hn a ha b hb) (pow_ne_zero 2 hx)) hab

/-- Adding the common origin changes caphood only when antipodal
coefficients could create a new distinct zero-sum triple. -/
theorem origin_insertion_cap_iff {S : Set K} (hn : NonAntipodal S) :
    Cap (insert (0 : Point K) (PSet S)) ↔ Cap (PSet S) := by
  constructor
  · exact Cap_mono (Set.subset_insert _ _)
  · intro hcap p hp q hq r hr hpq hpr hqr
    by_cases hp0 : p = 0
    · subst p
      have hqP : q ∈ PSet S := by
        rcases hq with hq | hq
        · exact False.elim (hpq hq.symm)
        · exact hq
      have hrP : r ∈ PSet S := by
        rcases hr with hr | hr
        · exact False.elim (hpr hr.symm)
        · exact hr
      exact origin_punctured_sum_ne_zero hn hqP hrP
    have hpP : p ∈ PSet S := (Set.mem_insert_iff.mp hp).resolve_left hp0
    by_cases hq0 : q = 0
    · subst q
      have hrP : r ∈ PSet S := by
        rcases hr with hr | hr
        · exact False.elim (hqr hr.symm)
        · exact hr
      simpa [add_comm, add_left_comm, add_assoc] using
        (origin_punctured_sum_ne_zero hn hpP hrP)
    have hqP : q ∈ PSet S := (Set.mem_insert_iff.mp hq).resolve_left hq0
    by_cases hr0 : r = 0
    · subst r
      simpa [add_comm, add_left_comm, add_assoc] using
        (origin_punctured_sum_ne_zero hn hpP hqP)
    have hrP : r ∈ PSet S := (Set.mem_insert_iff.mp hr).resolve_left hr0
    exact hcap p hpP q hqP r hrP hpq hpr hqr

/-- A coefficient/first-coordinate parameterization. The inverse follows
from punctured-fibre uniqueness, with no numerical field table premise. -/
def parabolaParameterMap (S : Set K) : S × {x : K // x ≠ 0} → PSet S :=
  fun q => ⟨parabolaPoint q.1.val q.2.val,
    parabola_membership q.1.property q.2.property⟩

theorem parabolaParameterMap_bijective (S : Set K) :
    Function.Bijective (parabolaParameterMap S) := by
  constructor
  · intro p q hpq
    have h := congrArg Subtype.val hpq
    obtain ⟨hc, hx⟩ := parabolaPoint_injective_parameters p.2.property h
    exact Prod.ext (Subtype.ext hc) (Subtype.ext hx)
  · rintro ⟨p, a, ha, x, hx, rfl⟩
    exact ⟨(⟨a, ha⟩, ⟨x, hx⟩), rfl⟩

def parabolaParameterEquiv (S : Set K) : S × {x : K // x ≠ 0} ≃ PSet S :=
  Equiv.ofBijective (parabolaParameterMap S) (parabolaParameterMap_bijective S)

theorem parabola_fibre_product_count [Fintype K] (S : Set K) :
    Nat.card (PSet S) = Nat.card S * Nat.card {x : K // x ≠ 0} := by
  rw [← Nat.card_congr (parabolaParameterEquiv S), Nat.card_prod]

/-- Narrow generic cardinality import, still uninhabited in the R5 source.
It concerns the complement of one field element, not the cap maximum. -/
def NonzeroFibreCardDuty (K : Type*) [Field K] : Prop :=
  Nat.card {x : K // x ≠ 0} = Nat.card K - 1

theorem nonzero_fibre_card_from_fintype [Fintype K] : NonzeroFibreCardDuty K := by
  classical
  unfold NonzeroFibreCardDuty
  simp only [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype_compl (fun x : K => x = 0), Fintype.card_subtype_eq]

theorem parabola_point_count [Fintype K] (hcard : NonzeroFibreCardDuty K)
    (S : Set K) : Nat.card (PSet S) = (Nat.card K - 1) * Nat.card S := by
  rw [parabola_fibre_product_count, hcard, Nat.mul_comm]

end
end Partials.Cap
