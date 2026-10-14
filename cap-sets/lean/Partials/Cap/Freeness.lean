import Partials.Cap.Symmetry
import Mathlib.Tactic.LinearCombination

/-! Blind source for main.tex, reciprocal lemma and free-action lemma.
The remaining action-power primitives concern maps on all 41 vertices;
they do not assume freeness of any five-set. -/
namespace Partials.Cap

noncomputable section

def opposite (u v : Vertex) : Vertex := -v + u
def oppositeImage (u : Vertex) (T : Finset Vertex) : Finset Vertex := T.image (opposite u)
def center (u : Vertex) : Vertex := u / 2

private theorem vertex_two_ne_zero : (2 : Vertex) ≠ 0 := by decide

theorem opposite_involutive (u : Vertex) : Function.Involutive (opposite u) := by
  intro v
  simp [opposite]

theorem center_twice (u : Vertex) : (2 : Vertex) * center u = u := by
  unfold center
  field_simp [vertex_two_ne_zero]

theorem opposite_fixed_iff (u v : Vertex) : opposite u v = v ↔ v = center u := by
  constructor
  · intro h
    apply mul_left_cancel₀ vertex_two_ne_zero
    rw [center_twice]
    unfold opposite at h
    linear_combination -h
  · rintro rfl
    unfold opposite
    have := center_twice u
    linear_combination -this

/-- A general finite parity argument, independent of the field certificate.
Remove one two-cycle and induct on cardinality. -/
theorem involution_even_of_no_fixed {α : Type*} [DecidableEq α]
    (f : α → α) (hinv : Function.Involutive f) (s : Finset α)
    (hstable : ∀ x ∈ s, f x ∈ s) (hno : ∀ x ∈ s, f x ≠ x) :
    s.card % 2 = 0 := by
  have aux : ∀ n : ℕ, ∀ r : Finset α, r.card = n →
      (∀ x ∈ r, f x ∈ r) → (∀ x ∈ r, f x ≠ x) → n % 2 = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro r hcard hst hnf
      by_cases he : r = ∅
      · subst r
        simpa using congrArg (fun m => m % 2) hcard.symm
      obtain ⟨x, hx⟩ := Finset.nonempty_iff_ne_empty.mpr he
      have hfx : f x ∈ r := hst x hx
      have hfxne : f x ≠ x := hnf x hx
      let r' := (r.erase x).erase (f x)
      have hc₁ : (r.erase x).card + 1 = r.card := Finset.card_erase_add_one hx
      have hfxerase : f x ∈ r.erase x := Finset.mem_erase.mpr ⟨hfxne, hfx⟩
      have hc₂ : r'.card + 1 = (r.erase x).card := Finset.card_erase_add_one hfxerase
      have hsmall : r'.card < n := by omega
      have hst' : ∀ y ∈ r', f y ∈ r' := by
        intro y hy
        obtain ⟨hyfx, hyerase⟩ := Finset.mem_erase.mp hy
        obtain ⟨hyx, hyr⟩ := Finset.mem_erase.mp hyerase
        have hyfx' : y ≠ f x := hyfx
        have hyx' : y ≠ x := hyx
        apply Finset.mem_erase.mpr
        refine ⟨?_, Finset.mem_erase.mpr ⟨?_, hst y hyr⟩⟩
        · intro h
          exact hyx' (hinv.injective h)
        · intro h
          have : y = f x := by simpa [hinv y] using congrArg f h
          exact hyfx' this
      have hnf' : ∀ y ∈ r', f y ≠ y := by
        intro y hy
        exact hnf y (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy))
      have hi : r'.card % 2 = 0 := ih r'.card hsmall r' rfl hst' hnf'
      omega
  exact aux s.card s rfl hstable hno

theorem odd_involution_has_fixed {α : Type*} [DecidableEq α]
    (f : α → α) (hinv : Function.Involutive f) (s : Finset α)
    (hstable : ∀ x ∈ s, f x ∈ s) (hodd : s.card % 2 = 1) :
    ∃ x ∈ s, f x = x := by
  by_contra h
  push_neg at h
  have he := involution_even_of_no_fixed f hinv s hstable h
  omega

def ArithmeticProgressionEdges (graph : Hypergraph Vertex) : Prop :=
  ∀ i d : Vertex, d ≠ 0 → ({i - d, i, i + d} : Finset Vertex) ∈ graph

theorem opposite_five_contains_progression (u : Vertex) (T : Finset Vertex)
    (hc : T.card = 5) (hst : oppositeImage u T = T) :
    ∃ d : Vertex, d ≠ 0 ∧ ({center u - d, center u, center u + d} : Finset Vertex) ⊆ T := by
  have hstable : ∀ x ∈ T, opposite u x ∈ T := by
    intro x hx
    rw [← hst]
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  obtain ⟨c, hcT, hcfix⟩ := odd_involution_has_fixed (opposite u) (opposite_involutive u)
    T hstable (by omega)
  have hceq : c = center u := (opposite_fixed_iff u c).1 hcfix
  have hcenter : center u ∈ T := hceq ▸ hcT
  have hex : ∃ v ∈ T, v ≠ center u := by
    by_contra h
    push_neg at h
    have hsub : T ⊆ {center u} := by
      intro v hv
      simpa using h v hv
    have := Finset.card_le_card hsub
    simp only [Finset.card_singleton] at this
    omega
  obtain ⟨v, hv, hvne⟩ := hex
  refine ⟨v - center u, sub_ne_zero.mpr hvne, ?_⟩
  have hop : center u - (v - center u) = opposite u v := by
    unfold opposite
    have := center_twice u
    linear_combination this
  have hv' : center u + (v - center u) = v := by ring
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · rw [hop]
    exact hstable v hv
  · exact hcenter
  · rw [hv']
    exact hv

theorem no_opposite_stabilizer_of_independent_five (graph : Hypergraph Vertex)
    (hap : ArithmeticProgressionEdges graph) (T : Finset Vertex)
    (hind : Independent graph T) (hc : T.card = 5) (u : Vertex) :
    oppositeImage u T ≠ T := by
  intro hst
  obtain ⟨d, hd, hsub⟩ := opposite_five_contains_progression u T hc hst
  exact hind _ (hap _ d hd) hsub

theorem image_iteration_stable {α : Type*} [DecidableEq α]
    (f : α → α) (s : Finset α) (h : s.image f = s) (n : ℕ) :
    s.image (f^[n]) = s := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      s.image (f^[n + 1]) = (s.image (f^[n])).image f := by
        rw [Finset.image_image]
        congr 1
        funext x
        exact Function.iterate_succ_apply' f n x
      _ = s.image f := by rw [ih]
      _ = s := h

/-- Unfinished primitive transitivity of a nonzero translation on Z/41.
This is a statement about all points and iterates, with no independent sets. -/
def PrimeTranslationCycleDuty : Prop :=
  ∀ t : Vertex, t ≠ 0 → ∀ x y : Vertex, ∃ n : ℕ, ((fun v => v + t)^[n]) x = y

/-- Unfinished primitive half-power reduction. The exponent j is not zero;
finite order 2/4/8 and the geometric sum should supply this map identity. -/
def AffineHalfPowerDuty : Prop :=
  ∀ t : Vertex, ∀ j : Fin 8, j ≠ 0 →
    ∃ n : ℕ, ∃ u : Vertex, 0 < n ∧ (affine t j)^[n] = opposite u

theorem translation_stable_nonempty_eq_univ (hcycle : PrimeTranslationCycleDuty)
    (t : Vertex) (ht : t ≠ 0) (T : Finset Vertex) (hne : T.Nonempty)
    (hst : translateImage t T = T) : T = Finset.univ := by
  obtain ⟨x, hx⟩ := hne
  apply Finset.eq_univ_of_forall
  intro y
  obtain ⟨n, hn⟩ := hcycle t ht x y
  have hi : T.image ((fun v => v + t)^[n]) = T := image_iteration_stable _ _ hst n
  rw [← hi]
  exact Finset.mem_image.mpr ⟨x, hx, hn⟩

theorem affine_five_freeness (graph : Hypergraph Vertex)
    (hap : ArithmeticProgressionEdges graph) (hcycle : PrimeTranslationCycleDuty)
    (hhalf : AffineHalfPowerDuty) (T : Finset Vertex)
    (hind : Independent graph T) (hc : T.card = 5)
    (t : Vertex) (j : Fin 8) (hst : affineImage t j T = T) : t = 0 ∧ j = 0 := by
  by_cases hj : j = 0
  · subst j
    refine ⟨?_, rfl⟩
    by_contra ht
    have hne : T.Nonempty := Finset.card_pos.mp (by omega)
    have hu := translation_stable_nonempty_eq_univ hcycle t ht T hne
      (by simpa [affine_zero_is_translation] using hst)
    have huniv : (Finset.univ : Finset Vertex).card = 41 := by simp [Vertex]
    rw [hu, huniv] at hc
    omega
  · obtain ⟨n, u, hn, hmap⟩ := hhalf t j hj
    have hi : oppositeImage u T = T := by
      simpa [oppositeImage, hmap] using image_iteration_stable (affine t j) T hst n
    exact False.elim ((no_opposite_stabilizer_of_independent_five graph hap T hind hc u) hi)

section Field
variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

theorem reciprocal_delta_identity {r : K} (hr : r ≠ 0) :
    delta 1 r r⁻¹ = -((r - 1) ^ 2) / r := by
  have hthree : (3 : K) = 0 := CharP.cast_eq_zero K 3
  unfold delta
  field_simp [hr]
  linear_combination -r * hthree

theorem reciprocal_delta_square {r : K} (hr : r ≠ 0)
    (hs : Square r) (hm : Square (-1 : K)) : Square (delta 1 r r⁻¹) := by
  obtain ⟨s, hs⟩ := hs
  obtain ⟨w, hw⟩ := hm
  have hsn : s ≠ 0 := by intro h; simp [h] at hs; exact hr hs.symm
  rw [reciprocal_delta_identity hr]
  refine ⟨w * (r - 1) / s, ?_⟩
  rw [div_pow, mul_pow, hw, hs]
  ring

theorem reciprocal_delta_nonzero {r : K} (hr : r ≠ 0) (hr1 : r ≠ 1) :
    delta 1 r r⁻¹ ≠ 0 := by
  rw [reciprocal_delta_identity hr]
  exact div_ne_zero (neg_ne_zero.mpr (pow_ne_zero 2 (sub_ne_zero.mpr hr1))) hr

theorem reciprocal_scaled_delta_square {u r : K} (hr : r ≠ 0)
    (hs : Square r) (hm : Square (-1 : K)) :
    Square (delta (u * r⁻¹) u (u * r)) := by
  have hsq := reciprocal_delta_square hr hs hm
  obtain ⟨w, hw⟩ := hsq
  refine ⟨u * w, ?_⟩
  calc
    (u * w) ^ 2 = u ^ 2 * delta 1 r r⁻¹ := by rw [mul_pow, hw]
    _ = delta (u * r⁻¹) u (u * r) := by unfold delta; ring

theorem progression_vertices_distinct (i d : Vertex) (hd : d ≠ 0) :
    i - d ≠ i ∧ i - d ≠ i + d ∧ i ≠ i + d := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have : d = 0 := by linear_combination -h
    exact hd this
  · intro h
    have htwo : (2 : Vertex) * d = 0 := by linear_combination -h
    exact hd ((mul_eq_zero.mp htwo).resolve_left vertex_two_ne_zero)
  · intro h
    have : d = 0 := by linear_combination -h
    exact hd this

theorem discriminant_progression_edges {z : K} (h : ExponentActionDuty z) :
    ArithmeticProgressionEdges (discriminantHypergraph z) := by
  intro i d hd
  obtain ⟨hid, hidd, hiadd⟩ := progression_vertices_distinct i d hd
  have hcoeff : coefficient z (i - d) = coefficient z i * (coefficient z d)⁻¹ := by
    rw [sub_eq_add_neg, h.coefficient_add, h.coefficient_neg]
  have hs : Square (delta (coefficient z (i - d)) (coefficient z i)
      (coefficient z (i + d))) := by
    rw [hcoeff, h.coefficient_add]
    exact reciprocal_scaled_delta_square (h.coefficient_nonzero d)
      (h.coefficient_square d) h.minus_one_square
  simp only [discriminantHypergraph, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨by simp [hid, hidd, hiadd], i - d, by simp, i, by simp,
    i + d, by simp, hid, hidd, hiadd, hs⟩

theorem independent_five_action_free {z : K} (h : ExponentActionDuty z)
    (hcycle : PrimeTranslationCycleDuty) (hhalf : AffineHalfPowerDuty)
    (T : Finset Vertex) (hind : Independent (discriminantHypergraph z) T)
    (hc : T.card = 5) (t : Vertex) (j : Fin 8) (hst : affineImage t j T = T) :
    t = 0 ∧ j = 0 :=
  affine_five_freeness _ (discriminant_progression_edges h) hcycle hhalf T hind hc t j hst

end Field
end
end Partials.Cap
