import Partials.Cap.Model
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum.Prime

/-! Blind R5 proof source, adapted from main.tex, §§3 and 5. No tactic in
this file has been run. Concrete order/Frobenius/exponent-coordinate facts
are named unfinished duties; they are not admitted instances or axioms. -/
namespace Partials.Cap

noncomputable section

private instance vertexPrime : Fact (Nat.Prime 41) := ⟨by norm_num⟩

/-- Exact finite arithmetic about 3 in Z/41. Not instantiated here. -/
structure ThreeOrderDuty : Prop where
  three_ne_zero : (3 : Vertex) ≠ 0
  power_four : (3 : Vertex) ^ 4 = -1
  power_eight : (3 : Vertex) ^ 8 = 1
  powers_injective : Function.Injective (fun j : Fin 8 => (3 : Vertex) ^ j.val)

theorem three_order_from_finite_arithmetic : ThreeOrderDuty := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  unfold Function.Injective
  decide

theorem affine_injective (h : ThreeOrderDuty) (t : Vertex) (j : Fin 8) :
    Function.Injective (affine t j) := by
  intro a b hab
  have hm : (3 : Vertex) ^ j.val ≠ 0 := pow_ne_zero _ h.three_ne_zero
  apply mul_left_cancel₀ hm
  exact add_right_cancel hab

theorem affine_parameter_injective (h : ThreeOrderDuty) :
    Function.Injective (fun p : Vertex × Fin 8 => affine p.1 p.2) := by
  intro p q hpq
  have ht : p.1 = q.1 := by
    have := congrFun hpq 0
    simpa [affine] using this
  have hk : (3 : Vertex) ^ p.2.val = (3 : Vertex) ^ q.2.val := by
    have := congrFun hpq 1
    simpa [affine, ht] using this
  exact Prod.ext ht (h.powers_injective hk)

theorem finset_image_injective {α β : Type*} [DecidableEq α] [DecidableEq β]
    {f : α → β} (hf : Function.Injective f) :
    Function.Injective (fun s : Finset α => s.image f) := by
  intro s t hst
  change s.image f = t.image f at hst
  apply Finset.ext
  intro a
  constructor
  · intro ha
    have hfa : f a ∈ t.image f := by rw [← hst]; exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hfa
    exact hf hba ▸ hb
  · intro ha
    have hfa : f a ∈ s.image f := by rw [hst]; exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hfa
    exact hf hba ▸ hb

theorem affineImage_card (h : ThreeOrderDuty) (t : Vertex) (j : Fin 8)
    (T : Finset Vertex) : (affineImage t j T).card = T.card := by
  exact Finset.card_image_of_injective T (affine_injective h t j)

def translateImage (t : Vertex) (T : Finset Vertex) : Finset Vertex :=
  T.image (fun v => v + t)

theorem translateImage_card (t : Vertex) (T : Finset Vertex) :
    (translateImage t T).card = T.card := by
  exact Finset.card_image_of_injective T (fun _ _ h => add_right_cancel h)

theorem translateImage_comp (s t : Vertex) (T : Finset Vertex) :
    translateImage s (translateImage t T) = translateImage (t + s) T := by
  unfold translateImage
  rw [Finset.image_image]
  congr 1
  funext v
  exact add_assoc v t s

theorem translateImage_zero (T : Finset Vertex) : translateImage 0 T = T := by
  simp [translateImage]

theorem translateImage_inverse (t : Vertex) (T : Finset Vertex) :
    translateImage (-t) (translateImage t T) = T := by
  rw [translateImage_comp]
  simp [translateImage_zero]

theorem translated_root {T : Finset Vertex} {v : Vertex} (hv : v ∈ T) :
    0 ∈ translateImage (-v) T := by
  exact Finset.mem_image.mpr ⟨v, hv, by simp⟩

theorem affine_zero_is_translation (t : Vertex) (T : Finset Vertex) :
    affineImage t 0 T = translateImage t T := by
  unfold affineImage translateImage
  congr 1
  funext v
  simp [affine]

/-- Finite edge transport, with equality of the entire graph rather than
only a forward implication on selected edges. -/
structure HypergraphSymmetry {α : Type*} [DecidableEq α]
    (graph : Hypergraph α) (f : α → α) : Prop where
  injective : Function.Injective f
  graph_image : graph.image (fun e => e.image f) = graph

theorem independent_image_iff {α : Type*} [DecidableEq α]
    {graph : Hypergraph α} {f : α → α} (h : HypergraphSymmetry graph f)
    (s : Finset α) : Independent graph (s.image f) ↔ Independent graph s := by
  constructor
  · intro hind e he hes
    have hei : e.image f ∈ graph := by
      rw [← h.graph_image]
      exact Finset.mem_image.mpr ⟨e, he, rfl⟩
    exact hind (e.image f) hei (Finset.image_subset_image hes)
  · intro hind e he hes
    have hei : e ∈ graph.image (fun e => e.image f) := by rw [h.graph_image]; exact he
    obtain ⟨e₀, he₀, heq⟩ := Finset.mem_image.mp hei
    apply hind e₀ he₀
    intro x hx
    have hfx : f x ∈ s.image f := hes (heq ▸ Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hfx
    exact h.injective hyx ▸ hy

theorem graph_image_of_edge_iff {α : Type*} [DecidableEq α]
    (graph : Hypergraph α) (f : α → α) (hf : Function.Injective f)
    (hedge : ∀ e, e.image f ∈ graph ↔ e ∈ graph) :
    HypergraphSymmetry graph f := by
  refine ⟨hf, ?_⟩
  have hsub : graph.image (fun e => e.image f) ⊆ graph := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact (hedge a).2 ha
  apply Finset.eq_of_subset_of_card_le hsub
  rw [Finset.card_image_of_injective graph (finset_image_injective hf)]

section Field
variable {K : Type*} [Field K] [CharP K 3]

theorem delta_scaling (u a b c : K) :
    delta (u * a) (u * b) (u * c) = u ^ 2 * delta a b c := by
  unfold delta
  ring

theorem square_scaling_iff {u d : K} (hu : u ≠ 0) :
    Square (u ^ 2 * d) ↔ Square d := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x / u, ?_⟩
    apply (mul_right_cancel₀ (pow_ne_zero 2 hu))
    calc
      (x / u) ^ 2 * u ^ 2 = x ^ 2 := by field_simp [hu] <;> ring
      _ = (u ^ 2 * d) := hx
      _ = d * u ^ 2 := by ring
  · rintro ⟨x, hx⟩
    refine ⟨u * x, ?_⟩
    rw [mul_pow, hx]

/-- Primitive field Frobenius facts. A generic Field/CharP 3 instance alone
does not make its cube map surjective; the concrete finite-field bridge is
therefore visible. This structure has no square-status or orbit conclusion. -/
structure CubeFrobeniusDuty (K : Type*) [Field K] [CharP K 3] : Prop where
  cube_add : ∀ a b : K, (a + b) ^ 3 = a ^ 3 + b ^ 3
  cube_neg : ∀ a : K, (-a) ^ 3 = -(a ^ 3)
  cube_bijective : Function.Bijective (fun a : K => a ^ 3)

theorem delta_cube (h : CubeFrobeniusDuty K) (a b c : K) :
    delta (a ^ 3) (b ^ 3) (c ^ 3) = (delta a b c) ^ 3 := by
  rw [delta, delta, h.cube_neg, h.cube_add, h.cube_add]
  ring

theorem square_cube_iff (h : CubeFrobeniusDuty K) (d : K) :
    Square (d ^ 3) ↔ Square d := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := h.cube_bijective.2 y
    refine ⟨x, h.cube_bijective.1 ?_⟩
    calc
      (x ^ 2) ^ 3 = (x ^ 3) ^ 2 := by ring
      _ = d ^ 3 := hy
  · rintro ⟨x, hx⟩
    refine ⟨x ^ 3, ?_⟩
    calc
      (x ^ 3) ^ 2 = (x ^ 2) ^ 3 := by ring
      _ = d ^ 3 := by rw [hx]

theorem delta_frobenius_power (h : CubeFrobeniusDuty K) (a b c : K) (n : ℕ) :
    delta (a ^ (3 ^ n)) (b ^ (3 ^ n)) (c ^ (3 ^ n)) = (delta a b c) ^ (3 ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ]
      simp only [pow_mul]
      rw [delta_cube h, ih]

theorem square_frobenius_power_iff (h : CubeFrobeniusDuty K) (d : K) (n : ℕ) :
    Square (d ^ (3 ^ n)) ↔ Square d := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.pow_succ, pow_mul, square_cube_iff h]
      exact ih

/-- Exact exponent-coordinate primitive duties, not finite-set classifications.
Their concrete discharge needs the specified h, order 41 and modular reduction. -/
structure ExponentActionDuty [DecidableEq K] (z : K) : Prop where
  coefficient_nonzero : ∀ i, coefficient z i ≠ 0
  coefficient_injective : Function.Injective (coefficient z)
  coefficient_add : ∀ i j, coefficient z (i + j) = coefficient z i * coefficient z j
  coefficient_neg : ∀ i, coefficient z (-i) = (coefficient z i)⁻¹
  coefficient_affine : ∀ t j i,
    coefficient z (affine t j i) = coefficient z t * (coefficient z i) ^ (3 ^ j.val)
  coefficient_square : ∀ i, Square (coefficient z i)
  minus_one_square : Square (-1 : K)

theorem affine_discriminant_square_iff [DecidableEq K] {z : K}
    (h : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (t : Vertex) (j : Fin 8) (a b c : Vertex) :
    Square (delta (coefficient z (affine t j a))
      (coefficient z (affine t j b)) (coefficient z (affine t j c))) ↔
      Square (delta (coefficient z a) (coefficient z b) (coefficient z c)) := by
  simp only [h.coefficient_affine]
  rw [delta_scaling, square_scaling_iff (h.coefficient_nonzero t),
    delta_frobenius_power hf, square_frobenius_power_iff hf]

theorem discriminantEdge_affine_iff [DecidableEq K] {z : K}
    (ho : ThreeOrderDuty) (h : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (t : Vertex) (j : Fin 8) (e : Finset Vertex) :
    DiscriminantEdge z (e.image (affine t j)) ↔ DiscriminantEdge z e := by
  have hinj := affine_injective ho t j
  constructor
  · rintro ⟨hc, a, ha, b, hb, c, hcmem, hab, hac, hbc, hs⟩
    obtain ⟨a₀, ha₀, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_image.mp hcmem
    refine ⟨?_, a₀, ha₀, b₀, hb₀, c₀, hc₀, ?_, ?_, ?_, ?_⟩
    · simpa [Finset.card_image_of_injective e hinj] using hc
    · exact fun h => hab (congrArg (affine t j) h)
    · exact fun h => hac (congrArg (affine t j) h)
    · exact fun h => hbc (congrArg (affine t j) h)
    · exact (affine_discriminant_square_iff h hf t j a₀ b₀ c₀).1 hs
  · rintro ⟨hc, a, ha, b, hb, c, hcmem, hab, hac, hbc, hs⟩
    refine ⟨?_, affine t j a, Finset.mem_image.mpr ⟨a, ha, rfl⟩,
      affine t j b, Finset.mem_image.mpr ⟨b, hb, rfl⟩,
      affine t j c, Finset.mem_image.mpr ⟨c, hcmem, rfl⟩,
      ?_, ?_, ?_, ?_⟩
    · simpa [Finset.card_image_of_injective e hinj] using hc
    · exact fun h => hab (hinj h)
    · exact fun h => hac (hinj h)
    · exact fun h => hbc (hinj h)
    · exact (affine_discriminant_square_iff h hf t j a b c).2 hs

theorem affine_hypergraph_symmetry [DecidableEq K] {z : K}
    (ho : ThreeOrderDuty) (h : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (t : Vertex) (j : Fin 8) :
    HypergraphSymmetry (discriminantHypergraph z) (affine t j) := by
  apply graph_image_of_edge_iff _ _ (affine_injective ho t j)
  intro e
  simpa [discriminantHypergraph] using discriminantEdge_affine_iff ho h hf t j e

theorem independent_affine_iff [DecidableEq K] {z : K}
    (ho : ThreeOrderDuty) (h : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (t : Vertex) (j : Fin 8) (T : Finset Vertex) :
    Independent (discriminantHypergraph z) (affineImage t j T) ↔
      Independent (discriminantHypergraph z) T := by
  exact independent_image_iff (affine_hypergraph_symmetry ho h hf t j) T

theorem independent_translate_iff [DecidableEq K] {z : K}
    (ho : ThreeOrderDuty) (h : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (t : Vertex) (T : Finset Vertex) :
    Independent (discriminantHypergraph z) (translateImage t T) ↔
      Independent (discriminantHypergraph z) T := by
  simpa [affine_zero_is_translation] using independent_affine_iff ho h hf t 0 T

theorem nonempty_independent_root_normalization [DecidableEq K] {z : K}
    (ho : ThreeOrderDuty) (h : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    {T : Finset Vertex} (hne : T.Nonempty) (hind : Independent (discriminantHypergraph z) T) :
    ∃ U : Finset Vertex, 0 ∈ U ∧ U.card = T.card ∧
      Independent (discriminantHypergraph z) U := by
  obtain ⟨v, hv⟩ := hne
  exact ⟨translateImage (-v) T, translated_root hv, translateImage_card _ _,
    (independent_translate_iff ho h hf _ _).2 hind⟩

end Field
end
end Partials.Cap
