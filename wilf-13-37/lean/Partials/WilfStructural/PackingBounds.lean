import Partials.WilfStructural.PackingModel

/-! UNCOMPILED source arguments. No algorithm below has been executed. -/
namespace Partials.WilfStructural.Packing

theorem value_mem_interval {s : ℕ} (B : Box s) (x : Fin s → ℤ)
    (hx : B.Contains x) (u : Monomial s) :
    value x u ∈ monomialInterval B u := by
  apply Finset.mem_Icc.mpr
  constructor
  · exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hx i).1 (Int.natCast_nonneg _)
  · exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hx i).2 (Int.natCast_nonneg _)

theorem value_mem_top {s : ℕ} (B : Box s) (x : Fin s → ℤ)
    (hx : B.Contains x) (u : Monomial s) (m ρ q : ℤ)
    (htop : value x u ∈ layer m ρ q) : value x u ∈ topInterval B m ρ q u := by
  exact Finset.mem_inter.mpr ⟨value_mem_interval B x hx u, htop⟩

theorem empty_coordinate_excludes {s : ℕ} (B : Box s) (i : Fin s)
    (hempty : B.upper i < B.lower i) : ¬ ∃ x, B.Contains x := by
  rintro ⟨x,hx⟩
  exact (not_lt_of_ge (le_trans (hx i).1 (hx i).2)) hempty

/- A source inequality before any division. The coefficient is the whole
exponent, not an independent copy of the same variable. -/
theorem isolate_repeated_coordinate (a b k x other lowerOther upperOther : ℤ)
    (hlo : a ≤ k*x+other) (hhi : k*x+other ≤ b)
    (hother : lowerOther ≤ other ∧ other ≤ upperOther) :
    a-upperOther ≤ k*x ∧ k*x ≤ b-lowerOther := by omega

theorem signed_floor_bound (k x b : ℤ) (hk : 0 < k) (h : k*x ≤ b) :
    x ≤ b/k := by
  exact (Int.le_ediv_iff_mul_le hk).2 (by simpa [mul_comm] using h)

/- -((-a)/k) is the exact signed ceiling a/k for positive k. -/
theorem signed_ceiling_bound (k x a : ℤ) (hk : 0 < k) (h : a ≤ k*x) :
    -((-a)/k) ≤ x := by
  have hneg : k*(-x) ≤ -a := by nlinarith
  have hf := signed_floor_bound k (-x) (-a) hk hneg
  omega

theorem propagation_preserves (a b k x other lowerOther upperOther L U : ℤ)
    (hk : 0 < k) (hx : L ≤ x ∧ x ≤ U)
    (hlo : a ≤ k*x+other) (hhi : k*x+other ≤ b)
    (hother : lowerOther ≤ other ∧ other ≤ upperOther) :
    max L (-((-(a-upperOther))/k)) ≤ x ∧
      x ≤ min U ((b-lowerOther)/k) := by
  obtain ⟨h₁,h₂⟩ := isolate_repeated_coordinate a b k x other lowerOther upperOther hlo hhi hother
  exact ⟨max_le hx.1 (signed_ceiling_bound k x (a-upperOther) hk h₁),
    le_min hx.2 (signed_floor_bound k x (b-lowerOther) hk h₂)⟩

theorem adjacent_propagation (L₁ U₂ x₁ x₂ : ℤ)
    (h₁ : L₁ ≤ x₁) (h₂ : x₂ ≤ U₂) (horder : x₁+1 ≤ x₂) :
    L₁+1 ≤ x₂ ∧ x₁ ≤ U₂-1 := by omega

theorem matching_card_le_capacity {L R : Type*} [DecidableEq L] [DecidableEq R]
    (graph edges : Finset (L × R)) (hsub : edges ⊆ graph)
    (hm : IsMatching edges) : edges.card ≤ matchingCapacity graph := by
  classical
  unfold matchingCapacity
  exact Finset.le_sup (Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hsub, hm⟩)

/- This builds the actual matching from injective numerical values. The graph
capacity hypothesis is not assumed; it is obtained from the constructed edges. -/
theorem selected_matching_bound {L R : Type*} [DecidableEq L] [DecidableEq R]
    (actual : Finset L) (val : L → R) (graph : Finset (L × R))
    (hval : Set.InjOn val (↑actual : Set L))
    (hedge : ∀ u ∈ actual, (u,val u) ∈ graph) :
    actual.card ≤ matchingCapacity graph := by
  classical
  let edges := actual.image fun u => (u,val u)
  have hcard : edges.card = actual.card := by
    apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    exact congrArg Prod.fst hab
  have hsub : edges ⊆ graph := by
    intro p hp
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
    exact hedge u hu
  have hm : IsMatching edges := by
    constructor
    · intro p hp q hq heq
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
      change u = v at heq
      subst v
      rfl
    · intro p hp q hq heq
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hq
      have huv : u = v := hval hu hv heq
      subst v
      rfl
  rw [← hcard]
  exact matching_card_le_capacity graph edges hsub hm

theorem joint_integer_cap {L : Type*} [DecidableEq L]
    (actual candidates : Finset L) (interval : L → Finset ℤ) (val : L → ℤ)
    (hsub : actual ⊆ candidates) (hval : Set.InjOn val (↑actual : Set L))
    (hinterval : ∀ u ∈ actual, val u ∈ interval u) (δ K : ℕ)
    (hpartition : δ = K + actual.card) :
    δ ≤ K + matchingCapacity (intervalGraph candidates interval) := by
  have h := selected_matching_bound actual val (intervalGraph candidates interval) hval (by
    intro u hu
    apply Finset.mem_biUnion.mpr
    exact ⟨u,hsub hu,Finset.mem_image.mpr ⟨val u,hinterval u hu,rfl⟩⟩)
  omega

theorem joint_residue_cap {L : Type*} [DecidableEq L]
    (actual candidates : Finset L) (interval : L → Finset ℤ) (val : L → ℤ)
    (m : ℤ) (hsub : actual ⊆ candidates)
    (hinj : Set.InjOn (fun u => val u % m) (↑actual : Set L))
    (hinterval : ∀ u ∈ actual, val u ∈ interval u) (s δ : ℕ)
    (hcard : actual.card = 1+s+δ) :
    1+s+δ ≤ matchingCapacity (residueGraph candidates interval m) ∧
      δ ≤ matchingCapacity (residueGraph candidates interval m)-1-s := by
  have h := selected_matching_bound actual (fun u => val u % m)
    (residueGraph candidates interval m) hinj (by
      intro u hu
      apply Finset.mem_image.mpr
      refine ⟨(u,val u), ?_, rfl⟩
      apply Finset.mem_biUnion.mpr
      exact ⟨u,hsub hu,Finset.mem_image.mpr ⟨val u,hinterval u hu,rfl⟩⟩)
  omega

/- The exchange step that makes upper-endpoint greedy matching special to
intervals. A generic matching search would supply only a lower bound. -/
theorem interval_exchange (lo hi laterLo laterHi x y : ℤ)
    (hy : lo ≤ y ∧ y ≤ hi) (hx : laterLo ≤ x ∧ x ≤ laterHi)
    (hxy : x ≤ y) (horder : hi ≤ laterHi) :
    laterLo ≤ y ∧ y ≤ laterHi := by omega

theorem split_covers (L U z x : ℤ) :
    (L ≤ x ∧ x ≤ U) ↔
      (L ≤ x ∧ x ≤ U ∧ x ≤ z) ∨ (L ≤ x ∧ x ≤ U ∧ z+1 ≤ x) := by omega

theorem split_disjoint (z x : ℤ) : ¬ (x ≤ z ∧ z+1 ≤ x) := by omega

theorem midpoint_strict (L U : ℤ) (h : L < U) :
    L ≤ (L+U)/2 ∧ (L+U)/2 < U := by omega

/- A closed finite binary tree carries local contradiction evidence at every
leaf and both children at every split. No successful-run flag is a premise. -/
inductive ClosedCover {X : Type*} (bad : X → Prop) : (X → Prop) → Prop
  | leaf {region} (contradiction : ∀ x, region x → ¬ bad x) : ClosedCover bad region
  | split {region left right} (cover : ∀ x, region x → left x ∨ right x)
      (hl : ClosedCover bad left) (hr : ClosedCover bad right) : ClosedCover bad region

theorem closed_cover_sound {X : Type*} (bad region : X → Prop)
    (tree : ClosedCover bad region) : ∀ x, region x → ¬ bad x := by
  induction tree with
  | leaf h => exact h
  | split cover hl hr ihl ihr =>
    intro x hx
    rcases cover x hx with hleft | hright
    · exact ihl x hleft
    · exact ihr x hright

end Partials.WilfStructural.Packing
