import Partials.Graceful.Model

/-! Transport a finite numerical parent presentation with exact leaf fibers
to the paper's fixed vertex type. Proof fields are explicit case obligations;
the adapter proves transport and does not instantiate a residue construction. -/
namespace Partials.Graceful

abbrev DepthCode := Σ i : Fin 3, Fin (depthTwoCount i)
abbrev InternalCode := Unit ⊕ (Fin 3 ⊕ DepthCode)
abbrev FlatLeafCode (u v : ℕ) :=
  Σ c : DepthCode, Fin (pendantCount u v c.1 c.2)

def profileCodeEquiv (u v : ℕ) : Vertex u v ≃ InternalCode ⊕ FlatLeafCode u v where
  toFun
    | .root => .inl (.inl ())
    | .levelOne i => .inl (.inr (.inl i))
    | .levelTwo i j => .inl (.inr (.inr ⟨i, j⟩))
    | .leaf i j k => .inr ⟨⟨i, j⟩, k⟩
  invFun
    | .inl (.inl _) => .root
    | .inl (.inr (.inl i)) => .levelOne i
    | .inl (.inr (.inr ⟨i, j⟩)) => .levelTwo i j
    | .inr ⟨⟨i, j⟩, k⟩ => .leaf i j k
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with x | ⟨⟨i, j⟩, k⟩
    · rcases x with a | x
      · cases a; rfl
      rcases x with i | ⟨i, j⟩ <;> rfl
    · rfl

/-- Structural finite partition, not a premise asserting the target graceful
labeling. Every concrete case must prove its exact fibers and incidences. -/
structure ProfileFrame (u v : ℕ) where
  numericParent : Fin (q u v + 1) → Fin (q u v + 1)
  internal : InternalCode → Fin (q u v + 1)
  internal_injective : Function.Injective internal
  root_zero : internal (.inl ()) = 0
  parent_root : numericParent 0 = 0
  parent_one : ∀ i, numericParent (internal (.inr (.inl i))) = internal (.inl ())
  parent_two : ∀ c : DepthCode,
    numericParent (internal (.inr (.inr c))) = internal (.inr (.inl c.1))
  fibers : DepthCode → Finset (Fin (q u v + 1))
  fiber_card : ∀ c, (fibers c).card = pendantCount u v c.1 c.2
  fiber_parent : ∀ c y, y ∈ fibers c → numericParent y = internal (.inr (.inr c))
  fiber_avoids_internal : ∀ c y, y ∈ fibers c → ∀ x, y ≠ internal x
  covers : ∀ y, (∃ x, internal x = y) ∨ ∃ c, y ∈ fibers c

namespace ProfileFrame

noncomputable def leafEquiv {u v : ℕ} (F : ProfileFrame u v) (c : DepthCode) :
    Fin (pendantCount u v c.1 c.2) ≃ ↥(F.fibers c) :=
  Fintype.equivOfCardEq (by simpa using (F.fiber_card c).symm)

noncomputable def leafMap {u v : ℕ} (F : ProfileFrame u v) :
    FlatLeafCode u v → Fin (q u v + 1) :=
  fun ⟨c, k⟩ => (F.leafEquiv c k).val

theorem leafMap_mem {u v : ℕ} (F : ProfileFrame u v) (c : DepthCode)
    (k : Fin (pendantCount u v c.1 c.2)) : F.leafMap ⟨c, k⟩ ∈ F.fibers c :=
  (F.leafEquiv c k).property

theorem leafMap_injective {u v : ℕ} (F : ProfileFrame u v) :
    Function.Injective F.leafMap := by
  rintro ⟨c, k⟩ ⟨d, l⟩ h
  have hc := F.fiber_parent c _ (F.leafMap_mem c k)
  have hd := F.fiber_parent d _ (F.leafMap_mem d l)
  rw [h] at hc
  have hi := F.internal_injective (hc.symm.trans hd)
  have hcd : c = d := by simpa using hi
  cases hcd
  have hsub : F.leafEquiv c k = F.leafEquiv c l := Subtype.ext h
  have hkl := (F.leafEquiv c).injective hsub
  cases hkl
  rfl

noncomputable def fullMap {u v : ℕ} (F : ProfileFrame u v) :
    InternalCode ⊕ FlatLeafCode u v → Fin (q u v + 1) :=
  Sum.elim F.internal F.leafMap

theorem fullMap_injective {u v : ℕ} (F : ProfileFrame u v) :
    Function.Injective F.fullMap := by
  intro a b h
  rcases a with a | ⟨c, k⟩ <;> rcases b with b | ⟨d, l⟩
  · exact congrArg Sum.inl (F.internal_injective h)
  · exact False.elim ((F.fiber_avoids_internal d _ (F.leafMap_mem d l) a) h.symm)
  · exact False.elim ((F.fiber_avoids_internal c _ (F.leafMap_mem c k) b) h)
  · exact congrArg Sum.inr (F.leafMap_injective h)

theorem fullMap_surjective {u v : ℕ} (F : ProfileFrame u v) :
    Function.Surjective F.fullMap := by
  intro y
  rcases F.covers y with ⟨x, hx⟩ | ⟨c, hc⟩
  · exact ⟨.inl x, hx⟩
  · refine ⟨.inr ⟨c, (F.leafEquiv c).symm ⟨y, hc⟩⟩, ?_⟩
    exact congrArg Subtype.val ((F.leafEquiv c).apply_symm_apply ⟨y, hc⟩)

noncomputable def realization {u v : ℕ} (F : ProfileFrame u v) :
    Vertex u v ≃ Fin (q u v + 1) :=
  (profileCodeEquiv u v).trans
    (Equiv.ofBijective F.fullMap ⟨F.fullMap_injective, F.fullMap_surjective⟩)

theorem realization_root {u v : ℕ} (F : ProfileFrame u v) :
    F.realization Vertex.root = 0 := F.root_zero

theorem realization_parent {u v : ℕ} (F : ProfileFrame u v) (x : Vertex u v) :
    F.numericParent (F.realization x) = F.realization (parent x) := by
  cases x with
  | root => simpa [realization, profileCodeEquiv, fullMap, parent, F.root_zero] using F.parent_root
  | levelOne i => exact F.parent_one i
  | levelTwo i j => exact F.parent_two ⟨i, j⟩
  | leaf i j k => exact F.fiber_parent ⟨i, j⟩ _ (F.leafMap_mem ⟨i, j⟩ k)

theorem realization_nonroot {u v : ℕ} (F : ProfileFrame u v) (x : Vertex u v)
    (hx : x ≠ .root) : F.realization x ≠ 0 := by
  intro h
  apply hx
  apply F.realization.injective
  exact h.trans F.realization_root.symm

theorem edge_difference {u v : ℕ} (F : ProfileFrame u v) (e : EdgeIndex u v) :
    Partials.Interface.EdgeDifference (graph u v) (fun x => (F.realization x).val) e =
      Nat.dist (F.numericParent (F.realization e.val)).val (F.realization e.val).val := by
  rw [F.realization_parent]
  rfl

end ProfileFrame

def NumericGraceful {u v : ℕ}
    (p : Fin (q u v + 1) → Fin (q u v + 1)) : Prop :=
  (∀ d : ℕ, (1 ≤ d ∧ d ≤ q u v) ↔
    ∃ y : Fin (q u v + 1), y ≠ 0 ∧ Nat.dist (p y).val y.val = d) ∧
  Function.Injective (fun y : {z : Fin (q u v + 1) // z ≠ 0} =>
    Nat.dist (p y.val).val y.val.val)

/-- Conditional structural/difference transport. A concrete ProfileFrame and
NumericGraceful proof must still be constructed; this is no main-target proof. -/
theorem rootZeroGraceful_of_profile {u v : ℕ} (F : ProfileFrame u v)
    (h : NumericGraceful F.numericParent) : RootZeroGraceful u v F.realization := by
  refine ⟨F.realization.bijective, F.realization_root, ?_, ?_⟩
  · intro d
    constructor
    · intro hd
      obtain ⟨y, hy, he⟩ := (h.1 d).mp hd
      let x := F.realization.symm y
      have hx : x ≠ Vertex.root := by
        intro hx
        apply hy
        have hxy : F.realization x = y := F.realization.apply_symm_apply y
        rw [hx, F.realization_root] at hxy
        exact hxy.symm
      refine ⟨⟨x, hx⟩, ?_⟩
      rw [F.edge_difference]
      simpa [x] using he
    · rintro ⟨e, he⟩
      apply (h.1 d).mpr
      refine ⟨F.realization e.val, F.realization_nonroot e.val e.property, ?_⟩
      exact (F.edge_difference e).symm.trans he
  · intro e f hef
    have hnum : Nat.dist (F.numericParent (F.realization e.val)).val (F.realization e.val).val =
        Nat.dist (F.numericParent (F.realization f.val)).val (F.realization f.val).val := by
      simpa only [F.edge_difference] using hef
    let ye : {z : Fin (q u v + 1) // z ≠ 0} :=
      ⟨F.realization e.val, F.realization_nonroot e.val e.property⟩
    let yf : {z : Fin (q u v + 1) // z ≠ 0} :=
      ⟨F.realization f.val, F.realization_nonroot f.val f.property⟩
    have hi : ye = yf := h.2 hnum
    apply Subtype.ext
    apply F.realization.injective
    exact congrArg Subtype.val hi

end Partials.Graceful
