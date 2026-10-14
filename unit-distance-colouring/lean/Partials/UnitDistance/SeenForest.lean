import Partials.UnitDistance.Network

/-! Blind source for main.tex lem:seen. Not compiled or replayed.
The state records exact complex coordinates, not word prefixes. An omitted
old endpoint remains the current point and does not terminate the path. -/
noncomputable section
namespace Partials.UnitDistance

local instance : DecidableEq ℂ := Classical.decEq ℂ

def ListedEdges (edges : List (ℂ × ℂ)) : Set (ℂ × ℂ) := {e | e ∈ edges}

/-- Constructive rooted-tree presentation by successive fresh-leaf additions.
It is independent of any particular graph-library tree representation. -/
inductive SeenLeafForest (root : ℂ) : Finset ℂ → List (ℂ × ℂ) → Prop
  | initial : SeenLeafForest root {root} []
  | attach {seen : Finset ℂ} {edges : List (ℂ × ℂ)} {x y : ℂ} :
      SeenLeafForest root seen edges → x ∈ seen → y ∉ seen →
      SeenLeafForest root (insert y seen) ((x, y) :: edges)

theorem seen_root_mem {root : ℂ} {seen : Finset ℂ} {edges : List (ℂ × ℂ)}
    (h : SeenLeafForest root seen edges) : root ∈ seen := by
  classical
  induction h with
  | initial => simp
  | attach h hx hy ih => exact Finset.mem_insert_of_mem ih

theorem seen_edge_endpoints {root : ℂ} {seen : Finset ℂ} {edges : List (ℂ × ℂ)}
    (h : SeenLeafForest root seen edges) :
    ∀ e ∈ edges, e.1 ∈ seen ∧ e.2 ∈ seen ∧ e.1 ≠ e.2 := by
  classical
  induction h with
  | initial => simp
  | @attach seen edges x y h hx hy ih =>
    intro e he
    rcases List.mem_cons.mp he with he | he
    · subst e
      refine ⟨Finset.mem_insert_of_mem hx, Finset.mem_insert_self _ _, ?_⟩
      intro hxy
      change x = y at hxy
      exact hy (hxy ▸ hx)
    · obtain ⟨ha, hb, hab⟩ := ih e he
      exact ⟨Finset.mem_insert_of_mem ha, Finset.mem_insert_of_mem hb, hab⟩

theorem seen_child_nodup {root : ℂ} {seen : Finset ℂ} {edges : List (ℂ × ℂ)}
    (h : SeenLeafForest root seen edges) : (edges.map Prod.snd).Nodup := by
  classical
  induction h with
  | initial => simp
  | @attach seen edges x y h hx hy ih =>
    simp only [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih⟩
    intro hyold
    obtain ⟨e, he, hye⟩ := List.mem_map.mp hyold
    have heSeen := (seen_edge_endpoints h e he).2.1
    exact hy (hye ▸ heSeen)

theorem seen_cardinality {root : ℂ} {seen : Finset ℂ} {edges : List (ℂ × ℂ)}
    (h : SeenLeafForest root seen edges) : seen.card = edges.length + 1 := by
  classical
  induction h with
  | initial => simp
  | attach h hx hy ih =>
    rw [Finset.card_insert_of_notMem hy, List.length_cons, ih]

theorem seen_connected {root : ℂ} {seen : Finset ℂ} {edges : List (ℂ × ℂ)}
    (h : SeenLeafForest root seen edges) :
    ∀ v ∈ seen, CoordinateWalk (ListedEdges edges) root v := by
  classical
  induction h with
  | initial =>
    intro v hv
    have hvroot : v = root := Finset.mem_singleton.mp hv
    subst v
    exact .refl root
  | @attach seen edges x y h hx hy ih =>
    have hincl : ListedEdges edges ⊆ ListedEdges ((x, y) :: edges) := by
      intro e he
      exact List.mem_cons_of_mem _ he
    intro v hv
    rcases Finset.mem_insert.mp hv with hv | hv
    · subst v
      exact CoordinateWalk.step
        (coordinate_walk_mono _ _ hincl (ih x hx))
        (Or.inl (List.mem_cons_self))
    · exact coordinate_walk_mono _ _ hincl (ih v hv)

/-- One prescribed step updates to y in both branches. `x ∈ seen` is a
precondition, so every retained gadget attaches to the existing component. -/
inductive PrescribedSeenStep (root : ℂ)
    (seen : Finset ℂ) (edges : List (ℂ × ℂ)) (x y : ℂ) :
    Finset ℂ → List (ℂ × ℂ) → Prop
  | old (hx : x ∈ seen) (hy : y ∈ seen) :
      PrescribedSeenStep root seen edges x y seen edges
  | fresh (hx : x ∈ seen) (hy : y ∉ seen) :
      PrescribedSeenStep root seen edges x y (insert y seen) ((x, y) :: edges)

theorem seen_step_preserves {root : ℂ} {seen nextSeen : Finset ℂ}
    {edges nextEdges : List (ℂ × ℂ)} {x y : ℂ}
    (htree : SeenLeafForest root seen edges)
    (hstep : PrescribedSeenStep root seen edges x y nextSeen nextEdges) :
    SeenLeafForest root nextSeen nextEdges ∧ y ∈ nextSeen ∧
      CoordinateWalk (ListedEdges nextEdges) root y := by
  classical
  cases hstep with
  | old hx hy => exact ⟨htree, hy, seen_connected htree y hy⟩
  | fresh hx hy =>
    have hnew := SeenLeafForest.attach htree hx hy
    have hymem : y ∈ insert y seen := Finset.mem_insert_self _ _
    exact ⟨hnew, hymem, seen_connected hnew y hymem⟩

inductive PrescribedSeenWalk (root : ℂ) :
    Finset ℂ → List (ℂ × ℂ) → ℂ → List ℂ → Finset ℂ → List (ℂ × ℂ) → ℂ → Prop
  | nil (seen : Finset ℂ) (edges : List (ℂ × ℂ)) (x : ℂ) :
      PrescribedSeenWalk root seen edges x [] seen edges x
  | cons {seen middleSeen finalSeen : Finset ℂ}
      {edges middleEdges finalEdges : List (ℂ × ℂ)} {x y z : ℂ} {tail : List ℂ} :
      PrescribedSeenStep root seen edges x y middleSeen middleEdges →
      PrescribedSeenWalk root middleSeen middleEdges y tail finalSeen finalEdges z →
      PrescribedSeenWalk root seen edges x (y :: tail) finalSeen finalEdges z

theorem seen_walk_preserves {root : ℂ} {seen finalSeen : Finset ℂ}
    {edges finalEdges : List (ℂ × ℂ)} {x z : ℂ} {path : List ℂ}
    (hwalk : PrescribedSeenWalk root seen edges x path finalSeen finalEdges z)
    (htree : SeenLeafForest root seen edges) (hx : x ∈ seen) :
    SeenLeafForest root finalSeen finalEdges ∧ z ∈ finalSeen ∧
      CoordinateWalk (ListedEdges finalEdges) root z := by
  revert htree hx
  induction hwalk with
  | nil seen edges x =>
    intro htree hx
    exact ⟨htree, hx, seen_connected htree x hx⟩
  | cons hstep htail ih =>
    intro htree hx
    obtain ⟨hmiddle, hy, hconnect⟩ := seen_step_preserves htree hstep
    exact ih hmiddle hy

theorem zero_length_path_needs_no_gadget (root : ℂ) :
    PrescribedSeenWalk root {root} [] root [] {root} [] root :=
  PrescribedSeenWalk.nil {root} [] root

/-- Skeleton separation uses a residue function whose constancy along the
concrete doubled paths must be proved by the quotient/coordinate adapter.
No separation of gadget interiors is inferred. -/
theorem distinct_fibre_seen_disjoint (residue : ℂ → BinaryCode)
    (a b : BinaryCode) (ha : a ≠ b) (A B : Finset ℂ)
    (hA : ∀ x ∈ A, residue x = a) (hB : ∀ x ∈ B, residue x = b) :
    Disjoint A B := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  exact ha ((hA x hxA).symm.trans (hB x hxB))

/- Remaining concrete duties: decode the fixed four order lists and all
4096 fibres, establish all prescribed endpoints/doubled steps, relate actual
retained occurrences to the leaf-attachment presentation, and prove the
graph-library tree correspondence if that library formulation is used.
No ROOT_WORDS/SHORT_FOREST recipe or endpoint replay was executed. -/
end Partials.UnitDistance
end
