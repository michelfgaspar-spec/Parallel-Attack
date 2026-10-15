import Partials.Graceful.Geometry
import Mathlib.Tactic.FinCases

/-!
Independent named presentations of the branch profiles in manuscript Section 1.
The merged tree has two reserved leaves at its final star. Splitting those leaves
changes the edge relation; no isomorphism between the unsplit merged tree and the
original family is asserted. Branch and star orderings are explicit parameters.
-/
namespace Partials.Graceful.ManuscriptPresentation

inductive Branch where
  | first | second | third
  deriving DecidableEq

inductive Star where
  | a1 | a2 | a3 | b1 | b2 | b3 | c1 | c2
  deriving DecidableEq

def starBranch : Star → Branch
  | .a1 | .a2 | .a3 => .first
  | .b1 | .b2 | .b3 => .second
  | .c1 | .c2 => .third

def leaves (u v : ℕ) : Star → ℕ
  | .a1 | .a2 | .b1 | .b2 | .c1 => 1
  | .a3 => 3
  | .b3 => 2 * v
  | .c2 => 2 * u

/-- Named vertices specified directly by the three manuscript branch profiles. -/
inductive NamedVertex (u v : ℕ) where
  | root
  | branch (b : Branch)
  | star (s : Star)
  | leaf (s : Star) (k : Fin (leaves u v s))
  deriving DecidableEq

def namedParent {u v : ℕ} : NamedVertex u v → NamedVertex u v
  | .root => .root
  | .branch _ => .root
  | .star s => .branch (starBranch s)
  | .leaf s _ => .star s

def namedDepth {u v : ℕ} : NamedVertex u v → ℕ
  | .root => 0
  | .branch _ => 1
  | .star _ => 2
  | .leaf _ _ => 3

def branchIndex : Branch → Fin 3
  | .first => 0
  | .second => 1
  | .third => 2

def starIndex : (s : Star) → Fin (depthTwoCount (branchIndex (starBranch s)))
  | .a1 => ⟨0, by decide⟩ | .a2 => ⟨1, by decide⟩ | .a3 => ⟨2, by decide⟩
  | .b1 => ⟨0, by decide⟩ | .b2 => ⟨1, by decide⟩ | .b3 => ⟨2, by decide⟩
  | .c1 => ⟨0, by decide⟩ | .c2 => ⟨1, by decide⟩

theorem leaves_eq_pendant (u v : ℕ) (s : Star) :
    leaves u v s = pendantCount u v (branchIndex (starBranch s)) (starIndex s) := by
  cases s <;> rfl

def encode {u v : ℕ} : NamedVertex u v → Vertex u v
  | .root => .root
  | .branch b => .levelOne (branchIndex b)
  | .star s => .levelTwo (branchIndex (starBranch s)) (starIndex s)
  | .leaf s k => .leaf (branchIndex (starBranch s)) (starIndex s)
      (Fin.cast (leaves_eq_pendant u v s) k)

def branchName (i : Fin 3) : Branch :=
  if i.val = 0 then .first else if i.val = 1 then .second else .third

def starName (i : Fin 3) (j : Fin (depthTwoCount i)) : Star :=
  if i.val = 0 then
    if j.val = 0 then .a1 else if j.val = 1 then .a2 else .a3
  else if i.val = 1 then
    if j.val = 0 then .b1 else if j.val = 1 then .b2 else .b3
  else if j.val = 0 then .c1 else .c2

theorem pendant_eq_leaves (u v : ℕ) (i : Fin 3) (j : Fin (depthTwoCount i)) :
    pendantCount u v i j = leaves u v (starName i j) := by
  fin_cases i <;> fin_cases j <;> rfl

def decode {u v : ℕ} : Vertex u v → NamedVertex u v
  | .root => .root
  | .levelOne i => .branch (branchName i)
  | .levelTwo i j => .star (starName i j)
  | .leaf i j k => .leaf (starName i j) (Fin.cast (pendant_eq_leaves u v i j) k)

theorem decode_encode {u v : ℕ} (x : NamedVertex u v) : decode (encode x) = x := by
  cases x with
  | root => rfl
  | branch b => cases b <;> rfl
  | star s => cases s <;> rfl
  | leaf s k => cases s <;> rfl

theorem encode_decode {u v : ℕ} (x : Vertex u v) : encode (decode x) = x := by
  cases x with
  | root => rfl
  | levelOne i => fin_cases i <;> rfl
  | levelTwo i j => fin_cases i <;> fin_cases j <;> rfl
  | leaf i j k => fin_cases i <;> fin_cases j <;> rfl

def namedEquiv (u v : ℕ) : NamedVertex u v ≃ Vertex u v where
  toFun := encode
  invFun := decode
  left_inv := decode_encode
  right_inv := encode_decode

theorem encode_parent {u v : ℕ} (x : NamedVertex u v) :
    encode (namedParent x) = parent (encode x) := by
  cases x <;> rfl

theorem encode_root_iff {u v : ℕ} (x : NamedVertex u v) :
    encode x = Vertex.root ↔ x = .root := by
  constructor
  · intro h
    exact (namedEquiv u v).injective h
  · rintro rfl
    rfl

def namedEdge {u v : ℕ} (a b : NamedVertex u v) : Prop :=
  b ≠ .root ∧ namedParent b = a

theorem named_parent_depth {u v : ℕ} (x : NamedVertex u v) (hx : x ≠ .root) :
    namedDepth (namedParent x) < namedDepth x := by
  cases x <;> simp_all [namedParent, namedDepth]

def namedGraph (u v : ℕ) : SimpleGraph (NamedVertex u v) where
  Adj a b := namedEdge a b ∨ namedEdge b a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h <;> have hd := named_parent_depth x h.1
    all_goals rw [h.2] at hd; exact Nat.lt_irrefl _ hd⟩

theorem namedEdge_iff_encoded {u v : ℕ} (a b : NamedVertex u v) :
    namedEdge a b ↔ Edge (encode a) (encode b) := by
  unfold namedEdge Edge
  rw [← encode_parent]
  exact and_congr (not_congr (encode_root_iff b)).symm
    (namedEquiv u v).injective.eq_iff.symm

/-- Exact oriented endpoints as used by the existing graceful labeling. -/
theorem namedEdge_iff_ends {u v : ℕ} (a b : NamedVertex u v) :
    namedEdge a b ↔ ∃ e : EdgeIndex u v, (graph u v).ends e = (encode a, encode b) := by
  rw [namedEdge_iff_encoded]
  exact (graph_parent_compatible u v (encode a) (encode b)).symm

def originalIso (u v : ℕ) : namedGraph u v ≃g simpleGraph u v where
  toEquiv := namedEquiv u v
  map_rel_iff' := by
    intro a b
    exact or_congr (namedEdge_iff_encoded a b).symm (namedEdge_iff_encoded b a).symm

theorem originalIso_root (u v : ℕ) : originalIso u v .root = .root := rfl

/-- The manuscript anchor names: A is the third branch parent and B its large star.
C becomes the new star after splitting; Z is C's sole child after splitting. -/
def anchorA (u v : ℕ) : NamedVertex u v := .branch .third
def anchorB (u v : ℕ) : NamedVertex u v := .star .c2
def anchorC (u v : ℕ) : NamedVertex u v := .star .c1
def anchorZ (u v : ℕ) : NamedVertex u v := .leaf .c1 ⟨0, by simp [leaves]⟩

theorem anchor_pairwise_distinct (u v : ℕ) :
    List.Pairwise (· ≠ ·) [anchorA u v, anchorB u v, anchorC u v, anchorZ u v] := by
  simp [anchorA, anchorB, anchorC, anchorZ]

/-- Before the local operation, C and Z are both leaves at B. -/
def mergedParent {u v : ℕ} : NamedVertex u v → NamedVertex u v
  | .root => .root
  | .branch _ => .root
  | .star .c1 => .star .c2
  | .star s => .branch (starBranch s)
  | .leaf .c1 _ => .star .c2
  | .leaf s _ => .star s

def mergedDepth {u v : ℕ} : NamedVertex u v → ℕ
  | .root => 0
  | .branch _ => 1
  | .star .c1 => 3
  | .star _ => 2
  | .leaf _ _ => 3

theorem merged_parent_depth {u v : ℕ} (x : NamedVertex u v) (hx : x ≠ .root) :
    mergedDepth (mergedParent x) < mergedDepth x := by
  cases x with
  | root => exact (hx rfl).elim
  | branch b => simp [mergedDepth, mergedParent]
  | star s => cases s <;> simp [mergedDepth, mergedParent]
  | leaf s k => cases s <;> simp [mergedDepth, mergedParent]

def mergedRootedTree (u v : ℕ) :
    Partials.Interface.RootedParentTree (NamedVertex u v) where
  root := .root
  parent := mergedParent
  depth := mergedDepth
  root_parent := rfl
  root_depth := rfl
  parent_depth := merged_parent_depth

def mergedEdge {u v : ℕ} (a b : NamedVertex u v) : Prop :=
  b ≠ .root ∧ mergedParent b = a

def mergedGraph (u v : ℕ) : SimpleGraph (NamedVertex u v) where
  Adj a b := mergedEdge a b ∨ mergedEdge b a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h <;> have hd := merged_parent_depth x h.1
    all_goals rw [h.2] at hd; exact Nat.lt_irrefl _ hd⟩

/-- Only two parent incidences are changed by manuscript Lemma 2. -/
def splitParent {u v : ℕ} (p : NamedVertex u v → NamedVertex u v)
    (x : NamedVertex u v) : NamedVertex u v :=
  if x = anchorC u v then anchorA u v else
  if x = anchorZ u v then anchorC u v else p x

theorem split_merged_parent {u v : ℕ} (x : NamedVertex u v) :
    splitParent mergedParent x = namedParent x := by
  cases x with
  | root => rfl
  | branch b => cases b <;> rfl
  | star s => cases s <;> rfl
  | leaf s k =>
    cases s <;> try rfl
    have hk : k = ⟨0, by simp [leaves]⟩ := Fin.eq_zero k
    subst k
    rfl

theorem merged_anchor_edges (u v : ℕ) :
    mergedEdge (anchorA u v) (anchorB u v) ∧
    mergedEdge (anchorB u v) (anchorC u v) ∧
    mergedEdge (anchorB u v) (anchorZ u v) := by
  simp [mergedEdge, anchorA, anchorB, anchorC, anchorZ, mergedParent, starBranch]

theorem split_anchor_edges (u v : ℕ) :
    namedEdge (anchorA u v) (anchorB u v) ∧
    namedEdge (anchorA u v) (anchorC u v) ∧
    namedEdge (anchorC u v) (anchorZ u v) := by
  simp [namedEdge, anchorA, anchorB, anchorC, anchorZ, namedParent, starBranch]

/-- Literal edge deletion/insertion, not a static isomorphism M ≅ T. -/
theorem split_edges_exact {u v : ℕ} (a b : NamedVertex u v) :
    namedEdge a b ↔
      (mergedEdge a b ∧ (a,b) ≠ (anchorB u v,anchorC u v) ∧
        (a,b) ≠ (anchorB u v,anchorZ u v)) ∨
      (a,b) = (anchorA u v,anchorC u v) ∨
      (a,b) = (anchorC u v,anchorZ u v) := by
  by_cases hC : b = anchorC u v
  · subst b
    simp [namedEdge, mergedEdge, anchorA, anchorB, anchorC, anchorZ,
      namedParent, mergedParent, starBranch, eq_comm]
  by_cases hZ : b = anchorZ u v
  · subst b
    simp [namedEdge, mergedEdge, anchorA, anchorB, anchorC, anchorZ,
      namedParent, mergedParent, eq_comm]
  have hp : mergedParent b = namedParent b := by
    simpa only [splitParent, if_neg hC, if_neg hZ] using split_merged_parent b
  simp [Prod.mk.injEq, hC, hZ, namedEdge, mergedEdge, hp]

/-- The old indexed carrier can represent M as well, with these two explicit
parent changes. This graph is distinct from the original indexed family. -/
def encodedMergedParent {u v : ℕ} (x : Vertex u v) : Vertex u v :=
  if x = Vertex.levelTwo 2 ⟨0, by decide⟩ then Vertex.levelTwo 2 ⟨1, by decide⟩ else
  if x = Vertex.leaf 2 ⟨0, by decide⟩ ⟨0, by simp [pendantCount]⟩ then Vertex.levelTwo 2 ⟨1, by decide⟩ else parent x

theorem encode_merged_parent {u v : ℕ} (x : NamedVertex u v) :
    encode (mergedParent x) = encodedMergedParent (encode x) := by
  cases x with
  | root => rfl
  | branch b => cases b <;> rfl
  | star s => cases s <;> rfl
  | leaf s k =>
    cases s <;> try rfl
    have hk : k = ⟨0, by simp [leaves]⟩ := Fin.eq_zero k
    subst k
    rfl

def encodedMergedEdge {u v : ℕ} (a b : Vertex u v) : Prop :=
  b ≠ .root ∧ encodedMergedParent b = a

theorem mergedEdge_iff_encoded {u v : ℕ} (a b : NamedVertex u v) :
    mergedEdge a b ↔ encodedMergedEdge (encode a) (encode b) := by
  unfold mergedEdge encodedMergedEdge
  rw [← encode_merged_parent]
  exact and_congr (not_congr (encode_root_iff b)).symm
    (namedEquiv u v).injective.eq_iff.symm

def encodedMergedGraph (u v : ℕ) : SimpleGraph (Vertex u v) where
  Adj a b := encodedMergedEdge a b ∨ encodedMergedEdge b a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro x h
    obtain ⟨y, rfl⟩ := (namedEquiv u v).surjective x
    exact (mergedGraph u v).loopless.irrefl y ((or_congr
      (mergedEdge_iff_encoded y y).symm (mergedEdge_iff_encoded y y).symm).mp h)⟩

def mergedIso (u v : ℕ) : mergedGraph u v ≃g encodedMergedGraph u v where
  toEquiv := namedEquiv u v
  map_rel_iff' := by
    intro a b
    exact or_congr (mergedEdge_iff_encoded a b).symm (mergedEdge_iff_encoded b a).symm

theorem mergedIso_root (u v : ℕ) : mergedIso u v .root = .root := rfl

/-- The same vertex names give different original and merged edge relations. -/
theorem mergedGraph_ne_original (u v : ℕ) : mergedGraph u v ≠ namedGraph u v := by
  intro h
  have he : (mergedGraph u v).Adj (anchorB u v) (anchorC u v) :=
    Or.inl (merged_anchor_edges u v).2.1
  rw [h] at he
  simp [namedGraph, namedEdge, namedParent, anchorB, anchorC, starBranch] at he

def splitEdge {u v : ℕ} (a b : NamedVertex u v) : Prop :=
  b ≠ .root ∧ splitParent mergedParent b = a

theorem splitEdge_iff_original {u v : ℕ} (a b : NamedVertex u v) :
    splitEdge a b ↔ namedEdge a b := by
  simp only [splitEdge, namedEdge, split_merged_parent]

def splitGraph (u v : ℕ) : SimpleGraph (NamedVertex u v) where
  Adj a b := splitEdge a b ∨ splitEdge b a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro x h
    exact (namedGraph u v).loopless.irrefl x
      ((or_congr (splitEdge_iff_original x x) (splitEdge_iff_original x x)).mp h)⟩

/-- The graph after the literal two-edge operation is the encoded original family. -/
def splitIso (u v : ℕ) : splitGraph u v ≃g simpleGraph u v where
  toEquiv := namedEquiv u v
  map_rel_iff' := by
    intro a b
    exact or_congr
      ((splitEdge_iff_original a b).trans (namedEdge_iff_encoded a b)).symm
      ((splitEdge_iff_original b a).trans (namedEdge_iff_encoded b a)).symm

theorem splitIso_root (u v : ℕ) : splitIso u v .root = .root := rfl

instance namedFintype (u v : ℕ) : Fintype (NamedVertex u v) :=
  Fintype.ofEquiv (Vertex u v) (namedEquiv u v).symm

theorem named_vertex_card (u v : ℕ) : Fintype.card (NamedVertex u v) = q u v + 1 := by
  rw [Fintype.card_congr (namedEquiv u v), vertex_card]

/-- The exceptional merged star has exactly the reserved pair and 2u other leaves. -/
theorem merged_B_children {u v : ℕ} (x : NamedVertex u v) :
    mergedEdge (anchorB u v) x ↔
      x = anchorC u v ∨ x = anchorZ u v ∨
      ∃ k : Fin (2 * u), x = .leaf .c2 k := by
  cases x with
  | root => simp [mergedEdge, mergedParent, anchorB, anchorC, anchorZ]
  | branch b => cases b <;> simp [mergedEdge, mergedParent, anchorB, anchorC, anchorZ]
  | star s => cases s <;> simp [mergedEdge, mergedParent, anchorB, anchorC, anchorZ]
  | leaf s k =>
    cases s with
    | a1 =>
      simp [mergedEdge, mergedParent, anchorB, anchorC, anchorZ]
      intro l h
      cases h
    | a2 =>
      simp [mergedEdge, mergedParent, anchorB, anchorC, anchorZ]
      intro l h
      cases h
    | a3 =>
      simp [mergedEdge, mergedParent, anchorB, anchorC, anchorZ]
      intro l h
      cases h
    | b1 =>
      simp [mergedEdge, mergedParent, anchorB, anchorC, anchorZ]
      intro l h
      cases h
    | b2 =>
      simp [mergedEdge, mergedParent, anchorB, anchorC, anchorZ]
      intro l h
      cases h
    | b3 =>
      simp [mergedEdge, mergedParent, anchorB, anchorC, anchorZ]
      intro l h
      cases h
    | c1 =>
      have hk : k = ⟨0, by simp [leaves]⟩ := Fin.eq_zero k
      subst k
      simp [mergedEdge, mergedParent, anchorB, anchorC, anchorZ]
    | c2 =>
      simp [mergedEdge, mergedParent, anchorB, anchorC, anchorZ]
      exact ⟨k, rfl⟩

def mergedChild (u v : ℕ) : Fin 2 ⊕ Fin (2 * u) → NamedVertex u v
  | .inl i => if i.val = 0 then anchorC u v else anchorZ u v
  | .inr k => .leaf .c2 k

theorem mergedChild_injective (u v : ℕ) : Function.Injective (mergedChild u v) := by
  intro a b h
  cases a with
  | inl i =>
    cases b with
    | inl j => fin_cases i <;> fin_cases j <;> simp_all [mergedChild, anchorC, anchorZ]
    | inr k =>
      fin_cases i <;> simp_all [mergedChild, anchorC, anchorZ]
      cases h
  | inr k =>
    cases b with
    | inl i =>
      fin_cases i <;> simp_all [mergedChild, anchorC, anchorZ]
      cases h
    | inr l =>
      simp only [mergedChild] at h
      cases h
      rfl

theorem mergedChild_mem (u v : ℕ) (i : Fin 2 ⊕ Fin (2 * u)) :
    mergedEdge (anchorB u v) (mergedChild u v i) := by
  cases i with
  | inl i => fin_cases i <;> simp [mergedChild, mergedEdge, mergedParent, anchorB, anchorC, anchorZ]
  | inr k => simp [mergedChild, mergedEdge, mergedParent, anchorB]

noncomputable def mergedChildEquiv (u v : ℕ) :
    (Fin 2 ⊕ Fin (2 * u)) ≃ {x : NamedVertex u v // mergedEdge (anchorB u v) x} :=
  Equiv.ofBijective (fun i => ⟨mergedChild u v i, mergedChild_mem u v i⟩) (by
    constructor
    · intro i j h
      exact mergedChild_injective u v (congrArg Subtype.val h)
    · intro ⟨x, hx⟩
      rcases (merged_B_children x).mp hx with hC | hZ | ⟨k, hk⟩
      · exact ⟨.inl 0, Subtype.ext hC.symm⟩
      · exact ⟨.inl 1, Subtype.ext hZ.symm⟩
      · exact ⟨.inr k, Subtype.ext hk.symm⟩)

noncomputable instance mergedChildrenFintype (u v : ℕ) :
    Fintype {x : NamedVertex u v // mergedEdge (anchorB u v) x} :=
  Fintype.ofEquiv (Fin 2 ⊕ Fin (2 * u)) (mergedChildEquiv u v)

theorem merged_B_child_count (u v : ℕ) :
    Fintype.card {x : NamedVertex u v // mergedEdge (anchorB u v) x} = 2 * u + 2 := by
  classical
  rw [← Fintype.card_congr (mergedChildEquiv u v)]
  simp [Nat.add_comm]

theorem merged_A_children {u v : ℕ} (x : NamedVertex u v) :
    mergedEdge (anchorA u v) x ↔ x = anchorB u v := by
  cases x with
  | root => simp [mergedEdge, mergedParent, anchorA, anchorB]
  | branch b => cases b <;> simp [mergedEdge, mergedParent, anchorA, anchorB]
  | star s => cases s <;> simp [mergedEdge, mergedParent, anchorA, anchorB, starBranch]
  | leaf s k => cases s <;> simp [mergedEdge, mergedParent, anchorA, anchorB]

theorem original_A_children {u v : ℕ} (x : NamedVertex u v) :
    namedEdge (anchorA u v) x ↔ x = anchorC u v ∨ x = anchorB u v := by
  cases x with
  | root => simp [namedEdge, namedParent, anchorA, anchorB, anchorC]
  | branch b => cases b <;> simp [namedEdge, namedParent, anchorA, anchorB, anchorC]
  | star s => cases s <;> simp [namedEdge, namedParent, anchorA, anchorB, anchorC, starBranch]
  | leaf s k => simp [namedEdge, namedParent, anchorA, anchorB, anchorC]

theorem original_B_children {u v : ℕ} (x : NamedVertex u v) :
    namedEdge (anchorB u v) x ↔ ∃ k : Fin (2 * u), x = .leaf .c2 k := by
  cases x with
  | root => simp [namedEdge, namedParent, anchorB]
  | branch b => simp [namedEdge, namedParent, anchorB]
  | star s => simp [namedEdge, namedParent, anchorB]
  | leaf s k =>
    cases s with
    | a1 =>
      simp [namedEdge, namedParent, anchorB]
      intro l h
      cases h
    | a2 =>
      simp [namedEdge, namedParent, anchorB]
      intro l h
      cases h
    | a3 =>
      simp [namedEdge, namedParent, anchorB]
      intro l h
      cases h
    | b1 =>
      simp [namedEdge, namedParent, anchorB]
      intro l h
      cases h
    | b2 =>
      simp [namedEdge, namedParent, anchorB]
      intro l h
      cases h
    | b3 =>
      simp [namedEdge, namedParent, anchorB]
      intro l h
      cases h
    | c1 =>
      simp [namedEdge, namedParent, anchorB]
      intro l h
      cases h
    | c2 =>
      simp [namedEdge, namedParent, anchorB]
      exact ⟨k, rfl⟩

theorem original_C_children {u v : ℕ} (x : NamedVertex u v) :
    namedEdge (anchorC u v) x ↔ x = anchorZ u v := by
  cases x with
  | root => simp [namedEdge, namedParent, anchorC, anchorZ]
  | branch b => simp [namedEdge, namedParent, anchorC, anchorZ]
  | star s => simp [namedEdge, namedParent, anchorC, anchorZ]
  | leaf s k =>
    cases s <;> simp [namedEdge, namedParent, anchorC, anchorZ]
    exact Fin.eq_zero k

end Partials.Graceful.ManuscriptPresentation
