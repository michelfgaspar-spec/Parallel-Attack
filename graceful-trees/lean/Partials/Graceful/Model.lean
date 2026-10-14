import Partials.Shared.FiniteGraphs
import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.RCases
import Lean.Elab.Tactic.Omega

/-! R2 blind source draft. Exact ordered representative of the paper's
unordered branch profiles. No local elaboration or kernel check has run. -/
namespace Partials.Graceful

def q (u v : ℕ) : ℕ := 19 + 2 * (u + v)

def depthTwoCount (i : Fin 3) : ℕ := if i.val = 2 then 2 else 3

def pendantCount (u v : ℕ) (i : Fin 3) (j : Fin (depthTwoCount i)) : ℕ :=
  if i.val = 0 then
    if j.val = 2 then 3 else 1
  else if i.val = 1 then
    if j.val = 2 then 2 * v else 1
  else if j.val = 1 then 2 * u else 1

inductive Vertex (u v : ℕ) where
  | root : Vertex u v
  | levelOne (i : Fin 3) : Vertex u v
  | levelTwo (i : Fin 3) (j : Fin (depthTwoCount i)) : Vertex u v
  | leaf (i : Fin 3) (j : Fin (depthTwoCount i))
      (k : Fin (pendantCount u v i j)) : Vertex u v
  deriving DecidableEq

abbrev LeafCode (u v : ℕ) :=
  Σ i : Fin 3, Σ j : Fin (depthTwoCount i), Fin (pendantCount u v i j)

abbrev VertexCode (u v : ℕ) :=
  Unit ⊕ (Fin 3 ⊕ ((Σ i : Fin 3, Fin (depthTwoCount i)) ⊕ LeafCode u v))

def vertexEquiv (u v : ℕ) : Vertex u v ≃ VertexCode u v where
  toFun
    | .root => .inl ()
    | .levelOne i => .inr (.inl i)
    | .levelTwo i j => .inr (.inr (.inl ⟨i, j⟩))
    | .leaf i j k => .inr (.inr (.inr ⟨i, j, k⟩))
  invFun
    | .inl _ => .root
    | .inr (.inl i) => .levelOne i
    | .inr (.inr (.inl ⟨i, j⟩)) => .levelTwo i j
    | .inr (.inr (.inr ⟨i, j, k⟩)) => .leaf i j k
  left_inv := by intro x; cases x <;> rfl
  right_inv := by
    intro x
    rcases x with a | x
    · cases a; rfl
    rcases x with i | x
    · rfl
    rcases x with ⟨i, j⟩ | ⟨i, j, k⟩ <;> rfl

instance (u v : ℕ) : Fintype (Vertex u v) :=
  Fintype.ofEquiv (VertexCode u v) (vertexEquiv u v).symm

def parent {u v : ℕ} : Vertex u v → Vertex u v
  | .root => .root
  | .levelOne _ => .root
  | .levelTwo i _ => .levelOne i
  | .leaf i j _ => .levelTwo i j

def depth {u v : ℕ} : Vertex u v → ℕ
  | .root => 0
  | .levelOne _ => 1
  | .levelTwo _ _ => 2
  | .leaf _ _ _ => 3

def Edge {u v : ℕ} (a b : Vertex u v) : Prop := b ≠ .root ∧ parent b = a

abbrev EdgeIndex (u v : ℕ) := {x : Vertex u v // x ≠ .root}

theorem parent_depth {u v : ℕ} (x : Vertex u v) (hx : x ≠ .root) :
    depth (parent x) < depth x := by
  cases x <;> simp_all [parent, depth]

def rootedTree (u v : ℕ) : Partials.Interface.RootedParentTree (Vertex u v) where
  root := .root
  parent := parent
  depth := depth
  root_parent := rfl
  root_depth := rfl
  parent_depth := parent_depth

def graph (u v : ℕ) :
    Partials.Interface.FiniteEdgeGraph (Vertex u v) (EdgeIndex u v) where
  ends e := (parent e.val, e.val)
  nonloop := by
    intro e h
    have hd := parent_depth e.val e.property
    change parent e.val = e.val at h
    rw [h] at hd
    exact (Nat.lt_irrefl _) hd
  unique_edge := by
    intro e f h
    rcases h with h | ⟨h₁, h₂⟩
    · apply Subtype.ext
      exact congrArg Prod.snd h
    · have he := parent_depth e.val e.property
      have hf := parent_depth f.val f.property
      change parent e.val = f.val at h₁
      change e.val = parent f.val at h₂
      rw [h₁] at he
      rw [← h₂] at hf
      omega

theorem graph_parent_compatible (u v : ℕ) :
    Partials.Interface.ParentCompatible (graph u v) (rootedTree u v) := by
  intro a b
  constructor
  · rintro ⟨e, he⟩
    have hb : e.val = b := congrArg Prod.snd he
    have ha : parent e.val = a := congrArg Prod.fst he
    exact ⟨by simpa [rootedTree, hb] using e.property, by simpa [rootedTree, hb] using ha⟩
  · rintro ⟨hb, ha⟩
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [graph, rootedTree] at ha ⊢
    exact Prod.ext ha rfl

def RootZeroGraceful (u v : ℕ) (f : Vertex u v → Fin (q u v + 1)) : Prop :=
  Partials.Interface.RootZeroGraceful (graph u v) .root (q u v) f

/-- Exact paper target, with no proof or desired-conclusion parameter hidden
inside its definition. It is not asserted inhabited by defining it. -/
def AllPositiveTarget : Prop :=
  ∀ u v : ℕ, 0 < u → 0 < v →
    ∃ f : Vertex u v → Fin (q u v + 1), RootZeroGraceful u v f

theorem depth_two_card :
    Fintype.card (Σ i : Fin 3, Fin (depthTwoCount i)) = 8 := by
  decide

theorem leaf_card (u v : ℕ) : Fintype.card (LeafCode u v) = 8 + 2 * (u + v) := by
  simp [LeafCode, Fintype.card_sigma, Fin.sum_univ_succ, depthTwoCount, pendantCount]
  omega

theorem vertex_card (u v : ℕ) : Fintype.card (Vertex u v) = q u v + 1 := by
  rw [Fintype.card_congr (vertexEquiv u v)]
  simp only [VertexCode, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin,
    depth_two_card, leaf_card, q]
  omega

theorem q23_parameters (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hq : q u v = 23) : u = 1 ∧ v = 1 := by
  dsimp [q] at hq
  omega

theorem q27_parameters (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hq : q u v = 27) :
    (u = 1 ∧ v = 3) ∨ (u = 2 ∧ v = 2) ∨ (u = 3 ∧ v = 1) := by
  dsimp [q] at hq
  omega

theorem edge_count_cases (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    q u v = 23 ∨ (∃ t : ℕ, q u v = 25 + 6 * t) ∨
    (∃ t : ℕ, q u v = 27 + 6 * t) ∨ (∃ t : ℕ, q u v = 29 + 6 * t) := by
  have hS : 2 ≤ u + v := by omega
  by_cases hsmall : u + v = 2
  · left
    dsimp [q]
    omega
  · have hlarge : 3 ≤ u + v := by omega
    have hmod : (u + v) % 3 < 3 := Nat.mod_lt _ (by decide)
    have hdiv := Nat.mod_add_div (u + v) 3
    by_cases hzero : (u + v) % 3 = 0
    · right
      left
      refine ⟨(u + v) / 3 - 1, ?_⟩
      dsimp [q]
      omega
    · by_cases hone : (u + v) % 3 = 1
      · right
        right
        left
        refine ⟨(u + v) / 3 - 1, ?_⟩
        dsimp [q]
        omega
      · right
        right
        right
        refine ⟨(u + v) / 3 - 1, ?_⟩
        dsimp [q]
        omega

end Partials.Graceful
