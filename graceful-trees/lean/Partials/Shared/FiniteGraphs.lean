import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Nat.Dist

/-! Finite graph, rooted-parent and labeling interfaces.
Graceful.Model instantiates these interfaces for the manuscript family;
Graceful.Geometry connects its incidences to the undirected simple graph. -/
namespace Partials.Interface

/-- Each undirected edge is represented once, with a chosen orientation. -/
structure FiniteEdgeGraph (V E : Type*) [Fintype V] [Fintype E] where
  ends : E → V × V
  nonloop : ∀ e, (ends e).1 ≠ (ends e).2
  unique_edge : ∀ e f, ends e = ends f ∨
    ((ends e).1 = (ends f).2 ∧ (ends e).2 = (ends f).1) → e = f

/-- A rooted-parent presentation with strictly decreasing depth away from
the root. Graph incidences are linked to it by `ParentCompatible`. -/
structure RootedParentTree (V : Type*) where
  root : V
  parent : V → V
  depth : V → ℕ
  root_parent : parent root = root
  root_depth : depth root = 0
  parent_depth : ∀ v, v ≠ root → depth (parent v) < depth v

def ParentCompatible {V E : Type*} [Fintype V] [Fintype E]
    (G : FiniteEdgeGraph V E) (T : RootedParentTree V) : Prop :=
  ∀ u v, (∃ e, G.ends e = (u, v)) ↔ v ≠ T.root ∧ T.parent v = u

def EdgeDifference {V E : Type*} [Fintype V] [Fintype E]
    (G : FiniteEdgeGraph V E) (label : V → ℕ) (e : E) : ℕ :=
  Nat.dist (label (G.ends e).1) (label (G.ends e).2)

def RootZeroGraceful {V E : Type*} [Fintype V] [Fintype E]
    (G : FiniteEdgeGraph V E) (root : V) (q : ℕ) (label : V → Fin (q + 1)) : Prop :=
  Function.Bijective label ∧ label root = 0 ∧
  (∀ d : ℕ, (1 ≤ d ∧ d ≤ q) ↔ ∃ e, EdgeDifference G (fun v ↦ (label v).val) e = d) ∧
  Function.Injective (EdgeDifference G (fun v ↦ (label v).val))

def ProperColoring {V E Color : Type*} [Fintype V] [Fintype E]
    (G : FiniteEdgeGraph V E) (color : V → Color) : Prop :=
  ∀ e, color (G.ends e).1 ≠ color (G.ends e).2

end Partials.Interface
