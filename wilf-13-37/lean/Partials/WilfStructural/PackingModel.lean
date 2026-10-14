import Mathlib.Data.Finset.Interval
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! R9 blind source, UNCOMPILED. Finite combinatorial models for L20--L27.
These definitions do not assert that a semigroup supplies the required data.
Monomials are exponent vectors; values and residues are separate maps. -/
namespace Partials.WilfStructural.Packing

abbrev Monomial (s : ℕ) := Fin s → ℕ

def degree {s : ℕ} (u : Monomial s) : ℕ := ∑ i, u i

def value {s : ℕ} (x : Fin s → ℤ) (u : Monomial s) : ℤ :=
  ∑ i, (u i : ℤ) * x i

structure Box (s : ℕ) where
  lower : Fin s → ℤ
  upper : Fin s → ℤ

def Box.Contains {s : ℕ} (B : Box s) (x : Fin s → ℤ) : Prop :=
  ∀ i, B.lower i ≤ x i ∧ x i ≤ B.upper i

def layer (m ρ j : ℤ) : Finset ℤ := Finset.Icc (j*m-ρ) ((j+1)*m-ρ-1)

def monomialInterval {s : ℕ} (B : Box s) (u : Monomial s) : Finset ℤ :=
  Finset.Icc (value B.lower u) (value B.upper u)

def topInterval {s : ℕ} (B : Box s) (m ρ q : ℤ)
    (u : Monomial s) : Finset ℤ := monomialInterval B u ∩ layer m ρ q

/- Zero denotes not selected left; it says nothing about top selection. -/
abbrev LeftLabels (s : ℕ) := Monomial s → ℕ
abbrev Allocation := ℕ → ℕ → ℕ

def labelCount {s : ℕ} (family : Finset (Monomial s))
    (labels : LeftLabels s) (d j : ℕ) : ℕ :=
  (family.filter fun u => degree u = d ∧ labels u = j).card

def HasQuotas {s : ℕ} (family : Finset (Monomial s))
    (labels : LeftLabels s) (h : Allocation) : Prop :=
  ∀ d j, 0 < j → labelCount family labels d j = h d j

def ImmediateDivisor {s : ℕ} (v u : Monomial s) : Prop :=
  (∀ i, v i ≤ u i) ∧ degree v + 1 = degree u

def IsMatching {L R : Type*} (edges : Finset (L × R)) : Prop :=
  Set.InjOn Prod.fst (↑edges : Set (L × R)) ∧
  Set.InjOn Prod.snd (↑edges : Set (L × R))

noncomputable def matchingCapacity {L R : Type*} [DecidableEq L] [DecidableEq R]
    (graph : Finset (L × R)) : ℕ := by
  classical
  exact (graph.powerset.filter IsMatching).sup Finset.card

def intervalGraph {L : Type*} [DecidableEq L]
    (vertices : Finset L) (interval : L → Finset ℤ) : Finset (L × ℤ) :=
  vertices.biUnion fun u => (interval u).image fun z => (u,z)

def residueGraph {L : Type*} [DecidableEq L]
    (vertices : Finset L) (interval : L → Finset ℤ) (m : ℤ) : Finset (L × ℤ) :=
  (intervalGraph vertices interval).image fun p => (p.1, p.2 % m)

/- Disjoint constructors prevent conflation of zero, variables and monomials.
Right primitives are deliberately absent, as in L25. -/
inductive ResidueVertex (s : ℕ)
  | zero
  | primitive (i : Fin s)
  | left (u : Monomial s)
  | top (u : Monomial s)
  deriving DecidableEq

end Partials.WilfStructural.Packing
