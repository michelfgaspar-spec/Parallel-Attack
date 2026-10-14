import Mathlib.Algebra.Group.Submonoid.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Range
import Mathlib.Algebra.Ring.Nat

/-! R1 signatures adapted from the old numerical-semigroup draft. Least-value
existence, cardinality laws and Wilf inequalities are left to R9/R10. -/
namespace Partials.Interface

structure NumericalSemigroup where
  carrier : AddSubmonoid ℕ
  finiteGaps : {x : ℕ | x ∉ carrier}.Finite

def IsConductor (S : NumericalSemigroup) (c : ℕ) : Prop :=
  (∀ n : ℕ, c ≤ n → n ∈ S.carrier) ∧
  (∀ b : ℕ, b < c → ∃ n : ℕ, b ≤ n ∧ n ∉ S.carrier)

def IsMultiplicity (S : NumericalSemigroup) (m : ℕ) : Prop :=
  0 < m ∧ m ∈ S.carrier ∧ ∀ n : ℕ, 0 < n → n ∈ S.carrier → m ≤ n

def IsDecomposable (S : NumericalSemigroup) (x : ℕ) : Prop :=
  ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ∈ S.carrier ∧ b ∈ S.carrier ∧ x = a + b

def IsPrimitive (S : NumericalSemigroup) (x : ℕ) : Prop :=
  x ∈ S.carrier ∧ 0 < x ∧ ¬IsDecomposable S x

def IsAperyAt (S : NumericalSemigroup) (m x : ℕ) : Prop :=
  x ∈ S.carrier ∧ ¬∃ y : ℕ, y ∈ S.carrier ∧ x = m + y

noncomputable def LeftBelow (S : NumericalSemigroup) (c : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range c).filter (fun x ↦ x ∈ S.carrier)

end Partials.Interface
