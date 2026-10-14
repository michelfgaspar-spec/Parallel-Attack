import Partials.WilfStructural.FoundationTargets

/-! Shared R10 ground objects, blind and uncompiled. Canonical identity is the
actual conductor together with its complete left set. The all-naturals case is
separate from this positive-conductor state space. No successful run or Wilf
conclusion is a field of these objects. -/
namespace Partials.WilfFinite.Core

abbrev CanonicalState := Σ c : ℕ, Partials.WilfStructural.Foundation.CanonicalLeft c

def conductor (a : CanonicalState) : ℕ := a.1
def left (a : CanonicalState) : Finset ℕ := a.2.left
def key (a : CanonicalState) : ℕ × Finset ℕ := (conductor a, left a)
def leftCount (a : CanonicalState) : ℕ := (left a).card

structure Parameters where
  C : ℕ
  u : ℕ
  v : ℕ
  C_two : 2 ≤ C
  u_pos : 1 ≤ u
  ordered : u ≤ v

def InTarget (p : Parameters) (a : CanonicalState) : Prop :=
  conductor a ≤ p.C ∧ p.u ≤ leftCount a ∧ leftCount a ≤ p.v

noncomputable def semigroup (a : CanonicalState) : Partials.Interface.NumericalSemigroup :=
  Partials.WilfStructural.Foundation.canonicalSemigroup a.2

theorem actual_conductor (a : CanonicalState) :
    Partials.Interface.IsConductor (semigroup a) (conductor a) :=
  Partials.WilfStructural.Foundation.canonical_conductor a.2

theorem complete_left (a : CanonicalState) :
    Partials.Interface.LeftBelow (semigroup a) (conductor a) = left a :=
  Partials.WilfStructural.Foundation.canonical_left_exact a.2

theorem key_injective : Function.Injective key := by
  intro x y h
  rcases x with ⟨c, a⟩
  rcases y with ⟨d, b⟩
  have hc : c = d := congrArg Prod.fst h
  cases hc
  have hl : a.left = b.left := congrArg Prod.snd h
  have hab : a = b := by
    cases a
    cases b
    simp_all
  subst b
  rfl

end Partials.WilfFinite.Core
