import Mathlib.Data.Fintype.Basic

/-! R1 arena signatures. No reset, compiler, all-history equivalence or
physical-realization theorem is asserted by these structures. -/
namespace Partials.Interface

structure ParityArenaData (V : Type*) [Fintype V] where
  edge : V → V → Prop
  even : V → Bool
  priority : V → ℕ
  total : ∀ v, ∃ w, edge v w

/-- Defined on every original vertex, including unreachable Even vertices. -/
structure CompleteEvenPolicy {V : Type*} [Fintype V] (A : ParityArenaData V) where
  move : V → V
  legal_even : ∀ v, A.even v = true → A.edge v (move v)

structure ParityExitInterface {V Exit : Type*} [Fintype V] [Fintype Exit]
    (A : ParityArenaData V) where
  vertex : Exit → V
  injective : Function.Injective vertex
  zero_priority : ∀ o, A.priority (vertex o) = 0
  sink : ∀ o w, A.edge (vertex o) w ↔ w = vertex o

def PolicyCompatible {V : Type*} [Fintype V]
    (A : ParityArenaData V) (policy : CompleteEvenPolicy A) (path : ℕ → V) : Prop :=
  ∀ n, A.edge (path n) (path (n + 1)) ∧
    (A.even (path n) = true → path (n + 1) = policy.move (path n))

/-- Ordered rotor slots may vary by vertex. Repeated destinations remain
distinct slots, including the source's four-slot compressed rotor. -/
structure OrderedRotorNetwork (V : Type*) [Fintype V] where
  slotCount : V → ℕ
  slots_positive : ∀ v, 0 < slotCount v
  successor : (v : V) → Fin (slotCount v) → V
  sink : V → Prop
  sink_fixed : ∀ v, sink v → ∀ slot, successor v slot = v

def IsBinaryRotorNetwork {V : Type*} [Fintype V] (N : OrderedRotorNetwork V) : Prop :=
  ∀ v, N.slotCount v = 2

def IsFourSlotRotorAt {V : Type*} [Fintype V] (N : OrderedRotorNetwork V) (v : V) : Prop :=
  N.slotCount v = 4

abbrev RotorState {V : Type*} [Fintype V] (N : OrderedRotorNetwork V) :=
  (v : V) → Fin (N.slotCount v)

end Partials.Interface
