import Partials.Shared.Arenas
import Mathlib.Tactic
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Log

/-! R3 shared vocabulary, drafted without Lean execution. Named upper outputs,
passive cut destinations and external inputs are different types. Repeated
destinations in the four-slot word retain their distinct slot indices. -/
namespace Partials.Arrival

inductive NamedOutput where
  | a0 | b0 | c0
  deriving DecidableEq

instance : Fintype NamedOutput where
  elems := {.a0, .b0, .c0}
  complete := by intro o; cases o <;> simp

inductive PassiveDestination where
  | feedback | b0 | c0
  deriving DecidableEq

instance : Fintype PassiveDestination where
  elems := {.feedback, .b0, .c0}
  complete := by intro o; cases o <;> simp

inductive InputPort where
  | E | F
  deriving DecidableEq

instance : Fintype InputPort where
  elems := {.E, .F}
  complete := by intro o; cases o <;> simp

structure Batch where
  N : ℕ
  M : ℕ
  deriving DecidableEq

def Batch.add (v w : Batch) : Batch := ⟨v.N + w.N, v.M + w.M⟩
def Batch.total (v : Batch) : ℕ := v.N + v.M

@[ext] structure NamedCounts where
  a0 : ℕ
  b0 : ℕ
  c0 : ℕ
  deriving DecidableEq

def NamedCounts.total (C : NamedCounts) : ℕ := C.a0 + C.b0 + C.c0
def NamedCounts.add (C D : NamedCounts) : NamedCounts :=
  ⟨C.a0 + D.a0, C.b0 + D.b0, C.c0 + D.c0⟩

structure InterfaceState (k : ℕ) where
  h : Fin (k + 1)
  r : Fin 4
  deriving DecidableEq

/-- The slot, rather than just its destination, is part of the state. -/
def passiveWord (k : ℕ) (slot : Fin 4) : PassiveDestination :=
  if slot.val = 0 then .feedback
  else if slot.val = 1 then
    if k % 2 = 1 then .b0 else .c0
  else if slot.val = 2 then
    if k % 2 = 1 then .c0 else .b0
  else .c0

def nextFourSlot (slot : Fin 4) : Fin 4 :=
  ⟨(slot.val + 1) % 4, Nat.mod_lt _ (by decide)⟩

theorem passiveWord_feedback_iff (k : ℕ) (slot : Fin 4) :
    passiveWord k slot = .feedback ↔ slot.val = 0 := by
  fin_cases slot <;> by_cases odd : k % 2 = 1 <;> simp [passiveWord, odd]

theorem passiveWord_last (k : ℕ) : passiveWord k ⟨3, by decide⟩ = .c0 := by
  simp [passiveWord]

theorem namedCounts_add_total (C D : NamedCounts) :
    (C.add D).total = C.total + D.total := by
  simp [NamedCounts.add, NamedCounts.total]
  omega

end Partials.Arrival
