import Partials.ParityAlgorithms.Normalization

/-! P3-C01--C03: acyclic fixed-policy evaluation is a different operation
from full-history optimized fronts. Every original choice is retained,
including bypassed siblings and the updated unreachable root. -/
namespace Partials.ParityAlgorithms.Context
open Partials.Parity
open Partials.ParityAlgorithms

inductive Closed (Exit : Type*) where
  | atom (a : Atom Exit)
  | prefix (p : Priority5) (x : Closed Exit)
  | even (originalId : Nat) (left right : Closed Exit)
  | odd (left right : Closed Exit)
  deriving DecidableEq

def Closed.originalChoices {Exit : Type*} : Closed Exit → List Nat
  | .atom _ => []
  | .prefix _ x => x.originalChoices
  | .even c x y => c :: (x.originalChoices ++ y.originalChoices)
  | .odd x y => x.originalChoices ++ y.originalChoices

/-- This supplies decisions at *all* original binary Even choices; false
chooses left. Forced original vertices still belong to the concrete arena
adapter; the datatype never removes the unused right or left occurrence. -/
abbrev ExteriorPolicy := Nat → Bool

def rawList {Exit : Type*} (σ : ExteriorPolicy) : Closed Exit → List (Atom Exit)
  | .atom a => [a]
  | .prefix p x => (rawList σ x).map (atomPrefix p)
  | .even c x y => if σ c then rawList σ y else rawList σ x
  | .odd x y => rawList σ x ++ rawList σ y

def rawSet {Exit : Type*} (σ : ExteriorPolicy) (x : Closed Exit) : Row Exit :=
  {o | ∃ a ∈ rawList σ x, o = a.outcome}

def fixedRow {Exit : Type*} (σ : ExteriorPolicy) (x : Closed Exit) : Row Exit :=
  MinRow (rawSet σ x)

theorem rawList_nonempty {Exit : Type*} (σ : ExteriorPolicy) (x : Closed Exit) :
    rawList σ x ≠ [] := by
  induction x with
  | atom a => simp [rawList]
  | «prefix» p x ih => simpa [rawList] using ih
  | even c x y ihx ihy => cases h : σ c <;> simp [rawList, h, ihx, ihy]
  | odd x y ihx ihy => simp [rawList, ihx, ihy]

theorem rawSet_finite {Exit : Type*} (σ : ExteriorPolicy) (x : Closed Exit) :
    (rawSet σ x).Finite := by
  classical
  have h : (rawSet σ x) = Atom.outcome '' {a | a ∈ rawList σ x} := by
    ext o
    simp [rawSet, eq_comm]
  rw [h]
  exact (List.finite_toSet _).image _

theorem fixedRow_finite {Exit : Type*} (σ : ExteriorPolicy) (x : Closed Exit) :
    (fixedRow σ x).Finite := (rawSet_finite σ x).subset (minRow_subset _)

theorem fixedRow_even {Exit : Type*} (σ : ExteriorPolicy) (c : Nat) (x y : Closed Exit) :
    fixedRow σ (.even c x y) = if σ c then fixedRow σ y else fixedRow σ x := by
  cases h : σ c <;> simp [fixedRow, rawSet, rawList, h]

theorem rawSet_odd {Exit : Type*} (σ : ExteriorPolicy) (x y : Closed Exit) :
    rawSet σ (.odd x y) = rawSet σ x ∪ rawSet σ y := by
  ext o
  simp [rawSet, rawList, List.mem_append, or_and_right, exists_or]

theorem fixedRow_odd {Exit : Type*} (σ : ExteriorPolicy) (x y : Closed Exit) :
    fixedRow σ (.odd x y) = rowMeet (fixedRow σ x) (fixedRow σ y) := by
  rw [fixedRow, rawSet_odd]
  exact minRow_union_minima _ _ (rawSet_finite σ x) (rawSet_finite σ y)

theorem atomPrefix_outcome {Exit : Type*} (p : Priority5) (a : Atom Exit) :
    (atomPrefix p a).outcome = prefixOutcome p a.outcome := by
  cases a <;> rfl

theorem rawSet_prefix {Exit : Type*} (σ : ExteriorPolicy) (p : Priority5) (x : Closed Exit) :
    rawSet σ (.prefix p x) = prefixOutcome p '' rawSet σ x := by
  ext o
  simp [rawSet, rawList, atomPrefix_outcome, eq_comm]

theorem fixedRow_prefix {Exit : Type*} (σ : ExteriorPolicy) (p : Priority5) (x : Closed Exit) :
    fixedRow σ (.prefix p x) = rowPrefix p (fixedRow σ x) := by
  rw [fixedRow, rawSet_prefix]
  exact minRow_monotone_image p _ (rawSet_finite σ x)

inductive Hole (Exit : Type*) where
  | hole
  | prefix (p : Priority5) (child : Hole Exit)
  | evenLeft (originalId : Nat) (child : Hole Exit) (sibling : Closed Exit)
  | evenRight (originalId : Nat) (sibling : Closed Exit) (child : Hole Exit)
  | oddLeft (child : Hole Exit) (sibling : Closed Exit)
  | oddRight (sibling : Closed Exit) (child : Hole Exit)

/-- At most one occurrence of U; a bypass is constant and preserves σ. -/
def transform {Exit : Type*} (σ : ExteriorPolicy) : Hole Exit → Row Exit → Row Exit
  | .hole, u => u
  | .prefix p c, u => rowPrefix p (transform σ c u)
  | .evenLeft id c d, u => if σ id then fixedRow σ d else transform σ c u
  | .evenRight id d c, u => if σ id then transform σ c u else fixedRow σ d
  | .oddLeft c d, u => rowMeet (transform σ c u) (fixedRow σ d)
  | .oddRight d c, u => rowMeet (fixedRow σ d) (transform σ c u)

theorem transform_finite {Exit : Type*} (σ : ExteriorPolicy) (c : Hole Exit)
    {u : Row Exit} (hu : u.Finite) : (transform σ c u).Finite := by
  induction c with
  | hole => exact hu
  | «prefix» p c ih => exact (ih.image _).subset (minRow_subset _)
  | evenLeft id c d ih => cases h : σ id <;> simp only [transform, h, Bool.false_eq_true, if_false, if_true]; exact ih; exact fixedRow_finite σ d
  | evenRight id d c ih => cases h : σ id <;> simp only [transform, h, Bool.false_eq_true, if_false, if_true]; exact fixedRow_finite σ d; exact ih
  | oddLeft c d ih => exact (ih.union (fixedRow_finite σ d)).subset (minRow_subset _)
  | oddRight d c ih => exact ((fixedRow_finite σ d).union ih).subset (minRow_subset _)

theorem transform_monotone {Exit : Type*} (σ : ExteriorPolicy) (c : Hole Exit)
    {u v : Row Exit} (hu : u.Finite) (hv : v.Finite) (h : RowLE u v) :
    RowLE (transform σ c u) (transform σ c v) := by
  induction c with
  | hole => exact h
  | «prefix» p c ih => exact rowPrefix_monotone p (transform_finite σ c hu) ih
  | evenLeft id c d ih => cases hc : σ id <;> simp only [transform, hc, Bool.false_eq_true, if_false, if_true]; exact ih; exact rowLE_refl _
  | evenRight id d c ih => cases hc : σ id <;> simp only [transform, hc, Bool.false_eq_true, if_false, if_true]; exact rowLE_refl _; exact ih
  | oddLeft c d ih =>
    exact rowMeet_monotone (transform_finite σ c hu) (fixedRow_finite σ d)
      (transform_finite σ c hv) (fixedRow_finite σ d) ih (rowLE_refl _)
  | oddRight d c ih =>
    exact rowMeet_monotone (fixedRow_finite σ d) (transform_finite σ c hu)
      (fixedRow_finite σ d) (transform_finite σ c hv) (rowLE_refl _) ih

def updateOne (σ : ExteriorPolicy) (c : Nat) : ExteriorPolicy := Function.update σ c true

theorem updateOne_elsewhere (σ : ExteriorPolicy) (c v : Nat) (h : v ≠ c) :
    updateOne σ c v = σ v := by simp [updateOne, Function.update, h]

theorem updateOne_at (σ : ExteriorPolicy) (c : Nat) : updateOne σ c c = true := by
  simp [updateOne]

def listCompare {Exit : Type*} [DecidableEq Exit] (a b : List (Atom Exit)) : Bool :=
  b.all fun y => a.any fun x => decide (atomLE x y)

theorem listCompare_correct {Exit : Type*} [DecidableEq Exit] (a b : List (Atom Exit)) :
    listCompare a b = true ↔ atomListLE a b := by
  simp [listCompare, atomListLE, List.all_eq_true, List.any_eq_true]

def Forward {Start Exit : Type*} (a b : Profile Start Exit) := ProfileLE a b
def Reverse {Start Exit : Type*} (a b : Profile Start Exit) := ProfileLE b a

theorem strict_iff_forward_not_reverse {Start Exit : Type*} (a b : Profile Start Exit) :
    StrictProfile a b ↔ Forward a b ∧ ¬ Reverse a b := Iff.rfl

theorem reverse_failure_witness {Start Exit : Type*} (a b : Profile Start Exit) :
    ¬ Reverse a b ↔ ∃ i x, x ∈ a i ∧ ∀ y ∈ b i, ¬ OutcomeLE y x := by
  classical
  simp [Reverse, ProfileLE, RowLE, not_forall, not_exists, not_and]

theorem tie_iff_mutual {Start Exit : Type*} (a b : Profile Start Exit)
    (ha : ∀ i, SourceAntichain (a i)) (hb : ∀ i, SourceAntichain (b i)) :
    a = b ↔ Forward a b ∧ Reverse a b := by
  constructor
  · rintro rfl
    exact ⟨profileLE_refl a, profileLE_refl a⟩
  · rintro ⟨hab, hba⟩
    exact profileLE_antisymm ha hb hab hba

/-- Two finite atom comparisons can mask strictness without losing assignments. -/
theorem priority_four_masks (p q : Priority5) : priorityJoin 4 p = priorityJoin 4 q := by
  apply Fin.ext
  have hp := p.isLt
  have hq := q.isLt
  simp only [priorityJoin]
  omega

theorem raw_equality_stronger_than_minima :
    MinRow ({Outcome.halt () 0, Outcome.halt () 2} : Set (Outcome Unit)) =
      MinRow ({Outcome.halt () 0} : Set (Outcome Unit)) := by
  ext x
  cases x <;> simp [MinRow, OutcomeLE, PriorityLE] <;> omega

/-- Precise unfinished literal graph/strategy correspondence for C01/C-T1:
construct the original edge arena and its original-node identity map; prove
all Odd histories equal rawList, that selected arms use the supplied complete
policy, and that each hole path induces transform. Include 1/2 entrances,
1/2 stopped exits, all fresh mergers, no L/backward/shared choice, and all
forced/unreachable policy entries. No optimized front appears in this duty. -/
theorem fixedPolicy_rows_are_finite_antichains (q : Nat)
    (σ : ExteriorPolicy) (d : Closed (Fin q)) :
    (fixedRow σ d).Finite ∧ SourceAntichain (fixedRow σ d) :=
  ⟨fixedRow_finite σ d,minRow_antichain _⟩

/-- Uniform machine-cost proof remains open: constant-size rows ≤2,
meet examines ≤4, prefix ≤2; all n unshared syntax nodes (including unused
siblings and both M folds) and graph nG are charged, arbitrary IDs at actual
bit lengths L, word width ceil(log2(n+2)), and full-policy/witness output.
No compressed DAG, arbitrary graph recognition, optimization or pivot-run
cost is derived here. -/
structure ContextCostTargets where
  syntaxNodes : Nat
  graphVertices : Nat
  labelBits : Nat
  indexedWordOps : Nat
  indexedWords : Nat
  bitWork : Nat
  bitStorage : Nat
  retainedPlays : Nat
  rowWidth : Nat
  rowWidth_cap : rowWidth ≤ 2
  retainedPlays_cap : retainedPlays ≤ 8

end Partials.ParityAlgorithms.Context
