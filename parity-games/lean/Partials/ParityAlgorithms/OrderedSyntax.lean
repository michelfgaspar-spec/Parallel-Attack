import Partials.Parity.Rows
import Partials.Parity.PlayTransport
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.BigOperators

/-! Blind R8 source, normalization.tex P3-D01/R01--R19. New mathematical
source follows the frozen manuscript; the retained GeneralTargets draft is
an interface antecedent only. All tactic text is unexecuted. Edge priorities
here are distinct from the vertex priorities of ReturnSpectra. -/
namespace Partials.ParityAlgorithms
open Partials.Parity

abbrev Priority5 := Fin 5

def sourceRank (p : Priority5) : Nat :=
  if p.val = 3 then 0 else if p.val = 1 then 1 else
    if p.val = 0 then 2 else if p.val = 2 then 3 else 4

def priorityJoin (p q : Priority5) : Priority5 :=
  ⟨max p.val q.val, max_lt p.isLt q.isLt⟩

theorem sourceRank_exact (p q : Priority5) :
    sourceRank p ≤ sourceRank q ↔ PriorityLE p.val q.val := by
  fin_cases p <;> fin_cases q <;> norm_num [sourceRank, PriorityLE]

theorem sourceRank_injective : Function.Injective sourceRank := by
  intro p q h
  fin_cases p <;> fin_cases q <;> simp_all [sourceRank]

theorem priorityJoin_zero (p : Priority5) : priorityJoin 0 p = p := by
  apply Fin.ext
  simp [priorityJoin]

theorem priorityJoin_assoc (p q r : Priority5) :
    priorityJoin (priorityJoin p q) r = priorityJoin p (priorityJoin q r) := by
  apply Fin.ext
  simp [priorityJoin, max_assoc]

theorem priorityJoin_comm (p q : Priority5) : priorityJoin p q = priorityJoin q p := by
  apply Fin.ext
  simp [priorityJoin, max_comm]

theorem priorityJoin_monotone (r p q : Priority5)
    (h : sourceRank p ≤ sourceRank q) :
    sourceRank (priorityJoin r p) ≤ sourceRank (priorityJoin r q) := by
  rw [sourceRank_exact] at h ⊢
  exact numerical_max_priority_monotone_left h r.val

inductive Atom (Exit : Type*) where
  | bottom
  | top
  | halt (exit : Exit) (priority : Priority5)
  deriving DecidableEq, Fintype

def Atom.outcome {Exit : Type*} : Atom Exit → Outcome Exit
  | .bottom => .bottom
  | .top => .top
  | .halt o p => .halt o p.val

def atomLE {Exit : Type*} (a b : Atom Exit) : Prop :=
  OutcomeLE a.outcome b.outcome

instance {Exit : Type*} [DecidableEq Exit] : DecidableRel (@atomLE Exit) :=
  fun a b => by
    unfold atomLE
    cases a <;> cases b <;> dsimp [Atom.outcome, OutcomeLE, PriorityLE] <;> infer_instance

def atomPrefix {Exit : Type*} (r : Priority5) : Atom Exit → Atom Exit
  | .bottom => .bottom
  | .top => .top
  | .halt o p => .halt o (priorityJoin r p)

theorem atomLE_refl {Exit : Type*} (a : Atom Exit) : atomLE a a := outcomeLE_refl _

theorem atomLE_trans {Exit : Type*} {a b c : Atom Exit}
    (hab : atomLE a b) (hbc : atomLE b c) : atomLE a c := outcomeLE_trans hab hbc

theorem atom_outcome_injective {Exit : Type*} :
    Function.Injective (@Atom.outcome Exit) := by
  intro a b h
  cases a <;> cases b <;> simp_all [Atom.outcome]
  congr
  apply Fin.ext
  exact h.2

theorem atomLE_antisymm {Exit : Type*} {a b : Atom Exit}
    (hab : atomLE a b) (hba : atomLE b a) : a = b :=
  atom_outcome_injective (outcomeLE_antisymm hab hba)

theorem atomPrefix_monotone {Exit : Type*} (r : Priority5)
    {a b : Atom Exit} (h : atomLE a b) : atomLE (atomPrefix r a) (atomPrefix r b) := by
  cases a <;> cases b <;> simp_all [atomLE, Atom.outcome, atomPrefix, OutcomeLE]
  exact numerical_max_priority_monotone_left h.2 r.val

def omegaAtom {Exit : Type*} (p : Priority5) : Atom Exit :=
  if p.val % 2 = 0 then .top else .bottom

/-- An odd lap can add a delayed finite outcome, but that outcome is
source-below immediate exit. This justifies front pruning, not raw equality. -/
theorem odd_lap_delayed_dominated (p q : Priority5) (hodd : p.val % 2 = 1) :
    PriorityLE (priorityJoin p q).val q.val := by
  fin_cases p <;> fin_cases q <;> norm_num [priorityJoin,PriorityLE] at *

theorem odd_lap_atom_dominated {Exit : Type*} (o : Exit) (p q : Priority5)
    (hodd : p.val % 2 = 1) : atomLE (.halt o (priorityJoin p q)) (.halt o q) :=
  ⟨rfl,odd_lap_delayed_dominated p q hodd⟩

inductive Owner where | even | odd deriving DecidableEq

/-- Each occurrence is a separate syntax node; recursively repeated children
are copied. No graph node-sharing operation exists in this datatype. -/
inductive Term (Exit : Type*) where
  | atom (a : Atom Exit)
  | prefix (r : Priority5) (child : Term Exit)
  | even (left right : Term Exit)
  | odd (left right : Term Exit)
  | leaf (owner : Owner) (exit : Exit) (p q : Priority5) (positive : 0 < p.val)
  deriving DecidableEq

def Term.leafCount {Exit : Type*} : Term Exit → Nat
  | .atom _ => 0
  | .prefix _ x => x.leafCount
  | .even x y | .odd x y => x.leafCount + y.leafCount
  | .leaf _ _ _ _ _ => 1

def Term.nodeCount {Exit : Type*} : Term Exit → Nat
  | .atom _ | .leaf _ _ _ _ _ => 1
  | .prefix _ x => x.nodeCount + 1
  | .even x y | .odd x y => x.nodeCount + y.nodeCount + 1

structure OrderedForest where
  exits : Nat
  exits_low : 1 ≤ exits
  exits_high : exits ≤ 2
  entrances : Nat
  entrances_low : 1 ≤ entrances
  entrances_high : entrances ≤ 2
  term : Fin entrances → Term (Fin exits)
  one_leaf : (Finset.univ.sum fun i => (term i).leafCount) ≤ 1

/-- Nonempty finite lists are the actual R19 guards, not game queries. -/
def atomListLE {Exit : Type*} (r s : List (Atom Exit)) : Prop :=
  ∀ b ∈ s, ∃ a ∈ r, atomLE a b

def minimizedAtomList {Exit : Type*} (r : List (Atom Exit)) : Prop :=
  r ≠ [] ∧ r.Nodup ∧ ∀ a ∈ r, ∀ b ∈ r, atomLE a b → a = b

def oddFold {Exit : Type*} (a : Atom Exit) : List (Atom Exit) → Term Exit
  | [] => .atom a
  | b :: bs => .odd (.atom a) (oddFold b bs)

def listTerm {Exit : Type*} : List (Atom Exit) → Term Exit
  | [] => .atom .bottom -- fallback excluded by each R19 guard
  | a :: rest => oddFold a rest

/-- The 19 manuscript equations, with fresh copies and feedback-free guards.
R17/18 are the only schemas mentioning a feedback leaf. -/
inductive Equation {Exit : Type*} : Term Exit → Term Exit → Prop where
  | r01 (x y) (hx : x.leafCount = 0) (hy : y.leafCount = 0) : Equation (.even x y) (.even y x)
  | r02 (x y z) (hx : x.leafCount = 0) (hy : y.leafCount = 0) (hz : z.leafCount = 0) : Equation (.even (.even x y) z) (.even x (.even y z))
  | r03 (x) (hx : x.leafCount = 0) : Equation (.even x x) x
  | r04 (x y) (hx : x.leafCount = 0) (hy : y.leafCount = 0) : Equation (.odd x y) (.odd y x)
  | r05 (x y z) (hx : x.leafCount = 0) (hy : y.leafCount = 0) (hz : z.leafCount = 0) : Equation (.odd (.odd x y) z) (.odd x (.odd y z))
  | r06 (x) (hx : x.leafCount = 0) : Equation (.odd x x) x
  | r07 (x y) (hx : x.leafCount = 0) (hy : y.leafCount = 0) : Equation (.even x (.odd x y)) x
  | r08 (x y) (hx : x.leafCount = 0) (hy : y.leafCount = 0) : Equation (.odd x (.even x y)) x
  | r09 (x y z) (hx : x.leafCount = 0) (hy : y.leafCount = 0) (hz : z.leafCount = 0) : Equation (.odd x (.even y z)) (.even (.odd x y) (.odd x z))
  | r10 (r x y) (hx : x.leafCount = 0) (hy : y.leafCount = 0) : Equation (.prefix r (.even x y)) (.even (.prefix r x) (.prefix r y))
  | r11 (r x y) (hx : x.leafCount = 0) (hy : y.leafCount = 0) : Equation (.prefix r (.odd x y)) (.odd (.prefix r x) (.prefix r y))
  | r12 (r o p) : Equation (.prefix r (.atom (.halt o p))) (.atom (.halt o (priorityJoin r p)))
  | r13 (r) : Equation (.prefix r (.atom .top)) (.atom .top)
  | r14 (r) : Equation (.prefix r (.atom .bottom)) (.atom .bottom)
  | r15 (a b) (h : atomLE a b) : Equation (.odd (.atom a) (.atom b)) (.atom a)
  | r16 (a b) (h : atomLE a b) : Equation (.even (.atom a) (.atom b)) (.atom b)
  | r17 (o p q hp) : Equation (.leaf .even o p q hp) (.even (.atom (.halt o q)) (.atom (omegaAtom p)))
  | r18 (o p q hp) : Equation (.leaf .odd o p q hp) (.odd (.atom (.halt o q)) (.odd (.atom (.halt o (priorityJoin p q))) (.atom (omegaAtom p))))
  | r19 (r s) (hr : minimizedAtomList r) (hs : minimizedAtomList s) (h : atomListLE r s) : Equation (.even (listTerm r) (listTerm s)) (listTerm s)

/-- Typed outer congruence: no surrounding arbitrary feedback operator. -/
inductive Derivation {Exit : Type*} : Term Exit → Term Exit → Prop where
  | refl (x) : Derivation x x
  | step {x y} : Equation x y → Derivation x y
  | symm {x y} : Derivation x y → Derivation y x
  | trans {x y z} : Derivation x y → Derivation y z → Derivation x z
  | prefix (r) {x y} : Derivation x y → Derivation (.prefix r x) (.prefix r y)
  | even_left {x y} (z) (hx : x.leafCount + z.leafCount ≤ 1) (hy : y.leafCount + z.leafCount ≤ 1) : Derivation x y → Derivation (.even x z) (.even y z)
  | even_right (z) {x y} (hx : z.leafCount + x.leafCount ≤ 1) (hy : z.leafCount + y.leafCount ≤ 1) : Derivation x y → Derivation (.even z x) (.even z y)
  | odd_left {x y} (z) (hx : x.leafCount + z.leafCount ≤ 1) (hy : y.leafCount + z.leafCount ≤ 1) : Derivation x y → Derivation (.odd x z) (.odd y z)
  | odd_right (z) {x y} (hx : z.leafCount + x.leafCount ≤ 1) (hy : z.leafCount + y.leafCount ≤ 1) : Derivation x y → Derivation (.odd z x) (.odd z y)

/-- Literal graph realization still must retain all forced and unreachable
original vertices, zero merger edges and stop/continuation distinctions. -/
structure EdgeArena (V EdgeId Exit : Type*) where
  source : EdgeId → V
  target : EdgeId → V
  priority : EdgeId → Priority5
  even : V → Bool
  outgoing : V → Finset EdgeId
  source_exact : ∀ v e, e ∈ outgoing v ↔ source e = v
  total : ∀ v, (outgoing v).Nonempty
  entrance : V
  exit : Exit → V
  exit_injective : Function.Injective exit
  entrance_disjoint : ∀ o, entrance ≠ exit o
  exit_even : ∀ o, even (exit o) = true
  exit_completion : ∀ o e, e ∈ outgoing (exit o) → target e = exit o ∧ priority e = 0

structure EdgeOriginalPolicy {V EdgeId Exit : Type*} (G : EdgeArena V EdgeId Exit) where
  choose : {v : V // G.even v = true} → EdgeId
  legal : ∀ v, choose v ∈ G.outgoing v.val

end Partials.ParityAlgorithms
