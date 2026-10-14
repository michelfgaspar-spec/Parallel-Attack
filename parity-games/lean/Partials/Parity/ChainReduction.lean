import Mathlib.Data.Fintype.Card
import Partials.Parity.ChainEndpoints

/-! Four-port reduction, compilation.tex P1-L01, P1-L04 and P1-L08.
The finite excursion completeness/attainment and surrounding-arena adapters
remain explicit. The recurrent-hub argument below reasons about ALL infinite
walks, with no eventual-periodicity or positional-Odd assumption. -/

namespace Partials.Parity.CompilerSource

inductive ChainEntrance where | left | right
  deriving DecidableEq
inductive ChainExit where | left | right
  deriving DecidableEq

def excursionWeight (s t : Int) : ChainEntrance → ChainExit → Int
  | .left, .left => 4 * s + 1
  | .left, .right => 4 * s
  | .right, .left => 4 * s + 1
  | .right, .right => 4 * t

structure ChainArm (C : IntervalChain) where
  hub : Nat
  bounded : hub ≤ C.last
  left : Bool

def armWeight (q : Nat → Int) {C : IntervalChain} (a : ChainArm C) : Int :=
  4 * q a.hub + if a.left then 1 else 0

theorem higher_hub_arm_smaller (C : IntervalChain) (q : Nat → Int)
    (hq : LegalChain C q) {i j : Nat} (hij : i < j) (hj : j ≤ C.last) :
    4 * q j + 1 < 4 * q i := by
  have hdrop := legal_drop C q hq (j - i) i (by omega)
  have hindex : i + (j - i) = j := by omega
  rw [hindex] at hdrop
  have hpositive : (1 : Int) ≤ ((j - i : Nat) : Int) := by omega
  linarith

structure ConfinedHubPath (C : IntervalChain) where
  hub : Nat → Nat
  bounded : ∀ n, hub n ≤ C.last
  left : Nat → Bool
  step : ∀ n,
    if left n then hub n = hub (n + 1) + 1
    else hub (n + 1) = hub n + 1

def IndexRecurs (hub : Nat → Nat) (a : Nat) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ hub n = a

def WeightRecurs (weight : Nat → Int) (p : Int) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ weight n = p

def LargestRecurringWeight (weight : Nat → Int) (p : Int) : Prop :=
  WeightRecurs weight p ∧ ∀ q, WeightRecurs weight q → q ≤ p

def confinedWeight (q : Nat → Int) {C : IntervalChain}
    (P : ConfinedHubPath C) (n : Nat) : Int :=
  4 * q (P.hub n) + if P.left n then 1 else 0

theorem recurring_weight_le_eventual_bound (weight : Nat → Int)
    (p bound : Int) (hp : WeightRecurs weight p)
    (hbound : ∃ N, ∀ n, N ≤ n → weight n ≤ bound) : p ≤ bound := by
  obtain ⟨N, hN⟩ := hbound
  obtain ⟨n, hn, heq⟩ := hp N
  rw [← heq]
  exact hN n hn

/-- Once lower hubs are absent, a visit to a cannot take its left arm.
In particular this covers a=0 without taking a predecessor of zero. -/
theorem recurrent_hub_right (C : IntervalChain) (P : ConfinedHubPath C)
    (a N n : Nat) (hsmall : ∀ k, N ≤ k → a ≤ P.hub k)
    (hn : N ≤ n) (ha : P.hub n = a) : P.left n = false := by
  cases hleft : P.left n with
  | false => rfl
  | true =>
      have hstep := P.step n
      simp [hleft] at hstep
      have hnext := hsmall (n + 1) (by omega)
      omega

theorem confined_recurrent_maximum_even (C : IntervalChain) (q : Nat → Int)
    (hq : LegalChain C q) (P : ConfinedHubPath C) (a : Nat)
    (ha : IndexRecurs P.hub a)
    (hsmall : ∃ N, ∀ n, N ≤ n → a ≤ P.hub n) :
    LargestRecurringWeight (confinedWeight q P) (4 * q a) ∧
      (4 * q a) % 2 = 0 := by
  obtain ⟨N, hN⟩ := hsmall
  have hrec : WeightRecurs (confinedWeight q P) (4 * q a) := by
    intro M
    obtain ⟨n, hn, hhub⟩ := ha (max N M)
    have hleft := recurrent_hub_right C P a N n hN
      (le_trans (le_max_left _ _) hn) hhub
    refine ⟨n, le_trans (le_max_right _ _) hn, ?_⟩
    simp [confinedWeight, hhub, hleft]
  have hbound : ∀ n, N ≤ n → confinedWeight q P n ≤ 4 * q a := by
    intro n hn
    have hge := hN n hn
    rcases lt_or_eq_of_le hge with hlt | heq
    · have hsep := higher_hub_arm_smaller C q hq hlt (P.bounded n)
      unfold confinedWeight
      cases P.left n <;> simp <;> linarith
    · have hhub : P.hub n = a := heq.symm
      have hleft := recurrent_hub_right C P a N n hN hn hhub
      simp [confinedWeight, hhub, hleft]
  refine ⟨⟨hrec, ?_⟩, ?_⟩
  · intro p hp
    exact recurring_weight_le_eventual_bound _ _ _ hp ⟨N, hbound⟩
  · omega

/-- The remaining finite pigeonhole duty is deliberately below the parity
conclusion: find a least recurrent hub and an eventual lower bound. -/
def LeastRecurringHubDuty : Prop :=
  ∀ (C : IntervalChain) (P : ConfinedHubPath C),
    ∃ a, IndexRecurs P.hub a ∧
      ∃ N, ∀ n, N ≤ n → a ≤ P.hub n

/-- A finite excursion is a list of original arm traversals; the geometry
decoder must identify starts, adjacent moves and the first outward exit. -/
structure FiniteExcursion (C : IntervalChain) where
  entrance : ChainEntrance
  exit : ChainExit
  arms : List (ChainArm C)
  nonempty : arms ≠ []

def excursionMaximum (q : Nat → Int) {C : IntervalChain}
    (E : FiniteExcursion C) : Int :=
  E.arms.foldr (fun a current => max (armWeight q a) current) 0

/-- Neither `legal` nor `sourceLE` is filled by a presumed matrix theorem.
The concrete legal excursion decoder and Int-to-Nat priority bridge are
separate duties; all minima require an attaining original finite word. -/
def FourPortFiniteDuty (C : IntervalChain) (q : Nat → Int)
    (legal : FiniteExcursion C → Prop) (sourceLE : Int → Int → Prop) : Prop :=
  ∀ entrance exit,
    (∀ E : FiniteExcursion C, legal E → E.entrance = entrance → E.exit = exit →
      sourceLE (excursionWeight (q 0) (q C.last) entrance exit)
        (excursionMaximum q E)) ∧
    ∃ E : FiniteExcursion C, legal E ∧ E.entrance = entrance ∧ E.exit = exit ∧
      excursionMaximum q E = excursionWeight (q 0) (q C.last) entrance exit

/-- Complete surrounding-arena reduction target. Raw finite spectra are
not equated; only same-exit minima and bottom availability are compared.
This is an OPEN target, not a theorem available to the compiler. -/
def FourPortReplacementTarget {V W Exit Start : Type*}
    (original : Arena V Exit) («macro» : Arena W Exit)
    (σ : EvenPolicy original) (τ : EvenPolicy «macro»)
    (originalStart : Start → V) (macroStart : Start → W) : Prop :=
  (∀ i, Outcome.bottom ∈ RawOutcomes original σ (originalStart i) ↔
    Outcome.bottom ∈ RawOutcomes «macro» τ (macroStart i)) ∧
  PolicyProfile original σ originalStart = PolicyProfile «macro» τ macroStart

/-- Boundary-preserving vertex↔edge encoding must prove first-exit maximum,
recurring alphabets and both all-history expansion/contraction directions.
Only source starts/exits of priority zero are admissible here. -/
def BoundaryEncodingDuty {V W Exit Start : Type*}
    (A : Arena V Exit) (A' : Arena W Exit)
    (σ : EvenPolicy A) (σ' : EvenPolicy A')
    (starts : Start → V) (starts' : Start → W) : Prop :=
  (∀ i, A.priority (starts i) = 0 ∧ A'.priority (starts' i) = 0) ∧
  ∀ i out, out ∈ RawOutcomes A σ (starts i) ↔
    out ∈ RawOutcomes A' σ' (starts' i)

/-- P1-L08 combinatorial target is independent of cap size. A proof must
retain an edge attaining the original maximum when shortening a walk,
rather than merely erase cycles. -/
def LocalWalkAndCycleDuty {V Target Edge : Type*} [Fintype V]
    (walkMaximum : List Edge → Int) (walkLegal : V → Target → List Edge → Prop)
    (losingInfinite : V → Prop) (oddSimpleCycle : V → Prop) : Prop :=
  (∀ start target word, walkLegal start target word →
    ∃ short, walkLegal start target short ∧
      short.length ≤ 2 * Fintype.card V + 1 ∧
      walkMaximum short = walkMaximum word) ∧
  ∀ start, losingInfinite start ↔ oddSimpleCycle start

end Partials.Parity.CompilerSource
