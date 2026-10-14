import Partials.Arrival.Operational

/-! R3/q0002, uncompiled. Source: arrival/main.tex §3.2,
lem:period, eq:word and eq:cumulative. Symbolic count propagation is proved
separately from its OPEN physical trace-realization bridge. -/
namespace Partials.Arrival

inductive PassiveInternal (k : ℕ) where
  | b : Fin (k - 1) → PassiveInternal k
  | c : Fin (k - 2) → PassiveInternal k
  deriving DecidableEq, Fintype

abbrev PassiveVertex (k : ℕ) := Sum (PassiveInternal k) PassiveDestination
abbrev PassiveRotors (k : ℕ) := PassiveInternal k → Fin 2

/-- Cutting b1→ak introduces feedback as an absorbing destination, distinct
from both named outputs and from external E/F injection. -/
def passiveSuccessor {k : ℕ} (hk : 3 ≤ k) :
    PassiveInternal k → Fin 2 → PassiveVertex k
  | .b i, slot =>
    if hi : i.val = 0 then
      if slot.val = 0 then .inr .feedback else .inr .c0
    else if slot.val = 0 then .inl (.b ⟨i.val - 1, by omega⟩)
    else .inl (.c ⟨i.val - 1, by omega⟩)
  | .c i, slot =>
    if hi : i.val = 0 then
      if slot.val = 0 then .inr .b0 else .inr .c0
    else if slot.val = 0 then .inl (.b ⟨i.val - 1, by omega⟩)
    else .inl (.c ⟨i.val - 1, by omega⟩)

def passiveNetwork {k : ℕ} (hk : 3 ≤ k) :
    Partials.Interface.OrderedRotorNetwork (PassiveVertex k) where
  slotCount := fun _ => 2
  slots_positive := fun _ => by decide
  successor := fun v slot => match v with
    | .inl internal => passiveSuccessor hk internal slot
    | .inr destination => .inr destination
  sink := fun v => match v with | .inl _ => False | .inr _ => True
  sink_fixed := by intro v hv slot; cases v <;> simp_all

structure PassiveRunningState (k : ℕ) where
  position : PassiveVertex k
  rotors : PassiveRotors k

def PassiveStep {k : ℕ} (hk : 3 ≤ k)
    (s t : PassiveRunningState k) : Prop :=
  ∃ v : PassiveInternal k, s.position = .inl v ∧
    t = ⟨passiveSuccessor hk v (s.rotors v),
      Function.update s.rotors v (nextBinarySlot (s.rotors v))⟩

inductive PassiveTrace {k : ℕ} (hk : 3 ≤ k) :
    PassiveRunningState k → PassiveRunningState k → ℕ → Prop where
  | nil (s) : PassiveTrace hk s s 0
  | cons {s t u n} : PassiveStep hk s t → PassiveTrace hk t u n →
      PassiveTrace hk s u (n + 1)

def passiveTop {k : ℕ} (hk : 3 ≤ k) : PassiveInternal k :=
  .b ⟨k - 2, by omega⟩

def CompletePassiveTraversal {k : ℕ} (hk : 3 ≤ k)
    (R R' : PassiveRotors k) (destination : PassiveDestination) : Prop :=
  ∃ cost, PassiveTrace hk ⟨.inl (passiveTop hk), R⟩ ⟨.inr destination, R'⟩ cost

inductive SequentialPassiveRouting {k : ℕ} (hk : 3 ≤ k) :
    PassiveRotors k → ℕ → PassiveRotors k → List PassiveDestination → Prop where
  | nil (R) : SequentialPassiveRouting hk R 0 R []
  | cons {R R₁ R₂ n destination destinations} :
      CompletePassiveTraversal hk R R₁ destination →
      SequentialPassiveRouting hk R₁ n R₂ destinations →
      SequentialPassiveRouting hk R (n + 1) R₂ (destination :: destinations)

structure PassiveCounts where
  feedback : ℕ
  b0 : ℕ
  c0 : ℕ
  deriving DecidableEq

def PassiveCounts.add (C D : PassiveCounts) : PassiveCounts :=
  ⟨C.feedback + D.feedback, C.b0 + D.b0, C.c0 + D.c0⟩

def passiveOutputCounts (destinations : List PassiveDestination) : PassiveCounts :=
  ⟨destinations.count .feedback, destinations.count .b0, destinations.count .c0⟩

def halfEven (n : ℕ) : ℕ := (n + 1) / 2
def halfOdd (n : ℕ) : ℕ := n / 2

theorem halfEven_add_two (n : ℕ) : halfEven (n + 2) = halfEven n + 1 := by
  unfold halfEven; omega

theorem halfOdd_add_two (n : ℕ) : halfOdd (n + 2) = halfOdd n + 1 := by
  unfold halfOdd; omega

/-- depth 0 is the first paired level immediately below b_(k-1).
At depth k-3 it is the bottom pair (b1,c1). -/
def pairedVisits (n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (halfEven n, halfOdd n)
  | depth + 1 =>
    let pair := pairedVisits n depth
    (halfEven pair.1 + halfEven pair.2, halfOdd pair.1 + halfOdd pair.2)

theorem pairedVisits_add_four (n depth : ℕ) :
    pairedVisits (n + 4) depth =
      ((pairedVisits n depth).1 + 2, (pairedVisits n depth).2 + 2) := by
  induction depth with
  | zero => simp [pairedVisits, halfEven, halfOdd]; omega
  | succ depth ih =>
    simp only [pairedVisits, ih, halfEven_add_two, halfOdd_add_two]
    congr 1 <;> omega

/-- Analytic visit counts, independently specified by acyclic level flow.
These are not defined as the output of a physical trace. -/
def allEvenPassiveVisits {k : ℕ} (n : ℕ) : PassiveInternal k → ℕ
  | .b i => if i.val = k - 2 then n
    else (pairedVisits n (k - 3 - i.val)).1
  | .c i => (pairedVisits n (k - 3 - i.val)).2

def allEvenPassiveState {k : ℕ} (n : ℕ) : PassiveRotors k :=
  fun v => ⟨allEvenPassiveVisits n v % 2, Nat.mod_lt _ (by decide)⟩

def allEvenPassiveCounts (k n : ℕ) : PassiveCounts :=
  let pair := pairedVisits n (k - 3)
  ⟨halfEven pair.1, halfEven pair.2, halfOdd pair.1 + halfOdd pair.2⟩

theorem allEvenPassiveState_add_four (k n : ℕ) :
    allEvenPassiveState (k := k) (n + 4) = allEvenPassiveState n := by
  funext v
  apply Fin.ext
  cases v with
  | b i =>
    by_cases top : i.val = k - 2
    · simp [allEvenPassiveState, allEvenPassiveVisits, top, Nat.add_mod]
    · simp [allEvenPassiveState, allEvenPassiveVisits, top,
        pairedVisits_add_four, Nat.add_mod]
  | c i =>
    simp [allEvenPassiveState, allEvenPassiveVisits, pairedVisits_add_four, Nat.add_mod]

theorem allEvenPassiveCounts_add_four (k n : ℕ) :
    allEvenPassiveCounts k (n + 4) = (allEvenPassiveCounts k n).add ⟨1, 1, 2⟩ := by
  simp only [allEvenPassiveCounts, pairedVisits_add_four, halfEven_add_two,
    halfOdd_add_two, PassiveCounts.add]
  congr 1 <;> omega

theorem pairedVisits_zero (depth : ℕ) : pairedVisits 0 depth = (0, 0) := by
  induction depth with
  | zero => simp [pairedVisits, halfEven, halfOdd]
  | succ depth ih => simp [pairedVisits, ih, halfEven, halfOdd]

theorem pairedVisits_one (depth : ℕ) : pairedVisits 1 depth = (1, 0) := by
  induction depth with
  | zero => simp [pairedVisits, halfEven, halfOdd]
  | succ depth ih => simp [pairedVisits, ih, halfEven, halfOdd]

theorem pairedVisits_two (depth : ℕ) :
    pairedVisits 2 depth = if depth % 2 = 0 then (1, 1) else (2, 0) := by
  induction depth with
  | zero => simp [pairedVisits, halfEven, halfOdd]
  | succ depth ih =>
    by_cases even : depth % 2 = 0
    · have oddNext : (depth + 1) % 2 ≠ 0 := by omega
      simp [pairedVisits, ih, even, oddNext, halfEven, halfOdd]
    · have evenNext : (depth + 1) % 2 = 0 := by omega
      simp [pairedVisits, ih, even, evenNext, halfEven, halfOdd]

theorem pairedVisits_three (depth : ℕ) : pairedVisits 3 depth = (2, 1) := by
  induction depth with
  | zero => simp [pairedVisits, halfEven, halfOdd]
  | succ depth ih => simp [pairedVisits, ih, halfEven, halfOdd]

theorem pairedVisits_four (depth : ℕ) : pairedVisits 4 depth = (2, 2) := by
  simpa [pairedVisits_zero] using pairedVisits_add_four 0 depth

theorem allEvenPassiveState_zero (k : ℕ) :
    allEvenPassiveState (k := k) 0 = fun _ => ⟨0, by decide⟩ := by
  funext v
  apply Fin.ext
  cases v <;> simp [allEvenPassiveState, allEvenPassiveVisits, pairedVisits_zero]

theorem allEvenPassiveCounts_zero (k : ℕ) : allEvenPassiveCounts k 0 = ⟨0, 0, 0⟩ := by
  simp [allEvenPassiveCounts, pairedVisits_zero, halfEven, halfOdd]

theorem allEvenPassiveCounts_one (k : ℕ) : allEvenPassiveCounts k 1 = ⟨1, 0, 0⟩ := by
  simp [allEvenPassiveCounts, pairedVisits_one, halfEven, halfOdd]

theorem allEvenPassiveCounts_two {k : ℕ} (hk : 3 ≤ k) :
    allEvenPassiveCounts k 2 =
      if k % 2 = 1 then ⟨1, 1, 0⟩ else ⟨1, 0, 1⟩ := by
  have parity : (k - 3) % 2 = 0 ↔ k % 2 = 1 := by omega
  by_cases odd : k % 2 = 1
  · have depthEven := parity.mpr odd
    simp [allEvenPassiveCounts, pairedVisits_two, odd, depthEven, halfEven, halfOdd]
  · have depthOdd : (k - 3) % 2 ≠ 0 := by omega
    simp [allEvenPassiveCounts, pairedVisits_two, odd, depthOdd, halfEven, halfOdd]

theorem allEvenPassiveCounts_three (k : ℕ) :
    allEvenPassiveCounts k 3 = ⟨1, 1, 1⟩ := by
  simp [allEvenPassiveCounts, pairedVisits_three, halfEven, halfOdd]

theorem allEvenPassiveCounts_four (k : ℕ) :
    allEvenPassiveCounts k 4 = ⟨1, 1, 2⟩ := by
  simp [allEvenPassiveCounts, pairedVisits_four, halfEven, halfOdd]

def singletonPassiveCount : PassiveDestination → PassiveCounts
  | .feedback => ⟨1, 0, 0⟩
  | .b0 => ⟨0, 1, 0⟩
  | .c0 => ⟨0, 0, 1⟩

/-- Parity-dependent word follows from the symbolic cumulative counts; this
theorem does not by itself establish a physical traversal. -/
theorem analyticPassiveWord {k : ℕ} (hk : 3 ≤ k) (r : Fin 4) :
    allEvenPassiveCounts k (r.val + 1) =
      (allEvenPassiveCounts k r.val).add (singletonPassiveCount (passiveWord k r)) := by
  fin_cases r <;> by_cases odd : k % 2 = 1 <;>
    simp [passiveWord, odd, allEvenPassiveCounts_zero, allEvenPassiveCounts_one,
      allEvenPassiveCounts_two hk, allEvenPassiveCounts_three,
      allEvenPassiveCounts_four, PassiveCounts.add, singletonPassiveCount]

/-- The orbit is exactly the four complete-traversal states from all-even.
No arbitrary passive vector has been assigned a residue. -/
def passiveOrbitState (k : ℕ) (r : Fin 4) : PassiveRotors k :=
  allEvenPassiveState r.val

theorem allEvenPassiveState_mod_four (k n : ℕ) :
    allEvenPassiveState (k := k) n =
      passiveOrbitState k ⟨n % 4, Nat.mod_lt _ (by decide)⟩ := by
  change allEvenPassiveState n = allEvenPassiveState (n % 4)
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases small : n < 4
    · simp [Nat.mod_eq_of_lt small]
    · have decrease : n - 4 < n := by omega
      have split : n = (n - 4) + 4 := by omega
      calc
        allEvenPassiveState n = allEvenPassiveState (n - 4) := by
          conv_lhs => rw [split, allEvenPassiveState_add_four]
        _ = allEvenPassiveState ((n - 4) % 4) := ih (n - 4) decrease
        _ = allEvenPassiveState (n % 4) := by congr 1; omega

def passiveTopSignature {k : ℕ} (hk : 3 ≤ k) (R : PassiveRotors k) :
    Fin 2 × Fin 2 × Fin 2 :=
  (R (passiveTop hk), R (.b ⟨k - 3, by omega⟩), R (.c ⟨k - 3, by omega⟩))

def fourPhaseSignature (r : Fin 4) : Fin 2 × Fin 2 × Fin 2 :=
  match r.val with
  | 0 => (⟨0, by decide⟩, ⟨0, by decide⟩, ⟨0, by decide⟩)
  | 1 => (⟨1, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩)
  | 2 => (⟨0, by decide⟩, ⟨1, by decide⟩, ⟨1, by decide⟩)
  | _ => (⟨1, by decide⟩, ⟨0, by decide⟩, ⟨1, by decide⟩)

theorem passiveOrbitState_signature {k : ℕ} (hk : 3 ≤ k) (r : Fin 4) :
    passiveTopSignature hk (passiveOrbitState k r) = fourPhaseSignature r := by
  have separate : k - 3 ≠ k - 2 := by omega
  have atTop : k - 3 - (k - 2) = 0 := by omega
  fin_cases r <;>
    simp [passiveTopSignature, passiveTop, passiveOrbitState,
      allEvenPassiveState, allEvenPassiveVisits, separate, atTop,
      fourPhaseSignature, pairedVisits, halfEven, halfOdd]

theorem passiveOrbitState_injective {k : ℕ} (hk : 3 ≤ k) :
    Function.Injective (passiveOrbitState k) := by
  intro r s equal
  have signatures := congrArg (passiveTopSignature hk) equal
  rw [passiveOrbitState_signature hk, passiveOrbitState_signature hk] at signatures
  fin_cases r <;> fin_cases s <;> simp_all [fourPhaseSignature]

/-- OPEN PASSIVE-ORBIT-REALIZATION. This is the exact missing physical bridge,
not an assumed decoder/compression theorem. It includes existence, the next
destination, and equality of the COMPLETE passive vector at both endpoints.
Its trace semantics permits arbitrary intermediate passive vertices; its
domain restricts endpoints to the stated four-phase orbit. -/
def PassiveOrbitRealizationObligation (k : ℕ) (hk : 3 ≤ k) : Prop :=
  ∀ (r : Fin 4) (R' : PassiveRotors k) (destination : PassiveDestination),
    CompletePassiveTraversal hk (passiveOrbitState k r) R' destination ↔
      R' = passiveOrbitState k (nextFourSlot r) ∧ destination = passiveWord k r

theorem passiveTraversal_of_orbitRealization {k : ℕ} (hk : 3 ≤ k)
    (realization : PassiveOrbitRealizationObligation k hk) (r : Fin 4) :
    CompletePassiveTraversal hk (passiveOrbitState k r)
      (passiveOrbitState k (nextFourSlot r)) (passiveWord k r) := by
  exact (realization r _ _).mpr ⟨rfl, rfl⟩

def passivePhaseAfter (r : Fin 4) (n : ℕ) : Fin 4 :=
  ⟨(r.val + n) % 4, Nat.mod_lt _ (by decide)⟩

theorem passivePhaseAfter_zero (r : Fin 4) : passivePhaseAfter r 0 = r := by
  apply Fin.ext
  simp [passivePhaseAfter, Nat.mod_eq_of_lt r.isLt]

theorem passivePhaseAfter_next (r : Fin 4) (n : ℕ) :
    passivePhaseAfter (nextFourSlot r) n = passivePhaseAfter r (n + 1) := by
  apply Fin.ext
  simp only [passivePhaseAfter, nextFourSlot]
  omega

def passiveOrbitOutputPrefix (k : ℕ) (r : Fin 4) : ℕ → List PassiveDestination
  | 0 => []
  | n + 1 => passiveWord k r :: passiveOrbitOutputPrefix k (nextFourSlot r) n

/-- Conditional physical period/orbit claim for EVERY finite number of
complete top traversals, not for intermediate token positions. -/
theorem passiveSequential_exact_of_realization {k : ℕ} (hk : 3 ≤ k)
    (realization : PassiveOrbitRealizationObligation k hk)
    {r : Fin 4} {n : ℕ} {R' : PassiveRotors k} {destinations : List PassiveDestination}
    (routing : SequentialPassiveRouting hk (passiveOrbitState k r) n R' destinations) :
    R' = passiveOrbitState k (passivePhaseAfter r n) ∧
      destinations = passiveOrbitOutputPrefix k r n := by
  induction n generalizing r R' destinations with
  | zero =>
    cases routing
    simp [passivePhaseAfter_zero, passiveOrbitOutputPrefix]
  | succ n ih =>
    cases routing with
    | cons traversal rest =>
      obtain ⟨vector, output⟩ := (realization r _ _).mp traversal
      subst_vars
      obtain ⟨last, word⟩ := ih rest
      exact ⟨by simpa only [passivePhaseAfter_next] using last,
        by simp only [passiveOrbitOutputPrefix, word]⟩

theorem passiveFourWord_counts (k : ℕ) (r : Fin 4) :
    passiveOutputCounts [passiveWord k r, passiveWord k (nextFourSlot r),
      passiveWord k (nextFourSlot (nextFourSlot r)),
      passiveWord k (nextFourSlot (nextFourSlot (nextFourSlot r)))] = ⟨1, 1, 2⟩ := by
  fin_cases r <;> by_cases odd : k % 2 = 1 <;>
    simp [passiveOutputCounts, passiveWord, nextFourSlot, odd]

theorem passiveFourTraversals_reset_of_realization {k : ℕ} (hk : 3 ≤ k)
    (realization : PassiveOrbitRealizationObligation k hk) (r : Fin 4) :
    SequentialPassiveRouting hk (passiveOrbitState k r) 4 (passiveOrbitState k r)
      [passiveWord k r, passiveWord k (nextFourSlot r),
        passiveWord k (nextFourSlot (nextFourSlot r)),
        passiveWord k (nextFourSlot (nextFourSlot (nextFourSlot r)))] := by
  have reset : nextFourSlot (nextFourSlot (nextFourSlot (nextFourSlot r))) = r := by
    fin_cases r <;> decide
  have routing : SequentialPassiveRouting hk (passiveOrbitState k r) 4
      (passiveOrbitState k (nextFourSlot (nextFourSlot (nextFourSlot (nextFourSlot r)))))
      [passiveWord k r, passiveWord k (nextFourSlot r),
        passiveWord k (nextFourSlot (nextFourSlot r)),
        passiveWord k (nextFourSlot (nextFourSlot (nextFourSlot r)))] :=
    .cons (passiveTraversal_of_orbitRealization hk realization r)
    (.cons (passiveTraversal_of_orbitRealization hk realization (nextFourSlot r))
      (.cons (passiveTraversal_of_orbitRealization hk realization (nextFourSlot (nextFourSlot r)))
        (.cons (passiveTraversal_of_orbitRealization hk realization
          (nextFourSlot (nextFourSlot (nextFourSlot r)))) (.nil _))))
  simpa only [reset] using routing

end Partials.Arrival
