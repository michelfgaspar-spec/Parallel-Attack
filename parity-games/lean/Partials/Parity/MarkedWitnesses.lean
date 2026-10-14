import Mathlib.Tactic.IntervalCases
import Partials.Parity.MarkedFixture
import Partials.Parity.FiniteOutcomes

/-!
# Finite explicit witness paths for P2-FB-COLLISION (uncompiled draft)

These list certificates establish only existence of particular paths if their
`by decide` proofs compile. Exact raw rows additionally require ruling out
odd cycles under `σ₂`, checking all reachable finite outcomes, and proving
the finite path/cycle characterization of infinite histories.
-/


namespace Partials.Parity.Fixture

/-- A finite selected walk. At Odd vertices, the `chosenMove` value is ignored. -/
def SelectedWalk {Z : Type} (marked : Option Z) (chooseThree : Bool)
    (vertices : List (FixtureVertex Z)) : Prop :=
  vertices.IsChain (fun x y =>
    edge marked x y ∧
      (evenOwned x = true → y = chosenMove marked chooseThree x))

instance selectedWalkDecidable {Z : Type} [DecidableEq Z]
    (marked : Option Z) (chooseThree : Bool) (vertices : List (FixtureVertex Z)) :
    Decidable (SelectedWalk marked chooseThree vertices) :=
  inferInstanceAs (Decidable (vertices.IsChain (fun x y =>
    edge marked x y ∧ (evenOwned x = true → y = chosenMove marked chooseThree x))))

def WalkPeak {Z : Type} (vertices : List (FixtureVertex Z)) : Nat :=
  (vertices.map priority).foldl max 0

/-- Odd's periodic return under the choice-3 policy. The last vertex repeats
the first, so the list contains one full positive cycle. -/
def losingFeedbackCycle : List FeedbackVertex :=
  [.hub .l1 0,
   .menu .l1_0_3,
   .leftArm .l1_0_3,
   .port .l1 .oL,
   .port .l2 .iL,
   .hub .l2 0,
   .menu .l2_0_3,
   .rightArm .l2_0_3,
   .hub .l2 1,
   .menu .l2_1_1,
   .rightArm .l2_1_1,
   .port .l2 .oR,
   .z PUnit.unit,
   .port .l1 .iL,
   .hub .l1 0]

theorem losingFeedbackCycle_selected :
    SelectedWalk (some PUnit.unit) true losingFeedbackCycle := by
  decide

theorem losingFeedbackCycle_peak :
    WalkPeak losingFeedbackCycle = 13 := by decide

/-- The U1 left arm gives the priority-17 finite exit under either policy.
The source router R10 is Odd-owned, so its U1 branch remains available. -/
def priority17ExitPath {Z : Type} : List (FixtureVertex Z) :=
  [.router 0 0,
   .port .u1 .iL,
   .hub .u1 0,
   .menu .u1_0_4,
   .leftArm .u1_0_4,
   .port .u1 .oL,
   .router 1 0,
   .router 2 0,
   .sink 0]

theorem priority17ExitPath_forward_two :
    SelectedWalk (none : Option Empty) false
      (priority17ExitPath (Z := Empty)) := by decide

theorem priority17ExitPath_forward_three :
    SelectedWalk (none : Option Empty) true
      (priority17ExitPath (Z := Empty)) := by decide

theorem priority17ExitPath_feedback_two :
    SelectedWalk (some PUnit.unit) false
      (priority17ExitPath (Z := PUnit)) := by decide

theorem priority17ExitPath_feedback_three :
    SelectedWalk (some PUnit.unit) true
      (priority17ExitPath (Z := PUnit)) := by decide

theorem priority17ExitPath_peak :
    WalkPeak (priority17ExitPath (Z := Empty)) = 17 := by decide

/-- The second global start has a forced zero path to s1 in both arenas. -/
def startOneZeroExitPath {Z : Type} : List (FixtureVertex Z) :=
  [.router 0 1, .router 1 1, .router 2 1, .sink 1]

theorem startOneZeroExitPath_forward :
    SelectedWalk (none : Option Empty) false
      (startOneZeroExitPath (Z := Empty)) := by decide

theorem startOneZeroExitPath_feedback :
    SelectedWalk (some PUnit.unit) true
      (startOneZeroExitPath (Z := PUnit)) := by decide

theorem startOneZeroExitPath_peak :
    WalkPeak (startOneZeroExitPath (Z := Empty)) = 0 := by decide


/-- Finite complete prefixes extend automatically by the global zero sink. -/
def priority17Vertices {Z : Type} (n : Nat) : FixtureVertex Z :=
  priority17ExitPath.getD n (.sink 0)

def zeroExitVertices {Z : Type} (n : Nat) : FixtureVertex Z :=
  startOneZeroExitPath.getD n (.sink 1)

def forward17Prefix (q : Bool) :
    FinitePrefix forwardArena (forwardPolicy q) (forwardStart 0) 0 17 where
  length := 8
  vertices := priority17Vertices
  initial := by rfl
  selected n hn := by cases q <;> interval_cases n <;> decide
  last := by rfl
  first n hn o := by interval_cases n <;> fin_cases o <;> decide
  peak := by decide

def feedback17Prefix (q : Bool) :
    FinitePrefix feedbackArena (feedbackPolicy q) (feedbackStart 0) 0 17 where
  length := 8
  vertices := priority17Vertices
  initial := by rfl
  selected n hn := by cases q <;> interval_cases n <;> decide
  last := by rfl
  first n hn o := by interval_cases n <;> fin_cases o <;> decide
  peak := by decide

def forwardZeroPrefix (q : Bool) :
    FinitePrefix forwardArena (forwardPolicy q) (forwardStart 1) 1 0 where
  length := 3
  vertices := zeroExitVertices
  initial := by rfl
  selected n hn := by cases q <;> interval_cases n <;> decide
  last := by rfl
  first n hn o := by interval_cases n <;> fin_cases o <;> decide
  peak := by decide

def feedbackZeroPrefix (q : Bool) :
    FinitePrefix feedbackArena (feedbackPolicy q) (feedbackStart 1) 1 0 where
  length := 3
  vertices := zeroExitVertices
  initial := by rfl
  selected n hn := by cases q <;> interval_cases n <;> decide
  last := by rfl
  first n hn o := by interval_cases n <;> fin_cases o <;> decide
  peak := by decide

theorem priority17_forward_raw (q : Bool) :
    Outcome.halt (0 : Fin 2) 17 ∈
      RawOutcomes forwardArena (forwardPolicy q) (forwardStart 0) :=
  finitePrefix_sound (forward17Prefix q)

theorem priority17_feedback_raw (q : Bool) :
    Outcome.halt (0 : Fin 2) 17 ∈
      RawOutcomes feedbackArena (feedbackPolicy q) (feedbackStart 0) :=
  finitePrefix_sound (feedback17Prefix q)

theorem zero_forward_raw (q : Bool) :
    Outcome.halt (1 : Fin 2) 0 ∈
      RawOutcomes forwardArena (forwardPolicy q) (forwardStart 1) :=
  finitePrefix_sound (forwardZeroPrefix q)

theorem zero_feedback_raw (q : Bool) :
    Outcome.halt (1 : Fin 2) 0 ∈
      RawOutcomes feedbackArena (feedbackPolicy q) (feedbackStart 1) :=
  finitePrefix_sound (feedbackZeroPrefix q)

/-- R10→L1.IL is Odd's legal entrance branch. The policy map's dummy value at
R10 neither forces it nor removes Odd's U1 alternative. -/
def l1Stem {Z : Type} (n : Nat) : FixtureVertex Z :=
  if n = 0 then .router 0 0 else .port .l1 .iL

/-- The duplicate endpoint at list index14 is omitted from this period. -/
def losingCycleSlots (i : Fin 14) : FeedbackVertex :=
  losingFeedbackCycle.getD i.val (.hub .l1 0)

theorem losingFeedback_in_raw :
    Outcome.bottom ∈ RawOutcomes feedbackArena (feedbackPolicy true)
      (feedbackStart 0) := by
  apply lasso_sound feedbackArena (feedbackPolicy true) (feedbackStart 0)
    2 14 (by decide) l1Stem losingCycleSlots 2
  · decide
  · intro n hn
    interval_cases n <;> decide
  · decide
  · intro n hn o
    interval_cases n <;> fin_cases o <;> decide
  · decide
  · decide
  · decide

/-- The internal L1 cycle wins under each of the two complete policies. -/
def winningCycle {Z : Type} (q : Bool) : List (FixtureVertex Z) :=
  [.hub .l1 0, .menu (chosenMenu q .l1 0),
   .rightArm (chosenMenu q .l1 0), .hub .l1 1,
   .menu .l1_1_1, .leftArm .l1_1_1]

def winningCycleSlots {Z : Type} (q : Bool) (i : Fin 6) : FixtureVertex Z :=
  (winningCycle q).getD i.val (.hub .l1 0)

theorem winningForward_in_raw (q : Bool) :
    Outcome.top ∈ RawOutcomes forwardArena (forwardPolicy q)
      (forwardStart 0) := by
  apply lasso_sound forwardArena (forwardPolicy q) (forwardStart 0)
    2 6 (by decide) l1Stem (winningCycleSlots q) 2
  · cases q <;> decide
  · intro n hn
    cases q <;> interval_cases n <;> decide
  · cases q <;> decide
  · intro n hn o
    interval_cases n <;> fin_cases o <;> decide
  · cases q <;> decide
  · cases q <;> decide
  · cases q <;> decide

theorem winningFeedback_in_raw (q : Bool) :
    Outcome.top ∈ RawOutcomes feedbackArena (feedbackPolicy q)
      (feedbackStart 0) := by
  apply lasso_sound feedbackArena (feedbackPolicy q) (feedbackStart 0)
    2 6 (by decide) l1Stem (winningCycleSlots q) 2
  · cases q <;> decide
  · intro n hn
    cases q <;> interval_cases n <;> decide
  · cases q <;> decide
  · intro n hn o
    interval_cases n <;> fin_cases o <;> decide
  · cases q <;> decide
  · cases q <;> decide
  · cases q <;> decide

/- Remaining D-FB-CYCLE-EXHAUSTION: rule out every reachable odd peak cycle
in the two forward original arenas and feedback choice2; prove the forced
second-start raw row and that all finite first-start outcomes stop at s0,
with priority17 subpriority-minimal. These are not inferred from the above
existence witnesses or from the selected45-vertex diagnostic. -/

end Partials.Parity.Fixture
