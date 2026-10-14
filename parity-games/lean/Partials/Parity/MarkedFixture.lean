import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card
import Partials.Parity.Model

/-!
# Original-vertex fixture for P2-FB-COLLISION (uncompiled draft)

The forward carrier is `FixtureVertex Empty` (47 intended original vertices).
The marked carrier is `FixtureVertex PUnit` (48 intended original vertices).
The source's Python replay constructs only the selected reachable graph and
reports 45 vertices; it is not an enumeration of the full original arena.
The finite count/legality declarations below are proposed unexecuted proofs.
No profile row, lasso completeness or parity outcome is accepted here.
-/


namespace Partials.Parity.Fixture

inductive Gadget | l1 | u1 | l2
  deriving DecidableEq

instance gadgetFintype : Fintype Gadget where
  elems := {.l1, .u1, .l2}
  complete := by intro x; cases x <;> simp

inductive Port | iL | iR | oL | oR
  deriving DecidableEq

instance portFintype : Fintype Port where
  elems := {.iL, .iR, .oL, .oR}
  complete := by intro x; cases x <;> simp

/-- Seven original menu vertices: three at L1, two at U1, two at L2. -/
inductive Menu
  | l1_0_2 | l1_0_3 | l1_1_1
  | u1_0_4 | u1_1_1
  | l2_0_3 | l2_1_1
  deriving DecidableEq

instance menuFintype : Fintype Menu where
  elems := {.l1_0_2, .l1_0_3, .l1_1_1, .u1_0_4, .u1_1_1, .l2_0_3, .l2_1_1}
  complete := by intro x; cases x <;> simp

def Menu.gadget : Menu → Gadget
  | .l1_0_2 | .l1_0_3 | .l1_1_1 => .l1
  | .u1_0_4 | .u1_1_1 => .u1
  | .l2_0_3 | .l2_1_1 => .l2

def Menu.hub : Menu → Fin 2
  | .l1_0_2 | .l1_0_3 | .u1_0_4 | .l2_0_3 => 0
  | .l1_1_1 | .u1_1_1 | .l2_1_1 => 1

def Menu.q : Menu → Nat
  | .l1_0_2 => 2
  | .l1_0_3 => 3
  | .l1_1_1 => 1
  | .u1_0_4 => 4
  | .u1_1_1 => 1
  | .l2_0_3 => 3
  | .l2_1_1 => 1

/-- Six routers, two global sinks, twelve ports, six hubs, seven menus,
fourteen forced arms, and one vertex for each `Z`. Choosing `Z = Empty`
omits the marked feedback vertex; choosing `Z = PUnit` includes it. -/
inductive FixtureVertex (Z : Type)
  | router (layer : Fin 3) (track : Fin 2)
  | sink (s : Fin 2)
  | port (g : Gadget) (p : Port)
  | hub (g : Gadget) (h : Fin 2)
  | menu (m : Menu)
  | rightArm (m : Menu)
  | leftArm (m : Menu)
  | z (tag : Z)
  deriving DecidableEq, Fintype

abbrev ForwardVertex := FixtureVertex Empty
abbrev FeedbackVertex := FixtureVertex PUnit

def priority {Z : Type} : FixtureVertex Z → Nat
  | .rightArm m => 4 * m.q
  | .leftArm m => 4 * m.q + 1
  | _ => 0

def evenOwned {Z : Type} : FixtureVertex Z → Bool
  | .router layer track => !(decide (layer = 0 ∧ track = 0))
  | .menu _ => false
  | _ => true

/-- This is the full original edge relation. Its nonselected L1 menu and both
arms remain present under either complete Even policy. -/
def edge {Z : Type} (marked : Option Z) :
    FixtureVertex Z → FixtureVertex Z → Prop
  | .router layer track, w =>
      if layer = 0 ∧ track = 0 then
        w = .port .l1 .iL ∨ w = .port .u1 .iL
      else if layer = 0 ∧ track = 1 then
        w = .router 1 1
      else if layer = 1 ∧ track = 0 then
        w = .router 2 0
      else if layer = 1 ∧ track = 1 then
        w = .router 2 1
      else if layer = 2 ∧ track = 0 then
        w = .sink 0
      else
        w = .sink 1
  | .sink s, w => w = .sink s
  | .port g p, w =>
      match p with
      | .iL => w = .hub g 0
      | .iR => w = .hub g 1
      | .oL =>
          match g with
          | .l1 => w = .port .l2 .iL
          | .u1 => w = .router 1 0
          | .l2 => w = .router 2 0
      | .oR =>
          match g with
          | .l1 => w = .port .l2 .iL
          | .u1 => w = .router 1 0
          | .l2 =>
              match marked with
              | none => w = .router 2 0
              | some tag => w = .z tag
  | .hub g h, w =>
      match g with
      | .l1 => if h = 0 then w = .menu .l1_0_2 ∨ w = .menu .l1_0_3
          else w = .menu .l1_1_1
      | .u1 => if h = 0 then w = .menu .u1_0_4 else w = .menu .u1_1_1
      | .l2 => if h = 0 then w = .menu .l2_0_3 else w = .menu .l2_1_1
  | .menu m, w => w = .rightArm m ∨ w = .leftArm m
  | .rightArm m, w =>
      if m.hub = 0 then w = .hub m.gadget 1
      else w = .port m.gadget .oR
  | .leftArm m, w =>
      if m.hub = 0 then w = .port m.gadget .oL
      else w = .hub m.gadget 0
  | .z _, w => w = .port .l1 .iL

instance edgeDecidable {Z : Type} [DecidableEq Z] (marked : Option Z)
    (v w : FixtureVertex Z) : Decidable (edge marked v w) := by
  cases v with
  | router l t => unfold edge; infer_instance
  | sink s => unfold edge; infer_instance
  | port g p => cases p <;> cases g <;> cases marked <;> unfold edge <;> infer_instance
  | hub g h => cases g <;> unfold edge <;> infer_instance
  | menu m => unfold edge; infer_instance
  | rightArm m => unfold edge; infer_instance
  | leftArm m => unfold edge; infer_instance
  | z tag => unfold edge; infer_instance

instance forwardEdgeDecidable (v w : ForwardVertex) : Decidable (edge none v w) :=
  edgeDecidable none v w

def forwardEdge : ForwardVertex → ForwardVertex → Prop := edge none
def feedbackEdge : FeedbackVertex → FeedbackVertex → Prop := edge (some PUnit.unit)

instance forwardEdgeWrapperDecidable (v w : ForwardVertex) : Decidable (forwardEdge v w) :=
  inferInstanceAs (Decidable (edge none v w))
instance feedbackEdgeWrapperDecidable (v w : FeedbackVertex) : Decidable (feedbackEdge v w) :=
  inferInstanceAs (Decidable (edge (some PUnit.unit) v w))

def start0 {Z : Type} : FixtureVertex Z := .router 0 0
def start1 {Z : Type} : FixtureVertex Z := .router 0 1

/-- The only varying original Even choice is the L1 first-hub menu. This
selector is a draft input to the eventual complete positional-policy map. -/
def chosenMenu (chooseThree : Bool) (g : Gadget) (h : Fin 2) : Menu :=
  if g = .l1 then
    if h = 0 then
      if chooseThree then .l1_0_3 else .l1_0_2
    else .l1_1_1
  else if g = .u1 then
    if h = 0 then .u1_0_4 else .u1_1_1
  else
    if h = 0 then .l2_0_3 else .l2_1_1

/-- A complete function on *every* original vertex. At Odd vertices its
value is arbitrary but legal; Odd still retains both arms and the R10 fork in
the selected graph. -/
def chosenMove {Z : Type} (marked : Option Z) (chooseThree : Bool) :
    FixtureVertex Z → FixtureVertex Z
  | .router layer track =>
      if layer = 0 ∧ track = 0 then .port .l1 .iL
      else if layer = 0 ∧ track = 1 then .router 1 1
      else if layer = 1 ∧ track = 0 then .router 2 0
      else if layer = 1 ∧ track = 1 then .router 2 1
      else if layer = 2 ∧ track = 0 then .sink 0
      else .sink 1
  | .sink s => .sink s
  | .port g p =>
      match p with
      | .iL => .hub g 0
      | .iR => .hub g 1
      | .oL =>
          match g with
          | .l1 => .port .l2 .iL
          | .u1 => .router 1 0
          | .l2 => .router 2 0
      | .oR =>
          match g with
          | .l1 => .port .l2 .iL
          | .u1 => .router 1 0
          | .l2 =>
              match marked with
              | none => .router 2 0
              | some tag => .z tag
  | .hub g h => .menu (chosenMenu chooseThree g h)
  | .menu m => .rightArm m
  | .rightArm m =>
      if m.hub = 0 then .hub m.gadget 1 else .port m.gadget .oR
  | .leftArm m =>
      if m.hub = 0 then .port m.gadget .oL else .hub m.gadget 0
  | .z _ => .port .l1 .iL

/- These are small finite decision proofs proposed for later Lean compilation.
   They certify the original vertex count, total arena and complete policies
   only if the final Lean project accepts them under its pinned toolchain. -/

theorem forwardVertexCount : Fintype.card ForwardVertex = 47 := by decide
theorem feedbackVertexCount : Fintype.card FeedbackVertex = 48 := by decide

def forwardArena : Partials.Parity.Arena ForwardVertex (Fin 2) where
  edge := forwardEdge
  even := evenOwned
  priority := priority
  exitVertex := FixtureVertex.sink
  exit_injective := by decide
  total := by decide
  exit_zero := by decide
  exit_sink := by decide

def feedbackArena : Partials.Parity.Arena FeedbackVertex (Fin 2) where
  edge := feedbackEdge
  even := evenOwned
  priority := priority
  exitVertex := FixtureVertex.sink
  exit_injective := by decide
  total := by decide
  exit_zero := by decide
  exit_sink := by decide

instance forwardArenaEdgeDecidable (v w : ForwardVertex) : Decidable (forwardArena.edge v w) :=
  inferInstanceAs (Decidable (forwardEdge v w))
instance feedbackArenaEdgeDecidable (v w : FeedbackVertex) : Decidable (feedbackArena.edge v w) :=
  inferInstanceAs (Decidable (feedbackEdge v w))

def forwardPolicy (chooseThree : Bool) : Partials.Parity.EvenPolicy forwardArena where
  move := chosenMove none chooseThree
  legal_even := by
    change ∀ v, evenOwned v = true → forwardEdge v (chosenMove none chooseThree v)
    cases chooseThree <;> decide

def feedbackPolicy (chooseThree : Bool) : Partials.Parity.EvenPolicy feedbackArena where
  move := chosenMove (some PUnit.unit) chooseThree
  legal_even := by
    change ∀ v, evenOwned v = true → feedbackEdge v (chosenMove (some PUnit.unit) chooseThree v)
    cases chooseThree <;> decide

def forwardStart : Fin 2 → ForwardVertex
  | 0 => start0
  | _ => start1

def feedbackStart : Fin 2 → FeedbackVertex
  | 0 => start0
  | _ => start1

/- Exact forward/feedback raw rows remain separate mathematical duties.
The finite `decide` declarations above are uncompiled. -/


/-- Exact full original menu incidence, not policy pruning. -/
theorem forward_hub_incidence (g : Gadget) (h : Fin 2) (w : ForwardVertex) :
    forwardEdge (.hub g h) w ↔
      ∃ m : Menu, m.gadget = g ∧ m.hub = h ∧ w = .menu m := by
  fin_cases g <;> fin_cases h <;> fin_cases w <;> decide

theorem feedback_hub_incidence (g : Gadget) (h : Fin 2) (w : FeedbackVertex) :
    feedbackEdge (.hub g h) w ↔
      ∃ m : Menu, m.gadget = g ∧ m.hub = h ∧ w = .menu m := by
  fin_cases g <;> fin_cases h <;> fin_cases w <;> decide

/-- All original menus, including the unchosen first-hub label, occur in the
finite original priority bound. This is larger than any selected diagnostic
alphabet and is independent of reachability. -/
theorem original_priority_bound_forward :
    ∀ v : ForwardVertex, priority v ≤ 17 := by decide

theorem original_priority_bound_feedback :
    ∀ v : FeedbackVertex, priority v ≤ 17 := by decide

/-- Each policy decreases in every original two-hub gadget, including any
unreachable occurrence; this is the source's additional admission condition. -/
theorem chosenMenu_decreases (q : Bool) :
    ∀ g : Gadget, (chosenMenu q g 1).q < (chosenMenu q g 0).q := by
  cases q <;> decide

/-- The first hub is the only Even choice. This determines every Even move,
while the arbitrary Odd dummy fields are deliberately ignored. -/
theorem chosenMove_determined {Z : Type} (marked : Option Z) (q : Bool)
    (move : FixtureVertex Z → FixtureVertex Z)
    (legal : ∀ v, evenOwned v = true → edge marked v (move v))
    (first : move (.hub .l1 0) = .menu (chosenMenu q .l1 0)) :
    ∀ v, evenOwned v = true → move v = chosenMove marked q v := by
  intro v hv
  have hlegal := legal v hv
  cases v with
  | router l t =>
      fin_cases l <;> fin_cases t <;>
        simp [evenOwned, edge, chosenMove] at hv hlegal ⊢ <;> assumption
  | sink s => simpa [edge, chosenMove] using hlegal
  | port g p =>
      cases g <;> cases p <;> cases marked <;>
        simpa [edge, chosenMove] using hlegal
  | hub g h =>
      cases g <;> fin_cases h
      · simpa [chosenMove] using first
      all_goals simpa [edge, chosenMove, chosenMenu] using hlegal
  | menu m => simp [evenOwned] at hv
  | rightArm m =>
      by_cases hm : m.hub = 0 <;> simpa [edge, chosenMove, hm] using hlegal
  | leftArm m =>
      by_cases hm : m.hub = 0 <;> simpa [edge, chosenMove, hm] using hlegal
  | z z => simpa [edge, chosenMove] using hlegal

/-- Literal legal wrappers can differ at Odd vertices. Exactly two agreement
classes of their complete Even assignments occur. No claim of exactly two
full vertex-to-vertex functions is made. -/
theorem forward_policy_cases (σ : EvenPolicy forwardArena) :
    ∃ q : Bool, PolicyAgreement forwardArena σ (forwardPolicy q) := by
  have h := σ.legal_even (.hub .l1 0) (by rfl)
  change σ.move (.hub .l1 0) = .menu .l1_0_2 ∨
    σ.move (.hub .l1 0) = .menu .l1_0_3 at h
  rcases h with h | h
  · refine ⟨false, ?_⟩
    exact chosenMove_determined none false σ.move σ.legal_even h
  · refine ⟨true, ?_⟩
    exact chosenMove_determined none true σ.move σ.legal_even h

theorem feedback_policy_cases (σ : EvenPolicy feedbackArena) :
    ∃ q : Bool, PolicyAgreement feedbackArena σ (feedbackPolicy q) := by
  have h := σ.legal_even (.hub .l1 0) (by rfl)
  change σ.move (.hub .l1 0) = .menu .l1_0_2 ∨
    σ.move (.hub .l1 0) = .menu .l1_0_3 at h
  rcases h with h | h
  · refine ⟨false, ?_⟩
    exact chosenMove_determined (some PUnit.unit) false σ.move σ.legal_even h
  · refine ⟨true, ?_⟩
    exact chosenMove_determined (some PUnit.unit) true σ.move σ.legal_even h

theorem forward_two_agreement_classes_distinct :
    ¬ PolicyAgreement forwardArena (forwardPolicy false) (forwardPolicy true) := by
  intro h
  have hfirst := h (.hub .l1 0) (by rfl)
  simp [forwardPolicy, chosenMove, chosenMenu] at hfirst

theorem feedback_two_agreement_classes_distinct :
    ¬ PolicyAgreement feedbackArena (feedbackPolicy false) (feedbackPolicy true) := by
  intro h
  have hfirst := h (.hub .l1 0) (by rfl)
  simp [feedbackPolicy, chosenMove, chosenMenu] at hfirst

/-- Exact product policy coordinates contain no dummy Odd assignments. -/
def toOriginal {V Exit : Type} {A : Arena V Exit} (σ : EvenPolicy A) :
    OriginalEvenPolicy A where
  choose v := σ.move v.val
  legal v := σ.legal_even v.val v.property

def forwardOriginalPolicy (q : Bool) : OriginalEvenPolicy forwardArena :=
  toOriginal (forwardPolicy q)

def feedbackOriginalPolicy (q : Bool) : OriginalEvenPolicy feedbackArena :=
  toOriginal (feedbackPolicy q)

/-- A legal product has a wrapper whose dummy values are fixed arbitrarily.
This does not restrict any original Even choice. -/
def originalWrapper {V Exit : Type} (A : Arena V Exit)
    [DecidablePred (fun v => A.even v = true)]
    (σ : OriginalEvenPolicy A) (dummy : V → V) : EvenPolicy A where
  move v := if hv : A.even v = true then σ.choose ⟨v, hv⟩ else dummy v
  legal_even v hv := by simpa [hv] using σ.legal ⟨v, hv⟩

theorem forward_original_policy_cases (σ : OriginalEvenPolicy forwardArena) :
    ∃ q : Bool, ∀ v, σ.choose v = (forwardOriginalPolicy q).choose v := by
  obtain ⟨q, hq⟩ := forward_policy_cases
    (originalWrapper forwardArena σ (chosenMove none false))
  refine ⟨q, ?_⟩
  intro v
  simpa [originalWrapper, forwardOriginalPolicy, toOriginal, v.property]
    using hq v.val v.property

theorem feedback_original_policy_cases (σ : OriginalEvenPolicy feedbackArena) :
    ∃ q : Bool, ∀ v, σ.choose v = (feedbackOriginalPolicy q).choose v := by
  obtain ⟨q, hq⟩ := feedback_policy_cases
    (originalWrapper feedbackArena σ (chosenMove (some PUnit.unit) false))
  refine ⟨q, ?_⟩
  intro v
  simpa [originalWrapper, feedbackOriginalPolicy, toOriginal, v.property]
    using hq v.val v.property

/-- Identity on all 47 original vertices; only the marked fresh vertex is new. -/
def forwardEmbedding : ForwardVertex → FeedbackVertex
  | .router l t => .router l t
  | .sink s => .sink s
  | .port g p => .port g p
  | .hub g h => .hub g h
  | .menu m => .menu m
  | .rightArm m => .rightArm m
  | .leftArm m => .leftArm m
  | .z z => nomatch z

theorem marked_continuation_forward :
    ∀ w : ForwardVertex, forwardEdge (.port .l2 .oR) w ↔ w = .router 2 0 := by
  decide

theorem marked_continuation_feedback :
    ∀ w : FeedbackVertex, feedbackEdge (.port .l2 .oR) w ↔ w = .z PUnit.unit := by
  decide

theorem fresh_continuation :
    ∀ w : FeedbackVertex, feedbackEdge (.z PUnit.unit) w ↔ w = .port .l1 .iL := by
  decide

theorem unmarked_edges_unchanged :
    ∀ u v : ForwardVertex, u ≠ .port .l2 .oR →
      (forwardEdge u v ↔ feedbackEdge (forwardEmbedding u) (forwardEmbedding v)) := by
  decide

theorem embedding_priority : ∀ v : ForwardVertex,
    priority (forwardEmbedding v) = priority v := by decide

theorem embedding_ownership : ∀ v : ForwardVertex,
    evenOwned (forwardEmbedding v) = evenOwned v := by decide

/- Precise finite-source duty: validate all unexecuted count/incidence/totality,
legality, policy-case and alteration proofs under the pinned project. This
file does not assert any of the four outcome table rows. -/

end Partials.Parity.Fixture
