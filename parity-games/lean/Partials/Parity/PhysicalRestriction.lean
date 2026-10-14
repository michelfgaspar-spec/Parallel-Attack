import Partials.Parity.MarkedFixture
import Partials.Parity.FiniteOutcomes

/-!
# Physical singleton-menu restriction for P2-FB-COLLISION (uncompiled draft)

The source changes the physical arena by replacing `[2,3]` at `L1.x0` with
`[2,2]`. This removes exactly one original menu and its two forced arms.
The finite `by decide` declarations below are proposed Lean checks for the
47→44 and 48→45 counts and the absence of selected incoming edges under
choice 2. The all-history subtype identity transport is authored below, uncompiled.
-/


namespace Partials.Parity.Fixture

def omittedBySingletonMenu {Z : Type} : FixtureVertex Z → Bool
  | .menu .l1_0_3 => true
  | .rightArm .l1_0_3 => true
  | .leftArm .l1_0_3 => true
  | _ => false

abbrev RestrictedVertex (Z : Type) :=
  {v : FixtureVertex Z // omittedBySingletonMenu v = false}

abbrev RestrictedForwardVertex := RestrictedVertex Empty
abbrev RestrictedFeedbackVertex := RestrictedVertex PUnit

theorem restrictedForwardVertexCount :
    Fintype.card RestrictedForwardVertex = 44 := by decide

theorem restrictedFeedbackVertexCount :
    Fintype.card RestrictedFeedbackVertex = 45 := by decide

def SelectedFixtureEdge {Z : Type}
    (marked : Option Z) (chooseThree : Bool)
    (u v : FixtureVertex Z) : Prop :=
  edge marked u v ∧
    (evenOwned u = true → v = chosenMove marked chooseThree u)

instance selectedFixtureEdgeDecidable {Z : Type} [DecidableEq Z]
    (marked : Option Z) (chooseThree : Bool) (u v : FixtureVertex Z) :
    Decidable (SelectedFixtureEdge marked chooseThree u v) :=
  inferInstanceAs (Decidable (edge marked u v ∧
    (evenOwned u = true → v = chosenMove marked chooseThree u)))

/-- No retained vertex can enter the deleted triple in the choice-2 selected
forward graph. Odd's R10 branch and every menu arm remain unrestricted. -/
theorem noSelectedEntry_forward :
    ∀ u v : ForwardVertex,
      omittedBySingletonMenu u = false →
      omittedBySingletonMenu v = true →
      SelectedFixtureEdge (none : Option Empty) false u v → False := by
  decide

theorem noSelectedEntry_feedback :
    ∀ u v : FeedbackVertex,
      omittedBySingletonMenu u = false →
      omittedBySingletonMenu v = true →
      SelectedFixtureEdge (some PUnit.unit) false u v → False := by
  decide

/-- Generic induction that converts the finite no-entry fact into avoidance
by every infinite selected path, not merely sampled finite walks. -/
theorem selectedPath_avoids_omitted
    {Z : Type} (marked : Option Z) (start : FixtureVertex Z)
    (hStart : omittedBySingletonMenu start = false)
    (hNoEntry : ∀ u v : FixtureVertex Z,
      omittedBySingletonMenu u = false →
      omittedBySingletonMenu v = true →
      SelectedFixtureEdge marked false u v → False)
    (ρ : Nat → FixtureVertex Z)
    (hFirst : ρ 0 = start)
    (hSelected : ∀ n, SelectedFixtureEdge marked false (ρ n) (ρ (n + 1))) :
    ∀ n, omittedBySingletonMenu (ρ n) = false := by
  intro n
  induction n with
  | zero => simpa [hFirst] using hStart
  | succ n ih =>
      cases hValue : omittedBySingletonMenu (ρ (n + 1)) with
      | false => rfl
      | true =>
          exact False.elim
            (hNoEntry (ρ n) (ρ (n + 1)) ih hValue (hSelected n))

/- On retained vertices the physical singleton-menu arena's edge relation
is the restriction of `edge`; the original choice-2 selected edge relation
also restricts there. The remaining formal obligation is a graph isomorphism
between the restricted physical arena and this subtype, then equivalence of
all finite first-exit and infinite no-exit histories and their outcomes. -/


/-- The physical deletion is independent of policy selection. Original Odd
branches and retained original vertices are not pruned. -/
theorem forward_keep_chosen_move : ∀ v : ForwardVertex,
    omittedBySingletonMenu v = false →
      omittedBySingletonMenu (chosenMove none false v) = false := by decide

theorem feedback_keep_chosen_move : ∀ v : FeedbackVertex,
    omittedBySingletonMenu v = false →
      omittedBySingletonMenu (chosenMove (some PUnit.unit) false v) = false := by decide

theorem forward_chosen_move_legal : ∀ v : ForwardVertex,
    forwardEdge v (chosenMove none false v) := by decide

theorem feedback_chosen_move_legal : ∀ v : FeedbackVertex,
    feedbackEdge v (chosenMove (some PUnit.unit) false v) := by decide

def restrictedForwardArena : Arena RestrictedForwardVertex (Fin 2) where
  edge u v := forwardEdge u.val v.val
  even u := evenOwned u.val
  priority u := priority u.val
  exitVertex o := ⟨.sink o, rfl⟩
  exit_injective := by
    intro o p h
    have hv := congrArg Subtype.val h
    exact FixtureVertex.sink.inj hv
  total u := ⟨⟨chosenMove none false u.val,
    forward_keep_chosen_move u.val u.property⟩, forward_chosen_move_legal u.val⟩
  exit_zero o := rfl
  exit_sink o w := by
    constructor
    · intro h
      apply Subtype.ext
      exact (forwardArena.exit_sink o w.val).mp h
    · intro h
      subst w
      exact (forwardArena.exit_sink o _).mpr rfl

def restrictedFeedbackArena : Arena RestrictedFeedbackVertex (Fin 2) where
  edge u v := feedbackEdge u.val v.val
  even u := evenOwned u.val
  priority u := priority u.val
  exitVertex o := ⟨.sink o, rfl⟩
  exit_injective := by
    intro o p h
    have hv := congrArg Subtype.val h
    exact FixtureVertex.sink.inj hv
  total u := ⟨⟨chosenMove (some PUnit.unit) false u.val,
    feedback_keep_chosen_move u.val u.property⟩, feedback_chosen_move_legal u.val⟩
  exit_zero o := rfl
  exit_sink o w := by
    constructor
    · intro h
      apply Subtype.ext
      exact (feedbackArena.exit_sink o w.val).mp h
    · intro h
      subst w
      exact (feedbackArena.exit_sink o _).mpr rfl

def restrictedForwardPolicy : EvenPolicy restrictedForwardArena where
  move u := ⟨chosenMove none false u.val, forward_keep_chosen_move u.val u.property⟩
  legal_even u _ := forward_chosen_move_legal u.val

def restrictedFeedbackPolicy : EvenPolicy restrictedFeedbackArena where
  move u := ⟨chosenMove (some PUnit.unit) false u.val,
    feedback_keep_chosen_move u.val u.property⟩
  legal_even u _ := feedback_chosen_move_legal u.val

def restrictedForwardStart (i : Fin 2) : RestrictedForwardVertex :=
  ⟨forwardStart i, by fin_cases i <;> rfl⟩

def restrictedFeedbackStart (i : Fin 2) : RestrictedFeedbackVertex :=
  ⟨feedbackStart i, by fin_cases i <;> rfl⟩

/-- First-exit maxima and recurring priorities are unchanged under identity
on retained vertices. This is an all-history statement, not finite sampling. -/
theorem retained_firstExit_iff {V Exit : Type} (P : V → Prop)
    (A : Arena V Exit) (B : Arena {v : V // P v} Exit)
    (hpriority : ∀ v, B.priority v = A.priority v.val)
    (hexit : ∀ o, (B.exitVertex o).val = A.exitVertex o)
    (ρ : Nat → {v : V // P v}) (n : Nat) (o : Exit) (p : Nat) :
    FirstExit B ρ n o p ↔ FirstExit A (fun k => (ρ k).val) n o p := by
  have hprior : (fun k => B.priority (ρ k)) =
      (fun k => A.priority (ρ k).val) := funext (fun k => hpriority (ρ k))
  constructor <;> rintro ⟨hstop, hfirst, hpeak⟩
  · refine ⟨(congrArg Subtype.val hstop).trans (hexit o), ?_, ?_⟩
    · intro k hk o' heq
      apply hfirst k hk o'
      apply Subtype.ext
      exact heq.trans (hexit o').symm
    · simpa [hprior] using hpeak
  · refine ⟨?_, ?_, ?_⟩
    · apply Subtype.ext
      exact hstop.trans (hexit o).symm
    · intro k hk o' heq
      apply hfirst k hk o'
      exact (congrArg Subtype.val heq).trans (hexit o')
    · simpa [hprior] using hpeak

theorem retained_outcome_iff {V Exit : Type} (P : V → Prop)
    (A : Arena V Exit) (B : Arena {v : V // P v} Exit)
    (hpriority : ∀ v, B.priority v = A.priority v.val)
    (hexit : ∀ o, (B.exitVertex o).val = A.exitVertex o)
    (ρ : Nat → {v : V // P v}) (out : Outcome Exit) :
    (FiniteOutcome B ρ out ∨ InfiniteOutcome B ρ out) ↔
      (FiniteOutcome A (fun k => (ρ k).val) out ∨
        InfiniteOutcome A (fun k => (ρ k).val) out) := by
  have hf : FiniteOutcome B ρ out ↔
      FiniteOutcome A (fun k => (ρ k).val) out := by
    simp only [FiniteOutcome, retained_firstExit_iff P A B hpriority hexit]
  have hrec : ∀ q, Recurs B ρ q ↔ Recurs A (fun k => (ρ k).val) q := by
    intro q
    simp only [Recurs, hpriority]
  have hlarge : ∀ q, LargestRecurring B ρ q ↔
      LargestRecurring A (fun k => (ρ k).val) q := by
    intro q
    simp only [LargestRecurring, hrec]
  have hno : (∀ n o, ρ n ≠ B.exitVertex o) ↔
      (∀ n o, (ρ n).val ≠ A.exitVertex o) := by
    constructor <;> intro h n o heq
    · apply h n o
      apply Subtype.ext
      exact heq.trans (hexit o).symm
    · apply h n o
      exact (congrArg Subtype.val heq).trans (hexit o)
  have hi : InfiniteOutcome B ρ out ↔
      InfiniteOutcome A (fun k => (ρ k).val) out := by
    simp only [InfiniteOutcome, hno, hlarge]
  exact or_congr hf hi

/-- A closed selected subarena matches all finite first-exit and infinite
histories by identity. The hypotheses are local edge/priority/exit facts and
selected closure, not equality of the desired raw sets. -/
theorem raw_retained_identity {V Exit : Type} (P : V → Prop)
    (A : Arena V Exit) (σ : EvenPolicy A)
    (B : Arena {v : V // P v} Exit) (τ : EvenPolicy B)
    (hselected : ∀ u v, selectedEdge B τ u v ↔ selectedEdge A σ u.val v.val)
    (hpriority : ∀ v, B.priority v = A.priority v.val)
    (hexit : ∀ o, (B.exitVertex o).val = A.exitVertex o)
    (closed : ∀ u v, P u → selectedEdge A σ u v → P v)
    (start : {v : V // P v}) :
    RawOutcomes B τ start = RawOutcomes A σ start.val := by
  have liftCompatible : ∀ ρ : Nat → {v : V // P v},
      Compatible B τ ρ ↔ Compatible A σ (fun k => (ρ k).val) := by
    intro ρ
    constructor <;> intro h n
    · exact (hselected (ρ n) (ρ (n + 1))).mp (h n)
    · exact (hselected (ρ n) (ρ (n + 1))).mpr (h n)
  ext out
  constructor
  · rintro ⟨ρ, hstart, hρ, hout⟩
    exact ⟨fun k => (ρ k).val, congrArg Subtype.val hstart,
      (liftCompatible ρ).mp hρ,
      (retained_outcome_iff P A B hpriority hexit ρ out).mp hout⟩
  · rintro ⟨ρ, hstart, hρ, hout⟩
    have hkeep : ∀ n, P (ρ n) := by
      intro n
      induction n with
      | zero => simpa [hstart] using start.property
      | succ n ih => exact closed (ρ n) (ρ (n + 1)) ih (hρ n)
    let small : Nat → {v : V // P v} := fun n => ⟨ρ n, hkeep n⟩
    refine ⟨small, ?_, ?_, ?_⟩
    · apply Subtype.ext
      exact hstart
    · exact (liftCompatible small).mpr hρ
    · exact (retained_outcome_iff P A B hpriority hexit small out).mpr hout

/-- Both original counts differ by the same deleted triple. The typed starts,
zero sinks, original retained menus, both Odd arms and the marked edge are
kept literally. The selected closure finite proof is then lifted to all paths. -/
theorem restricted_forward_raw (i : Fin 2) :
    RawOutcomes restrictedForwardArena restrictedForwardPolicy (restrictedForwardStart i) =
      RawOutcomes forwardArena (forwardPolicy false) (forwardStart i) := by
  apply raw_retained_identity (fun v : ForwardVertex => omittedBySingletonMenu v = false)
    forwardArena (forwardPolicy false) restrictedForwardArena restrictedForwardPolicy
  · intro u v
    constructor
    · rintro ⟨hedge, hmove⟩
      exact ⟨hedge, fun hv => congrArg Subtype.val (hmove hv)⟩
    · rintro ⟨hedge, hmove⟩
      refine ⟨hedge, ?_⟩
      intro hv
      apply Subtype.ext
      exact hmove hv
  · intro v; rfl
  · intro o; rfl
  · intro u v hu hedge
    cases hv : omittedBySingletonMenu v with
    | false => rfl
    | true => exact False.elim (noSelectedEntry_forward u v hu hv hedge)

theorem restricted_feedback_raw (i : Fin 2) :
    RawOutcomes restrictedFeedbackArena restrictedFeedbackPolicy (restrictedFeedbackStart i) =
      RawOutcomes feedbackArena (feedbackPolicy false) (feedbackStart i) := by
  apply raw_retained_identity (fun v : FeedbackVertex => omittedBySingletonMenu v = false)
    feedbackArena (feedbackPolicy false) restrictedFeedbackArena restrictedFeedbackPolicy
  · intro u v
    constructor
    · rintro ⟨hedge, hmove⟩
      exact ⟨hedge, fun hv => congrArg Subtype.val (hmove hv)⟩
    · rintro ⟨hedge, hmove⟩
      refine ⟨hedge, ?_⟩
      intro hv
      apply Subtype.ext
      exact hmove hv
  · intro v; rfl
  · intro o; rfl
  · intro u v hu hedge
    cases hv : omittedBySingletonMenu v with
    | false => rfl
    | true => exact False.elim (noSelectedEntry_feedback u v hu hv hedge)

theorem restricted_forward_profile :
    PolicyProfile restrictedForwardArena restrictedForwardPolicy restrictedForwardStart =
      PolicyProfile forwardArena (forwardPolicy false) forwardStart := by
  funext i
  exact congrArg MinRow (restricted_forward_raw i)

theorem restricted_feedback_profile :
    PolicyProfile restrictedFeedbackArena restrictedFeedbackPolicy restrictedFeedbackStart =
      PolicyProfile feedbackArena (feedbackPolicy false) feedbackStart := by
  funext i
  exact congrArg MinRow (restricted_feedback_raw i)

/-- The singleton original policy class is represented by a product on every
retained Even vertex. The missing menu cannot remain a legal first-hub value.
This pointwise source proof does not equate only sampled reachable policies. -/
theorem restricted_forward_policy_unique (σ : EvenPolicy restrictedForwardArena) :
    PolicyAgreement restrictedForwardArena σ restrictedForwardPolicy := by
  let fullMove : ForwardVertex → ForwardVertex := fun v =>
    if hv : omittedBySingletonMenu v = false then (σ.move ⟨v, hv⟩).val
    else chosenMove none false v
  have legal : ∀ v, evenOwned v = true → forwardEdge v (fullMove v) := by
    intro v heven
    by_cases hv : omittedBySingletonMenu v = false
    · simpa [fullMove, hv, restrictedForwardArena, restrictedFeedbackArena] using σ.legal_even ⟨v, hv⟩ heven
    · simpa [fullMove, hv] using forward_chosen_move_legal v
  have first : fullMove (.hub .l1 0) = .menu .l1_0_2 := by
    have h := legal (.hub .l1 0) (by rfl)
    change fullMove (.hub .l1 0) = .menu .l1_0_2 ∨
      fullMove (.hub .l1 0) = .menu .l1_0_3 at h
    rcases h with h | h
    · exact h
    · have hk : omittedBySingletonMenu (fullMove (.hub .l1 0)) = false := by
        simpa [fullMove, omittedBySingletonMenu] using (σ.move ⟨.hub .l1 0, rfl⟩).property
      rw [h] at hk
      simp [omittedBySingletonMenu] at hk
  have agree := chosenMove_determined none false fullMove legal first
  intro v hv
  apply Subtype.ext
  simpa [fullMove, v.property, restrictedForwardPolicy] using agree v.val hv

theorem restricted_feedback_policy_unique (σ : EvenPolicy restrictedFeedbackArena) :
    PolicyAgreement restrictedFeedbackArena σ restrictedFeedbackPolicy := by
  let fullMove : FeedbackVertex → FeedbackVertex := fun v =>
    if hv : omittedBySingletonMenu v = false then (σ.move ⟨v, hv⟩).val
    else chosenMove (some PUnit.unit) false v
  have legal : ∀ v, evenOwned v = true → feedbackEdge v (fullMove v) := by
    intro v heven
    by_cases hv : omittedBySingletonMenu v = false
    · simpa [fullMove, hv, restrictedForwardArena, restrictedFeedbackArena] using σ.legal_even ⟨v, hv⟩ heven
    · simpa [fullMove, hv] using feedback_chosen_move_legal v
  have first : fullMove (.hub .l1 0) = .menu .l1_0_2 := by
    have h := legal (.hub .l1 0) (by rfl)
    change fullMove (.hub .l1 0) = .menu .l1_0_2 ∨
      fullMove (.hub .l1 0) = .menu .l1_0_3 at h
    rcases h with h | h
    · exact h
    · have hk : omittedBySingletonMenu (fullMove (.hub .l1 0)) = false := by
        simpa [fullMove, omittedBySingletonMenu] using (σ.move ⟨.hub .l1 0, rfl⟩).property
      rw [h] at hk
      simp [omittedBySingletonMenu] at hk
  have agree := chosenMove_determined (some PUnit.unit) false fullMove legal first
  intro v hv
  apply Subtype.ext
  simpa [fullMove, v.property, restrictedFeedbackPolicy] using agree v.val hv

/- D-FB-PHYSICAL: compile and confirm that the physical `[2,2]` grammar is
isomorphic to these retained subtypes, including every unreachable original
Even coordinate and every Odd alternative. The all-history identity proof
above provides applicability once this literal grammar correspondence and
its unexecuted local finite facts are checked; no desired profile is assumed. -/

end Partials.Parity.Fixture
