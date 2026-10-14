import Partials.Parity.MarkedFixture
import Partials.Parity.FiniteOutcomes
import Partials.Parity.MarkedWitnesses
import Partials.Parity.PhysicalRestriction

/-!
# Exact marked-feedback certificate targets (uncompiled draft)

`collisionCertificateTarget` is the eight-row finite graph calculation that
must be discharged by a Lean-native bounded checker or direct proofs. It is
not asserted here. `collisionTable_of_certificate` only connects such a
certificate to the manuscript statement after four raw-outcome/lasso bridges.
-/


namespace Partials.Parity.Fixture

def forwardTwo : Profile (Fin 2) (Fin 2) :=
  PolicyProfile forwardArena (forwardPolicy false) forwardStart

def forwardThree : Profile (Fin 2) (Fin 2) :=
  PolicyProfile forwardArena (forwardPolicy true) forwardStart

def feedbackTwo : Profile (Fin 2) (Fin 2) :=
  PolicyProfile feedbackArena (feedbackPolicy false) feedbackStart

def feedbackThree : Profile (Fin 2) (Fin 2) :=
  PolicyProfile feedbackArena (feedbackPolicy true) feedbackStart

def certifiedForwardTwo : Profile (Fin 2) (Fin 2) :=
  CertifiedProfile forwardArena (forwardPolicy false) forwardStart

def certifiedForwardThree : Profile (Fin 2) (Fin 2) :=
  CertifiedProfile forwardArena (forwardPolicy true) forwardStart

def certifiedFeedbackTwo : Profile (Fin 2) (Fin 2) :=
  CertifiedProfile feedbackArena (feedbackPolicy false) feedbackStart

def certifiedFeedbackThree : Profile (Fin 2) (Fin 2) :=
  CertifiedProfile feedbackArena (feedbackPolicy true) feedbackStart

/-- The exact four-profile table of `feedback.tex:518`, computed using the
finite path/cycle predicates. Because each profile has two starts, this target
contains eight row equalities. It does not assume the Python replay. -/
def collisionCertificateTarget : Prop :=
  MarkedFeedbackTable certifiedForwardTwo certifiedForwardThree
    certifiedFeedbackTwo certifiedFeedbackThree

def collisionTableTarget : Prop :=
  MarkedFeedbackTable forwardTwo forwardThree feedbackTwo feedbackThree

/-- A completed finite certificate plus the finite graph/lasso bridge at
every one of the eight policy-start combinations gives the actual paper table.
Neither premise is currently proved. -/
theorem collisionTable_of_certificate
    (hCertificate : collisionCertificateTarget)
    (hForwardTwo : ∀ i, CertificateRawExactTarget
      forwardArena (forwardPolicy false) (forwardStart i))
    (hForwardThree : ∀ i, CertificateRawExactTarget
      forwardArena (forwardPolicy true) (forwardStart i))
    (hFeedbackTwo : ∀ i, CertificateRawExactTarget
      feedbackArena (feedbackPolicy false) (feedbackStart i))
    (hFeedbackThree : ∀ i, CertificateRawExactTarget
      feedbackArena (feedbackPolicy true) (feedbackStart i)) :
    collisionTableTarget := by
  have hF₂ : certifiedForwardTwo = forwardTwo :=
    certifiedProfile_eq_policyProfile
      forwardArena (forwardPolicy false) forwardStart hForwardTwo
  have hF₃ : certifiedForwardThree = forwardThree :=
    certifiedProfile_eq_policyProfile
      forwardArena (forwardPolicy true) forwardStart hForwardThree
  have hB₂ : certifiedFeedbackTwo = feedbackTwo :=
    certifiedProfile_eq_policyProfile
      feedbackArena (feedbackPolicy false) feedbackStart hFeedbackTwo
  have hB₃ : certifiedFeedbackThree = feedbackThree :=
    certifiedProfile_eq_policyProfile
      feedbackArena (feedbackPolicy true) feedbackStart hFeedbackThree
  change MarkedFeedbackTable certifiedForwardTwo certifiedForwardThree
    certifiedFeedbackTwo certifiedFeedbackThree at hCertificate
  rw [hF₂, hF₃, hB₂, hB₃] at hCertificate
  exact hCertificate

/-- The concrete policy-level conclusion remains conditional on the table.
This is a pure logical consequence and does not check the finite graph. -/
theorem noProfileOnlyTransfer_of_table (h : collisionTableTarget) :
    ¬ ∃ transfer : Profile (Fin 2) (Fin 2) → Profile (Fin 2) (Fin 2),
      ∀ q : Bool,
        transfer (if q then forwardThree else forwardTwo) =
          (if q then feedbackThree else feedbackTwo) := by
  rcases h with ⟨hF20, _hF21, hF3, hB2, hB30, _hB31⟩
  apply noPolicyProfileTransfer
    (fun q : Bool => if q then forwardThree else forwardTwo)
    (fun q : Bool => if q then feedbackThree else feedbackTwo)
    false true
  · simpa using hF3.symm
  · intro hEq
    have hEq0 := congrArg (fun p : Profile (Fin 2) (Fin 2) => p 0) hEq
    simp [hB2, hF20, hB30] at hEq0

/-- Historical abstract class-level target retained as a target. The actual
physical `[2,3] → [2,2]` arenas and their all-history comparison are assembled
below; this abstract definition alone would not justify physical restriction. -/
def relationCollisionTarget : Prop :=
  let f : Bool → Profile (Fin 2) (Fin 2) :=
    fun q => if q then forwardThree else forwardTwo
  let b : Bool → Profile (Fin 2) (Fin 2) :=
    fun q => if q then feedbackThree else feedbackTwo
  ProfileRelation f Set.univ = ProfileRelation f ({false} : Set Bool) ∧
    ProfileRelation b Set.univ ≠ ProfileRelation b ({false} : Set Bool)


/-- Bottom's presence suffices for the exact minimum singleton independently
of finite outcome enumeration. Its application below uses an explicit lasso. -/
theorem minRow_bottom {Exit : Type} (raw : Set (Outcome Exit))
    (hbottom : Outcome.bottom ∈ raw) : MinRow raw = {Outcome.bottom} := by
  ext x
  constructor
  · intro hx
    have hxb := hx.2 Outcome.bottom hbottom (by trivial)
    cases x <;> simp [OutcomeLE] at hxb ⊢
  · intro hx
    have hx' : x = Outcome.bottom := Set.mem_singleton_iff.mp hx
    subst x
    refine ⟨hbottom, ?_⟩
    intro y hy h
    cases y <;> trivial

/-- One actual semantic table component is derived from the explicit original
feedback lasso; this does not prove absence of losing histories in the other
three evaluations. -/
theorem feedback_three_first_row :
    feedbackThree 0 = ({Outcome.bottom} : Set (Outcome (Fin 2))) :=
  minRow_bottom _ losingFeedback_in_raw

/-- Priority17 is the subpriority-least member of the complete original
priority interval, not its numerical least priority. -/
theorem seventeen_le_original_priority (p : Nat) (hp : p ≤ 17) :
    PriorityLE 17 p := by
  rcases Nat.mod_two_eq_zero_or_one p with h | h
  · exact Or.inr (Or.inl ⟨rfl, h⟩)
  · exact Or.inl ⟨rfl, h, hp⟩

/-- Exact first-exit numerical bound from original arena data; unselected
menus are included in the priority premise. -/
theorem firstExit_peak_bound {V Exit : Type}
    (A : Arena V Exit) (ρ : Nat → V) (n : Nat) (o : Exit) (p d : Nat)
    (bound : ∀ v, A.priority v ≤ d) (h : FirstExit A ρ n o p) : p ≤ d := by
  rw [h.2.2]
  apply Finset.sup_le
  intro k hk
  exact bound (ρ k)

/-- The remaining finite table checks are explicit targets, not fields of a
fixture structure and not silently imported as established propositions. -/
def NoLosingFixtureDuty : Prop :=
  (∀ q : Bool, ¬ HasOddCycle forwardArena (forwardPolicy q) (forwardStart 0)) ∧
  ¬ HasOddCycle feedbackArena (feedbackPolicy false) (feedbackStart 0)

def FirstStartExitOnlyDuty : Prop :=
  (∀ q o p, FiniteExitPriority forwardArena (forwardPolicy q) (forwardStart 0) o p →
    o = 0 ∧ p ≤ 17) ∧
  (∀ q o p, FiniteExitPriority feedbackArena (feedbackPolicy q) (feedbackStart 0) o p →
    o = 0 ∧ p ≤ 17)

def SecondStartRawDuty : Prop :=
  (∀ q, CertificateRaw forwardArena (forwardPolicy q) (forwardStart 1) =
    ({Outcome.halt (1 : Fin 2) 0} : Set (Outcome (Fin 2)))) ∧
  (∀ q, CertificateRaw feedbackArena (feedbackPolicy q) (feedbackStart 1) =
    ({Outcome.halt (1 : Fin 2) 0} : Set (Outcome (Fin 2))))

theorem feedback_rows_distinct_of_table (h : collisionTableTarget) :
    feedbackTwo ≠ feedbackThree := by
  rcases h with ⟨hF20, _hF21, _hF3, hB2, hB30, _hB31⟩
  intro heq
  have hrow : ({Outcome.halt (0 : Fin 2) 17} : Set (Outcome (Fin 2))) =
      {Outcome.bottom} := by
    calc
      _ = forwardTwo 0 := hF20.symm
      _ = feedbackTwo 0 := congrArg (fun p : Profile (Fin 2) (Fin 2) => p 0) hB2.symm
      _ = feedbackThree 0 := congrArg (fun p : Profile (Fin 2) (Fin 2) => p 0) heq
      _ = _ := hB30
  have hmem : Outcome.halt (0 : Fin 2) 17 ∈
      ({Outcome.bottom} : Set (Outcome (Fin 2))) := by rw [← hrow]; simp
  simpa using hmem

abbrev FixtureProfile := Profile (Fin 2) (Fin 2)

def BooleanForward (q : Bool) : FixtureProfile :=
  PolicyProfile forwardArena (forwardPolicy q) forwardStart

def BooleanFeedback (q : Bool) : FixtureProfile :=
  PolicyProfile feedbackArena (feedbackPolicy q) feedbackStart

/-- Original complete-policy relations on each actual original arena. Legal
Even assignments have exactly the two agreement classes, both decreasing. -/
def FullForwardRelation : Set FixtureProfile :=
  JointAttainable forwardArena forwardStart Set.univ

def FullFeedbackRelation : Set FixtureProfile :=
  JointAttainable feedbackArena feedbackStart Set.univ

/-- Physical singleton-menu relations on the smaller original44/45 arenas;
these are not definitions that merely delete a policy from the original set. -/
def SingletonForwardRelation : Set FixtureProfile :=
  JointAttainable restrictedForwardArena restrictedForwardStart Set.univ

def SingletonFeedbackRelation : Set FixtureProfile :=
  JointAttainable restrictedFeedbackArena restrictedFeedbackStart Set.univ

theorem full_forward_relation_bool :
    FullForwardRelation = ProfileRelation BooleanForward Set.univ := by
  ext p
  constructor
  · rintro ⟨σ, hσ, hp⟩
    obtain ⟨q, hq⟩ := forward_policy_cases σ
    refine ⟨q, Set.mem_univ _, ?_⟩
    exact (profile_of_policyAgreement forwardArena σ (forwardPolicy q) hq forwardStart).symm.trans hp
  · rintro ⟨q, hq, hp⟩
    exact ⟨forwardPolicy q, Set.mem_univ _, hp⟩

theorem full_feedback_relation_bool :
    FullFeedbackRelation = ProfileRelation BooleanFeedback Set.univ := by
  ext p
  constructor
  · rintro ⟨σ, hσ, hp⟩
    obtain ⟨q, hq⟩ := feedback_policy_cases σ
    refine ⟨q, Set.mem_univ _, ?_⟩
    exact (profile_of_policyAgreement feedbackArena σ (feedbackPolicy q) hq feedbackStart).symm.trans hp
  · rintro ⟨q, hq, hp⟩
    exact ⟨feedbackPolicy q, Set.mem_univ _, hp⟩

theorem singleton_forward_relation : SingletonForwardRelation = {forwardTwo} := by
  ext p
  constructor
  · rintro ⟨σ, hσ, hp⟩
    apply Set.mem_singleton_iff.mpr
    calc
      p = PolicyProfile restrictedForwardArena σ restrictedForwardStart := hp.symm
      _ = PolicyProfile restrictedForwardArena restrictedForwardPolicy restrictedForwardStart :=
        profile_of_policyAgreement _ _ _ (restricted_forward_policy_unique σ) _
      _ = forwardTwo := restricted_forward_profile
  · intro hp
    have heq : p = forwardTwo := Set.mem_singleton_iff.mp hp
    exact ⟨restrictedForwardPolicy, Set.mem_univ _, restricted_forward_profile.trans heq.symm⟩

theorem singleton_feedback_relation : SingletonFeedbackRelation = {feedbackTwo} := by
  ext p
  constructor
  · rintro ⟨σ, hσ, hp⟩
    apply Set.mem_singleton_iff.mpr
    calc
      p = PolicyProfile restrictedFeedbackArena σ restrictedFeedbackStart := hp.symm
      _ = PolicyProfile restrictedFeedbackArena restrictedFeedbackPolicy restrictedFeedbackStart :=
        profile_of_policyAgreement _ _ _ (restricted_feedback_policy_unique σ) _
      _ = feedbackTwo := restricted_feedback_profile
  · intro hp
    have heq : p = feedbackTwo := Set.mem_singleton_iff.mp hp
    exact ⟨restrictedFeedbackPolicy, Set.mem_univ _, restricted_feedback_profile.trans heq.symm⟩

/-- Both components now compare actual physical arenas. The source table is
still an explicit, unproved mathematical duty of this conditional theorem. -/
theorem physical_relation_collision_of_table (h : collisionTableTarget) :
    FullForwardRelation = SingletonForwardRelation ∧
      FullFeedbackRelation ≠ SingletonFeedbackRelation := by
  have hforward : forwardThree = forwardTwo := h.2.2.1
  have hdistinct := feedback_rows_distinct_of_table h
  constructor
  · rw [full_forward_relation_bool, singleton_forward_relation]
    ext p
    constructor
    · rintro ⟨q, hq, hp⟩
      apply Set.mem_singleton_iff.mpr
      cases q
      · exact hp.symm
      · exact hp.symm.trans hforward
    · intro hp
      have heq : p = forwardTwo := Set.mem_singleton_iff.mp hp
      exact ⟨false, Set.mem_univ _, heq.symm⟩
  · intro heq
    have hthree : feedbackThree ∈ FullFeedbackRelation := by
      exact ⟨feedbackPolicy true, Set.mem_univ _, rfl⟩
    rw [heq, singleton_feedback_relation] at hthree
    exact hdistinct (Set.mem_singleton_iff.mp hthree).symm

/-- false denotes original47/48; true denotes physical44/45. A transfer whose
only input is the forward closed winning/minimum relation cannot distinguish
these arenas once the exact table duty is discharged. -/
def MarkedForwardClass (restricted : Bool) : Set FixtureProfile :=
  if restricted then SingletonForwardRelation else FullForwardRelation

def MarkedFeedbackClass (restricted : Bool) : Set FixtureProfile :=
  if restricted then SingletonFeedbackRelation else FullFeedbackRelation

theorem no_physical_relation_transfer_of_table (h : collisionTableTarget) :
    ¬ ∃ transfer : Set FixtureProfile → Set FixtureProfile,
      ∀ restricted : Bool,
        transfer (MarkedForwardClass restricted) = MarkedFeedbackClass restricted := by
  obtain ⟨hsame, hdifferent⟩ := physical_relation_collision_of_table h
  rintro ⟨transfer, htransfer⟩
  apply hdifferent
  calc
    FullFeedbackRelation = transfer FullForwardRelation := (htransfer false).symm
    _ = transfer SingletonForwardRelation := congrArg transfer hsame
    _ = SingletonFeedbackRelation := htransfer true

/- D-FB-TABLE: discharge NoLosingFixtureDuty, FirstStartExitOnlyDuty and
SecondStartRawDuty over exact original graphs, connect explicit17/zero/lasso
witnesses to the finite reachability certificates, and derive the finite
minimum table; prove all eight CertificateRawExactTarget bridges. Only then
use collisionTable_of_certificate and the two nonfactorization conclusions.
No lower bound on richer arena/policy/marker-aware or post-feedback zone
representations is asserted. No R8 boundary-forget claim is authored here. -/

end Partials.Parity.Fixture
