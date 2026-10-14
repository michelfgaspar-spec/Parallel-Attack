import Partials.Parity.PhysicalRestriction
import Partials.Parity.TieComparison
import Partials.Parity.HistorySemantics

/-! neighbors.tex: original coordinate edits and physical pinning. No
endpoint reconstruction or profile-only baseline is a local policy edit.
Compiler/effectivity duties inherited from R7 remain open. -/
namespace Partials.ParityAlgorithms.Neighborhoods

structure CoordinateGrammar (r layers : Nat) where
  lower : Fin r → Int
  upper : Fin r → Int
  immediate : Fin r → Fin r → Prop
  immediate_decidable : DecidableRel immediate
  /- Original two router identities per layer are retained, even when forced.
  Odd routers are excluded by the explicit Even mask below. -/
  routerEven : Fin (2 * layers) → Bool
  routerTargets : Fin (2 * layers) → Finset Nat
  targets_nonempty : ∀ k, (routerTargets k).Nonempty
  targets_at_most_two : ∀ k, (routerTargets k).card ≤ 2

structure OriginalCoordinates (r layers : Nat) where
  hub : Fin r → Int
  router : Fin (2 * layers) → Nat

def Admitted {r layers : Nat} (G : CoordinateGrammar r layers)
    (σ : OriginalCoordinates r layers) : Prop :=
  (∀ j, G.lower j ≤ σ.hub j ∧ σ.hub j ≤ G.upper j) ∧
  (∀ j k, G.immediate j k → σ.hub k < σ.hub j) ∧
  (∀ k, G.routerEven k = true → σ.router k ∈ G.routerTargets k)

inductive OriginalCoordinate (r layers : Nat) where
  | hub (j : Fin r)
  | router (k : Fin (2 * layers))

def UnitHubEdit {r layers : Nat} (F : Set (OriginalCoordinate r layers))
    (old new : OriginalCoordinates r layers) : Prop :=
  ∃ j, .hub j ∈ F ∧
    (new.hub j = old.hub j + 1 ∨ new.hub j = old.hub j - 1) ∧
    (∀ k, k ≠ j → new.hub k = old.hub k) ∧ new.router = old.router

def DistinctRouterEdit {r layers : Nat} (G : CoordinateGrammar r layers)
    (F : Set (OriginalCoordinate r layers))
    (old new : OriginalCoordinates r layers) : Prop :=
  ∃ k, .router k ∈ F ∧ G.routerEven k = true ∧
    new.router k ∈ G.routerTargets k ∧ new.router k ≠ old.router k ∧
    (∀ j, j ≠ k → new.router j = old.router j) ∧ new.hub = old.hub

def OneChoiceNeighborhood {r layers : Nat} (G : CoordinateGrammar r layers)
    (old : OriginalCoordinates r layers) (F : Set (OriginalCoordinate r layers)) :
    Set (OriginalCoordinates r layers) :=
  {σ | Admitted G σ ∧ (UnitHubEdit F old σ ∨ DistinctRouterEdit G F old σ)}

def editHub {r layers : Nat} (σ : OriginalCoordinates r layers)
    (j : Fin r) (q : Int) : OriginalCoordinates r layers :=
  ⟨Function.update σ.hub j q, σ.router⟩

def editRouter {r layers : Nat} (σ : OriginalCoordinates r layers)
    (k : Fin (2 * layers)) (target : Nat) : OriginalCoordinates r layers :=
  ⟨σ.hub, Function.update σ.router k target⟩

theorem hub_edit_keeps_other_original_choices {r layers : Nat}
    (σ : OriginalCoordinates r layers) (j : Fin r) (q : Int) :
    (∀ k, k ≠ j → (editHub σ j q).hub k = σ.hub k) ∧
      (editHub σ j q).router = σ.router := by
  constructor
  · intro k hk; simp [editHub, Function.update, hk]
  · rfl

theorem router_edit_keeps_other_original_choices {r layers : Nat}
    (σ : OriginalCoordinates r layers) (k : Fin (2 * layers)) (t : Nat) :
    (∀ j, j ≠ k → (editRouter σ k t).router j = σ.router j) ∧
      (editRouter σ k t).hub = σ.hub := by
  constructor
  · intro j hj; simp [editRouter, Function.update, hj]
  · rfl

theorem unit_edit_is_single_update {r layers : Nat}
    {F : Set (OriginalCoordinate r layers)} {old new : OriginalCoordinates r layers}
    (h : UnitHubEdit F old new) :
    ∃ j q, .hub j ∈ F ∧ (q = old.hub j + 1 ∨ q = old.hub j - 1) ∧
      new = editHub old j q := by
  obtain ⟨j, hj, hq, hother, hr⟩ := h
  refine ⟨j, new.hub j, hj, hq, ?_⟩
  cases new with
  | mk hub router =>
    simp only [editHub, OriginalCoordinates.mk.injEq]
    refine ⟨?_, hr⟩
    funext k
    by_cases hk : k = j
    · subst k; simp
    · simpa [Function.update, hk] using hother k hk

theorem forced_router_has_no_distinct_edit {r layers : Nat}
    (G : CoordinateGrammar r layers) (σ : OriginalCoordinates r layers)
    (k : Fin (2 * layers)) (t : Nat)
    (hforced : G.routerTargets k = {σ.router k})
    (ht : t ∈ G.routerTargets k) : t = σ.router k := by
  simpa [hforced] using ht

/-- The only descent checks that can change are the original incident links.
No separate chain endpoint solver is called by this local test. -/
def IncidentHubCheck {r layers : Nat} (G : CoordinateGrammar r layers)
    (σ : OriginalCoordinates r layers) (j : Fin r) (q : Int) : Prop :=
  G.lower j ≤ q ∧ q ≤ G.upper j ∧
    (∀ k, G.immediate k j → q < σ.hub k) ∧
    (∀ k, G.immediate j k → σ.hub k < q)

/-- A chain cannot have a self-link under an admitted strict descent. -/
theorem admitted_no_self_link {r layers : Nat} (G : CoordinateGrammar r layers)
    (σ : OriginalCoordinates r layers) (h : Admitted G σ) (j : Fin r) :
    ¬ G.immediate j j := by
  intro hj; exact (lt_irrefl (σ.hub j)) (h.2.1 j j hj)

theorem incident_check_preserves_admission {r layers : Nat}
    (G : CoordinateGrammar r layers) (σ : OriginalCoordinates r layers)
    (hσ : Admitted G σ) (j : Fin r) (q : Int)
    (hq : IncidentHubCheck G σ j q) : Admitted G (editHub σ j q) := by
  refine ⟨?_, ?_, hσ.2.2⟩
  · intro k
    by_cases hk : k = j
    · subst k; simpa [editHub] using And.intro hq.1 hq.2.1
    · simpa [editHub, Function.update, hk] using hσ.1 k
  · intro a b hab
    by_cases ha : a = j
    · subst a
      have hb : b ≠ j := by intro he; subst b; exact admitted_no_self_link G σ hσ j hab
      simpa [editHub, Function.update, hb] using hq.2.2.2 b hab
    · by_cases hb : b = j
      · subst b; simpa [editHub, Function.update, ha] using hq.2.2.1 a hab
      · simpa [editHub, Function.update, ha, hb] using hσ.2.1 a b hab

def candidateBound (r layers : Nat) : Nat := 2 * r + 2 * layers
def fullInputLength (N oldLength baselineLength mutableLength : Nat) : Nat :=
  N + oldLength + baselineLength + mutableLength

/-- Host-authorable enumeration skeleton: unit hub candidates only, then
distinct admitted existing Even-router targets. No loop through menu ranges.
Odd-router dummy entries are copied literally and never enumerated. -/
noncomputable def enumerateNeighbors {r layers : Nat} (G : CoordinateGrammar r layers)
    (old : OriginalCoordinates r layers) (F : Set (OriginalCoordinate r layers)) :
    List (OriginalCoordinates r layers) := by
  classical
  let hubs := (List.finRange r).flatMap fun j =>
    if .hub j ∈ F then [editHub old j (old.hub j + 1), editHub old j (old.hub j - 1)]
    else []
  let routers := (List.finRange (2 * layers)).flatMap fun k =>
    if .router k ∈ F ∧ G.routerEven k = true then
      ((G.routerTargets k).erase (old.router k)).toList.map (editRouter old k)
    else []
  exact (hubs ++ routers).filter fun σ => decide (Admitted G σ)

/-- Exact primitive facts needed from the physical singleton generator;
these are retained-vertex/edge statements, not a desired profile equation. -/
structure PinnedIdentity {V Exit Start : Type} (A : Partials.Parity.Arena V Exit)
    (σ : Partials.Parity.EvenPolicy A) (start : Start → V) where
  keep : V → Prop
  small : Partials.Parity.Arena {v : V // keep v} Exit
  policy : Partials.Parity.EvenPolicy small
  start_kept : ∀ i, keep (start i)
  selected : ∀ u v, Partials.Parity.selectedEdge small policy u v ↔
    Partials.Parity.selectedEdge A σ u.val v.val
  priorities : ∀ v, small.priority v = A.priority v.val
  exits : ∀ o, (small.exitVertex o).val = A.exitVertex o
  closed : ∀ u v, keep u → Partials.Parity.selectedEdge A σ u v → keep v
  unique : ∀ τ, Partials.Parity.PolicyAgreement small τ policy
  /- Original forced arms omitted from small are still completed in σ.
  The explicit generator-to-original-product adapter remains a duty. -/

theorem pinned_all_history_profile {V Exit Start : Type}
    (A : Partials.Parity.Arena V Exit) (σ : Partials.Parity.EvenPolicy A)
    (start : Start → V) (P : PinnedIdentity A σ start) :
    Partials.Parity.PolicyProfile P.small P.policy
      (fun i => ⟨start i, P.start_kept i⟩) =
      Partials.Parity.PolicyProfile A σ start := by
  funext i
  apply congrArg Partials.Parity.MinRow
  exact Partials.Parity.Fixture.raw_retained_identity P.keep A σ
    P.small P.policy P.selected P.priorities P.exits P.closed ⟨start i, P.start_kept i⟩

theorem pinned_joint_singleton {V Exit Start : Type}
    (A : Partials.Parity.Arena V Exit) (σ : Partials.Parity.EvenPolicy A)
    (start : Start → V) (P : PinnedIdentity A σ start) :
    Partials.Parity.JointAttainable P.small (fun i => ⟨start i, P.start_kept i⟩) Set.univ =
      {Partials.Parity.PolicyProfile A σ start} := by
  ext profile
  constructor
  · rintro ⟨τ, _, hprofile⟩
    have hagree := Partials.Parity.policyProfile_agreement (P.unique τ)
      (fun i => ⟨start i, P.start_kept i⟩)
    have hp := pinned_all_history_profile A σ start P
    exact hprofile.symm.trans (hagree.trans hp)
  · intro hprofile
    have heq : profile = Partials.Parity.PolicyProfile A σ start := hprofile
    refine ⟨P.policy, Set.mem_univ _, ?_⟩
    exact (pinned_all_history_profile A σ start P).trans heq.symm

structure NeighborWitness {r layers : Nat} {Start Exit : Type}
    (G : CoordinateGrammar r layers) (old : OriginalCoordinates r layers)
    (F : Set (OriginalCoordinate r layers))
    (profile : OriginalCoordinates r layers → Partials.Parity.Profile Start Exit) where
  policy : OriginalCoordinates r layers
  wholeProfile : Partials.Parity.Profile Start Exit
  legal_original_edit : policy ∈ OneChoiceNeighborhood G old F
  exact_whole_profile : wholeProfile = profile policy
  strict : Partials.Parity.StrictProfile (profile old) wholeProfile

/-- Direct strict comparison needs no attainable-baseline premise in the
pinned arena. In particular b need not belong to its singleton relation. -/
def DirectStrict {Start Exit : Type}
    (baseline candidate : Partials.Parity.Profile Start Exit) : Prop :=
  Partials.Parity.ProfileLE baseline candidate ∧
    ¬ Partials.Parity.ProfileLE candidate baseline

theorem direct_strict_is_paper_predicate {Start Exit : Type}
    (b c : Partials.Parity.Profile Start Exit) :
    DirectStrict b c ↔ Partials.Parity.StrictProfile b c := Iff.rfl

/-- Precise finite decision target. A negative answer excludes only the
enumerated original neighborhood. No global optimality predicate appears. -/
def ExactNeighborDecision {r layers : Nat} {Start Exit : Type}
    (G : CoordinateGrammar r layers) (old : OriginalCoordinates r layers)
    (F : Set (OriginalCoordinate r layers))
    (profile : OriginalCoordinates r layers → Partials.Parity.Profile Start Exit)
    (answer : Option (OriginalCoordinates r layers)) : Prop :=
  match answer with
  | some σ => σ ∈ OneChoiceNeighborhood G old F ∧ DirectStrict (profile old) (profile σ)
  | none => ∀ σ ∈ OneChoiceNeighborhood G old F, ¬ DirectStrict (profile old) (profile σ)

/-- Original explicit fixtures reused for displayed rows only. The exact
forward two-router generator, all-history exhaustion and reachable tie
control are R8-D-neighbor-forward-fixture, not the feedback tie theorem. -/
def displayedStrictFixture := Partials.Parity.Tie.isolatedProfile

theorem displayed_fixture_profile_strict :
    DirectStrict (displayedStrictFixture false) (displayedStrictFixture true) :=
  Partials.Parity.Tie.displayed_local_strict

def displayedTieControl : Partials.Parity.Profile (Fin 2) (Fin 2) :=
  fun _ => {.halt 0 13, .halt 1 12}

theorem displayed_tie_rejected : ¬ DirectStrict displayedTieControl displayedTieControl := by
  intro h; exact h.2 h.1

end Partials.ParityAlgorithms.Neighborhoods
