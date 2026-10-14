import Partials.Parity.TieComparison
import Partials.Parity.Rows

/-! R7 conditional assembly. Concrete local raw and cycle/path observations
remain unaccepted targets. Displayed set comparison is not their admission. -/
namespace Partials.Parity.Tie

theorem global_minimum_from_observations (h : GlobalHistoryDuty) (new : Bool) (i : Fin 4) :
    PolicyProfile globalArena (globalPolicy new) globalStarts i = {.bottom} := by
  apply minRow_eq_singleton_bottom
  rw [global_raw_from_observations h new i]
  simp [globalRawTarget]

theorem global_profile_tie_from_observations (h : GlobalHistoryDuty) :
    PolicyProfile globalArena (globalPolicy false) globalStarts =
      PolicyProfile globalArena (globalPolicy true) globalStarts := by
  funext i
  rw [global_minimum_from_observations h false i,global_minimum_from_observations h true i]

theorem global_strict_rejected (h : GlobalHistoryDuty) :
    ¬ StrictProfile (PolicyProfile globalArena (globalPolicy false) globalStarts)
      (PolicyProfile globalArena (globalPolicy true) globalStarts) := by
  rw [global_profile_tie_from_observations h]
  exact strictProfile_irrefl _

def appendedLocalProfile (new : Bool) (unchangedB : Profile (Fin 2) (Fin 2)) :
    Profile (Fin 2 ⊕ Fin 2) (Fin 2) := Sum.elim (isolatedProfile new) unchangedB

theorem append_unchanged_preserves_strict (unchangedB : Profile (Fin 2) (Fin 2)) :
    StrictProfile (appendedLocalProfile false unchangedB) (appendedLocalProfile true unchangedB) := by
  obtain ⟨hforward,hnotreverse⟩ := displayed_local_strict
  constructor
  · intro i
    cases i with
    | inl i => exact hforward i
    | inr i => exact rowLE_refl (unchangedB i)
  · intro hreverse
    exact hnotreverse (fun i => hreverse (Sum.inl i))

def LocalMinimumAdmissionTarget : Prop :=
  ∀ new : Bool, PolicyProfile (localArena .a) (localPolicy .a new) (localStart .a) =
    isolatedProfile new

def ExactTieConclusion : Prop :=
  StrictProfile (PolicyProfile (localArena .a) (localPolicy .a false) (localStart .a))
    (PolicyProfile (localArena .a) (localPolicy .a true) (localStart .a)) ∧
  (PolicyProfile globalArena (globalPolicy false) globalStarts =
    PolicyProfile globalArena (globalPolicy true) globalStarts) ∧
  (∀ i : Fin 4, .bottom ∈ RawOutcomes globalArena (globalPolicy false) (globalStarts i) ∧
    .bottom ∈ RawOutcomes globalArena (globalPolicy true) (globalStarts i))

theorem tie_from_local_and_global_inputs (hlocal : LocalMinimumAdmissionTarget)
    (hglobal : GlobalHistoryDuty) : ExactTieConclusion := by
  refine ⟨?_,global_profile_tie_from_observations hglobal,?_⟩
  · rw [hlocal false,hlocal true]
    exact displayed_local_strict
  · intro i
    rw [global_raw_from_observations hglobal false i,global_raw_from_observations hglobal true i]
    simp [globalRawTarget]

/- LocalMinimumAdmissionTarget is an explicit unproved finite semantic target;
its witness must come from the exact local raw-table/exclusion argument. It is
not supplied by hlocal here. GlobalHistoryDuty is also uninstantiated. -/
end Partials.Parity.Tie
