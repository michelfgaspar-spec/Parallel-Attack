import Mathlib.Tactic.NormNum
import Partials.Parity.TieFixture

/-! R7 blind explicit row comparison and raw-set targets. The formal link
from the literal27-vertex instance to these rows remains a separate duty. -/
namespace Partials.Parity.Tie

def isolatedProfile (new : Bool) : Profile (Fin 2) (Fin 2) :=
  fun i => if i = 0 then {Outcome.halt 0 13, Outcome.halt 1 12}
    else {Outcome.halt 0 13, Outcome.halt 1 (if new then 8 else 4)}

theorem displayed_local_strict : StrictProfile (isolatedProfile false) (isolatedProfile true) := by
  constructor
  · intro i
    fin_cases i
    · intro d hd
      refine ⟨d, hd, ?_⟩
      rcases hd with rfl | rfl <;> norm_num [OutcomeLE, PriorityLE]
    · intro d hd
      simp only [isolatedProfile, Bool.false_eq_true, if_false, if_true, Fin.isValue, Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with rfl | rfl
      · exact ⟨.halt 0 13, by simp [isolatedProfile], by norm_num [OutcomeLE, PriorityLE]⟩
      · exact ⟨.halt 1 4, by simp [isolatedProfile], by norm_num [OutcomeLE, PriorityLE]⟩
  · intro h
    obtain ⟨r, hr, hle⟩ := h 1 (.halt 1 4) (by simp [isolatedProfile])
    simp only [isolatedProfile, if_true, Fin.isValue,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl <;> norm_num [OutcomeLE, PriorityLE] at hle

def globalRawTarget : Set (Outcome (Fin 1)) := {.bottom, .top, .halt 0 13}

def LocalRawTableTarget : Prop :=
  (∀ new : Bool, RawOutcomes (localArena .a) (localPolicy .a new) (localStart .a 0) =
    ({.halt 0 13,.halt 1 12,.top} : Set (Outcome (Fin 2)))) ∧
  (∀ new : Bool, RawOutcomes (localArena .a) (localPolicy .a new) (localStart .a 1) =
    ({.halt 0 13,.halt 1 (if new then 8 else 4),.halt 1 12,.top} : Set (Outcome (Fin 2))))

def GlobalRawTableTarget : Prop :=
  ∀ new : Bool, ∀ i : Fin 4,
    RawOutcomes globalArena (globalPolicy new) (globalStarts i) = globalRawTarget

/-- Primitive observations needed from the literal graph: two compatible
nonexit histories and the finite first-exit max identity. No full raw-set
equality, global tie or strictness result is a field of this duty. -/
structure GlobalHistoryDuty : Prop where
  bottom_history : ∀ new : Bool, ∀ i : Fin 4, ∃ ρ : ℕ → Vertex,
    ρ 0 = globalStarts i ∧ Compatible globalArena (globalPolicy new) ρ ∧
      InfiniteOutcome globalArena ρ .bottom
  top_history : ∀ new : Bool, ∀ i : Fin 4, ∃ ρ : ℕ → Vertex,
    ρ 0 = globalStarts i ∧ Compatible globalArena (globalPolicy new) ρ ∧
      InfiniteOutcome globalArena ρ .top
  exit_history : ∀ new : Bool, ∀ i : Fin 4, ∃ ρ : ℕ → Vertex,
    ρ 0 = globalStarts i ∧ Compatible globalArena (globalPolicy new) ρ ∧
      FiniteOutcome globalArena ρ (.halt 0 13)
  last_exit_max : ∀ new : Bool, ∀ i : Fin 4, ∀ ρ : ℕ → Vertex,
    ρ 0 = globalStarts i → Compatible globalArena (globalPolicy new) ρ →
    ∀ n o p, FirstExit globalArena ρ n o p → p = 13

theorem global_raw_from_observations (h : GlobalHistoryDuty) : GlobalRawTableTarget := by
  intro new i
  apply Set.ext
  intro out
  constructor
  · rintro ⟨ρ, hstart, hc, hf | hinf⟩
    · obtain ⟨n,o,p,hfirst,rfl⟩ := hf
      have hp := h.last_exit_max new i ρ hstart hc n o p hfirst
      have ho : o = 0 := Subsingleton.elim _ _
      simp [globalRawTarget,hp,ho]
    · obtain ⟨havoid,p,hrec,hparity⟩ := hinf
      rcases hparity with ⟨hp,rfl⟩ | ⟨hp,rfl⟩ <;> simp [globalRawTarget]
  · intro hout
    simp only [globalRawTarget,Set.mem_insert_iff,Set.mem_singleton_iff] at hout
    rcases hout with rfl | rfl | rfl
    · obtain ⟨ρ,hs,hc,ho⟩ := h.bottom_history new i
      exact ⟨ρ,hs,hc,Or.inr ho⟩
    · obtain ⟨ρ,hs,hc,ho⟩ := h.top_history new i
      exact ⟨ρ,hs,hc,Or.inr ho⟩
    · obtain ⟨ρ,hs,hc,ho⟩ := h.exit_history new i
      exact ⟨ρ,hs,hc,Or.inl ho⟩

theorem global_raw_tie_from_observations (h : GlobalHistoryDuty) (i : Fin 4) :
    RawOutcomes globalArena (globalPolicy false) (globalStarts i) =
      RawOutcomes globalArena (globalPolicy true) (globalStarts i) := by
  rw [global_raw_from_observations h false i,global_raw_from_observations h true i]

def literalVertexCount (r M : ℕ) : ℕ := r + 4 + 3 * M
theorem literal_fragment_lower (r M : ℕ) (hr : 2 ≤ r) (hM : r ≤ M) :
    12 ≤ literalVertexCount r M := by unfold literalVertexCount; omega
theorem changed_fragment_lower (r M : ℕ) (hr : 2 ≤ r) (hM : r + 1 ≤ M) :
    15 ≤ literalVertexCount r M := by unfold literalVertexCount; omega
theorem literal_pair_bounds (rA mA rB mB : ℕ)
    (ha : 2 ≤ rA) (hb : 2 ≤ rB) (hma : rA ≤ mA) (hmb : rB ≤ mB) :
    24 ≤ literalVertexCount rA mA + literalVertexCount rB mB := by
  have := literal_fragment_lower rA mA ha hma
  have := literal_fragment_lower rB mB hb hmb
  omega
theorem changing_pair_lower (rA mA rB mB : ℕ)
    (ha : 2 ≤ rA) (hb : 2 ≤ rB) (hma : rA + 1 ≤ mA) (hmb : rB ≤ mB) :
    27 ≤ literalVertexCount rA mA + literalVertexCount rB mB := by
  have := changed_fragment_lower rA mA ha hma
  have := literal_fragment_lower rB mB hb hmb
  omega
theorem literal_instance_attains : literalVertexCount 2 3 = 15 ∧
    literalVertexCount 2 2 = 12 ∧ literalVertexCount 2 3 + literalVertexCount 2 2 = 27 := by
  norm_num [literalVertexCount]

end Partials.Parity.Tie
