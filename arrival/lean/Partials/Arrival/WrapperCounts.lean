import Partials.Arrival.Physical

/-! R3 unchecked source. The lower and boundary lemmas prove arithmetic
consequences of local firing/conservation equations. No constructor contains
N=H, M bounds, lower powers, or decoder correctness as witness fields. The
operational extraction of these equations is explicitly a separate duty. -/
namespace Partials.Arrival.Physical

def wrapperH (k : ℕ) : ℕ := 2 ^ (k + 2)

/-- Counts are indexed by the manuscript label j, including ell_1.
`up` is an even-slot departure to a_k; `down` is an odd-slot departure to
ell_(j-1). Balance at ell_j and the alternation/last-departure condition are
separate hypotheses. They still need extraction from a complete legal run. -/
def LowerConservation (k : ℕ) (visits up down : ℕ → ℕ) : Prop :=
  visits 1 = 1 ∧
    ∀ j, 2 ≤ j → j ≤ k + 3 →
      visits j = up j + down j ∧ up j = down j ∧ down j = visits (j - 1)

theorem lower_visit_power (h : LowerConservation k visits up down)
    (q : ℕ) (hq : q ≤ k + 2) : visits (q + 1) = 2 ^ q := by
  revert hq
  induction q with
  | zero => intro hq; simpa using h.1
  | succ q ih =>
    intro hq
    have hq' : q ≤ k + 2 := by omega
    obtain ⟨hvisit, hslots, hflow⟩ := h.2 (q + 2) (by omega) (by omega)
    have hprev := ih hq'
    have hdown : down (q + 2) = 2 ^ q := by
      simpa using hflow.trans (by simpa using hprev)
    simp only [pow_succ]
    have hup : up (q + 2) = 2 ^ q := hslots.trans hdown
    have hnext : visits (q + 2) = 2 ^ q + 2 ^ q := by
      rw [hvisit, hup, hdown]
    simpa [Nat.succ_eq_add_one, Nat.add_assoc, Nat.mul_two] using hnext

theorem lower_up_power (h : LowerConservation k visits up down)
    (q : ℕ) (hq : q < k + 2) : up (q + 2) = 2 ^ q := by
  obtain ⟨_, hslots, hflow⟩ := h.2 (q + 2) (by omega) (by omega)
  calc
    up (q + 2) = down (q + 2) := hslots
    _ = visits (q + 1) := by simpa using hflow
    _ = 2 ^ q := lower_visit_power h q (by omega)

theorem geometric_binary_sum (n : ℕ) :
    1 + ∑ q ∈ Finset.range n, 2 ^ q = 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, pow_succ]
    omega

/-- Number of external E entries, once the event-to-ledger bridge is proved. -/
def lowerExternalMass (k : ℕ) (up : ℕ → ℕ) : ℕ :=
  1 + ∑ q ∈ Finset.range (k + 2), up (q + 2)

theorem lower_counter_bridge (h : LowerConservation k visits up down) :
    visits (k + 3) = wrapperH k ∧ lowerExternalMass k up = wrapperH k := by
  have htop := lower_visit_power h (k + 2) (by omega)
  refine ⟨by simpa [wrapperH] using htop, ?_⟩
  have hsum : (∑ q ∈ Finset.range (k + 2), up (q + 2)) =
      ∑ q ∈ Finset.range (k + 2), 2 ^ q := by
    apply Finset.sum_congr rfl
    intro q hq
    exact lower_up_power h q (Finset.mem_range.mp hq)
  simpa [lowerExternalMass, hsum, wrapperH] using geometric_binary_sum (k + 2)

def namedCountAt (T : NamedCounts) : NamedOutput → ℕ
  | .a0 => T.a0
  | .b0 => T.b0
  | .c0 => T.c0

def boundaryDownMass (T : NamedCounts) : ℕ := T.a0 / 2 + T.b0 / 2 + T.c0 / 2
def boundaryOddMass (T : NamedCounts) : ℕ := T.a0 % 2 + T.b0 % 2 + T.c0 % 2

theorem boundary_divmod_balance (T : NamedCounts) :
    T.total = 2 * boundaryDownMass T + boundaryOddMass T := by
  have ha := Nat.mod_add_div T.a0 2
  have hb := Nat.mod_add_div T.b0 2
  have hc := Nat.mod_add_div T.c0 2
  dsimp [NamedCounts.total, boundaryDownMass, boundaryOddMass]
  omega

/-- The final boundary departure is odd (descending), hence that boundary
has an even total. This local operational fact rules out three odd totals. -/
theorem boundary_odd_mass_le_two (T : NamedCounts)
    (hlast : ∃ t, namedCountAt T t % 2 = 0) : boundaryOddMass T ≤ 2 := by
  have ha := Nat.mod_lt T.a0 (by decide : 0 < 2)
  have hb := Nat.mod_lt T.b0 (by decide : 0 < 2)
  have hc := Nat.mod_lt T.c0 (by decide : 0 < 2)
  obtain ⟨t, ht⟩ := hlast
  cases t <;> simp only [namedCountAt] at ht
  all_goals dsimp [boundaryOddMass]
  all_goals omega

/-- A substantive boundary arithmetic implication. Its premises are local
particle balance, descending departures, and one final even boundary count;
they do not supply M's requested bounds. -/
theorem boundary_count_bridge (T : NamedCounts) (N M H : ℕ)
    (hN : N = H) (htotal : N + M = T.total)
    (hdown : boundaryDownMass T = H) (hlast : ∃ t, namedCountAt T t % 2 = 0) :
    H ≤ M ∧ M ≤ H + 2 := by
  have hbalance := boundary_divmod_balance T
  have hodd := boundary_odd_mass_le_two T hlast
  omega

/-- Integrates the proved lower-counter and boundary arithmetic, while
exposing exactly which event/ledger correspondences still have to be proved.
This is not a theorem that an actual source run satisfies its hypotheses. -/
theorem wrapper_count_from_local_balances (hk : 3 ≤ k)
    (events : List (Event k)) (visits up down : ℕ → ℕ)
    (hlower : LowerConservation k visits up down)
    (hE : (externalBatch hk events).N = lowerExternalMass k up)
    (hupper : (externalBatch hk events).total = (boundaryReturns events).total)
    (hboundary : boundaryDownMass (boundaryReturns events) = visits (k + 3))
    (hlast : ∃ t, namedCountAt (boundaryReturns events) t % 2 = 0) :
    (externalBatch hk events).N = wrapperH k ∧
    wrapperH k ≤ (externalBatch hk events).M ∧
    (externalBatch hk events).M ≤ wrapperH k + 2 := by
  obtain ⟨htop, hmass⟩ := lower_counter_bridge hlower
  have hN := hE.trans hmass
  have hdown := hboundary.trans htop
  have hbounds := boundary_count_bridge (boundaryReturns events)
    (externalBatch hk events).N (externalBatch hk events).M (wrapperH k)
    hN (by simpa [Batch.total] using hupper) hdown hlast
  exact ⟨hN, hbounds⟩

/-! Exact open extraction duties. A later ARRIVAL proof must obtain these
from `CompleteAllEven`, not add them as new physical-run hypotheses. -/
def LowerExtractionDuty (hk : 3 ≤ k) : Prop :=
  ∀ D events, CompleteAllEven hk D events →
    ∃ visits up down : ℕ → ℕ,
      LowerConservation k visits up down ∧
      (externalBatch hk events).N = lowerExternalMass k up ∧
      (externalBatch hk events).total = (boundaryReturns events).total ∧
      boundaryDownMass (boundaryReturns events) = visits (k + 3) ∧
      (∃ t, namedCountAt (boundaryReturns events) t % 2 = 0)

def SourceCountDuty (hk : 3 ≤ k) : Prop :=
  ∀ D events, CompleteAllEven hk D events →
    (externalBatch hk events).N = wrapperH k ∧
    wrapperH k ≤ (externalBatch hk events).M ∧
    (externalBatch hk events).M ≤ wrapperH k + 2

theorem lower_extraction_implies_source_count (hk : 3 ≤ k)
    (h : LowerExtractionDuty hk) : SourceCountDuty hk := by
  intro D events hr
  obtain ⟨visits, up, down, hlow, hE, hu, hb, hl⟩ := h D events hr
  exact wrapper_count_from_local_balances hk events visits up down hlow hE hu hb hl

/-- `C0` is the arithmetic author's exact named decoder, once its API is
agreed. This duty needs cutting actual excursions at the named boundaries,
showing the initial upper state is canonical/all-even, and the operational
decoder/abelian theorem. No equality is put into a realization structure. -/
def UpperAggregateDecoderDuty (hk : 3 ≤ k) (C0 : Batch → NamedCounts) : Prop :=
  ∀ D events, CompleteAllEven hk D events →
    boundaryReturns events = C0 (externalBatch hk events)

/-- Cost is a different observable from boundary/external counts. No cost
estimate follows merely from the external count bridge. -/
def physicalStepCost (events : List (Event k)) : ℕ := events.length
def internalFeedbackCount (hk : 3 ≤ k) (events : List (Event k)) : ℕ :=
  (events.filter (fun e => decide
    (e.from = .b ⟨0, by omega⟩ ∧ e.to = source hk))).length

end Partials.Arrival.Physical
