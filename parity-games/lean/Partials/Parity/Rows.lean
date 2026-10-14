import Mathlib.Data.Set.Finite.Basic
import Partials.Parity.Orders
import Partials.Parity.HistorySemantics

/-! Finite source minima and upper/result row order, preliminaries/P1-D05.
These are properties of the outcome poset, not optimized policy semantics.
No unbounded subset of the Nat-priority outcome domain is asserted finite. -/

namespace Partials.Parity

def SourceAntichain {Exit : Type*} (r : Set (Outcome Exit)) : Prop :=
  ∀ x ∈ r, ∀ y ∈ r, OutcomeLE x y → x = y

def NonemptyRow {Exit : Type*} (r : Set (Outcome Exit)) : Prop :=
  r.Nonempty ∧ SourceAntichain r

def OutcomeUpset {Exit : Type*} (r : Set (Outcome Exit)) : Set (Outcome Exit) :=
  {x | ∃ y ∈ r, OutcomeLE y x}

theorem minRow_subset {Exit : Type*} (raw : Set (Outcome Exit)) :
    MinRow raw ⊆ raw := by
  intro x hx
  exact hx.1

theorem minRow_antichain {Exit : Type*} (raw : Set (Outcome Exit)) :
    SourceAntichain (MinRow raw) := by
  intro x hx y hy hxy
  exact outcomeLE_antisymm hxy (hy.2 x hx.1 hxy)

/-- Inserting one element into a finite poset preserves a minimal element
below a previously chosen minimum: either use the new element or keep it. -/
theorem minimal_insert {Exit : Type*} [DecidableEq Exit]
    (s : Finset (Outcome Exit)) (a y : Outcome Exit)
    (hy : y ∈ s)
    (hminimal : ∀ z ∈ s, OutcomeLE z y → OutcomeLE y z) :
    ∃ z ∈ insert a s, OutcomeLE z y ∧
      ∀ w ∈ insert a s, OutcomeLE w z → OutcomeLE z w := by
  classical
  by_cases hay : OutcomeLE a y
  · refine ⟨a, Finset.mem_insert_self a s, hay, ?_⟩
    intro w hw hwa
    rcases Finset.mem_insert.mp hw with heq | hw
    · subst w
      exact outcomeLE_refl a
    · exact outcomeLE_trans hay (hminimal w hw (outcomeLE_trans hwa hay))
  · refine ⟨y, Finset.mem_insert_of_mem hy, outcomeLE_refl y, ?_⟩
    intro w hw hwy
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact False.elim (hay hwy)
    · exact hminimal w hw hwy

/-- Finite descent is proved by insertion, without adding an order instance
or assuming that a source-minimal outcome already exists. -/
theorem finite_minimal_below {Exit : Type*} [DecidableEq Exit]
    (s : Finset (Outcome Exit)) :
    ∀ x ∈ s, ∃ y ∈ s, OutcomeLE y x ∧
      ∀ z ∈ s, OutcomeLE z y → OutcomeLE y z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    intro x hx
    rcases Finset.mem_insert.mp hx with heq | hx
    · subst x
      by_cases h : ∃ w ∈ s, OutcomeLE w a
      · obtain ⟨w, hw, hwa⟩ := h
        obtain ⟨y, hy, hyw, hmin⟩ := ih w hw
        obtain ⟨z, hz, hzy, hzmin⟩ := minimal_insert s a y hy hmin
        exact ⟨z, hz, outcomeLE_trans hzy (outcomeLE_trans hyw hwa), hzmin⟩
      · refine ⟨a, Finset.mem_insert_self a s, outcomeLE_refl a, ?_⟩
        intro z hz hza
        rcases Finset.mem_insert.mp hz with heq | hz
        · subst z
          exact outcomeLE_refl a
        · exact False.elim (h ⟨z, hz, hza⟩)
    · obtain ⟨y, hy, hyx, hmin⟩ := ih x hx
      obtain ⟨z, hz, hzy, hzmin⟩ := minimal_insert s a y hy hmin
      exact ⟨z, hz, outcomeLE_trans hzy hyx, hzmin⟩

theorem finite_minRow_below {Exit : Type*}
    (raw : Set (Outcome Exit)) (hfinite : raw.Finite)
    {x : Outcome Exit} (hx : x ∈ raw) :
    ∃ y ∈ MinRow raw, OutcomeLE y x := by
  classical
  obtain ⟨y, hy, hyx, hmin⟩ :=
    finite_minimal_below hfinite.toFinset x (by simpa using hx)
  refine ⟨y, ⟨by simpa using hy, ?_⟩, hyx⟩
  intro z hz hzy
  exact hmin z (by simpa using hz) hzy

theorem finite_minRow_nonempty {Exit : Type*}
    (raw : Set (Outcome Exit)) (hfinite : raw.Finite) (hne : raw.Nonempty) :
    NonemptyRow (MinRow raw) := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy, _⟩ := finite_minRow_below raw hfinite hx
  exact ⟨⟨y, hy⟩, minRow_antichain raw⟩

theorem minRow_eq_singleton_bottom {Exit : Type*}
    (raw : Set (Outcome Exit)) (hb : Outcome.bottom ∈ raw) :
    MinRow raw = ({Outcome.bottom} : Set (Outcome Exit)) := by
  ext x
  constructor
  · intro hx
    have hxb : OutcomeLE x Outcome.bottom := hx.2 Outcome.bottom hb trivial
    have heq := outcomeLE_antisymm hxb (show OutcomeLE Outcome.bottom x from trivial)
    simpa using heq
  · intro hx
    have heq : x = Outcome.bottom := by simpa using hx
    subst x
    exact ⟨hb, fun y _ _ => trivial⟩

theorem rowLE_refl {Exit : Type*} (r : Set (Outcome Exit)) : RowLE r r := by
  intro x hx
  exact ⟨x, hx, outcomeLE_refl x⟩

theorem rowLE_trans {Exit : Type*} {r s t : Set (Outcome Exit)}
    (hrs : RowLE r s) (hst : RowLE s t) : RowLE r t := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hst x hx
  obtain ⟨z, hz, hzy⟩ := hrs y hy
  exact ⟨z, hz, outcomeLE_trans hzy hyx⟩

theorem rowLE_iff_upset {Exit : Type*} (r s : Set (Outcome Exit)) :
    RowLE r s ↔ OutcomeUpset s ⊆ OutcomeUpset r := by
  constructor
  · intro hrs x hx
    obtain ⟨y, hy, hyx⟩ := hx
    obtain ⟨z, hz, hzy⟩ := hrs y hy
    exact ⟨z, hz, outcomeLE_trans hzy hyx⟩
  · intro hup x hx
    exact hup ⟨x, hx, outcomeLE_refl x⟩

theorem rowLE_antisymm {Exit : Type*} {r s : Set (Outcome Exit)}
    (hr : SourceAntichain r) (hs : SourceAntichain s)
    (hrs : RowLE r s) (hsr : RowLE s r) : r = s := by
  have subset_of_mutual : ∀ {a b : Set (Outcome Exit)},
      SourceAntichain a → RowLE a b → RowLE b a → a ⊆ b := by
    intro a b ha hab hba x hx
    obtain ⟨y, hy, hyx⟩ := hba x hx
    obtain ⟨z, hz, hzy⟩ := hab y hy
    have hzx : z = x := ha z hz x hx (outcomeLE_trans hzy hyx)
    have hxy : OutcomeLE x y := by simpa [hzx] using hzy
    have hy_eq : y = x := outcomeLE_antisymm hyx hxy
    simpa [hy_eq] using hy
  exact Set.Subset.antisymm (subset_of_mutual hr hrs hsr)
    (subset_of_mutual hs hsr hrs)

theorem profileLE_refl {Start Exit : Type*} (p : Profile Start Exit) :
    ProfileLE p p := fun i => rowLE_refl (p i)

theorem profileLE_trans {Start Exit : Type*} {p q r : Profile Start Exit}
    (hpq : ProfileLE p q) (hqr : ProfileLE q r) : ProfileLE p r :=
  fun i => rowLE_trans (hpq i) (hqr i)

theorem profileLE_antisymm {Start Exit : Type*} {p q : Profile Start Exit}
    (hp : ∀ i, SourceAntichain (p i)) (hq : ∀ i, SourceAntichain (q i))
    (hpq : ProfileLE p q) (hqp : ProfileLE q p) : p = q := by
  funext i
  exact rowLE_antisymm (hp i) (hq i) (hpq i) (hqp i)

/-- `HistoryPolicy` is the *whole* history-strategy carrier supplied by an
adapter. This nested front maximizes separately at `i`; no common witness
for all starts is inserted, and no maximal profile pruning is done to J. -/
def EntranceOptimizedFront {HistoryPolicy Start Exit : Type*}
    (historyRows : HistoryPolicy → Profile Start Exit) (i : Start) :
    Set (Set (Outcome Exit)) :=
  {r | (∃ σ, historyRows σ i = r) ∧
    ∀ s, (∃ τ, historyRows τ i = s) → RowLE r s → RowLE s r}

def OptimizedArenaFront {V Exit Start : Type*} (A : Arena V Exit)
    (starts : Start → V) (i : Start) : Set (Set (Outcome Exit)) :=
  EntranceOptimizedFront (fun σ : EvenHistoryStrategy A =>
    HistoryPolicyProfile A σ starts) i

theorem jointAttainable_empty {V Exit Start : Type*}
    (A : Arena V Exit) (starts : Start → V) :
    JointAttainable A starts ∅ = ∅ := by
  ext p
  simp [JointAttainable]

theorem jointAttainable_one_common_policy {V Exit Start : Type*}
    (A : Arena V Exit) (starts : Start → V) (admitted : Set (EvenPolicy A))
    {p : Profile Start Exit} (hp : p ∈ JointAttainable A starts admitted) :
    ∃ σ ∈ admitted, ∀ i, MinRow (RawOutcomes A σ (starts i)) = p i := by
  obtain ⟨σ, hσ, heq⟩ := hp
  exact ⟨σ, hσ, fun i => congrFun heq i⟩

end Partials.Parity
