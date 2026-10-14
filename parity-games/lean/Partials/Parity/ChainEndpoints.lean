import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Partials.Parity.Model

/-! Blind R7 source for compilation.tex, P1-L03 (lines 311--356).
All interval arithmetic below is integral. No numerical menu is enumerated.
The recurrence-realization and finite minimum adapter at the end are explicit
unfinished duties, not trusted axioms or assumptions of compiler exactness. -/

namespace Partials.Parity.CompilerSource

structure IntervalChain where
  last : Nat
  positive : 0 < last
  lower : Nat → Int
  upper : Nat → Int
  menus : ∀ i, i ≤ last → 1 ≤ lower i ∧ lower i ≤ upper i

def LegalChain (C : IntervalChain) (q : Nat → Int) : Prop :=
  (∀ i, i ≤ C.last → C.lower i ≤ q i ∧ q i ≤ C.upper i) ∧
  ∀ i, i < C.last → q (i + 1) + 1 ≤ q i

/-- Only indices through `last` have mathematical meaning. -/
def LowerEnvelope (C : IntervalChain) (g : Nat → Int) : Prop :=
  g C.last = C.lower C.last ∧
  ∀ i, i < C.last → g i = max (C.lower i) (g (i + 1) + 1)

def EnvelopeFeasible (C : IntervalChain) (g : Nat → Int) : Prop :=
  ∀ i, i ≤ C.last → g i ≤ C.upper i

/-- This is the paper's endpoint conjunction, with `t ≤ H` written as
all its finite upper bounds. This formulation avoids a hidden minimum. -/
def EndpointRelation (C : IntervalChain) (g : Nat → Int) (s t : Int) : Prop :=
  EnvelopeFeasible C g ∧ g 0 ≤ s ∧ s ≤ C.upper 0 ∧
  C.lower C.last ≤ t ∧
  (∀ i, i ≤ C.last → t + (C.last : Int) - (i : Int) ≤ C.upper i) ∧
  t + (C.last : Int) ≤ s

def EndpointRealized (C : IntervalChain) (s t : Int) : Prop :=
  ∃ q, LegalChain C q ∧ q 0 = s ∧ q C.last = t

/-- Backward recurrence has exactly `n+1` interval accesses. -/
def backwardEnvelope (L : Nat → Int) : Nat → Nat → Int
  | 0, i => L i
  | n + 1, i => max (L i) (backwardEnvelope L n (i + 1) + 1)

def computedEnvelope (C : IntervalChain) (i : Nat) : Int :=
  backwardEnvelope C.lower (C.last - i) i

theorem computedEnvelope_recurrence (C : IntervalChain) :
    LowerEnvelope C (computedEnvelope C) := by
  constructor
  · simp [computedEnvelope, backwardEnvelope]
  · intro i hi
    have hsub : C.last - i = (C.last - (i + 1)) + 1 := by omega
    unfold computedEnvelope
    rw [hsub]
    rfl

theorem envelope_lower (C : IntervalChain) (g : Nat → Int)
    (hg : LowerEnvelope C g) {i : Nat} (hi : i ≤ C.last) :
    C.lower i ≤ g i := by
  by_cases heq : i = C.last
  · subst i
    rw [hg.1]
  · have hlt : i < C.last := by omega
    rw [hg.2 i hlt]
    exact le_max_left _ _

theorem envelope_step (C : IntervalChain) (g : Nat → Int)
    (hg : LowerEnvelope C g) {i : Nat} (hi : i < C.last) :
    g (i + 1) + 1 ≤ g i := by
  rw [hg.2 i hi]
  exact le_max_right _ _

theorem legal_drop (C : IntervalChain) (q : Nat → Int)
    (hq : LegalChain C q) :
    ∀ n i, i + n ≤ C.last → q (i + n) + (n : Int) ≤ q i := by
  intro n
  induction n with
  | zero => intro i hi; simp
  | succ n ih =>
      intro i hi
      have hi' : i < C.last := by omega
      have hnext : i + 1 + n ≤ C.last := by omega
      have htail := ih (i + 1) hnext
      have hstep := hq.2 i hi'
      have heq : i + 1 + n = i + (n + 1) := by omega
      rw [heq] at htail
      push_cast
      linarith

theorem envelope_majorized (C : IntervalChain) (g q : Nat → Int)
    (hg : LowerEnvelope C g) (hq : LegalChain C q) :
    ∀ i, i ≤ C.last → g i ≤ q i := by
  have hback : ∀ n i, i + n = C.last → g i ≤ q i := by
    intro n
    induction n with
    | zero =>
        intro i hi
        have heq : i = C.last := by omega
        subst i
        rw [hg.1]
        exact (hq.1 C.last le_rfl).1
    | succ n ih =>
        intro i hi
        have hlt : i < C.last := by omega
        have htail := ih (i + 1) (by omega)
        have hstep := hq.2 i hlt
        rw [hg.2 i hlt]
        apply max_le
        · exact (hq.1 i (by omega)).1
        · linarith
  intro i hi
  exact hback (C.last - i) i (by omega)

theorem endpoints_necessary (C : IntervalChain) (g q : Nat → Int)
    (hg : LowerEnvelope C g) (hq : LegalChain C q) :
    EndpointRelation C g (q 0) (q C.last) := by
  have hmajor := envelope_majorized C g q hg hq
  refine ⟨?_, hmajor 0 (by omega), (hq.1 0 (by omega)).2,
    (hq.1 C.last le_rfl).1, ?_, ?_⟩
  · intro i hi
    exact le_trans (hmajor i hi) (hq.1 i hi).2
  · intro i hi
    have hdrop := legal_drop C q hq (C.last - i) i (by omega)
    have hindex : i + (C.last - i) = C.last := by omega
    rw [hindex] at hdrop
    have hcast : ((C.last - i : Nat) : Int) = (C.last : Int) - (i : Int) := by omega
    rw [hcast] at hdrop
    linarith [(hq.1 i hi).2]
  · simpa using legal_drop C q hq C.last 0 (by omega)

/-- A single vector fills every original hub, including unreachable hubs. -/
def recoverChain (C : IntervalChain) (g : Nat → Int) (s t : Int)
    (i : Nat) : Int :=
  if i = 0 then s else max (g i) (t + (C.last : Int) - (i : Int))

theorem recoverChain_first (C : IntervalChain) (g : Nat → Int) (s t : Int) :
    recoverChain C g s t 0 = s := by simp [recoverChain]

theorem recoverChain_last (C : IntervalChain) (g : Nat → Int) (s t : Int)
    (hg : LowerEnvelope C g) (ht : C.lower C.last ≤ t) :
    recoverChain C g s t C.last = t := by
  have hne : C.last ≠ 0 := Nat.ne_of_gt C.positive
  simp [recoverChain, hne, hg.1, max_eq_right ht]

theorem recoveredChain_legal (C : IntervalChain) (g : Nat → Int) (s t : Int)
    (hg : LowerEnvelope C g) (he : EndpointRelation C g s t) :
    LegalChain C (recoverChain C g s t) := by
  rcases he with ⟨hfeas, hgs, hsU, htL, htU, hst⟩
  constructor
  · intro i hi
    by_cases hz : i = 0
    · subst i
      simp only [recoverChain, if_pos rfl]
      exact ⟨le_trans (envelope_lower C g hg (by omega)) hgs, hsU⟩
    · simp only [recoverChain, if_neg hz]
      exact ⟨le_trans (envelope_lower C g hg hi) (le_max_left _ _),
        max_le (hfeas i hi) (htU i hi)⟩
  · intro i hi
    have hnext : i + 1 ≠ 0 := by omega
    have henv := envelope_step C g hg hi
    by_cases hz : i = 0
    · subst i
      simp only [recoverChain, if_pos, if_neg hnext]
      rcases le_total (g (0 + 1)) (t + (C.last : Int) - ((0 + 1 : Nat) : Int)) with h | h
      · rw [max_eq_right h]
        norm_num
        linarith
      · rw [max_eq_left h]
        linarith
    · simp only [recoverChain, if_neg hz, if_neg hnext]
      have hleft := le_max_left (g i) (t + (C.last : Int) - (i : Int))
      have hright := le_max_right (g i) (t + (C.last : Int) - (i : Int))
      rcases le_total (g (i + 1)) (t + (C.last : Int) - ((i + 1 : Nat) : Int)) with h | h
      · rw [max_eq_right h]
        push_cast
        linarith
      · rw [max_eq_left h]
        linarith

theorem endpoint_exact_of_envelope (C : IntervalChain) (g : Nat → Int)
    (hg : LowerEnvelope C g) (s t : Int) :
    EndpointRealized C s t ↔ EndpointRelation C g s t := by
  constructor
  · rintro ⟨q, hq, hs, ht⟩
    have h := endpoints_necessary C g q hg hq
    simpa [hs, ht] using h
  · intro he
    exact ⟨recoverChain C g s t, recoveredChain_legal C g s t hg he,
      recoverChain_first C g s t,
      recoverChain_last C g s t hg he.2.2.2.1⟩

theorem computed_endpoint_exact (C : IntervalChain) (s t : Int) :
    EndpointRealized C s t ↔ EndpointRelation C (computedEnvelope C) s t :=
  endpoint_exact_of_envelope C (computedEnvelope C)
    (computedEnvelope_recurrence C) s t

theorem computed_envelope_legal (C : IntervalChain)
    (hfeas : EnvelopeFeasible C (computedEnvelope C)) :
    LegalChain C (computedEnvelope C) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    exact ⟨envelope_lower C _ (computedEnvelope_recurrence C) hi, hfeas i hi⟩
  · intro i hi
    exact envelope_step C _ (computedEnvelope_recurrence C) hi

theorem chain_feasibility_exact (C : IntervalChain) :
    (∃ q, LegalChain C q) ↔ EnvelopeFeasible C (computedEnvelope C) := by
  constructor
  · rintro ⟨q, hq⟩ i hi
    exact le_trans (envelope_majorized C _ q (computedEnvelope_recurrence C) hq i hi)
      (hq.1 i hi).2
  · intro hfeas
    exact ⟨computedEnvelope C, computed_envelope_legal C hfeas⟩

theorem le_fold_min_iff (values : List Int) (initial t : Int) :
    t ≤ values.foldr min initial ↔
      t ≤ initial ∧ ∀ c ∈ values, t ≤ c := by
  induction values with
  | nil => simp
  | cons a as ih =>
      change (t ≤ min a (as.foldr min initial)) ↔ _
      rw [le_min_iff, ih]
      constructor
      · rintro ⟨hta, hti, hall⟩
        refine ⟨hti, ?_⟩
        intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact hta
        · exact hall c hc
      · rintro ⟨hti, hall⟩
        exact ⟨hall a (by simp), hti, fun c hc => hall c (by simp [hc])⟩

def upperSlackEntries (C : IntervalChain) : List Int :=
  (List.range (C.last + 1)).map
    (fun i => C.upper i - ((C.last : Int) - (i : Int)))

/-- The initial value is the existing i=0 bound, so it adds no constraint
and makes the fold total without a fictitious infinity sentinel. -/
def computedUpperSlack (C : IntervalChain) : Int :=
  (upperSlackEntries C).foldr min (C.upper 0 - (C.last : Int))

theorem computedUpperSlack_exact (C : IntervalChain) (t : Int) :
    t ≤ computedUpperSlack C ↔ ∀ i, i ≤ C.last →
      t + (C.last : Int) - (i : Int) ≤ C.upper i := by
  unfold computedUpperSlack
  rw [le_fold_min_iff]
  constructor
  · rintro ⟨hfirst, hall⟩ i hi
    have hentry : C.upper i - ((C.last : Int) - (i : Int)) ∈
        upperSlackEntries C := by
      exact List.mem_map.mpr ⟨i, List.mem_range.mpr (by omega), rfl⟩
    have hbound := hall _ hentry
    linarith
  · intro hall
    constructor
    · have hzero := hall 0 (by omega)
      norm_num at hzero
      linarith
    · intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      have hi' : i ≤ C.last := by
        have hirange := List.mem_range.mp hi
        omega
      have hbound := hall i hi'
      linarith

def PaperEndpointRelation (C : IntervalChain) (s t : Int) : Prop :=
  EnvelopeFeasible C (computedEnvelope C) ∧
  computedEnvelope C 0 ≤ s ∧ s ≤ C.upper 0 ∧ C.lower C.last ≤ t ∧
  t ≤ computedUpperSlack C ∧ t + (C.last : Int) ≤ s

theorem paper_endpoint_exact (C : IntervalChain) (s t : Int) :
    EndpointRealized C s t ↔ PaperEndpointRelation C s t := by
  rw [computed_endpoint_exact]
  unfold EndpointRelation PaperEndpointRelation
  rw [computedUpperSlack_exact]

/-- The recurrence target is source-proved by computedEnvelope_recurrence.
Actual binary implementation/resource accounting remains separate. -/
def ComputedEnvelopeDuty : Prop :=
  ∀ C : IntervalChain, LowerEnvelope C (computedEnvelope C)

/-- Exact finite slack target; computedUpperSlack_exact instantiates it
with the concrete finite minimum, including h=1. -/
def UpperSlackDuty (C : IntervalChain) (H : Int) : Prop :=
  ∀ t, t ≤ H ↔ ∀ i, i ≤ C.last →
    t + (C.last : Int) - (i : Int) ≤ C.upper i

end Partials.Parity.CompilerSource
