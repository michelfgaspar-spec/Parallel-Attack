import Partials.ParityAlgorithms.PathPivot

/-! Concrete candidate ceiling, FIFO worklist and replay checker. All
computations below are source only. The least original answer is specified
independently by IsEvaluation; its completed-anchor membership is a retained
primitive duty, and is not inferred from successful rounded execution. -/
namespace Partials.ParityAlgorithms.Path

noncomputable def candidateDomain {n : Nat} (A : Arena n) (ell : Nat)
    (v : Fin n) : Finset Nat :=
  match A.priority v with
  | .one => insert 0 (insert ell (anchorDistances A v))
  | .two => {0, ell}

theorem candidateDomain_zero {n : Nat} (A : Arena n) (ell : Nat) (v : Fin n) :
    0 ∈ candidateDomain A ell v := by cases h : A.priority v <;> simp [candidateDomain, h]

theorem candidateDomain_top {n : Nat} (A : Arena n) (ell : Nat) (v : Fin n) :
    ell ∈ candidateDomain A ell v := by cases h : A.priority v <;> simp [candidateDomain, h]

theorem candidateDomain_at_most_four {n : Nat} (A : Arena n) (ell : Nat) (v : Fin n) :
    (candidateDomain A ell v).card ≤ 4 := by
  cases hp : A.priority v with
  | one =>
    have ha := anchorDistances_at_most_two A v
    have h1 := Finset.card_insert_le ell (anchorDistances A v)
    have h0 := Finset.card_insert_le 0 (insert ell (anchorDistances A v))
    simp only [candidateDomain, hp]; omega
  | two =>
    have hc := Finset.card_insert_le 0 ({ell} : Finset Nat)
    have he : ({ell} : Finset Nat).card = 1 := Finset.card_singleton ell
    simp only [candidateDomain, hp]; omega

def CandidateVector {n : Nat} (A : Arena n) (ell : Nat) (x : Vector n) : Prop :=
  ∀ v, x v ∈ candidateDomain A ell v

/-- Saturation makes the source function total on malformed raw inputs.
Within 0..ell it is exactly the paper's least candidate ceiling. -/
noncomputable def upperCandidates (D : Finset Nat) (ell t : Nat) : Finset Nat :=
  (insert ell D).filter (min t ell ≤ ·)

theorem upperCandidates_nonempty (D : Finset Nat) (ell t : Nat) :
    (upperCandidates D ell t).Nonempty := by
  exact ⟨ell, by simp [upperCandidates, Nat.min_le_right]⟩

noncomputable def ceilRank (D : Finset Nat) (ell t : Nat) : Nat :=
  (upperCandidates D ell t).min' (upperCandidates_nonempty D ell t)

theorem ceilRank_member (D : Finset Nat) (ell t : Nat) :
    ceilRank D ell t ∈ insert ell D := by
  have h := Finset.min'_mem (upperCandidates D ell t) (upperCandidates_nonempty D ell t)
  exact (Finset.mem_filter.mp h).1

theorem ceilRank_extensive (D : Finset Nat) (ell t : Nat) (ht : t ≤ ell) :
    t ≤ ceilRank D ell t := by
  have h := Finset.min'_mem (upperCandidates D ell t) (upperCandidates_nonempty D ell t)
  have hb : min t ell ≤ ceilRank D ell t := (Finset.mem_filter.mp h).2
  simpa [min_eq_left ht] using hb

theorem ceilRank_le_candidate (D : Finset Nat) (ell t c : Nat)
    (hc : c ∈ insert ell D) (htc : t ≤ c) : ceilRank D ell t ≤ c := by
  apply Finset.min'_le
  apply Finset.mem_filter.mpr
  exact ⟨hc, (min_le_left t ell).trans htc⟩

theorem ceilRank_fixes_candidate (D : Finset Nat) (ell c : Nat)
    (hc : c ∈ insert ell D) (hb : c ≤ ell) : ceilRank D ell c = c := by
  exact Nat.le_antisymm (ceilRank_le_candidate D ell c c hc (le_refl c))
    (ceilRank_extensive D ell c hb)

theorem ceilRank_monotone (D : Finset Nat) (ell : Nat) {t u : Nat}
    (htu : t ≤ u) : ceilRank D ell t ≤ ceilRank D ell u := by
  have hm := Finset.min'_mem (upperCandidates D ell u) (upperCandidates_nonempty D ell u)
  have hc := (Finset.mem_filter.mp hm).1
  have hb := (Finset.mem_filter.mp hm).2
  apply Finset.min'_le
  apply Finset.mem_filter.mpr
  exact ⟨hc, (min_le_min htu (le_refl ell)).trans hb⟩

noncomputable def roundedH {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) (x : Vector n) (v : Fin n) : Nat :=
  ceilRank (candidateDomain A ell v) ell (originalF ell τ x v)

theorem roundedH_inflationary {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) {x : Vector n} (hx : ValidVector ell x) (v : Fin n) :
    x v ≤ roundedH ell τ x v :=
  (originalF_inflationary ell τ x v).trans
    (ceilRank_extensive _ ell _ (originalF_bounded ell τ hx v))

theorem roundedH_candidate {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) (x : Vector n) (v : Fin n) :
    roundedH ell τ x v ∈ candidateDomain A ell v := by
  have h := ceilRank_member (candidateDomain A ell v) ell (originalF ell τ x v)
  simpa only [roundedH, Finset.insert_eq_of_mem (candidateDomain_top A ell v)] using h

/-- Local stability/monotonicity bridge proved immediately below from
the actual finite selected minima. No evaluator correctness field exists. -/
structure OriginalCoordinateBridge {n : Nat} (A : Arena n) (ell : Nat)
    (τ : OddPolicy A) : Prop where
  monotone : ∀ x y, ValidVector ell x → ValidVector ell y →
    VectorLE x y → ∀ v, originalF ell τ x v ≤ originalF ell τ y v
  fixed_iff : ∀ x, ValidVector ell x →
    ((∀ v, originalF ell τ x v = x v) ↔ Feasible ell τ x)

def originalCoordinateBridge {n : Nat} (A : Arena n) (ell : Nat)
    (τ : OddPolicy A) : OriginalCoordinateBridge A ell τ where
  monotone x y _ _ hxy v := originalF_monotone ell τ hxy v
  fixed_iff x hx := original_fixed_iff_feasible ell τ hx

theorem rounded_step_dominated {n : Nat} {A : Arena n} {ell : Nat}
    {τ : OddPolicy A} (B : OriginalCoordinateBridge A ell τ)
    {floor z x : Vector n} (hz : IsEvaluation ell τ floor z)
    (hzC : CandidateVector A ell z) (hx : ValidVector ell x)
    (hxz : VectorLE x z) (v : Fin n) : roundedH ell τ x v ≤ z v := by
  have hmono := B.monotone x z hx hz.1 hxz v
  have hfixed := (B.fixed_iff z hz.1).mpr hz.2.2.1 v
  apply ceilRank_le_candidate
  · exact Finset.mem_insert_of_mem (hzC v)
  · exact hmono.trans (le_of_eq hfixed)

theorem stable_rounded_is_original {n : Nat} {A : Arena n} {ell : Nat}
    {τ : OddPolicy A} {x : Vector n} (hx : ValidVector ell x)
    (hs : ∀ v, roundedH ell τ x v = x v) :
    ∀ v, originalF ell τ x v = x v := by
  intro v
  have hle := ceilRank_extensive (candidateDomain A ell v) ell
    (originalF ell τ x v) (originalF_bounded ell τ hx v)
  exact Nat.le_antisymm (hle.trans (le_of_eq (hs v)))
    (originalF_inflationary ell τ x v)

def enqueueOnce {n : Nat} (queue : List (Fin n)) (v : Fin n) : List (Fin n) :=
  if v ∈ queue then queue else queue ++ [v]

def notify {n : Nat} (A : Arena n) (queue : List (Fin n)) (v : Fin n) : List (Fin n) :=
  ((List.finRange n).filter (fun u => decide (u ≠ v ∧ Edge A u v))).foldl enqueueOnce
    (enqueueOnce queue v)

structure WorkState (n : Nat) where
  ranks : Vector n
  queue : List (Fin n)
  /- A list of strict coordinate updates is sufficient as certificate; the
  queue need not be emitted or trusted by its checker. -/
  changes : List (Fin n × Nat)

noncomputable def workStep {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) (s : WorkState n) : WorkState n :=
  match s.queue with
  | [] => s
  | v :: rest =>
    let t := roundedH ell τ s.ranks v
    if s.ranks v < t then
      ⟨replace s.ranks v t, notify A rest v, s.changes ++ [(v, t)]⟩
    else ⟨s.ranks, rest, s.changes⟩

/-- Explicit fuel permits source definition without using the desired time
bound as a termination oracle. An exhausted result is reported as failure.
The primitive queue accounting must show 10*n+1 fuel suffices on reachable
floors; it is not silently asserted by this definition. -/
noncomputable def runWork {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) : Nat → WorkState n → Option (WorkState n)
  | 0, s => if s.queue.isEmpty then some s else none
  | fuel + 1, s => if s.queue.isEmpty then some s else
      runWork ell τ fuel (workStep ell τ s)

noncomputable def roundedWorklist {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) (floor : Vector n) : Option (WorkState n) :=
  runWork ell τ (10 * n + 1) ⟨floor, List.finRange n, []⟩

/-- Logical accepted trace gives exactly the concrete checker comparisons.
It deliberately has no queue transcript or floor-reachability assertion. -/
inductive Replay {n : Nat} {A : Arena n} (ell : Nat) (τ : OddPolicy A) :
    Vector n → List (Fin n × Nat) → Vector n → Prop where
  | nil (x) : Replay ell τ x [] x
  | cons (x y v t rest) :
      t = roundedH ell τ x v → x v < t →
      Replay ell τ (replace x v t) rest y →
      Replay ell τ x ((v, t) :: rest) y

noncomputable def replayCheck {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) : Vector n → List (Fin n × Nat) → Option (Vector n)
  | x, [] => some x
  | x, (v,t) :: rest =>
    if t ≤ ell ∧ t = roundedH ell τ x v ∧ x v < t then
      replayCheck ell τ (replace x v t) rest
    else none

structure Certificate (n : Nat) where
  final : Vector n
  changes : List (Fin n × Nat)

noncomputable def certificateCheck {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) (floor : Vector n) (c : Certificate n) : Bool := by
  classical
  exact decide (c.changes.length ≤ 3 * n ∧ ValidVector ell floor ∧
    ValidVector ell c.final ∧ replayCheck ell τ floor c.changes = some c.final ∧
    ∀ v, originalF ell τ c.final v = c.final v)

theorem replayCheck_sound {n : Nat} {A : Arena n} (ell : Nat) (τ : OddPolicy A)
    (steps : List (Fin n × Nat)) : ∀ x y,
    replayCheck ell τ x steps = some y → Replay ell τ x steps y := by
  induction steps with
  | nil =>
    intro x y h
    have heq : x = y := Option.some.inj h
    subst y; exact Replay.nil x
  | cons step rest ih =>
    rcases step with ⟨v, t⟩
    intro x y h
    simp only [replayCheck] at h
    split at h
    · rename_i htest
      exact Replay.cons x y v t rest htest.2.1 htest.2.2
        (ih (replace x v t) y h)
    · contradiction

theorem replay_dominated {n : Nat} {A : Arena n} {ell : Nat} {τ : OddPolicy A}
    (B : OriginalCoordinateBridge A ell τ) {floor z x y : Vector n}
    (hz : IsEvaluation ell τ floor z) (hzC : CandidateVector A ell z)
    {steps : List (Fin n × Nat)} (htrace : Replay ell τ x steps y)
    (hx : ValidVector ell x) (hfloor : VectorLE floor x) (hxz : VectorLE x z) :
    ValidVector ell y ∧ VectorLE floor y ∧ VectorLE y z := by
  induction htrace with
  | nil x => exact ⟨hx, hfloor, hxz⟩
  | cons x y v t rest ht hstrict hrest ih =>
    have htbound : t ≤ z v := by
      rw [ht]; exact rounded_step_dominated B hz hzC hx hxz v
    have hvalid : ValidVector ell (replace x v t) := by
      intro u; by_cases hu : u = v
      · subst u; simpa [replace, ValidRank] using htbound.trans (hz.1 v)
      · simpa [replace, Function.update, hu] using hx u
    have hlow : VectorLE floor (replace x v t) := by
      intro u; by_cases hu : u = v
      · subst u; simpa [replace] using (hfloor v).trans (le_of_lt hstrict)
      · simpa [replace, Function.update, hu] using hfloor u
    have hhigh : VectorLE (replace x v t) z := by
      intro u; by_cases hu : u = v
      · subst u; simpa [replace] using htbound
      · simpa [replace, Function.update, hu] using hxz u
    exact ih hvalid hlow hhigh

theorem accepted_trace_exact {n : Nat} {A : Arena n} {ell : Nat} {τ : OddPolicy A}
    (B : OriginalCoordinateBridge A ell τ) {floor z supplied endpoint : Vector n}
    (hz : IsEvaluation ell τ floor z) (hzC : CandidateVector A ell z)
    (hf : ValidVector ell floor) {steps : List (Fin n × Nat)}
    (htrace : Replay ell τ floor steps endpoint) (heq : supplied = endpoint)
    (hfixed : ∀ v, originalF ell τ endpoint v = endpoint v) : supplied = z := by
  obtain ⟨hend, hfloor, hdom⟩ := replay_dominated B hz hzC htrace hf
    (fun _ => le_refl _) hz.2.1
  have hfeas := (B.fixed_iff endpoint hend).mp hfixed
  have hleast := hz.2.2.2 endpoint hend hfloor hfeas
  rw [heq]
  funext v; exact Nat.le_antisymm (hdom v) (hleast v)

/-- Concrete Bool checker soundness. Its input does not contain z: z is an
independently characterized original least answer in the proof. Its
candidate membership follows only after the outstanding original completed
anchor proof, not from an accepted certificate. Reachability is deliberately
not certified by the Boolean checker. -/
theorem certificateCheck_exact_under_original_candidates {n : Nat}
    {A : Arena n} {ell : Nat} {τ : OddPolicy A} {floor z : Vector n}
    (hz : IsEvaluation ell τ floor z) (hzC : CandidateVector A ell z)
    (c : Certificate n) (hcheck : certificateCheck ell τ floor c = true) : c.final = z := by
  classical
  have hc : c.changes.length ≤ 3 * n ∧ ValidVector ell floor ∧
      ValidVector ell c.final ∧ replayCheck ell τ floor c.changes = some c.final ∧
      ∀ v, originalF ell τ c.final v = c.final v := of_decide_eq_true hcheck
  have htrace := replayCheck_sound ell τ c.changes floor c.final hc.2.2.2.1
  exact accepted_trace_exact (originalCoordinateBridge A ell τ) hz hzC hc.2.1
    htrace rfl hc.2.2.2.2

/-- Explicit endpoint equality is indispensable: the singleton priority-two
loop permits both zero and TOP as feasible labels. A zero replay must not
certify an unrelated supplied TOP vector. -/
theorem empty_replay_endpoint {n : Nat} {A : Arena n} {ell : Nat} {τ : OddPolicy A}
    {floor endpoint : Vector n} (h : Replay ell τ floor [] endpoint) : endpoint = floor := by
  cases h; rfl

end Partials.ParityAlgorithms.Path
