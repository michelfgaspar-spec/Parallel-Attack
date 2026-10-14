import Mathlib.Data.Finset.Union
import Mathlib.Data.Finset.Range
import Mathlib.Tactic.Push
import Partials.Parity.HistorySemantics
import Partials.Parity.Rows

/-! Finite first-exit and infinite finite-alphabet semantics, and the
departing-vertex source edge encoding in P1-L01/P2-L1. This file does not
silently change local exits into global stops or identify original choices.
All source is uncompiled and all tactic text is unevaluated. -/

namespace Partials.Parity

def PriorityRecurs (f : Nat → Nat) (p : Nat) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ f n = p

def GreatestPriorityRecurs (f : Nat → Nat) (p : Nat) : Prop :=
  PriorityRecurs f p ∧ ∀ q, PriorityRecurs f q → q ≤ p

theorem priorityRecurs_tail_iff (f : Nat → Nat) (p offset : Nat) :
    PriorityRecurs (fun n => f (n + offset)) p ↔ PriorityRecurs f p := by
  constructor
  · intro h N
    obtain ⟨n, hn, heq⟩ := h N
    exact ⟨n + offset, by omega, heq⟩
  · intro h N
    obtain ⟨n, hn, heq⟩ := h (N + offset)
    refine ⟨n - offset, by omega, ?_⟩
    have hcancel : n - offset + offset = n := by omega
    simpa only [hcancel] using heq

/-- An explicit finite-alphabet induction: if the largest allowed label
does not recur, remove it after its last occurrence and recurse on the
shifted tail. No eventual-periodicity premise is used. -/
theorem bounded_largest_recurring (B : Nat) :
    ∀ f : Nat → Nat, (∀ n, f n ≤ B) →
      ∃ p, GreatestPriorityRecurs f p := by
  induction B with
  | zero =>
    intro f hb
    refine ⟨0, ?_, ?_⟩
    · intro N
      exact ⟨N, le_refl N, by have := hb N; omega⟩
    · intro q hq
      obtain ⟨n, _, hn⟩ := hq 0
      have := hb n
      omega
  | succ B ih =>
    intro f hb
    by_cases htop : PriorityRecurs f (B + 1)
    · refine ⟨B + 1, htop, ?_⟩
      intro q hq
      obtain ⟨n, _, hn⟩ := hq 0
      have := hb n
      omega
    · unfold PriorityRecurs at htop
      push_neg at htop
      obtain ⟨N, hN⟩ := htop
      have htail : ∀ n, f (n + N) ≤ B := by
        intro n
        have hbound := hb (n + N)
        have hneq := hN (n + N) (by omega)
        omega
      obtain ⟨p, hp, hgreatest⟩ := ih (fun n => f (n + N)) htail
      refine ⟨p, (priorityRecurs_tail_iff f p N).mp hp, ?_⟩
      intro q hq
      exact hgreatest q ((priorityRecurs_tail_iff f q N).mpr hq)

theorem largestRecurring_unique {V Exit : Type*} {A : Arena V Exit}
    {ρ : Nat → V} {p q : Nat}
    (hp : LargestRecurring A ρ p) (hq : LargestRecurring A ρ q) : p = q := by
  exact Nat.le_antisymm (hq.2 p hp.1) (hp.2 q hq.1)

def BoundedPriority {V Exit : Type*} (A : Arena V Exit) (B : Nat) : Prop :=
  ∀ v, A.priority v ≤ B

theorem boundedPriority_has_largestRecurring {V Exit : Type*}
    (A : Arena V Exit) (B : Nat) (hb : BoundedPriority A B) (ρ : Nat → V) :
    ∃ p, LargestRecurring A ρ p := by
  exact bounded_largest_recurring B (fun n => A.priority (ρ n)) (fun n => hb (ρ n))

theorem finiteArena_boundedPriority {V Exit : Type*} [Fintype V]
    (A : Arena V Exit) : ∃ B, BoundedPriority A B := by
  classical
  refine ⟨Finset.univ.sup A.priority, ?_⟩
  intro v
  exact Finset.le_sup (Finset.mem_univ v)

theorem firstExit_unique {V Exit : Type*} {A : Arena V Exit}
    {ρ : Nat → V} {n m : Nat} {o o' : Exit} {p q : Nat}
    (hn : FirstExit A ρ n o p) (hm : FirstExit A ρ m o' q) :
    n = m ∧ o = o' ∧ p = q := by
  have hnm : n = m := by
    by_cases hlt : n < m
    · exact False.elim (hm.2.1 n hlt o hn.1)
    · by_cases hgt : m < n
      · exact False.elim (hn.2.1 m hgt o' hm.1)
      · omega
  subst m
  have hoo : o = o' := A.exit_injective (hn.1.symm.trans hm.1)
  exact ⟨rfl, hoo, hn.2.2.trans hm.2.2.symm⟩

theorem finiteOutcome_unique {V Exit : Type*} {A : Arena V Exit}
    {ρ : Nat → V} {x y : Outcome Exit}
    (hx : FiniteOutcome A ρ x) (hy : FiniteOutcome A ρ y) : x = y := by
  obtain ⟨n, o, p, hn, rfl⟩ := hx
  obtain ⟨m, o', q, hm, rfl⟩ := hy
  obtain ⟨_, ho, hp⟩ := firstExit_unique hn hm
  simp only [ho, hp]

theorem finite_infinite_disjoint {V Exit : Type*} {A : Arena V Exit}
    {ρ : Nat → V} {x y : Outcome Exit}
    (hx : FiniteOutcome A ρ x) (hy : InfiniteOutcome A ρ y) : False := by
  obtain ⟨n, o, p, hn, _⟩ := hx
  exact hy.1 n o hn.1

noncomputable def policyOrbit {V Exit : Type*} {A : Arena V Exit}
    (σ : EvenPolicy A) (start : V) : Nat → V
  | 0 => start
  | n + 1 => policySuccessor σ (policyOrbit σ start n)

theorem policyOrbit_compatible {V Exit : Type*} {A : Arena V Exit}
    (σ : EvenPolicy A) (start : V) : Compatible A σ (policyOrbit σ start) := by
  intro n
  exact policySuccessor_selected σ (policyOrbit σ start n)

/-- Totality constructs a selected path; least exit arrival or bounded
recurrence then constructs its outcome. Raw nonemptiness is a consequence. -/
theorem rawOutcomes_nonempty_of_bound {V Exit : Type*}
    (A : Arena V Exit) (σ : EvenPolicy A) (start : V)
    (B : Nat) (hb : BoundedPriority A B) : (RawOutcomes A σ start).Nonempty := by
  classical
  let ρ := policyOrbit σ start
  have hc : Compatible A σ ρ := policyOrbit_compatible σ start
  by_cases hexit : ∃ n, ∃ o, ρ n = A.exitVertex o
  · let n := Nat.find hexit
    obtain ⟨o, ho⟩ := Nat.find_spec hexit
    let p := (Finset.range (n + 1)).sup (fun k => A.priority (ρ k))
    have hfirst : FirstExit A ρ n o p := by
      refine ⟨ho, ?_, rfl⟩
      intro k hk o' hko
      have hnk : n ≤ k := Nat.find_min' hexit ⟨o', hko⟩
      omega
    exact ⟨Outcome.halt o p, ρ, rfl, hc, Or.inl ⟨n, o, p, hfirst, rfl⟩⟩
  · have hno : ∀ n o, ρ n ≠ A.exitVertex o := by
      intro n o ho
      exact hexit ⟨n, o, ho⟩
    obtain ⟨p, hp⟩ := boundedPriority_has_largestRecurring A B hb ρ
    by_cases heven : p % 2 = 0
    · exact ⟨Outcome.top, ρ, rfl, hc, Or.inr ⟨hno, p, hp, Or.inl ⟨heven, rfl⟩⟩⟩
    · have hodd : p % 2 = 1 := by omega
      exact ⟨Outcome.bottom, ρ, rfl, hc, Or.inr ⟨hno, p, hp, Or.inr ⟨hodd, rfl⟩⟩⟩

noncomputable def boundedOutcomeDomain {Exit : Type*} [Fintype Exit]
    (B : Nat) : Finset (Outcome Exit) := by
  classical
  exact {Outcome.bottom, Outcome.top} ∪
    Finset.univ.biUnion (fun o => (Finset.range (B + 1)).image (Outcome.halt o))

theorem finiteOutcome_priority_bound {V Exit : Type*} {A : Arena V Exit}
    {ρ : Nat → V} {n : Nat} {o : Exit} {p B : Nat}
    (hb : BoundedPriority A B) (he : FirstExit A ρ n o p) : p ≤ B := by
  rw [he.2.2]
  apply Finset.sup_le
  intro k _
  exact hb (ρ k)

theorem rawOutcomes_finite_of_bound {V Exit : Type*} [Fintype Exit]
    (A : Arena V Exit) (σ : EvenPolicy A) (start : V)
    (B : Nat) (hb : BoundedPriority A B) : (RawOutcomes A σ start).Finite := by
  classical
  apply (boundedOutcomeDomain (Exit := Exit) B).finite_toSet.subset
  intro out hout
  obtain ⟨ρ, _, _, hfinite | hinfinite⟩ := hout
  · obtain ⟨n, o, p, he, rfl⟩ := hfinite
    have hp : p < B + 1 := by
      have := finiteOutcome_priority_bound hb he
      omega
    simp [boundedOutcomeDomain, hp]
  · obtain ⟨_, p, _, heven | hodd⟩ := hinfinite
    · rcases heven with ⟨_, rfl⟩
      simp [boundedOutcomeDomain]
    · rcases hodd with ⟨_, rfl⟩
      simp [boundedOutcomeDomain]

theorem finiteArena_policyRows {V Exit Start : Type*}
    [Fintype V] [Fintype Exit] (A : Arena V Exit)
    (σ : EvenPolicy A) (starts : Start → V) :
    ∀ i, NonemptyRow (PolicyProfile A σ starts i) := by
  obtain ⟨B, hb⟩ := finiteArena_boundedPriority A
  intro i
  exact finite_minRow_nonempty (RawOutcomes A σ (starts i))
    (rawOutcomes_finite_of_bound A σ (starts i) B hb)
    (rawOutcomes_nonempty_of_bound A σ (starts i) B hb)

/-- Edge label on the actual departing vertex, not on the arriving target. -/
def DepartingPriority {V Exit : Type*} (A : Arena V Exit) (ρ : Nat → V)
    (n : Nat) : Nat := A.priority (ρ n)

def EdgePrefixMaximum {V Exit : Type*} (A : Arena V Exit)
    (ρ : Nat → V) (n : Nat) : Nat :=
  (Finset.range n).sup (DepartingPriority A ρ)

theorem departing_firstExit_maximum {V Exit : Type*} {A : Arena V Exit}
    {ρ : Nat → V} {n : Nat} {o : Exit} {p : Nat}
    (he : FirstExit A ρ n o p) : p = EdgePrefixMaximum A ρ n := by
  have hzero : A.priority (ρ n) = 0 := by rw [he.1, A.exit_zero]
  rw [he.2.2, Finset.range_add_one, Finset.sup_insert]
  simp [EdgePrefixMaximum, hzero]
  rfl

theorem departing_recurs_iff {V Exit : Type*} (A : Arena V Exit)
    (ρ : Nat → V) (p : Nat) :
    PriorityRecurs (DepartingPriority A ρ) p ↔ Recurs A ρ p := Iff.rfl

theorem departing_largest_iff {V Exit : Type*} (A : Arena V Exit)
    (ρ : Nat → V) (p : Nat) :
    GreatestPriorityRecurs (DepartingPriority A ρ) p ↔ LargestRecurring A ρ p := Iff.rfl

/-- Alternate zero original vertices with distinct forced priority arms. -/
def SubdivisionLabels (f : Nat → Nat) (n : Nat) : Nat :=
  if n % 2 = 0 then 0 else f (n / 2)

theorem subdivision_nonzero_recurs (f : Nat → Nat) {p : Nat} (hp : 0 < p) :
    PriorityRecurs (SubdivisionLabels f) p ↔ PriorityRecurs f p := by
  constructor
  · intro h N
    obtain ⟨n, hn, heq⟩ := h (2 * N)
    have hodd : n % 2 ≠ 0 := by
      intro hz
      simp [SubdivisionLabels, hz] at heq
      omega
    refine ⟨n / 2, by omega, ?_⟩
    simpa [SubdivisionLabels, hodd] using heq
  · intro h N
    obtain ⟨n, hn, heq⟩ := h N
    refine ⟨2 * n + 1, by omega, ?_⟩
    have hmod : (2 * n + 1) % 2 = 1 := by omega
    have hdiv : (2 * n + 1) / 2 = n := by omega
    simp [SubdivisionLabels, hmod, hdiv, heq]

theorem subdivision_zero_recurs (f : Nat → Nat) :
    PriorityRecurs (SubdivisionLabels f) 0 := by
  intro N
  refine ⟨2 * N, by omega, ?_⟩
  have hmod : (2 * N) % 2 = 0 := by omega
  simp [SubdivisionLabels, hmod]

theorem subdivision_largest (f : Nat → Nat) {p : Nat}
    (hp : GreatestPriorityRecurs f p) :
    GreatestPriorityRecurs (SubdivisionLabels f) p := by
  constructor
  · by_cases hz : p = 0
    · subst p
      exact subdivision_zero_recurs f
    · exact (subdivision_nonzero_recurs f (by omega)).mpr hp.1
  · intro q hq
    by_cases hz : q = 0
    · omega
    · exact hp.2 q ((subdivision_nonzero_recurs f (by omega)).mp hq)

/-- Unfinished finite fold for forced-arm subdivision. This names the
concrete arithmetic/Finset equality, not all-history outcome correspondence. -/
def SubdivisionFiniteFoldDuty : Prop :=
  ∀ (f : Nat → Nat) (n : Nat),
    (Finset.range (2 * n + 1)).sup (SubdivisionLabels f) =
      (Finset.range n).sup f

/-- Unfinished graph adapter: establish forced-arm expansion/contraction of
compatible histories beginning at original vertices. Original positions have
time 2*n; only the pre-exit steps use inserted arms. After a global exit the
expanded history stays at that same absorbing sink, including exit starts.
Priority transport alone cannot certify these physical graph facts. -/
def ForcedArmHistoryAdapterDuty {V W Exit : Type*}
    (source : Arena V Exit) (expanded : Arena W Exit)
    (sourcePolicy : OriginalEvenPolicy source)
    (expandedPolicy : OriginalEvenPolicy expanded)
    (originalVertex : V → W)
    (expand : (Nat → V) → Nat → W)
    (contract : (Nat → W) → Nat → V) : Prop :=
  Function.Injective originalVertex ∧
  (∀ o, originalVertex (source.exitVertex o) = expanded.exitVertex o) ∧
  (∀ ρ, Compatible source (canonicalPolicy sourcePolicy) ρ →
    Compatible expanded (canonicalPolicy expandedPolicy) (expand ρ)) ∧
  (∀ ρ, Compatible source (canonicalPolicy sourcePolicy) ρ →
    ∀ n, expand ρ (2 * n) = originalVertex (ρ n)) ∧
  (∀ η, (∃ v, η 0 = originalVertex v) →
    Compatible expanded (canonicalPolicy expandedPolicy) η →
    Compatible source (canonicalPolicy sourcePolicy) (contract η)) ∧
  (∀ ρ, Compatible source (canonicalPolicy sourcePolicy) ρ →
    contract (expand ρ) = ρ) ∧
  (∀ η, (∃ v, η 0 = originalVertex v) →
    Compatible expanded (canonicalPolicy expandedPolicy) η →
    expand (contract η) = η) ∧
  (∀ ρ, Compatible source (canonicalPolicy sourcePolicy) ρ →
    ∀ n o, ρ n = source.exitVertex o ↔
      expand ρ (2 * n) = expanded.exitVertex o) ∧
  (∀ ρ, Compatible source (canonicalPolicy sourcePolicy) ρ →
    ∀ n, (∀ k ≤ n, ∀ o, ρ k ≠ source.exitVertex o) →
      ∀ o, expand ρ (2 * n + 1) ≠ expanded.exitVertex o) ∧
  (∀ ρ, Compatible source (canonicalPolicy sourcePolicy) ρ →
    ∀ n o, ρ n = source.exitVertex o →
      ∀ m, 2 * n ≤ m → expand ρ m = expanded.exitVertex o)

/-- Completing forced arms is unique and creates no policy option. The
unfinished concrete encoding must exhibit this product equivalence and the
selected menu-to-arm move at each nonexit original Even source vertex.
The original global exit coordinate keeps its forced self-loop; that loop
is not replaced by a distinct fresh arm. Unreachable choices remain in e. -/
def ForcedArmOriginalPolicyDuty {V W Exit : Type*}
    (source : Arena V Exit) (expanded : Arena W Exit)
    (originalVertex : V → W) (edgeArm : V → V → W) : Prop :=
  ∃ e : OriginalEvenPolicy source ≃ OriginalEvenPolicy expanded,
    Function.Injective originalVertex ∧
    (∀ v, expanded.even (originalVertex v) = source.even v) ∧
    (∀ o, originalVertex (source.exitVertex o) = expanded.exitVertex o) ∧
    (∀ σ v (hv : source.even v = true),
      (∀ o, v ≠ source.exitVertex o) →
      ∃ he : expanded.even (originalVertex v) = true,
        (e σ).choose ⟨originalVertex v, he⟩ = edgeArm v (σ.choose ⟨v, hv⟩)) ∧
    (∀ σ o, (canonicalPolicy σ).move (source.exitVertex o) = source.exitVertex o ∧
      (canonicalPolicy (e σ)).move (expanded.exitVertex o) = expanded.exitVertex o) ∧
    (∀ σ o (ho : source.even (source.exitVertex o) = true),
      ∃ he : expanded.even (expanded.exitVertex o) = true,
        σ.choose ⟨source.exitVertex o, ho⟩ = source.exitVertex o ∧
        (e σ).choose ⟨expanded.exitVertex o, he⟩ = expanded.exitVertex o)

/-- Stops are global typed exits in each supplied Arena. A local port whose
completion is replaced by a continuation is not silently an exit here. -/
def LocalContinuationApplicabilityDuty {V Exit : Type*} (A : Arena V Exit)
    (localPort : V) (continuation : V) : Prop :=
  (∀ o, localPort ≠ A.exitVertex o) ∧
  (∀ w, A.edge localPort w ↔ w = continuation) ∧
  A.priority localPort = 0

end Partials.Parity
