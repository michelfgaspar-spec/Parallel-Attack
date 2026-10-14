import Mathlib.Data.Finset.Range
import Partials.Parity.Model

/-!
# Finite certificate semantics for parity raw outcomes (uncompiled draft)

This file states the exact finite graph questions behind the Python diagnostic
without importing or translating that Python code. The graph-theoretic
characterization `CertificateRaw = RawOutcomes` remains an unproved target.
Its eventual proof must handle finite first exits, all compatible histories,
and the largest recurring priority of an infinite nonexit play.
-/


universe u v w

namespace Partials.Parity

def IsExit {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (x : V) : Prop :=
  ∃ o, x = A.exitVertex o

/-- All legal selected edges, with Odd alternatives left intact. -/
def SelectedEdge {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A) (x y : V) : Prop :=
  A.edge x y ∧ (A.even x = true → y = σ.move x)

instance selectedEdgeDecidable {V : Type u} {Exit : Type v} [DecidableEq V]
    (A : Arena V Exit) [DecidableRel A.edge] (σ : EvenPolicy A) (x y : V) :
    Decidable (SelectedEdge A σ x y) :=
  inferInstanceAs (Decidable (A.edge x y ∧ (A.even x = true → y = σ.move x)))

def NonExitEdge {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A) (x y : V) : Prop :=
  ¬ IsExit A x ∧ ¬ IsExit A y ∧ SelectedEdge A σ x y

def ReachWithoutExit {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A) (start x : V) : Prop :=
  ¬ IsExit A start ∧ Relation.ReflTransGen (NonExitEdge A σ) start x

/-- A positive cycle in the subgraph of nonexit vertices of priority at most
`p`, with a vertex of priority exactly `p` on that cycle. -/
def EdgeAtMost {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A) (p : Nat) (x y : V) : Prop :=
  NonExitEdge A σ x y ∧ A.priority x ≤ p ∧ A.priority y ≤ p

def ReachableCyclePeak {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A) (start : V) (p : Nat) : Prop :=
  ∃ x y, ReachWithoutExit A σ start x ∧
    A.priority x = p ∧
    EdgeAtMost A σ p x y ∧
    Relation.ReflTransGen (EdgeAtMost A σ p) y x

def HasOddCycle {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A) (start : V) : Prop :=
  ∃ p, p % 2 = 1 ∧ ReachableCyclePeak A σ start p

def HasEvenCycle {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A) (start : V) : Prop :=
  ∃ p, p % 2 = 0 ∧ ReachableCyclePeak A σ start p

/-- State-space reachability for finite-exit priorities. Power can replace
the unbounded `Nat` maximum by a bounded finite priority alphabet in the
fixture checker; the mathematical state transition is fixed here. -/
def MaxStateEdge {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A)
    (s t : V × Nat) : Prop :=
  ¬ IsExit A s.1 ∧ SelectedEdge A σ s.1 t.1 ∧
  t.2 = max s.2 (A.priority t.1)

def FiniteExitPriority {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A)
    (start : V) (o : Exit) (p : Nat) : Prop :=
  Relation.ReflTransGen (MaxStateEdge A σ)
    (start, A.priority start) (A.exitVertex o, p)

/-- This is a *predicate*, not a completed theorem. A checked instance of
this predicate says exactly which finite exits and recurrent cycle parities
are possible from one start under one complete policy. -/
def CertificateRaw {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A) (start : V) :
    Set (Outcome Exit) :=
  {out | match out with
    | .bottom => HasOddCycle A σ start
    | .top => HasEvenCycle A σ start
    | .halt o p => FiniteExitPriority A σ start o p}

/-- Target theorem for the finite parity/lasso bridge. It is intentionally a
definition so its proof cannot be mistaken for an available theorem. -/
def CertificateRawExactTarget {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A) (start : V) : Prop :=
  CertificateRaw A σ start = RawOutcomes A σ start

def CertifiedProfile {V : Type u} {Exit : Type v} {Start : Type w}
    (A : Arena V Exit) (σ : EvenPolicy A) (startVertex : Start → V) :
    Profile Start Exit :=
  fun i => MinRow (CertificateRaw A σ (startVertex i))

/-- Pure substitution: this does not establish the finite parity/lasso bridge;
the bridge is exactly the hypothesis at every start. -/
theorem certifiedProfile_eq_policyProfile
    {V : Type u} {Exit : Type v} {Start : Type w}
    (A : Arena V Exit) (σ : EvenPolicy A) (startVertex : Start → V)
    (h : ∀ i, CertificateRawExactTarget A σ (startVertex i)) :
    CertifiedProfile A σ startVertex = PolicyProfile A σ startVertex := by
  funext i
  exact congrArg MinRow (h i)

/- The fixture needs this bridge at each of the two starts for each of four
arena/policy pairs, plus a finite decision proof of the proposed cycle and
max-state facts. -/


/-- Numerical prefix maximum; the extra vertex is the zero exit on stopping. -/
def PrefixPeak {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (vertices : Nat → V) (n : Nat) : Nat :=
  (Finset.range (n + 1)).sup (fun k => A.priority (vertices k))

theorem prefixPeak_succ {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (vertices : Nat → V) (n : Nat) :
    PrefixPeak A vertices (n + 1) =
      max (PrefixPeak A vertices n) (A.priority (vertices (n + 1))) := by
  simp [PrefixPeak, Finset.range_add_one, Finset.sup_insert, max_comm]

/-- A finite certificate carries the actual original selected vertices,
first-exit condition and ordinary numerical peak. It is not a desired row. -/
structure FinitePrefix {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A) (start : V) (o : Exit) (p : Nat) where
  length : Nat
  vertices : Nat → V
  initial : vertices 0 = start
  selected : ∀ n < length, SelectedEdge A σ (vertices n) (vertices (n + 1))
  last : vertices length = A.exitVertex o
  first : ∀ n < length, ∀ o', vertices n ≠ A.exitVertex o'
  peak : p = PrefixPeak A vertices length

def CompletePrefix {V : Type u} {Exit : Type v}
    {A : Arena V Exit} {σ : EvenPolicy A} {start : V} {o : Exit} {p : Nat}
    (c : FinitePrefix A σ start o p) (n : Nat) : V :=
  if n ≤ c.length then c.vertices n else A.exitVertex o

theorem selected_exit_loop {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A) (o : Exit) :
    SelectedEdge A σ (A.exitVertex o) (A.exitVertex o) := by
  refine ⟨(A.exit_sink o _).mpr rfl, ?_⟩
  intro heven
  exact ((A.exit_sink o _).mp (σ.legal_even _ heven)).symm

/-- Totality of a finite exit witness follows by its absorbing completion;
no Odd alternatives are discarded. -/
theorem completePrefix_compatible {V : Type u} {Exit : Type v}
    {A : Arena V Exit} {σ : EvenPolicy A} {start : V} {o : Exit} {p : Nat}
    (c : FinitePrefix A σ start o p) : Compatible A σ (CompletePrefix c) := by
  intro n
  by_cases hn : n < c.length
  · have hn₀ : n ≤ c.length := by omega
    have hn₁ : n + 1 ≤ c.length := by omega
    simpa [CompletePrefix, hn₀, hn₁, SelectedEdge] using c.selected n hn
  · by_cases heq : n = c.length
    · subst n
      have hs : ¬ c.length + 1 ≤ c.length := by omega
      simpa [CompletePrefix, c.last, SelectedEdge, hs] using selected_exit_loop A σ o
    · have hn₀ : ¬ n ≤ c.length := by omega
      have hn₁ : ¬ n + 1 ≤ c.length := by omega
      simpa [CompletePrefix, hn₀, hn₁, SelectedEdge] using selected_exit_loop A σ o

theorem completePrefix_firstExit {V : Type u} {Exit : Type v}
    {A : Arena V Exit} {σ : EvenPolicy A} {start : V} {o : Exit} {p : Nat}
    (c : FinitePrefix A σ start o p) :
    FirstExit A (CompletePrefix c) c.length o p := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [CompletePrefix] using c.last
  · intro k hk o'
    have hle : k ≤ c.length := by omega
    simpa [CompletePrefix, hle] using c.first k hk o'
  · apply c.peak.trans
    simp only [PrefixPeak]
    apply Finset.sup_congr rfl
    intro k hk
    have hle : k ≤ c.length := by
      have := Finset.mem_range.mp hk
      omega
    simp [PrefixPeak, CompletePrefix, hle]

theorem finitePrefix_sound {V : Type u} {Exit : Type v}
    {A : Arena V Exit} {σ : EvenPolicy A} {start : V} {o : Exit} {p : Nat}
    (c : FinitePrefix A σ start o p) :
    Outcome.halt o p ∈ RawOutcomes A σ start := by
  refine ⟨CompletePrefix c, ?_, completePrefix_compatible c, Or.inl ?_⟩
  · simpa [CompletePrefix] using c.initial
  · exact ⟨c.length, o, p, completePrefix_firstExit c, rfl⟩

/-- The positive period counts vertices of the cycle, not its duplicated
endpoint. Repetition begins after a finite stem, whose high priorities are
transient for the infinite outcome. -/
def LassoPath {V : Type u} (cut period : Nat) (positive : 0 < period)
    (stem : Nat → V) (cycle : Fin period → V) (n : Nat) : V :=
  if n < cut then stem n
  else cycle ⟨(n - cut) % period, Nat.mod_lt _ positive⟩

/-- Every cycle vertex occurs arbitrarily late. This arithmetic fact supplies
recurrence rather than incorrectly using the maximum of the finite stem. -/
theorem lasso_repeats {V : Type u} (cut period : Nat) (positive : 0 < period)
    (stem : Nat → V) (cycle : Fin period → V) (i : Fin period) (N : Nat) :
    ∃ n, N ≤ n ∧ LassoPath cut period positive stem cycle n = cycle i := by
  let n := cut + i.val + (N + 1) * period
  have hperiod : 1 ≤ period := positive
  have hmul₁ : (N + 1) * 1 ≤ (N + 1) * period :=
    Nat.mul_le_mul_left (N + 1) hperiod
  have hmul : N ≤ (N + 1) * period :=
    (Nat.le_succ N).trans (by simpa using hmul₁)
  have hN : N ≤ n := by dsimp [n]; omega
  have hcut : cut ≤ n := by dsimp [n]; omega
  refine ⟨n, hN, ?_⟩
  have hsub : n - cut = i.val + (N + 1) * period := by dsimp [n]; omega
  simp only [LassoPath, if_neg (Nat.not_lt.mpr hcut)]
  congr 1
  apply Fin.ext
  simp [hsub, Nat.add_mod, Nat.mod_eq_of_lt i.isLt]

/-- A bounded finite stem and a cyclic selected edge at every finite slot
certify compatibility of the entire infinite lasso. Odd choices in these
finite certificates select a legal history; they do not prune the arena. -/
theorem lasso_compatible {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A)
    (cut period : Nat) (positive : 0 < period)
    (stem : Nat → V) (cycle : Fin period → V)
    (hstem : ∀ n < cut, SelectedEdge A σ
      (LassoPath cut period positive stem cycle n)
      (LassoPath cut period positive stem cycle (n + 1)))
    (hcycle : ∀ i : Fin period, SelectedEdge A σ (cycle i)
      (cycle ⟨(i.val + 1) % period, Nat.mod_lt _ positive⟩)) :
    Compatible A σ (LassoPath cut period positive stem cycle) := by
  intro n
  by_cases hn : n < cut
  · exact hstem n hn
  · have hn₀ : cut ≤ n := by omega
    have hn₁ : ¬ n + 1 < cut := by omega
    have hsub : n + 1 - cut = n - cut + 1 := by omega
    have hindex :
        (⟨(n + 1 - cut) % period, Nat.mod_lt _ positive⟩ : Fin period) =
          ⟨(((n - cut) % period + 1) % period), Nat.mod_lt _ positive⟩ := by
      apply Fin.ext
      simp [hsub, Nat.add_mod]
    simpa [LassoPath, hn, hn₁, hindex, SelectedEdge]
      using hcycle ⟨(n - cut) % period, Nat.mod_lt _ positive⟩

/-- Eventual numerical boundedness rules out any larger recurring priority;
one arbitrarily recurring peak gives the exact largest recurring priority. -/
theorem largestRecurring_of_eventualBound {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (ρ : Nat → V) (p cut : Nat)
    (hpeak : Recurs A ρ p)
    (hbound : ∀ n, cut ≤ n → A.priority (ρ n) ≤ p) :
    LargestRecurring A ρ p := by
  refine ⟨hpeak, ?_⟩
  intro q hq
  obtain ⟨n, hn, heq⟩ := hq cut
  simpa [heq] using hbound n hn

theorem lasso_largestRecurring {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (cut period : Nat) (positive : 0 < period)
    (stem : Nat → V) (cycle : Fin period → V) (peak : Fin period)
    (bounded : ∀ i, A.priority (cycle i) ≤ A.priority (cycle peak)) :
    LargestRecurring A (LassoPath cut period positive stem cycle)
      (A.priority (cycle peak)) := by
  apply largestRecurring_of_eventualBound A _ _ cut
  · intro N
    obtain ⟨n, hn, heq⟩ := lasso_repeats cut period positive stem cycle peak N
    exact ⟨n, hn, congrArg A.priority heq⟩
  · intro n hn
    simpa [LassoPath, Nat.not_lt.mpr hn] using
      bounded ⟨(n - cut) % period, Nat.mod_lt _ positive⟩

/-- Full soundness of a finite lasso witness. Completeness in the converse
direction (every arbitrary compatible infinite history has a finite reachable
cycle with the same recurrent maximum) is a separate retained obligation. -/
theorem lasso_sound {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A) (start : V)
    (cut period : Nat) (positive : 0 < period)
    (stem : Nat → V) (cycle : Fin period → V) (peak : Fin period)
    (initial : LassoPath cut period positive stem cycle 0 = start)
    (hstem : ∀ n < cut, SelectedEdge A σ
      (LassoPath cut period positive stem cycle n)
      (LassoPath cut period positive stem cycle (n + 1)))
    (hcycle : ∀ i : Fin period, SelectedEdge A σ (cycle i)
      (cycle ⟨(i.val + 1) % period, Nat.mod_lt _ positive⟩))
    (stem_nonexit : ∀ n < cut, ∀ o, stem n ≠ A.exitVertex o)
    (cycle_nonexit : ∀ i o, cycle i ≠ A.exitVertex o)
    (bounded : ∀ i, A.priority (cycle i) ≤ A.priority (cycle peak))
    (out : Outcome Exit)
    (parity : (A.priority (cycle peak) % 2 = 0 ∧ out = .top) ∨
      (A.priority (cycle peak) % 2 = 1 ∧ out = .bottom)) :
    out ∈ RawOutcomes A σ start := by
  refine ⟨LassoPath cut period positive stem cycle, initial,
    lasso_compatible A σ cut period positive stem cycle hstem hcycle,
    Or.inr ?_⟩
  refine ⟨?_, A.priority (cycle peak),
    lasso_largestRecurring A cut period positive stem cycle peak bounded, parity⟩
  intro n o
  by_cases hn : n < cut
  · simpa [LassoPath, hn] using stem_nonexit n hn o
  · simpa [LassoPath, hn] using
      cycle_nonexit ⟨(n - cut) % period, Nat.mod_lt _ positive⟩ o

/-- All selected edges and therefore every raw/profile outcome are invariant
under agreement at complete Even coordinates. This is what policy exhaustion
uses; exact equality of irrelevant Odd dummy fields is unnecessary. -/
theorem compatible_of_policyAgreement {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ τ : EvenPolicy A) (h : PolicyAgreement A σ τ)
    (ρ : Nat → V) : Compatible A σ ρ ↔ Compatible A τ ρ := by
  constructor <;> intro hρ n
  · refine ⟨(hρ n).1, ?_⟩
    intro hv
    exact ((hρ n).2 hv).trans (h (ρ n) hv)
  · refine ⟨(hρ n).1, ?_⟩
    intro hv
    exact ((hρ n).2 hv).trans (h (ρ n) hv).symm

theorem raw_of_policyAgreement {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ τ : EvenPolicy A) (h : PolicyAgreement A σ τ)
    (start : V) : RawOutcomes A σ start = RawOutcomes A τ start := by
  ext out
  constructor <;> rintro ⟨ρ, hstart, hρ, hout⟩
  · exact ⟨ρ, hstart, (compatible_of_policyAgreement A σ τ h ρ).mp hρ, hout⟩
  · exact ⟨ρ, hstart, (compatible_of_policyAgreement A σ τ h ρ).mpr hρ, hout⟩

theorem profile_of_policyAgreement {V : Type u} {Exit : Type v} {Start : Type w}
    (A : Arena V Exit) (σ τ : EvenPolicy A) (h : PolicyAgreement A σ τ)
    (starts : Start → V) : PolicyProfile A σ starts = PolicyProfile A τ starts := by
  funext i
  exact congrArg MinRow (raw_of_policyAgreement A σ τ h (starts i))

/- Deferred D-FB-FINITE-BRIDGE: with finite original V/priority alphabet,
prove every MaxStateEdge reachability path has a finite first-exit prefix and
conversely, every compatible nonexit history yields an eventually bounded
reachable positive cycle through a recurrent peak; construct lasso witnesses
from such cycles. Then prove CertificateRawExactTarget. This definition and
the four fixture table targets remain unaccepted. No Python checker ran. -/

end Partials.Parity
