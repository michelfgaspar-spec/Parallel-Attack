import Partials.ParityAlgorithms.PathEvaluator
import Partials.ParityAlgorithms.Neighborhoods
import Mathlib.Tactic.Ring

/-! Rank/bit RAM charges and external source boundaries. Costs on arbitrary
leaf names, input preparation and requested output are charged explicitly.
No same-order multitape simulation or arbitrary-floor bound is claimed. -/
namespace Partials.ParityAlgorithms.Path

structure StarEmbedding (m ell : Nat) where
  map : Fin m → Fin ell
  injective : Function.Injective map
  strict : StrictMono map

def HeightOneUniversal (n ell : Nat) : Prop :=
  ∀ m, m ≤ n → Nonempty (StarEmbedding m ell)

theorem height_one_universal_leaf_bound {n ell : Nat}
    (h : HeightOneUniversal n ell) : n ≤ ell := by
  obtain ⟨f⟩ := h n (le_refl n)
  have hc := Fintype.card_le_of_injective f.map f.injective
  simpa using hc

theorem height_one_universal_of_leaf_bound {n ell : Nat} (h : n ≤ ell) :
    HeightOneUniversal n ell := by
  intro m hm
  let f : Fin m → Fin ell := fun i => ⟨i.val, lt_of_lt_of_le i.isLt (hm.trans h)⟩
  refine ⟨⟨f, ?_, ?_⟩⟩
  · intro a b hab
    apply Fin.ext
    simpa [f] using congrArg (fun i : Fin ell => i.val) hab
  · intro a b hab
    exact hab

theorem height_one_universal_iff (n ell : Nat) :
    HeightOneUniversal n ell ↔ n ≤ ell :=
  ⟨height_one_universal_leaf_bound, height_one_universal_of_leaf_bound⟩

def PairBefore {n : Nat} (a b : Fin n × Fin n) : Prop :=
  a.1.val < b.1.val ∨ (a.1 = b.1 ∧ a.2.val < b.2.val)

noncomputable def eligibleArcs {n : Nat} (A : Arena n) (ell : Nat)
    (x : Vector n) : List (Fin n × Fin n) := by
  classical
  exact ((List.finRange n).flatMap fun v =>
    (List.finRange n).map (fun w => (v,w))).filter
    (fun e => decide (Eligible A ell x e.1 e.2))

/-- Source specification of R1's original identity tie-break; an effective
path-neighbor scan must avoid the quadratic all-pairs source list above. -/
noncomputable def ruleR1 {n : Nat} (A : Arena n) (ell : Nat)
    (x : Vector n) : Option (Fin n × Fin n) := by
  classical
  exact (eligibleArcs A ell x).foldl (fun best e =>
    match best with
    | none => some e
    | some b => if PairBefore e b then some e else best) none

noncomputable def ruleR2 {n : Nat} (A : Arena n) (ell : Nat)
    (x : Vector n) : Option (Fin n × Fin n) := by
  classical
  exact (eligibleArcs A ell x).foldl (fun best e =>
    match best with
    | none => some e
    | some b =>
      if x b.2 < x e.2 ∨ (x b.2 = x e.2 ∧ PairBefore e b)
      then some e else best) none

/-- Explicit two-neighbor original-arc enumeration is the ranked scan input.
It retains endpoint loops and deduplicates the n=1 sole loop. -/
def pathArcList {n : Nat} (A : Arena n) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun v =>
    (neighborList A v).map (fun w => (v,w))

/-- Constant-size neighborList is authored; prove exact Edge membership/no
duplicates and refine ruleR1/ruleR2 to this linear physical-arc scan. List
queue membership and indexed memory remain separate cost obligations. -/
def PrimitiveRAMCharge (width operations actualCost constant : Nat) : Prop :=
  actualCost ≤ constant * width * operations

structure RepresentationCharges where
  treeReadValidateAndRankInterface : Nat
  graphIdentityConversion : Nat
  externalFloorInverseConversion : Nat
  rankInputBits : Nat
  requestedRankOutputBits : Nat
  leafNameDecodeAndOutput : Nat
  retainedInterfaceStorage : Nat
  retainedOutputsStorage : Nat

def preparationCharge (C : RepresentationCharges) : Nat :=
  C.treeReadValidateAndRankInterface + C.graphIdentityConversion +
    C.externalFloorInverseConversion + C.rankInputBits

def outputCharge (C : RepresentationCharges) : Nat :=
  C.requestedRankOutputBits + C.leafNameDecodeAndOutput

def totalRAMCost (C : RepresentationCharges) (rankedCost : Nat) : Nat :=
  preparationCharge C + rankedCost + outputCharge C

/-- Exact width condition substitutes for evaluating logarithms. B>=1 and
ell<2^B imply representation of every rank/index on the actual input.
Queue address/tag enlargement needs an implementation-specific constant. -/
def RankWidth (ell B : Nat) : Prop := 1 ≤ B ∧ ell < 2 ^ B

theorem path_index_fits_rank_width (n ell B : Nat) (hn : n ≤ ell)
    (hB : RankWidth ell B) (i : Fin n) : i.val < 2 ^ B := by
  exact lt_trans (lt_of_lt_of_le i.isLt hn) hB.2

theorem rank_fits_width (ell B rank : Nat) (hB : RankWidth ell B)
    (hr : rank ≤ ell) : rank < 2 ^ B := lt_of_le_of_lt hr hB.2

/-- At most initial n insertions plus three attempts per strict change.
This arithmetic is separated from the still-open concrete queue invariant. -/
theorem successful_queue_insertions_bound (n changes insertions : Nat)
    (hc : changes ≤ 3 * n) (hi : insertions ≤ n + 3 * changes) :
    insertions ≤ 10 * n := by omega

theorem trajectory_evaluation_count (n pivots : Nat) (hp : pivots ≤ 2 * n) :
    pivots + 1 ≤ 2 * n + 1 := by omega

theorem quadratic_rank_work (n pivots c operations : Nat) (hn : 1 ≤ n)
    (hp : pivots ≤ 2 * n) (hw : operations ≤ c * n * (pivots + 1)) :
    operations ≤ 3 * c * n * n := by
  have hc : pivots + 1 ≤ 3 * n := by omega
  calc
    operations ≤ c * n * (pivots + 1) := hw
    _ ≤ c * n * (3 * n) := Nat.mul_le_mul_left _ hc
    _ = 3 * c * n * n := by ring

theorem quadratic_RAM_work (n pivots c operations B actual constant : Nat)
    (hn : 1 ≤ n) (hp : pivots ≤ 2 * n)
    (hw : operations ≤ c * n * (pivots + 1))
    (hc : PrimitiveRAMCharge B operations actual constant) :
    actual ≤ 3 * constant * c * n * n * B := by
  have ho := quadratic_rank_work n pivots c operations hn hp hw
  calc
    actual ≤ constant * B * operations := hc
    _ ≤ constant * B * (3 * c * n * n) := Nat.mul_le_mul_left _ ho
    _ = 3 * constant * c * n * n * B := by ring

/-- The original external interpretation is a precise unsupplied theorem
correspondence duty, rather than an axiom or a locally proved optimality
claim. Finite labels at a terminal state mark Even's winning region. -/
def KohLohoTerminalInterpretation {n : Nat} (A : Arena n) (ell : Nat)
    (EvenWins : Fin n → Prop) : Prop :=
  ∀ τ x, Completed A ell τ x →
    (∀ v w, ¬ Eligible A ell x v w) →
    ∀ v, (x v < ell ↔ EvenWins v)

def TightenCorrespondence {n : Nat} (A : Arena n) (ell : Nat)
    (externalTighten : Vector n → Fin n → Fin n → Nat) : Prop :=
  ∀ x, ValidVector ell x → ∀ v w,
    externalTighten x v w = theta A ell x v w

/-- Authoritative scope flags are false: neither the open-game row order,
an arbitrary starting floor nor a higher tree height is simulated here. -/
structure PathScope where
  arbitraryGraph : Bool := false
  arbitraryPriority : Bool := false
  arbitraryHeight : Bool := false
  arbitraryExternalFloorCostBound : Bool := false
  openGameValuationSimulation : Bool := false
  globalOptimalityProvedLocally : Bool := false
  sameOrderMultitapeSimulation : Bool := false
  implicitTreeAccessFree : Bool := false
  inverseLeafLookupFree : Bool := false
  initializationCountedAsPivot : Bool := false

end Partials.ParityAlgorithms.Path

namespace Partials.ParityAlgorithms.Neighborhoods

def neighborWorkBound (r layers M Q constant : Nat) : Nat :=
  constant * (candidateBound r layers + 1) * (M + 1) ^ 125 + Q

def neighborScratchBound (M constant : Nat) : Nat := constant * (M + 1) ^ 64

theorem neighbor_output_charge_present (r layers M Q c : Nat) :
    Q ≤ neighborWorkBound r layers M Q c := by
  unfold neighborWorkBound; omega

/-- A full forced original map can be exponentially longer than the
succinct generator; Q is actual original-identity output length, including
arms physically absent from candidate restrictions. -/
def OriginalForcedOutputCharge (requestedLength emittedLength : Nat) : Prop :=
  requestedLength = emittedLength

end Partials.ParityAlgorithms.Neighborhoods
