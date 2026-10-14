import Partials.UnitDistance.DataAdmissions
import Partials.UnitDistance.LineHit
import Partials.UnitDistance.Counts
import Partials.UnitDistance.Height

/-! Exact frozen headline targets, not imported witnesses. No declaration
below supplies existence, a checked numeral, or an admitted paper theorem. -/
namespace Partials.UnitDistance.Targets

def MainConclusion : Prop :=
  ∃ G : PhysicalGraph, IsSelectedUnitGraph G ∧
    (∀ z ∈ G.vertices, z ∈ M2) ∧
    NoFourColouring G ∧
    G.vertices.card ≤ 3535305907 ∧ G.edges.card ≤ 20579719785 ∧
    ∀ z ∈ G.vertices, ∃ c : IntegerCode, z = point49 c ∧ Height49AtMost c 3304

def ExactMainDuty : Prop := MainConclusion

def FixedWholeLineThreshold (F : CommonBinaryLineFamily BinaryCode) : Prop :=
  (∃ S : Finset (Fin 21), S.card = 18 ∧ NoFourCayleyColouring F S) ∧
  (∀ S : Finset (Fin 21), S.card ≤ 17 → HasFourCayleyColouring F S)

def ExactThresholdDuty (F : CommonBinaryLineFamily BinaryCode) : Prop :=
  FixedWholeLineThreshold F

def LiteralContainerTargets : Prop :=
  Data.rawLineRows.length = 21 ∧ Data.rawForbiddenMasks.length = 196 ∧
  Data.rawDeletionMasks.length = 379 ∧ Data.rawDirections.length = 63 ∧
  Data.seedNumeratorsOver7.length = 740 ∧ Data.seedEdges.length = 3985 ∧
  Data.rawRootRecords.length = 2835 ∧ Data.rawForestRows.length = 4096 ∧
  Data.rawMatchingRows.length = 4096

/-- These are source targets for exact numerical admission, with separate
direction/Fourier, graph/forest and maximum matching meanings. Earlier
consecutive pairs1450915 and illustrative deletion1,7,8 remain distinct. -/
structure FinalLedgerTargets where
  quotientVertices : ℕ
  quotientEdges : ℕ
  fullWordOccurrences : ℕ
  prefixOccurrences : ℕ
  forestOccurrences : ℕ
  eligiblePairs : ℕ
  largestRootWord : ℕ
  largestFullWord : ℕ
  anchorHeight : ℕ
  vertex_eq : quotientVertices = 4096
  edge_eq : quotientEdges = 110592
  full_eq : fullWordOccurrences = 3649656
  prefix_eq : prefixOccurrences = 3439213
  forest_eq : forestOccurrences = 3437445
  pairs_eq : eligiblePairs = 1460199
  root_eq : largestRootWord = 66
  full_length_eq : largestFullWord = 90
  anchor_eq : anchorHeight = 3087

/- Exclusions retained: no five-colouring or exact chromatic number, induced
edge bound, unrestricted graph/plane minimum, global word/network optimum,
priority, complete physical H relation/nonemptiness, fresh G1 SAT proof,
candidate_count/tie-break admission, graph expansion or checker replay. -/
end Partials.UnitDistance.Targets
