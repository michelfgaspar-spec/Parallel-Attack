import Partials.UnitDistance.Data
import Partials.UnitDistance.Lift

/-! R6 BLIND guarded decoding and source/data duties. Copied JSON booleans,
stored container sizes and SHA256 digests do not inhabit these propositions.
Actual raw acceptance, geometry and finite-domain coverage remain unproved. -/
noncomputable section
namespace Partials.UnitDistance.DataAdmissions

local instance : DecidableEq ℂ := Classical.decEq _

def decodeIntegerRow (row : List ℤ) : IntegerCode := fun i => row.getD i.val 0
def decodeRootCounts (row : List ℕ) : RootLetterCount := fun i => row.getD i.val 0
def decodeBinaryLabel (label : ℕ) : BinaryCode :=
  fun i => ((label / 2 ^ i.val) % 2 : ℕ)

def decodeLineMask (mask : ℕ) : Finset (Fin 21) :=
  Finset.univ.filter (fun i => (mask / 2 ^ i.val) % 2 = 1)

noncomputable def rawSeedPoint (id : ℕ) : ℂ :=
  evalInteger (decodeIntegerRow (Data.seedNumeratorsOver7.getD id [])) / 7

def RawRootShape (r : Data.RawRootRecord) : Prop :=
  r.numerator.length = 12 ∧ r.counts.length = 42

def RawDirectionShape (r : Data.RawDirection) : Prop :=
  r.shell < 3 ∧ r.power < 21 ∧ r.denominator = 7 ^ r.shell ∧
  r.numerator.length = 12 ∧ r.residue < 4096 ∧ r.residue ≠ 0

def RawDataShape : Prop :=
  Data.rawLineRows.length = 21 ∧
  (∀ row ∈ Data.rawLineRows, row.length = 3 ∧ row.Nodup ∧
    ∀ label ∈ row, label < 4096 ∧ label ≠ 0) ∧
  Data.rawForbiddenMasks.Nodup ∧ Data.rawDeletionMasks.Nodup ∧
  (∀ mask ∈ Data.rawForbiddenMasks, mask < 2 ^ 21 ∧ mask ≠ 0) ∧
  (∀ mask ∈ Data.rawDeletionMasks, mask < 2 ^ 21) ∧
  (∀ r ∈ Data.rawDirections, RawDirectionShape r) ∧
  (∀ row ∈ Data.seedNumeratorsOver7, row.length = 12) ∧
  (∀ e ∈ Data.seedEdges, e.1 < Data.seedNumeratorsOver7.length ∧
    e.2 < Data.seedNumeratorsOver7.length ∧ e.1 < e.2) ∧
  (∀ r ∈ Data.rawRootRecords, RawRootShape r) ∧
  (Data.rawRootRecords.map (fun r => r.numerator)).Nodup ∧
  (∀ row ∈ Data.rootOrders, row.length = 42 ∧ row.Nodup ∧
    ∀ r ∈ row, r < 42) ∧
  (∀ row ∈ Data.rawForestRows, row.length = 8) ∧
  (∀ row ∈ Data.rawMatchingRows, row.length = 3)

instance rawDataShapeDecidable : Decidable RawDataShape := by
  unfold RawDataShape RawRootShape RawDirectionShape
  infer_instance

def rawDataShapeCheck : Bool := decide RawDataShape

theorem rawDataShapeCheck_sound (h : rawDataShapeCheck = true) : RawDataShape := by
  simpa [rawDataShapeCheck] using h

/-- Bounds are proved before casting to finite indices or forgetting duplicate
raw rows. Default getD values have no mathematical authority without shape. -/
structure ExactRawAcceptanceDuty : Prop where
  accepted : rawDataShapeCheck = true
  binary_label_injective : ∀ a < 4096, ∀ b < 4096,
    decodeBinaryLabel a = decodeBinaryLabel b → a = b
  binary_label_surjective : ∀ v : BinaryCode, ∃ a < 4096, decodeBinaryLabel a = v
  mask_injective : ∀ a < 2 ^ 21, ∀ b < 2 ^ 21,
    decodeLineMask a = decodeLineMask b → a = b
  mask_surjective : ∀ s : Finset (Fin 21), ∃ a < 2 ^ 21, decodeLineMask a = s

def SeedGeometryDuty (G1 : PhysicalGraph) : Prop :=
  G1.vertices = (Data.seedNumeratorsOver7.map
    (fun row => evalInteger (decodeIntegerRow row) / 7)).toFinset ∧
  G1.edges = (Data.seedEdges.map (fun e => (rawSeedPoint e.1, rawSeedPoint e.2))).toFinset ∧
  G1.vertices.card = 740 ∧ G1.edges.card = 3985 ∧
  (∀ z ∈ G1.vertices, z ∈ M1) ∧
  rawSeedPoint (Data.seedTerminalIds.getD 0 0) = 0 ∧
  rawSeedPoint (Data.seedTerminalIds.getD 1 0) = delta ∧
  (∀ a b, InducedUnitPair G1 a b ↔ (a, b) ∈ G1.edges ∨ (b, a) ∈ G1.edges)

/-- Word equality only. Minimality and the147 candidate/real-face bridges are
different duties in WordMetric/Minimization; candidateCountMetadata is omitted. -/
def RootIdentityDuty : Prop :=
  ∀ r ∈ Data.rawRootRecords,
    rootWordValue (decodeRootCounts r.counts) = evalInteger (decodeIntegerRow r.numerator)

def RootTargetCoverageDuty (residue : HalfUnitIndex → BinaryCode)
    (retained : Finset HalfUnitIndex) : Prop :=
  ∀ i ∈ retained, ∀ a b, b = a + residue i →
    ∃ r ∈ Data.rawRootRecords,
      evalInteger (decodeIntegerRow r.numerator) = Lift.integralTarget a b i

/-- Exact local two-H data stays in CHAIN_GEOMETRY.json. This specification
must be implemented against all3 shells, all2045 identified point rows and
selected/induced edges, occurrence maps, boundaries and9 proof DAG nodes;
it is not witnessed by a retained all_assertions_passed flag. -/
structure LocalGeometryDecodingDuty where
  shellGraph : Fin 3 → PhysicalGraph
  occurrenceGraph : Fin 3 → Fin 2 → PhysicalGraph
  endpoints : Fin 3 → Fin 3 → ℂ
  selected_count : ∀ j, (shellGraph j).edges.card = 11944
  vertex_count : ∀ j, (shellGraph j).vertices.card = 2045
  unit_edges : ∀ j, IsSelectedUnitGraph (shellGraph j)
  selected_union : ∀ j, (shellGraph j).edges =
    (occurrenceGraph j 0).edges ∪ (occurrenceGraph j 1).edges
  vertex_union : ∀ j, (shellGraph j).vertices =
    (occurrenceGraph j 0).vertices ∪ (occurrenceGraph j 1).vertices
  common_vertices : ∀ j,
    ((occurrenceGraph j 0).vertices ∩ (occurrenceGraph j 1).vertices).card = 87
  common_edges : ∀ j,
    ((occurrenceGraph j 0).edges ∩ (occurrenceGraph j 1).edges).card = 198
  single_vertices : ∀ j k, (occurrenceGraph j k).vertices.card = 1066
  single_edges : ∀ j k, (occurrenceGraph j k).edges.card = 6071
  all_induced_pairs : ∀ j, ∃ E : Finset (ℂ × ℂ),
    E.card = 12697 ∧ ∀ a b, InducedUnitPair (shellGraph j) a b ↔
      (a, b) ∈ E ∨ (b, a) ∈ E

end Partials.UnitDistance.DataAdmissions

end
