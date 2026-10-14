import Partials.Cap.Data
import Partials.Cap.FieldEncoding
import Partials.Cap.Checkers
import Partials.Cap.Reduction

/-! Exact data interpretation and acceptance boundaries. All concrete checker
equalities and field/data semantic witnesses below are unprovided. -/
namespace Partials.Cap.Admission

noncomputable section
open Partials.Cap

def checkerRow (r : Data.TripleRow) : Certificate.NaturalTripleRow :=
  ⟨r.i, r.j, r.k, r.discriminant, r.forbidden⟩
def checkerRows : List Certificate.NaturalTripleRow := Data.rawHypergraphRows.map checkerRow
def familyResidue : Finset (Finset Vertex) :=
  Data.familyNat.image (fun s => s.image (fun v : ℕ => (v : Vertex)))
def graphResidue : Hypergraph Vertex :=
  Data.graphNat.image (fun e => e.image (fun v : ℕ => (v : Vertex)))
def labelOfNat (n : ℕ) : Label := ⟨n % 6561, Nat.mod_lt n (by decide)⟩
def hCode (i : ℕ) : Code8 := Encoding.labelDigits (labelOfNat (Data.hLabels.getD i 0))
def discriminantCode (i j k : ℕ) : ℕ :=
  Encoding.codeLabelValue (Encoding.negCode
    (Encoding.addCode (Encoding.addCode (Encoding.mulCode (hCode i) (hCode j))
      (Encoding.mulCode (hCode i) (hCode k))) (Encoding.mulCode (hCode j) (hCode k))))
def squareCode (n : ℕ) : Bool :=
  decide (∃ a : Code8, Encoding.mulCode a a = Encoding.labelDigits (labelOfNat n))

def graphShapeCheck : Bool := Certificate.checkGraphRows checkerRows 41 6561 5740 4920 0
def graphArithmeticCheck : Bool := Certificate.checkRowCodes checkerRows discriminantCode squareCode
def rawFamilyCheck : Bool := Certificate.checkRawFamily 41 Data.rawFamily
def residueFamilyCheck : Bool := Certificate.checkRootedResidueFamily graphResidue familyResidue

def expectedRank (k : ℕ) : ℕ :=
  if k = 1 then 1 else if k = 2 then 40 else if k = 3 then 360
    else if k = 4 then 488 else if k = 5 then 40 else 0
def naturalFamilyCheck : Bool := Certificate.checkFamily Data.graphNat Data.familyNat
  41 929 5 expectedRank Data.witnessVertices.toFinset 10182 928

def RootedStatistics : Prop :=
  (∀ T ∈ familyResidue, T.card ≤ 5) ∧ witnessExponents ∈ familyResidue ∧
    (familyResidue.filter (fun T => T.card = 5)).card = 40

instance rootedStatistics_decidable : Decidable RootedStatistics := by
  unfold RootedStatistics
  infer_instance
def rootedStatisticsCheck : Bool := decide RootedStatistics

theorem graph_shape_from_acceptance (h : graphShapeCheck = true) :
    Certificate.GraphRowsAccepted checkerRows 41 6561 5740 4920 0 :=
  Certificate.checkGraphRows_sound checkerRows 41 6561 5740 4920 0 h
theorem graph_codes_from_acceptance (h : graphArithmeticCheck = true) :
    ∀ r ∈ checkerRows, Certificate.RowCodeConsistent discriminantCode squareCode r :=
  Certificate.checkRowCodes_sound checkerRows discriminantCode squareCode h
theorem raw_family_from_acceptance (h : rawFamilyCheck = true) :
    Certificate.RawFamilyAccepted 41 Data.rawFamily :=
  Certificate.checkRawFamily_sound 41 Data.rawFamily h
theorem natural_family_from_acceptance (h : naturalFamilyCheck = true) :
    Certificate.FamilyAccepted Data.graphNat Data.familyNat 41 929 5 expectedRank
      Data.witnessVertices.toFinset 10182 928 :=
  Certificate.checkFamily_sound Data.graphNat Data.familyNat 41 929 5 expectedRank
    Data.witnessVertices.toFinset 10182 928 h
theorem rooted_statistics_from_acceptance (h : rootedStatisticsCheck = true) : RootedStatistics := by
  simpa [rootedStatisticsCheck] using h

variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

/-- Exact aggregate table interpretation target. Its fine quotient decoding,
square-code and canonical triple/permutation obligations are stated below;
neither this equality nor any acceptance Boolean is asserted. -/
def HypergraphTableMeaningDuty (z : K) : Prop := graphResidue = discriminantHypergraph z
def RowFieldMeaningDuty (z : K) : Prop :=
  Certificate.CodeEdgeMeaningDuty checkerRows discriminantCode squareCode
    (fun e => DiscriminantEdge z (e.image (fun v : ℕ => (v : Vertex))))

theorem rows_refine_discriminant_target (z : K)
    (hs : graphShapeCheck = true) (ha : graphArithmeticCheck = true)
    (hm : RowFieldMeaningDuty z) (e : Finset ℕ) :
    e ∈ Certificate.graphFromRows checkerRows ↔ e ∈ Certificate.tripleUniverse 41 ∧
      DiscriminantEdge z (e.image (fun v : ℕ => (v : Vertex))) := by
  apply Certificate.graph_rows_refine_target checkerRows 41 6561 5740 4920 0 _
    (graph_shape_from_acceptance hs)
  exact Certificate.row_flags_mean_edges checkerRows discriminantCode squareCode _ ha hm

theorem rooted_certificate_from_actual_acceptance (z : K)
    (hm : HypergraphTableMeaningDuty z) (h : residueFamilyCheck = true) :
    Certificate.RootedCertificate (discriminantHypergraph z) familyResidue := by
  have hc := Certificate.checkRootedResidueFamily_sound graphResidue familyResidue h
  change graphResidue = discriminantHypergraph z at hm
  rw [hm] at hc
  exact hc

def CoordinateLabelMeaningDuty (r : Encoding.FieldRealization K) (z : K) : Prop :=
  ∀ i : Vertex, r.equiv (quotientDecode (hCode i.val)) = coefficient z i
def QuotientSquareCodeDuty (r : Encoding.FieldRealization K) : Prop :=
  ∀ n : Label, squareCode n.val = true ↔
    Square (r.equiv (quotientDecode (Encoding.labelDigits n)))
def QuotientDiscriminantCodeDuty (r : Encoding.FieldRealization K) : Prop :=
  ∀ i j k : Vertex, r.equiv (quotientDecode
    (Encoding.labelDigits (labelOfNat (discriminantCode i.val j.val k.val)))) =
      delta (r.equiv (quotientDecode (hCode i.val)))
        (r.equiv (quotientDecode (hCode j.val))) (r.equiv (quotientDecode (hCode k.val)))

/-- Actual future acceptance must bottom out in evaluated checks and precise
field/table/label proofs, not hashes or stored cardinality metadata. -/
def ExactDataAcceptanceDuty (z : K) : Prop :=
  graphShapeCheck = true ∧ graphArithmeticCheck = true ∧ rawFamilyCheck = true ∧
    naturalFamilyCheck = true ∧ residueFamilyCheck = true ∧ rootedStatisticsCheck = true ∧
    RowFieldMeaningDuty z ∧ HypergraphTableMeaningDuty z

end
end Partials.Cap.Admission
