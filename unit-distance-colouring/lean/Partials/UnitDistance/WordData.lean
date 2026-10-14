import Partials.UnitDistance.DataAdmissions
import Partials.UnitDistance.WordMetric

/-! BLIND exact integer candidate-cost checker interface for the retained
2835 root records. Identity and global-minimum meaning are separated.
No candidate_count/tie-break assertion occurs in acceptance. -/
namespace Partials.UnitDistance.WordData

def targetPairs (r : Data.RawRootRecord) : SevenPairs :=
  Words.deterministicSevenPairs (DataAdmissions.decodeIntegerRow r.numerator)

def CandidateCostAccepted (r : Data.RawRootRecord) : Prop :=
  DataAdmissions.RawRootShape r ∧
  r.shift ∈ Words.candidatePoints (targetPairs r) ∧
  (rootWordCost (DataAdmissions.decodeRootCounts r.counts) : ℤ) =
    Words.shiftObjective (targetPairs r) r.shift.1 r.shift.2 ∧
  ∀ c ∈ Words.candidatePoints (targetPairs r),
    Words.shiftObjective (targetPairs r) r.shift.1 r.shift.2 ≤
      Words.shiftObjective (targetPairs r) c.1 c.2

instance candidateCostDecidable (r : Data.RawRootRecord) : Decidable (CandidateCostAccepted r) := by
  unfold CandidateCostAccepted DataAdmissions.RawRootShape
  infer_instance

def candidateCostCheck (r : Data.RawRootRecord) : Bool := decide (CandidateCostAccepted r)

theorem candidateCostCheck_sound (r : Data.RawRootRecord)
    (h : candidateCostCheck r = true) : CandidateCostAccepted r := by
  simpa [candidateCostCheck] using h

theorem accepted_record_shortest (r : Data.RawRootRecord)
    (basis : Words.SevenBasisDuty) (roots : Words.RootClassEvaluationDuty)
    (plane : Words.PrimitivePlaneDuty)
    (hcost : candidateCostCheck r = true)
    (hidentity : rootWordValue (DataAdmissions.decodeRootCounts r.counts) =
      evalInteger (DataAdmissions.decodeIntegerRow r.numerator)) :
    Words.IsShortestRootWord (evalInteger (DataAdmissions.decodeIntegerRow r.numerator))
      (DataAdmissions.decodeRootCounts r.counts) := by
  obtain ⟨hshape, hmember, hscore, hbest⟩ := candidateCostCheck_sound r hcost
  obtain ⟨c, hc, hshort, hcanonical, hglobal⟩ :=
    Words.shortest_root_word_at_candidate basis roots plane (targetPairs r)
  have htarget : sevenPairValue (targetPairs r) =
      evalInteger (DataAdmissions.decodeIntegerRow r.numerator) := by
    exact Words.deterministic_seven_representation roots _
  refine ⟨hidentity, ?_⟩
  intro d hd
  have hmin := hshort.2 d (by simpa only [htarget] using hd)
  have hcandidate := hbest c hc
  have hcostR : (rootWordCost (DataAdmissions.decodeRootCounts r.counts) : ℤ) ≤
      (rootWordCost (Words.canonicalWord (targetPairs r) c.1 c.2) : ℤ) := by
    rw [hscore, hcanonical]
    exact hcandidate
  omega

/-- Exact data success is an unproved finite target. Root identities must
be admitted separately in the actual cyclotomic embedding. -/
def AllRootCandidateCostsAccepted : Prop :=
  ∀ r ∈ Data.rawRootRecords, candidateCostCheck r = true

theorem all_records_shortest_from_actual_acceptance
    (basis : Words.SevenBasisDuty) (roots : Words.RootClassEvaluationDuty)
    (plane : Words.PrimitivePlaneDuty)
    (hcost : AllRootCandidateCostsAccepted) (hidentity : DataAdmissions.RootIdentityDuty) :
    ∀ r ∈ Data.rawRootRecords,
      Words.IsShortestRootWord (evalInteger (DataAdmissions.decodeIntegerRow r.numerator))
        (DataAdmissions.decodeRootCounts r.counts) := by
  intro r hr
  exact accepted_record_shortest r basis roots plane (hcost r hr) (hidentity r hr)

end Partials.UnitDistance.WordData
