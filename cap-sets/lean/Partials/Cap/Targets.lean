import Partials.Cap.Model
import Partials.Cap.FieldEncoding
import Partials.Cap.Data

/-! Exact headline and diagnostic targets, not theorem witnesses. -/
namespace Partials.Cap.Targets

noncomputable section
open Partials.Cap
variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

def hImage (z : K) (p : Vertex × Fin 8) : Finset K :=
  (witnessCoefficients z).image (fun c => coefficient z p.1 * c ^ (3 ^ p.2.val))
def hImages (z : K) : Finset (Finset K) :=
  (Finset.univ : Finset (Vertex × Fin 8)).image (hImage z)
def cosetImage (z : K) (S : Finset K) : Finset K :=
  S.image (fun c => primitive z * c)
def oppositeImages (z : K) : Finset (Finset K) := (hImages z).image (cosetImage z)
def dImages (z : K) : Finset (Finset K) := hImages z ∪ oppositeImages z

def H41Conclusion (z : K) : Prop :=
  MaximumFive (H41 z) ∧
  CapCoefficientSet (H41 z) (witnessCoefficients z) ∧
  (witnessCoefficients z).card = 5 ∧
  (P (witnessCoefficients z)).ncard = 32800 ∧
  (∀ S : Finset K, S ∈ hImages z ↔ CapCoefficientSet (H41 z) S ∧ S.card = 5) ∧
  (hImages z).card = 328 ∧ Function.Injective (hImage z)

def D82Conclusion (z : K) : Prop :=
  MaximumFive (domainD z) ∧
  (∀ S : Finset K, S ∈ dImages z ↔ CapCoefficientSet (domainD z) S ∧ S.card = 5) ∧
  (hImages z).card = 328 ∧ (oppositeImages z).card = 328 ∧
  Disjoint (hImages z) (oppositeImages z) ∧ (dImages z).card = 656 ∧
  (∀ S ∈ dImages z, (P S).ncard = 32800)

def FieldCoordinateConclusion (r : Encoding.FieldRealization K) : Prop :=
  let decode := r.equiv ∘ quotientDecode
  let z := r.equiv quotientZ
  Nat.card K = 6561 ∧
    decode (Encoding.labelDigits ⟨38, by norm_num⟩) = primitive z ∧
    decode (Encoding.labelDigits ⟨993, by norm_num⟩) = subgroupGenerator z ∧
    subgroupGenerator z = primitive z ^ 160 ∧
    (∀ i : Vertex, ∃ label ∈ Data.hLabels,
      ∃ hl : label < 6561, decode (Encoding.labelDigits ⟨label, hl⟩) = coefficient z i)

/-- Concrete field-coordinate, finite data and classification targets have
no asserted inhabitants. They remain separate future admissions. -/
def ExactFieldCoordinateDuty (r : Encoding.FieldRealization K) : Prop := FieldCoordinateConclusion r
def ExactH41AssemblyDuty (z : K) : Prop := H41Conclusion z
def ExactD82AssemblyDuty (z : K) : Prop := D82Conclusion z

def DirectWitnessRootDuty (z : K) : Prop :=
  ∀ a ∈ witnessCoefficients z, ∀ b ∈ witnessCoefficients z,
    ∀ c ∈ witnessCoefficients z, ∀ t : K,
      ratioAdmissible t → quadratic a b c t = 0 → a = b ∧ b = c ∧ t = 1

def TwoCosetDiagnosticCountsDuty : Prop :=
  -- These are the frozen source's counts, not a performed 82-vertex search.
  Data.expectedWitnessEquations = 229565 ∧
    (2 * Nat.choose 41 2 = 1640) ∧ (41 ^ 2 = 1681) ∧ (Nat.choose 82 3 = 88560)

end
end Partials.Cap.Targets
