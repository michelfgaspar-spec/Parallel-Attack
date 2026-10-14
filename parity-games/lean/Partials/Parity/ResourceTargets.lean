import Mathlib.Tactic.NormNum
import Partials.Parity.Model

/-! R7 exact binary resource goals. Semantic equality is not a cost model.
No constants/algorithm/run witnesses are supplied by the following targets. -/
namespace Partials.Parity.Resources

def PolynomialBound (cost : ℕ → ℕ) (exponent : ℕ) : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ N, cost N ≤ C * (N + 1) ^ exponent

structure CompilerCosts where
  zones : ℕ → ℕ
  zoneTagCoefficientBits : ℕ → ℕ
  templateBits : ℕ → ℕ
  preprocessingBitOperations : ℕ → ℕ
  scratchBits : ℕ → ℕ
  queryNonforcedBits : ℕ → ℕ
  flatOutputBits : ℕ → ℕ → ℕ

def ExactBinaryCompilerGoal (c : CompilerCosts) : Prop :=
  PolynomialBound c.zones 12 ∧ PolynomialBound c.zoneTagCoefficientBits 13 ∧
  PolynomialBound c.templateBits 14 ∧ PolynomialBound c.preprocessingBitOperations 125 ∧
  PolynomialBound c.scratchBits 64 ∧
  (∃ k, PolynomialBound c.queryNonforcedBits k) ∧
  (∃ C, 0 < C ∧ ∀ N Q, c.flatOutputBits N Q ≤ c.queryNonforcedBits N + C * Q)

def StrictQueryGoal (time scratch : ℕ → ℕ) : Prop :=
  PolynomialBound time 125 ∧ PolynomialBound scratch 64

theorem final_cell_exponent_arithmetic : 3 * 4 = (12 : ℕ) ∧
    3 * 20 = (60 : ℕ) ∧ 60 + 60 + 1 + 1 = (122 : ℕ) ∧ 12 + 2 = (14 : ℕ) := by
  norm_num

/- To inhabit ExactBinaryCompilerGoal, define a uniform machine/encoding and
charge input validation, capped-cell/branch enumeration, integral DBM work,
recovery/templates, queries and actual outputQ. Bounds for the numerical cap
may not replace the complete binary inputN or charge exponential forced
output as polynomial preprocessing. R8 neighbor/iteration costs are reserved. -/
end Partials.Parity.Resources
