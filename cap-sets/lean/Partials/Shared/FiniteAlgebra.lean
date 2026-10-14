import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! R1 exact encoding interfaces. The cap field and binary quotient use
different structures: no field assumption is imposed on the latter. -/
namespace Partials.Interface

abbrev TernaryCode8 := Fin 8 → ZMod 3
abbrev BinaryQuotientCode12 := Fin 12 → ZMod 2

/-- Polynomial-reduction operations on codes are explicit inputs, never the
pointwise multiplication of eight coordinates. Concrete laws are proved in R5. -/
structure ExactFieldEncoding (K : Type*) [Field K] [CharP K 3] where
  decode : TernaryCode8 → K
  bijective : Function.Bijective decode
  zeroCode : TernaryCode8
  oneCode : TernaryCode8
  addCode : TernaryCode8 → TernaryCode8 → TernaryCode8
  mulCode : TernaryCode8 → TernaryCode8 → TernaryCode8
  decode_zero : decode zeroCode = 0
  decode_one : decode oneCode = 1
  decode_add : ∀ a b, decode (addCode a b) = decode a + decode b
  decode_mul : ∀ a b, decode (mulCode a b) = decode a * decode b

def PuncturedParabola {K : Type*} [Field K] (coefficient : K) : Set (K × K) :=
  {point | ∃ x : K, x ≠ 0 ∧ point = (x, coefficient * x ^ 2)}

def ParabolaUnion {K : Type*} [Field K] (coefficients : Set K) : Set (K × K) :=
  {point | ∃ c ∈ coefficients, point ∈ PuncturedParabola c}

/-- Three distinct points in characteristic three, preserving the distinction
from repeated labels in the later coefficient/discriminant bridge. The
characteristic-three instance is a caller obligation, not proved here. -/
def IsCap {K : Type*} [Field K] [CharP K 3] (points : Set (K × K)) : Prop :=
  ∀ a ∈ points, ∀ b ∈ points, ∀ c ∈ points,
    a ≠ b → a ≠ c → b ≠ c → a + b + c ≠ 0

end Partials.Interface
