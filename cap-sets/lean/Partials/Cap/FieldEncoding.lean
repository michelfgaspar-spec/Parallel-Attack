import Partials.Cap.Model
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.BigOperators.Fin

/-! Polynomial-reduction code operations. This source is uncompiled.
The exact quotient-field realization and decoding bijection remain unproved. -/
namespace Partials.Cap.Encoding

noncomputable section
open Partials.Cap Polynomial

def zeroCode : Code8 := fun _ => 0
def oneCode : Code8 := fun i => if i = 0 then 1 else 0
def addCode (a b : Code8) : Code8 := fun i => a i + b i
def negCode (a : Code8) : Code8 := fun i => -a i

/-- Multiplication by z uses z^8=1+2z^2, not a coordinatewise product. -/
def timesZ (a : Code8) : Code8 := ![a 7, a 0, a 1 + 2 * a 7, a 2, a 3, a 4, a 5, a 6]
def mulCode (a b : Code8) : Code8 :=
  fun j => ∑ i : Fin 8, b i * ((timesZ^[i.val]) a) j
def labelDigits (n : Label) : Code8 :=
  fun i => ((n.val / 3 ^ i.val) % 3 : ℕ)
def codeLabelValue (a : Code8) : ℕ := ∑ i : Fin 8, (a i).val * 3 ^ i.val

def evalCode {R : Type*} [CommRing R] (ι : ZMod 3 →+* R) (z : R) (a : Code8) : R :=
  ∑ i : Fin 8, ι (a i) * z ^ i.val

theorem eval_zero {R : Type*} [CommRing R] (ι : ZMod 3 →+* R) (z : R) :
    evalCode ι z zeroCode = 0 := by simp [evalCode, zeroCode]
theorem eval_one {R : Type*} [CommRing R] (ι : ZMod 3 →+* R) (z : R) :
    evalCode ι z oneCode = 1 := by simp [evalCode, oneCode]
theorem eval_add {R : Type*} [CommRing R] (ι : ZMod 3 →+* R) (z : R) (a b : Code8) :
    evalCode ι z (addCode a b) = evalCode ι z a + evalCode ι z b := by
  simp [evalCode, addCode, add_mul, Finset.sum_add_distrib]
theorem eval_neg {R : Type*} [CommRing R] (ι : ZMod 3 →+* R) (z : R) (a : Code8) :
    evalCode ι z (negCode a) = -evalCode ι z a := by simp [evalCode, negCode]

theorem eval_timesZ {R : Type*} [CommRing R] (ι : ZMod 3 →+* R) (z : R)
    (hz : z ^ 8 = 1 + 2 * z ^ 2) (a : Code8) :
    evalCode ι z (timesZ a) = z * evalCode ι z a := by
  have htwo : ι (2 : ZMod 3) = (2 : R) := by
    calc
      ι (2 : ZMod 3) = ι (1 + 1) := congrArg ι (by decide)
      _ = 2 := by rw [map_add, map_one]; ring
  norm_num [evalCode, timesZ, Fin.sum_univ_succ]
  rw [htwo]
  change ι (a 7) + (ι (a 0) * z + ((ι (a 1) + 2 * ι (a 7)) * z ^ 2 +
    (ι (a 2) * z ^ 3 + (ι (a 3) * z ^ 4 + (ι (a 4) * z ^ 5 +
    (ι (a 5) * z ^ 6 + ι (a 6) * z ^ 7)))))) =
    z * (ι (a 0) + (ι (a 1) * z + (ι (a 2) * z ^ 2 + (ι (a 3) * z ^ 3 +
      (ι (a 4) * z ^ 4 + (ι (a 5) * z ^ 5 + (ι (a 6) * z ^ 6 + ι (a 7) * z ^ 7)))))))
  linear_combination -ι (a 7) * hz

theorem eval_iterate {R : Type*} [CommRing R] (ι : ZMod 3 →+* R) (z : R)
    (hz : z ^ 8 = 1 + 2 * z ^ 2) (a : Code8) (n : ℕ) :
    evalCode ι z ((timesZ^[n]) a) = z ^ n * evalCode ι z a := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', eval_timesZ ι z hz, ih]
      simp [pow_succ, mul_assoc, mul_comm, mul_left_comm]

theorem eval_linear_combination {R : Type*} [CommRing R]
    (ι : ZMod 3 →+* R) (z : R) (b : Code8) (f : Fin 8 → Code8) :
    evalCode ι z (fun j => ∑ i : Fin 8, b i * f i j) =
      ∑ i : Fin 8, ι (b i) * evalCode ι z (f i) := by
  simp only [evalCode, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem eval_mul {R : Type*} [CommRing R] (ι : ZMod 3 →+* R) (z : R)
    (hz : z ^ 8 = 1 + 2 * z ^ 2) (a b : Code8) :
    evalCode ι z (mulCode a b) = evalCode ι z a * evalCode ι z b := by
  change evalCode ι z (fun j => ∑ i : Fin 8, b i * ((timesZ^[i.val]) a) j) = _
  rw [eval_linear_combination]
  simp_rw [eval_iterate ι z hz]
  change _ = evalCode ι z a * ∑ i : Fin 8, ι (b i) * z ^ i.val
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def quotientConstants : ZMod 3 →+* QuotientRing :=
  (Ideal.Quotient.mk fieldIdeal).comp Polynomial.C

theorem quotientDecode_eq_eval (a : Code8) :
    quotientDecode a = evalCode quotientConstants quotientZ a := by
  simp [quotientDecode, codePolynomial, evalCode, quotientConstants, quotientZ]

/-- Fine algebraic quotient relation duty, not a field or cap conclusion. -/
def QuotientReductionDuty : Prop := quotientZ ^ 8 = 1 + 2 * quotientZ ^ 2

/-- The reduction relation follows in the actual ideal quotient without a field instance. -/
theorem quotient_reduction_from_modulus : QuotientReductionDuty := by
  have hm : Ideal.Quotient.mk fieldIdeal fieldModulus = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have hrel : quotientZ ^ 8 + quotientZ ^ 2 + 2 = 0 := by
    simpa only [fieldModulus, map_add, map_pow, Polynomial.C_ofNat, map_ofNat,
      quotientZ] using hm
  have hthree : (3 : QuotientRing) = 0 := by
    have h := congrArg quotientConstants (show (3 : ZMod 3) = 0 by decide)
    simpa only [map_ofNat, map_zero] using h
  unfold QuotientReductionDuty
  linear_combination hrel - (quotientZ ^ 2 + 1) * hthree

theorem quotient_decode_zero : quotientDecode zeroCode = 0 := by
  rw [quotientDecode_eq_eval, eval_zero]
theorem quotient_decode_one : quotientDecode oneCode = 1 := by
  rw [quotientDecode_eq_eval, eval_one]
theorem quotient_decode_add (a b : Code8) :
    quotientDecode (addCode a b) = quotientDecode a + quotientDecode b := by
  simp_rw [quotientDecode_eq_eval]
  exact eval_add _ _ _ _
theorem quotient_decode_mul (h : QuotientReductionDuty) (a b : Code8) :
    quotientDecode (mulCode a b) = quotientDecode a * quotientDecode b := by
  simp_rw [quotientDecode_eq_eval]
  exact eval_mul _ _ h a b

theorem quotient_decode_mul_unconditional (a b : Code8) :
    quotientDecode (mulCode a b) = quotientDecode a * quotientDecode b :=
  quotient_decode_mul quotient_reduction_from_modulus a b

variable (K : Type*) [Field K] [CharP K 3]

/-- No inhabitant is provided. A primitive-cycle or irreducible-modulus proof
must first construct the exact quotient field and this characteristic-three
realization, rather than using pointwise Code8 multiplication. -/
structure FieldRealization where
  equiv : QuotientRing ≃+* K
  code_bijective : Function.Bijective quotientDecode

def exactEncoding (r : FieldRealization K) (hq : QuotientReductionDuty) :
    Partials.Interface.ExactFieldEncoding K where
  decode := r.equiv ∘ quotientDecode
  bijective := r.equiv.bijective.comp r.code_bijective
  zeroCode := zeroCode
  oneCode := oneCode
  addCode := addCode
  mulCode := mulCode
  decode_zero := by simp [Function.comp_def, quotient_decode_zero]
  decode_one := by simp [Function.comp_def, quotient_decode_one]
  decode_add := by intro a b; simp [Function.comp_def, quotient_decode_add]
  decode_mul := by intro a b; simp [Function.comp_def, quotient_decode_mul hq]

/-- Exact finite base-three normal-form duty; no value has been evaluated. -/
def LabelNormalFormDuty : Prop :=
  Function.Bijective labelDigits ∧ ∀ n : Label, codeLabelValue (labelDigits n) = n.val

def CoordinateCycleDuty (r : FieldRealization K) : Prop :=
  let decode := r.equiv ∘ quotientDecode
  let g := decode (labelDigits ⟨38, by norm_num⟩)
  let h := decode (labelDigits ⟨993, by norm_num⟩)
  (∀ x : K, x ≠ 0 → ∃ i : Fin 6560, g ^ i.val = x) ∧
    Function.Injective (fun i : Fin 6560 => g ^ i.val) ∧ g ^ 6560 = 1 ∧
    h = g ^ 160 ∧ h ^ 41 = 1 ∧
    Function.Injective (fun i : Fin 41 => h ^ i.val)

end
end Partials.Cap.Encoding
