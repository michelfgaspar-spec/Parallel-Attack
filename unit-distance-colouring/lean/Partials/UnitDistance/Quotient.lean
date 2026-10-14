import Partials.UnitDistance.Model

/-! R6 blind source; no elaboration or arithmetic evaluation is asserted.
The polynomial quotient and its twelve binary coordinates are additive/ring
objects. Neither this module nor its consumers impose a Field instance on V.
The geometric quotient is represented below by an explicit congruence rather
than by an unproved identification of physical coordinates. -/
namespace Partials.UnitDistance

def TwiceCongruent (M : AddSubgroup ℂ) (a b : ℂ) : Prop :=
  ∃ y ∈ M, a - b = 2 * y

theorem twiceCongruent_refl (M : AddSubgroup ℂ) (a : ℂ) :
    TwiceCongruent M a a := by
  exact ⟨0, M.zero_mem, by ring⟩

theorem twiceCongruent_symm (M : AddSubgroup ℂ) {a b : ℂ}
    (h : TwiceCongruent M a b) : TwiceCongruent M b a := by
  obtain ⟨y, hy, he⟩ := h
  refine ⟨-y, M.neg_mem hy, ?_⟩
  linear_combination -he

theorem twiceCongruent_trans (M : AddSubgroup ℂ) {a b c : ℂ}
    (hab : TwiceCongruent M a b) (hbc : TwiceCongruent M b c) :
    TwiceCongruent M a c := by
  obtain ⟨y, hy, hey⟩ := hab
  obtain ⟨z, hz, hez⟩ := hbc
  refine ⟨y + z, M.add_mem hy hz, ?_⟩
  linear_combination hey + hez

/-- Elementary divisibility underlying injectivity at the odd denominator.
This proof text has not been evaluated. -/
theorem odd49_divides_of_twice {c : ℤ} (h : (49 : ℤ) ∣ 2 * c) :
    (49 : ℤ) ∣ c := by
  obtain ⟨k, hk⟩ := h
  refine ⟨25 * k - c, ?_⟩
  linear_combination 25 * hk

/-- Surjectivity on residue representatives needs only the scaling and module
closure. The witness is -24y, since y-49y=2(-24y). -/
theorem odd49_residue_representative (L M : AddSubgroup ℂ)
    (hscale : ∀ y ∈ M, 49 * y ∈ L) (y : ℂ) (hy : y ∈ M) :
    ∃ o ∈ L, TwiceCongruent M y o := by
  refine ⟨49 * y, hscale y hy, -(24 • y), M.neg_mem (M.nsmul_mem hy 24), ?_⟩
  simp only [nsmul_eq_mul]
  ring

/-- Primitive coordinate facts needed to instantiate the physical quotient.
`half_integral` is the lattice fact obtained coefficientwise from
odd49_divides_of_twice and the unique twelve-coefficient power basis. It is
not a supplied colouring or line-hit conclusion. -/
structure OddDenominatorLatticeDuty where
  lattice : AddSubgroup ℂ
  module : AddSubgroup ℂ
  lattice_exact : (lattice : Set ℂ) = O
  module_exact : (module : Set ℂ) = M2
  inclusion : lattice ≤ module
  scale49 : ∀ y ∈ module, 49 * y ∈ lattice
  half_integral : ∀ y ∈ module, 2 * y ∈ lattice → y ∈ lattice

theorem inclusion_reflects_twice_congruence (D : OddDenominatorLatticeDuty)
    (a b : ℂ) (ha : a ∈ D.lattice) (hb : b ∈ D.lattice) :
    TwiceCongruent D.module a b ↔ TwiceCongruent D.lattice a b := by
  constructor
  · rintro ⟨y, hy, he⟩
    have htwo : 2 * y ∈ D.lattice := by
      rw [← he]
      exact D.lattice.sub_mem ha hb
    exact ⟨y, D.half_integral y hy htwo, he⟩
  · rintro ⟨y, hy, he⟩
    exact ⟨y, D.inclusion hy, he⟩

theorem inclusion_surjective_on_residues (D : OddDenominatorLatticeDuty)
    (y : ℂ) (hy : y ∈ D.module) :
    ∃ o ∈ D.lattice, TwiceCongruent D.module y o :=
  odd49_residue_representative D.lattice D.module D.scale49 y hy

/-- Concrete normal-form/reduction obligations. The last iff states the
kernel, not a finite graph or chromatic claim. The additive equivalence must
be the degree-below-twelve polynomial normal form with the frozen coefficient
order; an arbitrary bijection is insufficient. -/
structure BinaryReductionDuty (D : OddDenominatorLatticeDuty) where
  normalForm : BinaryCode ≃+ BinaryPolynomialQuotient
  normalForm_coefficients : ∀ v : BinaryCode,
    normalForm v = Ideal.Quotient.mk _
      (∑ i : Fin 12, Polynomial.C (v i) * Polynomial.X ^ i.val)
  reduce : D.module →+ BinaryCode
  surjective : Function.Surjective reduce
  kernel : ∀ a b : D.module,
    reduce a = reduce b ↔ TwiceCongruent D.module a.val b.val
  section_mem : ∀ v : BinaryCode, «section» v ∈ D.module
  section_right_inverse : ∀ v : BinaryCode,
    reduce ⟨«section» v, section_mem v⟩ = v

theorem section_classes_distinct (D : OddDenominatorLatticeDuty)
    (B : BinaryReductionDuty D) (a b : BinaryCode)
    (h : TwiceCongruent D.module («section» a) («section» b)) : a = b := by
  have he := (B.kernel ⟨«section» a, B.section_mem a⟩
    ⟨«section» b, B.section_mem b⟩).2 h
  simpa only [B.section_right_inverse] using he

/-- Common multiplication by [rho], with its characteristic-two relation.
This is enough for the paired-character converse. The full F4 module
instance, if desired, must be constructed separately from this action. -/
structure CommonBinaryLineFamily (V : Type*) [AddCommGroup V] where
  R : V →+ V
  square : ∀ v, R (R v) = v + R v
  two_torsion : ∀ v : V, v + v = 0
  head : Fin 21 → V
  head_nonzero : ∀ i, head i ≠ 0
  head_distinct_rotate : ∀ i, head i ≠ R (head i)

variable {V : Type*} [AddCommGroup V]

theorem common_rotation_sum (F : CommonBinaryLineFamily V) (v : V) :
    F.R (v + F.R v) = v := by
  rw [map_add, F.square]
  calc
    F.R v + (v + F.R v) = v + (F.R v + F.R v) := by abel
    _ = v := by rw [F.two_torsion]; simp

theorem common_rotation_cube (F : CommonBinaryLineFamily V) (v : V) :
    F.R (F.R (F.R v)) = v := by
  rw [F.square v]
  exact common_rotation_sum F v

end Partials.UnitDistance
