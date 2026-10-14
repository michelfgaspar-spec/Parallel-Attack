import Partials.UnitDistance.Model

/-! BLIND source for main.tex endpoint lifting. Parity/normal-form admissions
are separate primitive duties; a word of length zero is allowed. -/
namespace Partials.UnitDistance.Lift

def shellDenominator (j : Fin 3) : ℕ := 7 ^ j.val
def tailLength (j : Fin 3) : ℕ := (shellDenominator j - 1) / 2

noncomputable def integralTarget (a b : BinaryCode) (i : HalfUnitIndex) : ℂ :=
  («section» a - «section» b + (shellDenominator i.1 : ℂ) * halfUnit i) / 2

noncomputable def liftedEndpoint (a : BinaryCode) (i : HalfUnitIndex) : ℂ :=
  «section» a + halfUnit i

theorem odd_denominator_tail (j : Fin 3) :
    shellDenominator j = 2 * tailLength j + 1 := by
  fin_cases j <;> norm_num [shellDenominator, tailLength]

theorem target_displacement (a b : BinaryCode) (i : HalfUnitIndex) :
    integralTarget a b i - (tailLength i.1 : ℂ) * halfUnit i =
      (liftedEndpoint a i - «section» b) / 2 := by
  have hd := odd_denominator_tail i.1
  have hdc : (shellDenominator i.1 : ℂ) = 2 * (tailLength i.1 : ℂ) + 1 := by
    exact_mod_cast hd
  unfold integralTarget liftedEndpoint
  rw [hdc]
  ring

noncomputable def doubledPathEnd (start : ℂ) (word : List ℂ) : ℂ :=
  start + 2 * word.sum

theorem empty_path (start : ℂ) : doubledPathEnd start [] = start := by
  simp [doubledPathEnd]

theorem append_path_end (start : ℂ) (p q : List ℂ) :
    doubledPathEnd start (p ++ q) = doubledPathEnd (doubledPathEnd start p) q := by
  simp only [doubledPathEnd, List.sum_append]
  ring

theorem exact_lifted_endpoint (a b : BinaryCode) (i : HalfUnitIndex)
    (rootPart tailPart : List ℂ)
    (hroot : rootPart.sum = integralTarget a b i)
    (htail : tailPart.sum = -(tailLength i.1 : ℂ) * halfUnit i) :
    doubledPathEnd («section» b) (rootPart ++ tailPart) = liftedEndpoint a i := by
  have h := target_displacement a b i
  simp only [doubledPathEnd, List.sum_append, hroot, htail]
  linear_combination 2 * h

/-- The actual quotient residue is an input map. Its bijective code/ring
correspondence and exact retained-direction list remain separately unproved. -/
def QuotientAdjacent (residue : HalfUnitIndex → BinaryCode)
    (retained : Finset HalfUnitIndex) (a b : BinaryCode) : Prop :=
  ∃ i ∈ retained, b = a + residue i

def ProperQuotient (residue : HalfUnitIndex → BinaryCode)
    (retained : Finset HalfUnitIndex) (c : BinaryCode → Colour4) : Prop :=
  ∀ a b, QuotientAdjacent residue retained a b → c a ≠ c b

structure ParityAndPathDuty (residue : HalfUnitIndex → BinaryCode)
    (retained : Finset HalfUnitIndex) : Prop where
  representative_mod2 : ∀ a, «section» a ∈ M2
  direction_mod2 : ∀ i ∈ retained, halfUnit i ∈ M2
  nonzero_residue : ∀ i ∈ retained, residue i ≠ 0
  target_integral : ∀ i ∈ retained, ∀ a b, b = a + residue i →
    integralTarget a b i ∈ O
  direction_unit : ∀ i ∈ retained, Complex.normSq (halfUnit i) = 1

theorem physical_to_quotient (G : PhysicalGraph)
    (residue : HalfUnitIndex → BinaryCode) (retained : Finset HalfUnitIndex)
    (c : ℂ → Colour4) (hproper : ProperPhysical G c)
    (hedge : ∀ i ∈ retained, ∀ a b, b = a + residue i →
      («section» a, liftedEndpoint a i) ∈ G.edges)
    (hequality : ∀ i ∈ retained, ∀ a b, b = a + residue i →
      c (liftedEndpoint a i) = c («section» b)) :
    ProperQuotient residue retained (fun a => c («section» a)) := by
  intro a b hab
  obtain ⟨i, hi, hb⟩ := hab
  have hn := hproper («section» a, liftedEndpoint a i) (hedge i hi a b hb)
  simpa only [hequality i hi a b hb] using hn

theorem finite_obstruction (G : PhysicalGraph)
    (residue : HalfUnitIndex → BinaryCode) (retained : Finset HalfUnitIndex)
    (hquotient : ¬ ∃ q, ProperQuotient residue retained q)
    (hedge : ∀ i ∈ retained, ∀ a b, b = a + residue i →
      («section» a, liftedEndpoint a i) ∈ G.edges)
    (hnetwork : ∀ c, ProperPhysical G c → ∀ i ∈ retained, ∀ a b,
      b = a + residue i → c (liftedEndpoint a i) = c («section» b)) :
    NoFourColouring G := by
  rintro ⟨c, hc⟩
  exact hquotient ⟨fun a => c («section» a),
    physical_to_quotient G residue retained c hc hedge (hnetwork c hc)⟩

end Partials.UnitDistance.Lift
