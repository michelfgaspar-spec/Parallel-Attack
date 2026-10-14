import Partials.Shared.FiniteAlgebra
import Partials.Shared.FiniteGraphs
import Partials.Shared.FiniteCertificates
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! R6 BLIND SOURCE, NOT COMPILED. Exact definitions from frozen main.tex
and supplement.tex. No numerical, cyclotomic, geometric or checker evaluation
has been performed. The binary quotient is a ring/vector-space presentation;
this module supplies no Field instance for it. -/
namespace Partials.UnitDistance

abbrev BinaryCode := Partials.Interface.BinaryQuotientCode12
abbrev IntegerCode := Fin 12 → ℤ
abbrev RationalCode := Fin 12 → ℚ
abbrev Colour4 := Fin 4
abbrev BinaryPalette := ZMod 2 × ZMod 2

noncomputable def phi42 : Polynomial ℤ :=
  Polynomial.X ^ 12 + Polynomial.X ^ 11 - Polynomial.X ^ 9 -
  Polynomial.X ^ 8 + Polynomial.X ^ 6 - Polynomial.X ^ 4 -
  Polynomial.X ^ 3 + Polynomial.X + 1

noncomputable def numeratorPolynomial : Polynomial ℤ :=
  2 + Polynomial.X + 3 * Polynomial.X ^ 2 - 2 * Polynomial.X ^ 4 +
  Polynomial.X ^ 5 + 5 * Polynomial.X ^ 6 + Polynomial.X ^ 7 +
  Polynomial.X ^ 8 - 6 * Polynomial.X ^ 9 - 4 * Polynomial.X ^ 10 +
  4 * Polynomial.X ^ 11

noncomputable def binaryPhi42 : Polynomial (ZMod 2) :=
  phi42.map (Int.castRingHom (ZMod 2))

abbrev BinaryPolynomialQuotient :=
  (Polynomial (ZMod 2)) ⧸ Ideal.span ({binaryPhi42} : Set (Polynomial (ZMod 2)))

noncomputable def w : ℂ := Complex.exp (((Real.pi / 21 : ℝ) : ℂ) * Complex.I)
noncomputable def rho : ℂ := w ^ 7
noncomputable def delta : ℂ := 2 * rho - 1
noncomputable def t : ℂ := numeratorPolynomial.eval₂ (Int.castRingHom ℂ) w / 7

noncomputable def evalInteger (c : IntegerCode) : ℂ :=
  ∑ i : Fin 12, (c i : ℂ) * w ^ i.val

noncomputable def evalRational (c : RationalCode) : ℂ :=
  ∑ i : Fin 12, (c i : ℂ) * w ^ i.val

def O : Set ℂ := Set.range evalInteger
def M1 : Set ℂ := {z | ∃ a ∈ O, ∃ b ∈ O, z = a + t * b}
def M2 : Set ℂ := {z | ∃ a ∈ O, ∃ b ∈ O, ∃ c ∈ O,
  z = a + t * b + t ^ 2 * c}

noncomputable def point49 (c : IntegerCode) : ℂ := evalInteger c / 49
def Height49AtMost (c : IntegerCode) (bound : ℕ) : Prop :=
  ∀ i, |c i| ≤ (bound : ℤ)

noncomputable def «section» (v : BinaryCode) : ℂ :=
  ∑ i : Fin 12, ((v i).val : ℂ) * w ^ i.val

abbrev UnitIndex := Fin 3 × Fin 42
abbrev HalfUnitIndex := Fin 3 × Fin 21
noncomputable def indexedUnit (i : UnitIndex) : ℂ := t ^ i.1.val * w ^ i.2.val
noncomputable def halfUnit (i : HalfUnitIndex) : ℂ := t ^ i.1.val * w ^ i.2.val
noncomputable def seedTransport (i : UnitIndex) (z : ℂ) : ℂ :=
  if i.1.val = 2 then -(indexedUnit i) * star z else indexedUnit i * z

noncomputable def UnitDistance (a b : ℂ) : Prop := Complex.normSq (a - b) = 1

/-- Finite, identified physical coordinates with selected oriented edges.
Induced unit edges are a separate relation; unordered-edge deduplication is a
consumer duty. No count or unit-distance fact is hidden in this structure. -/
structure PhysicalGraph where
  vertices : Finset ℂ
  edges : Finset (ℂ × ℂ)
  endpoints : ∀ e ∈ edges, e.1 ∈ vertices ∧ e.2 ∈ vertices
  nonloop : ∀ e ∈ edges, e.1 ≠ e.2

def ProperPhysical (G : PhysicalGraph) (c : ℂ → Colour4) : Prop :=
  ∀ e ∈ G.edges, c e.1 ≠ c e.2

def IsSelectedUnitGraph (G : PhysicalGraph) : Prop :=
  ∀ e ∈ G.edges, UnitDistance e.1 e.2

def InducedUnitPair (G : PhysicalGraph) (a b : ℂ) : Prop :=
  a ∈ G.vertices ∧ b ∈ G.vertices ∧ a ≠ b ∧ UnitDistance a b

def NoFourColouring (G : PhysicalGraph) : Prop :=
  ¬ ∃ c : ℂ → Colour4, ProperPhysical G c

/-- Imported terminal separation is explicit. A local SAT status UNKNOWN
supplies no witness. Coordinate/unit-edge applicability is a different duty. -/
def ExternalSeedForce (G1 : PhysicalGraph) : Prop :=
  ∀ c : ℂ → Colour4, ProperPhysical G1 c → c 0 ≠ c delta

def RootLetterCount := Fin 42 → ℕ
noncomputable def rootWordValue (counts : RootLetterCount) : ℂ :=
  ∑ r : Fin 42, (counts r : ℂ) * w ^ r.val
def rootWordCost (counts : RootLetterCount) : ℕ := ∑ r : Fin 42, counts r

abbrev SevenPairs := Fin 7 → ℤ × ℤ
noncomputable def zeta : ℂ := w ^ 6
noncomputable def sevenPairValue (p : SevenPairs) : ℂ :=
  ∑ k : Fin 7, ((p k).1 + (p k).2 * rho) * zeta ^ k.val

/-- Primitive basis/membership bridge, not a headline non-colouring witness. -/
structure CyclotomicBasisDuty : Prop where
  annihilation : phi42.eval₂ (Int.castRingHom ℂ) w = 0
  basis_unique : Function.Injective evalRational
  order42 : w ^ 42 = 1
  rho_relation : rho ^ 2 - rho + 1 = 0
  w_norm : Complex.normSq w = 1
  t_norm : Complex.normSq t = 1
  conjugate_t : star t * t = 1
  denominator : ∀ z ∈ M2, ∃ c : IntegerCode, z = point49 c
  rotation : ∀ z ∈ M2, ∀ r : Fin 42, z * w ^ r.val ∈ M2
  translation : ∀ x ∈ M2, ∀ y ∈ M2, x + y ∈ M2

end Partials.UnitDistance
