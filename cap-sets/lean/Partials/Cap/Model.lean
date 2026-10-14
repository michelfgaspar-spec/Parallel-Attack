import Partials.Shared.FiniteAlgebra
import Partials.Shared.FiniteCertificates

/-! R5 blind source model. All finite field/certificate admissions remain
explicit duties. Integer labels are not field arithmetic. -/
namespace Partials.Cap

noncomputable section
open Polynomial

abbrev Code8 := Partials.Interface.TernaryCode8
abbrev Label := Fin 6561
abbrev Vertex := ZMod 41
abbrev Point (K : Type*) := K × K
abbrev Hypergraph (α : Type*) := Finset (Finset α)

def Independent {α : Type*} [DecidableEq α]
    (graph : Hypergraph α) (s : Finset α) : Prop :=
  ∀ e ∈ graph, ¬ e ⊆ s

def fieldModulus : Polynomial (ZMod 3) := X ^ 8 + X ^ 2 + C 2
def fieldIdeal : Ideal (Polynomial (ZMod 3)) := Ideal.span {fieldModulus}
abbrev QuotientRing := Polynomial (ZMod 3) ⧸ fieldIdeal
def quotientZ : QuotientRing := Ideal.Quotient.mk fieldIdeal X
def codePolynomial (a : Code8) : Polynomial (ZMod 3) :=
  ∑ i : Fin 8, C (a i) * X ^ i.val
def quotientDecode (a : Code8) : QuotientRing :=
  Ideal.Quotient.mk fieldIdeal (codePolynomial a)

section Field
variable {K : Type*} [Field K] [CharP K 3]

def parabolaPoint (a x : K) : Point K := (x, a * x ^ 2)
def PSet (S : Set K) : Set (Point K) := Partials.Interface.ParabolaUnion S
def P (S : Finset K) : Set (Point K) := PSet (S : Set K)
def Cap (U : Set (Point K)) : Prop := Partials.Interface.IsCap U
def Square (a : K) : Prop := ∃ x : K, x ^ 2 = a
def delta (a b c : K) : K := -(a * b + a * c + b * c)
def quadratic (a b c t : K) : K := (a + c) * t ^ 2 + 2 * c * t + (b + c)
def ratioAdmissible (t : K) : Prop := t ≠ 0 ∧ t ≠ -1
def normA (a t : K) : Point K := parabolaPoint a t
def normB (b : K) : Point K := parabolaPoint b 1
def normC (c t : K) : Point K := parabolaPoint c (-t - 1)
def NonAntipodal (S : Set K) : Prop := ∀ a ∈ S, ∀ b ∈ S, a + b ≠ 0
def NonzeroCoefficients (S : Set K) : Prop := ∀ a ∈ S, a ≠ 0

def primitive (z : K) : K := z ^ 3 + z ^ 2 + 2
def subgroupGenerator (z : K) : K := z ^ 6 + z ^ 5 + 2 * z ^ 2 + z
def coefficient (z : K) (i : Vertex) : K := subgroupGenerator z ^ i.val
def H41 (z : K) : Set K := Set.range (coefficient z)
def oppositeCoset (z : K) : Set K := {b | ∃ a ∈ H41 z, b = primitive z * a}
def domainD (z : K) : Set K := H41 z ∪ oppositeCoset z

def ExponentCoefficients [DecidableEq K] (z : K) (T : Finset Vertex) : Finset K :=
  T.image (coefficient z)
def witnessExponents : Finset Vertex := {0, 2, 6, 13, 23}
def witnessCoefficients [DecidableEq K] (z : K) : Finset K :=
  ExponentCoefficients z witnessExponents

def DiscriminantEdge [DecidableEq K] (z : K) (e : Finset Vertex) : Prop :=
  e.card = 3 ∧ ∃ i ∈ e, ∃ j ∈ e, ∃ k ∈ e,
    i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ Square (delta (coefficient z i) (coefficient z j) (coefficient z k))
def discriminantHypergraph [DecidableEq K] (z : K) : Hypergraph Vertex := by
  classical
  exact Finset.univ.filter (DiscriminantEdge z)

def CapCoefficientSet [DecidableEq K] (E : Set K) (S : Finset K) : Prop :=
  (↑S : Set K) ⊆ E ∧ Cap (P S)
def MaximumFive [DecidableEq K] (E : Set K) : Prop :=
  (∀ S : Finset K, CapCoefficientSet E S → S.card ≤ 5) ∧
    ∃ S : Finset K, CapCoefficientSet E S ∧ S.card = 5
def Maximizers [DecidableEq K] (E : Set K) : Set (Finset K) :=
  {S | CapCoefficientSet E S ∧ S.card = 5}

end Field

def affine (t : Vertex) (j : Fin 8) (v : Vertex) : Vertex := (3 : Vertex) ^ j.val * v + t
def affineImage (t : Vertex) (j : Fin 8) (T : Finset Vertex) : Finset Vertex :=
  T.image (affine t j)
def witnessOrbit : Finset (Finset Vertex) :=
  (Finset.univ : Finset (Vertex × Fin 8)).image (fun p => affineImage p.1 p.2 witnessExponents)

end
end Partials.Cap
