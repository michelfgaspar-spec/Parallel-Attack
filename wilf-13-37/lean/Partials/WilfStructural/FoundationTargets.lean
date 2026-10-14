import Partials.WilfStructural.MixedInterval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Quotient.Basic

/-! Full targets are Prop definitions, NOT theorem declarations. Imported results
and unavailable semigroup instantiations remain explicit. No axiom, sorry,
conclusion-containing bridge instance, or import of another R9 worker is used. -/
namespace Partials.WilfStructural.Foundation
open Partials.Interface
open scoped BigOperators

/-- Complete L1 residue and profile target. Basic subsum/cutoff components have
separate theorems; this proposition is deliberately not supplied an inhabitant. -/
def AperyPartitionTarget (d : Data) : Prop :=
  (∀ r < d.m, ∃! a, IsAperyAt d.S d.m a ∧ a % d.m = r) ∧
  (A d).card = d.m ∧ d.m = e d + delta d ∧
  n d = depth d + ∑ i ∈ Finset.Icc 1 (depth d-1), (depth d-i)*alpha d i ∧
  1 ≤ depth d ∧ depth d ≤ n d ∧ kappa d 1 = 0 ∧ max 2 (1+s d) ≤ e d

def CompressionTarget (d : Data) : Prop := (compressed d).card ≤ rho d

def WeightedPairsTarget (d : Data) : Prop :=
  (depth d : ℤ)*delta d-rho d ≤ ((tL d : ℤ)+1)*nu d

def ShallowTarget : Prop := ∀ d : Data, depth d ≤ 2 → 0 ≤ W d

def QuadraticTarget : Prop := ∀ d : Data, W d < 0 →
  5 ≤ n d ∧ 3 ≤ depth d ∧ depth d ≤ n d-2 ∧
  2 ≤ e d ∧ e d ≤ tL d ∧ (tL d : ℤ) ≤ nu d ∧
  2*n d ≤ d.c ∧ (d.c : ℤ) ≤ (n d : ℤ)*tL d+nu d ∧
  (n d : ℤ)*tL d+nu d ≤ nu d*((n d : ℤ)+1) ∧
  nu d*((n d : ℤ)+1) ≤ ((n d : ℤ)-3)*((n d : ℤ)+1)

def MixedPositiveTarget : Prop := ∀ (d : Data) (h : MixedFamily d),
  (1 ≤ mixedLowCount h → (rho d : ℤ) ≤ W0 d) ∧
  (mixedLowCount h=0 → (rho d : ℤ)-(h.X.card : ℤ)+4 ≤ W0 d ∧
    5 ≤ (rho d : ℤ)-(h.X.card : ℤ)+4) ∧ 0 < W0 d

/-- GRAPH uses all positive Apéry values; incident vertices automatically lie
left by the universal proper-subsum argument. The graph has loops. -/
noncomputable def graphX (d : Data) : Finset ℕ := (A d).erase 0
noncomputable def graphEdges (d : Data) : Finset (ℕ × ℕ) := by
  classical
  exact (unorderedPairs (graphX d)).filter (fun p => p.1+p.2 ∈ graphX d)
def touched (F : Finset (ℕ × ℕ)) : Finset ℕ := F.biUnion (fun p => {p.1,p.2})
def IsMatching (F : Finset (ℕ × ℕ)) : Prop :=
  ∀ p ∈ F, ∀ p' ∈ F, p ≠ p' → Disjoint ({p.1,p.2} : Finset ℕ) {p'.1,p'.2}
noncomputable def graphVertices (d : Data) : Finset ℕ := touched (graphEdges d)
noncomputable def graphMatchingNumber (d : Data) : ℕ := by
  classical
  exact ((graphEdges d).powerset.filter IsMatching).sup (fun F => (touched F).card)
def graphDepth (d : Data) (x : ℕ) : ℕ := depth d-level d x
noncomputable def normalEdges (d : Data) (F : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  F.filter (fun p => depth d ≤ graphDepth d p.1+graphDepth d p.2)
noncomputable def normalTouchedMaximum (d : Data) : ℕ := by
  classical
  exact ((graphEdges d).powerset.filter (fun F =>
    IsMatching F ∧ (touched F).card=graphMatchingNumber d)).sup
      (fun F => (touched (normalEdges d F)).card)

def GraphTarget : Prop := ∀ d : Data,
  4 ≤ e d → 4 ≤ depth d → n d ≤ 3*depth d-1 → 0 ≤ W d

/-- Integer form of the cited matching-depth inequality gives k<=4; the full
case analysis is still the exact external GRAPH import, never inferred here. -/
 theorem graph_matching_cap (q tau k b normal : ℤ)
    (hq : 4 ≤ q) (htau : tau ≤ 2*q-1) (hb : k ≤ b) (hnormal : 0 ≤ normal)
    (hdepth : k*(q-1)+normal+2*(b-k) ≤ 2*tau) : k ≤ 4 := by
  by_contra hk
  have hprod := mul_nonneg (show 0 ≤ k-5 by omega) (show 0 ≤ q-1 by omega)
  nlinarith

 theorem graph_five_vertex_collision_exclusion (edges delta : ℤ)
    (hd : 8 ≤ delta) (hsurj : delta ≤ edges)
    (hafter_delete : edges ≤ 2+4) : False := by omega

 theorem graph_delta_ten_repair (e tau q rho W : ℤ)
    (he : 5 ≤ e) (hq : 4 ≤ q) (htau : tau=2*q-1) (hrho : 6 ≤ rho)
    (hW : W=e*tau-10*q+rho) : 1 ≤ W := by
  have hprod := mul_nonneg (show 0 ≤ e-5 by omega) (show 0 ≤ tau by omega)
  nlinarith

 theorem graph_delta_nine_repair (e tau q rho W : ℤ)
    (he : 5 ≤ e) (hq : 4 ≤ q) (htau : tau=2*q-1) (hrho : 0 ≤ rho)
    (hweak : q=4 → 1 ≤ rho) (hW : W=e*tau-9*q+rho) : 0 ≤ W := by
  have hprod := mul_nonneg (show 0 ≤ e-5 by omega) (show 0 ≤ tau by omega)
  by_cases hq4 : q=4
  · have hr := hweak hq4
    nlinarith
  · have hq5 : 5 ≤ q := by omega
    nlinarith

/-- U05: FGH. Exact external premise, currently uninhabited. -/
def ExternalEmbeddingThree : Prop := ∀ d : Data, e d ≤ 3 → 0 ≤ W d
/-- U06: MACAULAY Prop.3.13/Cor.6.5; stronger than authored q<=2 case. -/
def ExternalDepthThree : Prop := ∀ d : Data, depth d ≤ 3 → 0 ≤ W d
/-- U07: EMA12 Thm.3.1/Prop.2.7 with the exact half-depth index. -/
def ExternalEarlyEmpty : Prop := ∀ d : Data, 4 ≤ depth d →
  (∀ i : ℕ, 1 ≤ i → i < (depth d+1)/2 → alpha d i=0) → 0 ≤ W d
/-- U08 includes the frozen corrected graph adapter and unprovided GRAPH cases. -/
def ExternalGraphCases : Prop := GraphTarget
/-- U10 is a reported finite computation, with no certificate bytes in the ZIP. -/
def ExternalConductor200 : Prop := ∀ d : Data, d.c ≤ 200 → 0 ≤ W d

/-- A concrete standard graded Q quotient is a polynomial ring modulo a
homogeneous ideal. The relation subspace has ideal closure and homogeneous
components. This standalone U09 interface does not import another R9 worker. -/
def monomialDegree {vars : ℕ} (a : Fin vars →₀ ℕ) : ℕ := a.sum (fun _ n => n)
noncomputable def degreeSpace (vars degree : ℕ) : Submodule ℚ (MvPolynomial (Fin vars) ℚ) :=
  Submodule.span ℚ {p | ∃ a : Fin vars →₀ ℕ,
    monomialDegree a=degree ∧ p=MvPolynomial.monomial a (1 : ℚ)}
structure HomogeneousPresentation (vars : ℕ) where
  relations : Submodule ℚ (MvPolynomial (Fin vars) ℚ)
  ideal_closed : ∀ p ∈ relations, ∀ f, f*p ∈ relations
  homogeneous : ∀ p ∈ relations, ∀ degree : ℕ,
    AddMonoidAlgebra.ofCoeff (Finsupp.filter (fun a => monomialDegree a=degree)
      (AddMonoidAlgebra.coeff p)) ∈ relations
  proper : (1 : MvPolynomial (Fin vars) ℚ) ∉ relations
noncomputable def hilbert {vars : ℕ} (R : HomogeneousPresentation vars) (j : ℕ) : ℕ :=
  Module.finrank ℚ ((degreeSpace vars j) ⧸
    R.relations.comap (degreeSpace vars j).subtype)

/-- Exact full binomial expansion including zero tails; existence, uniqueness,
and its growth theorem are external/open duties, not postulated inhabitants. -/
def FullBinomialExpansion (j a : ℕ) (top : ℕ → ℕ) : Prop :=
  1 ≤ j ∧ (∀ i, 1 ≤ i → i ≤ j → i-1 ≤ top i) ∧
  (∀ i, 1 ≤ i → i < j → top i < top (i+1)) ∧
  a = ∑ i ∈ Finset.Icc 1 j, Nat.choose (top i) i

def ExternalMacaulayGrowth : Prop := ∀ (vars : ℕ) (R : HomogeneousPresentation vars)
  (j : ℕ) (top : ℕ → ℕ), FullBinomialExpansion j (hilbert R j) top →
    hilbert R (j+1) ≤ ∑ i ∈ Finset.Icc 1 j, Nat.choose (top i+1) (i+1)

/-- Introduction cross-reference only. Not a proved theorem and not part of the
quadratic reduction proof; it retains all historical external/finite duties. -/
def Recorded13To37Application : Prop := ∀ d : Data,
  13 ≤ n d → n d ≤ 37 → 0 ≤ W d
end Partials.WilfStructural.Foundation
