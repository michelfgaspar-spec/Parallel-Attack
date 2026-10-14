import Partials.WilfFinite.ForestSoundness
import Partials.WilfStructural.PackingTargets
import Partials.WilfStructural.Refinements

/-! Signed residual domains for the historical profile route. They are not
PRIMARY forests. Enumeration/retention kernels are proved as source; semigroup
profile, selected ideal and external cap adapters remain explicit. UNCOMPILED. -/
namespace Partials.WilfFinite.Forest
open Partials.WilfStructural.Packing
open scoped BigOperators

def compositions : List ℕ → ℕ → List (List ℕ)
  | [],ν => if ν = 0 then [[]] else []
  | w::weights,ν => (List.range (ν/w+1)).flatMap (fun a =>
      (compositions weights (ν-w*a)).map (fun rest => a::rest))

inductive WeightedEquation : List ℕ → List ℕ → ℕ → Prop
  | nil : WeightedEquation [] [] 0
  | cons {w a ν : ℕ} {weights rest : List ℕ}
      (positive : 0 < w) (term : w*a ≤ ν)
      (tail : WeightedEquation weights rest (ν-w*a)) :
      WeightedEquation (w::weights) (a::rest) ν

theorem weighted_composition_complete {weights data : List ℕ} {ν : ℕ}
    (h : WeightedEquation weights data ν) : data ∈ compositions weights ν := by
  induction h with
  | nil => simp [compositions]
  | @cons w a ν weights rest hw ht htail ih =>
    have ha : a ≤ ν/w := (Nat.le_div_iff_mul_le hw).2 (by simpa [mul_comm] using ht)
    simp only [compositions,List.mem_flatMap]
    refine ⟨a,by simpa [Nat.lt_succ_iff] using ha,?_⟩
    exact List.mem_map.mpr ⟨rest,ih,rfl⟩

theorem weighted_composition_sound (weights : List ℕ) :
    (∀ w ∈ weights, 0 < w) → ∀ ν data,
      data ∈ compositions weights ν → WeightedEquation weights data ν := by
  induction weights with
  | nil =>
    intro hw ν data hd
    by_cases hν : ν=0
    · subst ν
      have heq : data=[] := by simpa [compositions] using hd
      subst data
      exact .nil
    · simp [compositions,hν] at hd
  | cons w weights ih =>
    intro hw ν data hd
    have hwpos : 0 < w := hw w (by simp)
    change data ∈ (List.range (ν/w+1)).flatMap (fun a =>
      (compositions weights (ν-w*a)).map (fun rest => a::rest)) at hd
    obtain ⟨a,ha,hd⟩ := List.mem_flatMap.mp hd
    obtain ⟨xs,hxs,rfl⟩ := List.mem_map.mp hd
    have habound : a ≤ ν/w := by simpa [Nat.lt_succ_iff] using ha
    have ht : w*a ≤ ν := by
      simpa [mul_comm] using (Nat.le_div_iff_mul_le hwpos).1 habound
    exact .cons hwpos ht (ih (fun v hv => hw v (by simp [hv])) _ _ hxs)

def ResidualDepth (n q : ℕ) : Prop := 4 ≤ q ∧ 3*q ≤ n

theorem residual_depth_interval (n q : ℕ) :
    ResidualDepth n q ↔ 4 ≤ q ∧ q ≤ n/3 := by
  unfold ResidualDepth
  rw [Nat.le_div_iff_mul_le (by omega : 0 < 3)]
  simp [mul_comm]

def KappaRectangle (q : ℕ) (alpha kappa : ℕ → ℕ) : Prop :=
  kappa 1 = 0 ∧ ∀ i, 2 ≤ i → i < q → kappa i ≤ alpha i

/-- A single h is threaded through every prefix, selected shadow, label and box.
These are actual degree/layer counts, without independently optimized h's. -/
def GlobalAllocation (q : ℕ) (kappa : ℕ → ℕ) (h : Allocation) : Prop :=
  (∀ d j, h d j ≠ 0 → 2 ≤ d ∧ d ≤ j ∧ j < q) ∧
  ∀ j, 2 ≤ j → j < q → ∑ d ∈ Finset.Icc 2 j, h d j = kappa j

theorem minimum_preserves_cap (actual a b : ℤ)
    (ha : actual ≤ a) (hb : actual ≤ b) : actual ≤ min a b := le_min ha hb

theorem cutoff_equality_rejection (L Q m rho r q H Mmax : ℤ)
    (hm : 0 < m) (hM : 0 < Mmax) (hr : 2 ≤ r)
    (hstrict : (L-Q-1)*m < (r-1)*rho)
    (hratio : rho*Mmax ≤ m*(q*Mmax-(H+1)))
    (hfilter : (r-1)*(q*Mmax-(H+1)) ≤ (L-Q-1)*Mmax) : False :=
  Partials.WilfStructural.Shadow.cutoff_scaled_impossible L Q m rho r q H Mmax
    hm hM (by omega) hstrict hratio hfilter

structure SignedCaps where
  F : ℤ
  N : ℤ
  E : ℤ
  sigma : ℤ
  deriving DecidableEq

def ValidCaps (delta nc embedding compressedDebit : ℤ) (caps : SignedCaps) : Prop :=
  delta ≤ caps.F ∧ nc ≤ caps.N ∧ embedding ≤ caps.E ∧ compressedDebit ≤ caps.sigma

def intersectCaps (a b : SignedCaps) : SignedCaps :=
  ⟨min a.F b.F,min a.N b.N,min a.E b.E,min a.sigma b.sigma⟩

theorem intersectCaps_valid (delta nc e debit : ℤ) (a b : SignedCaps)
    (ha : ValidCaps delta nc e debit a) (hb : ValidCaps delta nc e debit b) :
    ValidCaps delta nc e debit (intersectCaps a b) := by
  simp only [ValidCaps,intersectCaps] at *
  omega

def Refines (a b : SignedCaps) : Prop :=
  b.F ≤ a.F ∧ b.N ≤ a.N ∧ b.E ≤ a.E ∧ b.sigma ≤ a.sigma

def capPotential (lower a : SignedCaps) : ℕ :=
  (a.F-lower.F).toNat+(a.N-lower.N).toNat+
    (a.E-lower.E).toNat+(a.sigma-lower.sigma).toNat

theorem strict_refinement_potential (lower a b : SignedCaps)
    (ha : Refines a b) (hlo : Refines b lower) (hne : b ≠ a) :
    capPotential lower b < capPotential lower a := by
  rcases a with ⟨af,an,ae,asig⟩
  rcases b with ⟨bf,bn,be,bsig⟩
  rcases lower with ⟨lf,ln,le,ls⟩
  simp only [Refines] at ha hlo
  simp only [capPotential]
  simp only [ne_eq,SignedCaps.mk.injEq] at hne
  omega

theorem stationary_preserves_validity (delta nc e debit : ℤ) (a b : SignedCaps)
    (hvalid : ValidCaps delta nc e debit a) (hstationary : b=a) :
    ValidCaps delta nc e debit b := hstationary.symm ▸ hvalid

def RhoInterval (n q e delta m rho sigma N H : ℤ) : Prop :=
  max 0 (max (q*delta-sigma) (delta-N)) ≤ rho ∧
  rho ≤ min (m-1) (min (q*m-n*e-1) (q*m-H-1))

theorem exact_rho_interval (n q e delta m rho sigma N H : ℤ) :
    RhoInterval n q e delta m rho sigma N H ↔
      0 ≤ rho ∧ q*delta-rho ≤ sigma ∧ delta ≤ rho+N ∧
      rho < m ∧ n*e < q*m-rho ∧ H < q*m-rho := by
  exact (rho_domain_iff n q e delta m rho sigma N H).symm

theorem rho_complement_six (n q e delta m rho sigma N H : ℤ) :
    ¬ RhoInterval n q e delta m rho sigma N H ↔
      rho < 0 ∨ sigma < q*delta-rho ∨ rho+N < delta ∨
      m ≤ rho ∨ q*m-rho ≤ n*e ∨ q*m-rho ≤ H := by
  rw [exact_rho_interval]
  omega

def ExactResidualTuple (n q emin E K F sigma N H e delta m rho c : ℤ) : Prop :=
  emin ≤ e ∧ e ≤ E ∧ K ≤ delta ∧ delta ≤ F ∧ m=e+delta ∧
  c=q*m-rho ∧ RhoInterval n q e delta m rho sigma N H

/-- All e values are full embedding dimensions. The s coordinate enters only
the necessary lower bound max(4,1+s); it never replaces e. -/
theorem full_embedding_lower_bound (e s : ℤ) (he : 4 ≤ e) (hs : 1+s ≤ e) :
    max 4 (1+s) ≤ e := max_le he hs

/-- Zero tails use top(i)=i-1, so the raised term is choose(i,i+1)=0.
This supplies the exact zero convention, not the external growth theorem. -/
theorem macaulay_zero_raised (j : ℕ) :
    (∑ i ∈ Finset.Icc 1 j, Nat.choose ((i-1)+1) (i+1)) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  apply Nat.choose_eq_zero_of_lt
  omega

def GreedyBinomialCorrespondence : Prop := ∀ j s : ℕ, 1 ≤ j →
  ∃ top : ℕ → ℕ, Partials.WilfStructural.Foundation.FullBinomialExpansion j s top

/-- Exact imported premises for the historical residual route. No instance of
this bundle is supplied, and no reported n=14..37 run is encoded as its proof. -/
structure ResidualImports : Prop where
  embedding : Partials.WilfStructural.Foundation.ExternalEmbeddingThree
  depth : Partials.WilfStructural.Foundation.ExternalDepthThree
  earlyEmpty : Partials.WilfStructural.Foundation.ExternalEarlyEmpty
  graph : Partials.WilfStructural.Foundation.ExternalGraphCases
  conductor200 : Partials.WilfStructural.Foundation.ExternalConductor200
  macaulay : Partials.WilfStructural.Foundation.ExternalMacaulayGrowth

end Partials.WilfFinite.Forest
