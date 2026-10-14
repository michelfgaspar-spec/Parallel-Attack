import Partials.WilfStructural.Reductions
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Finite weighted counting and structural arithmetic. Independent local
incidence obligations are visible; no Structure contains the desired headline
inequality. The complete semigroup instantiation is an open source duty. -/
namespace Partials.WilfStructural.Foundation
open scoped BigOperators

/-- The matrix entries count endpoint occurrences, so a loop has multiplicity
2 in its own column. This theorem performs the actual exchange of finite sums. -/
 theorem weighted_incidence_mass {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (edges : Finset ι) (vertices : Finset κ) (inc : ι → κ → ℤ)
    (weight : κ → ℤ) (r : ℤ)
    (hinc : ∀ v ∈ vertices, ∑ a ∈ edges, inc a v = r) :
    (∑ a ∈ edges, ∑ v ∈ vertices, inc a v * weight v) =
      r * ∑ v ∈ vertices, weight v := by
  rw [Finset.sum_comm]
  calc
    (∑ v ∈ vertices, ∑ a ∈ edges, inc a v * weight v) =
        ∑ v ∈ vertices, r * weight v := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [← Finset.sum_mul, hinc v hv]
    _ = r * ∑ v ∈ vertices, weight v := by rw [Finset.mul_sum]

/-- One selected edge per D-value. Boundary indicators mark selected pairs of
level sum q+1. Their images are compressed and therefore receive a single rho
allowance. hsmall and hlarge concern individual edges, not the final bound. -/
 theorem selected_weight_bound {ι : Type*} [DecidableEq ι]
    (selected all : Finset ι) (hsub : selected ⊆ all)
    (wt : ι → ℤ) (boundary : ι → Prop) [DecidablePred boundary]
    (q rho : ℤ)
    (hnonneg : ∀ a ∈ all, 0 ≤ wt a)
    (hsmall : ∀ a ∈ selected, boundary a → q-1 ≤ wt a)
    (hlarge : ∀ a ∈ selected, ¬boundary a → q ≤ wt a)
    (hallowance : ((selected.filter boundary).card : ℤ) ≤ rho) :
    q * (selected.card : ℤ) - rho ≤ ∑ a ∈ all, wt a := by
  have hpoint : ∀ a ∈ selected, q - (if boundary a then 1 else 0) ≤ wt a := by
    intro a ha
    by_cases hb : boundary a
    · simpa [hb] using hsmall a ha hb
    · simpa [hb] using hlarge a ha hb
  have hsum := Finset.sum_le_sum hpoint
  have hone : (∑ a ∈ selected, (if boundary a then (1 : ℤ) else 0)) =
      (selected.filter boundary).card := by simp
  have hselected : q * (selected.card : ℤ) - rho ≤ ∑ a ∈ selected, wt a := by
    rw [Finset.sum_sub_distrib, hone] at hsum
    simp only [Finset.sum_const, nsmul_eq_mul] at hsum
    nlinarith
  exact hselected.trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (by intro a ha hnot; exact hnonneg a ha))

 theorem weighted_pairs_from_incidence {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (selected all : Finset ι) (vertices : Finset κ)
    (hsub : selected ⊆ all) (inc : ι → κ → ℤ) (weight : κ → ℤ)
    (boundary : ι → Prop) [DecidablePred boundary] (q rho : ℤ)
    (hinc : ∀ v ∈ vertices, ∑ a ∈ all, inc a v = (vertices.card : ℤ)+1)
    (hincpos : ∀ a ∈ all, ∀ v ∈ vertices, 0 ≤ inc a v)
    (hwpos : ∀ v ∈ vertices, 0 ≤ weight v)
    (hsmall : ∀ a ∈ selected, boundary a →
      q-1 ≤ ∑ v ∈ vertices, inc a v * weight v)
    (hlarge : ∀ a ∈ selected, ¬boundary a →
      q ≤ ∑ v ∈ vertices, inc a v * weight v)
    (hallowance : ((selected.filter boundary).card : ℤ) ≤ rho) :
    q * (selected.card : ℤ) - rho ≤
      ((vertices.card : ℤ)+1) * ∑ v ∈ vertices, weight v := by
  have h := selected_weight_bound selected all hsub
    (fun a => ∑ v ∈ vertices, inc a v * weight v) boundary q rho
    (by intro a ha; exact Finset.sum_nonneg (by
      intro v hv; exact mul_nonneg (hincpos a ha v hv) (hwpos v hv)))
    hsmall hlarge hallowance
  rw [weighted_incidence_mass all vertices inc weight _ hinc] at h
  exact h

/-- Pure arithmetic consequence; hpair remains explicitly conditional until
selected pairs are instantiated on the exact Apéry model. -/
 theorem structural_arithmetic (n q e delta rho t c : ℤ)
    (hpair : q*delta-rho ≤ (t+1)*(n-q))
    (hc : c=q*(e+delta)-rho) :
    (n-q)*(e-t-1) ≤ n*e-c := by nlinarith

 theorem negative_forces_embedding_cap (n q e delta rho t c : ℤ)
    (hpair : q*delta-rho ≤ (t+1)*(n-q))
    (hc : c=q*(e+delta)-rho) (hnu : 0 ≤ n-q) (hneg : n*e-c < 0) :
    0 < n-q ∧ e ≤ t := by
  have hb := structural_arithmetic n q e delta rho t c hpair hc
  constructor
  · by_contra hn; have hz : n-q=0 := by omega
    rw [hz] at hb
    omega
  · by_contra he
    have hf : 0 ≤ e-t-1 := by omega
    have hp := mul_nonneg hnu hf
    omega

 theorem structural_conductor_cap (n q e delta rho t c : ℤ)
    (hpair : q*delta-rho ≤ (t+1)*(n-q))
    (hc : c=q*(e+delta)-rho) (hq : 0 ≤ q) (hn : 0 ≤ n)
    (hnu : 0 ≤ n-q) (ht : t ≤ n-q) (hneg : n*e-c < 0) :
    c ≤ n*t+(n-q) ∧ n*t+(n-q) ≤ (n-q)*(n+1) := by
  have he := (negative_forces_embedding_cap n q e delta rho t c hpair hc hnu hneg).2
  have hp := mul_le_mul_of_nonneg_left he hq
  have hp' := mul_le_mul_of_nonneg_left ht hn
  constructor <;> nlinarith

 theorem multiplicity_cap (m e delta t : ℤ) (hm : m=e+delta)
    (he : e ≤ t) (hpairs : 2*delta ≤ t*(t+1)) :
    2*m ≤ t*(t+3) := by nlinarith

 theorem quadratic_region_arithmetic (n q e delta rho t c : ℤ)
    (hpair : q*delta-rho ≤ (t+1)*(n-q))
    (hc : c=q*(e+delta)-rho) (hq : 3 ≤ q) (he : 2 ≤ e)
    (hnu : 0 ≤ n-q) (ht : t ≤ n-q) (hneg : n*e-c < 0)
    (hreflect : 2*n ≤ c) :
    5 ≤ n ∧ 3 ≤ q ∧ q ≤ n-2 ∧ 2 ≤ e ∧ e ≤ t ∧ t ≤ n-q ∧
      2*n ≤ c ∧ c ≤ n*t+(n-q) ∧ n*t+(n-q) ≤ (n-q)*(n+1) ∧
      (n-q)*(n+1) ≤ (n-3)*(n+1) := by
  have hE := (negative_forces_embedding_cap n q e delta rho t c hpair hc hnu hneg).2
  have hn : 0 ≤ n := by omega
  have hC := structural_conductor_cap n q e delta rho t c hpair hc (by omega) hn hnu ht hneg
  have hp := mul_nonneg (show 0 ≤ q-3 by omega) (show 0 ≤ n+1 by omega)
  exact ⟨by omega,hq,by omega,he,hE,ht,hreflect,hC.1,hC.2,by nlinarith⟩

 theorem cutoff_monotone (n v : ℤ) (hn : 5 ≤ n) (hnv : n ≤ v) :
    (n-3)*(n+1) ≤ (v-3)*(v+1) := by
  have hprod := mul_nonneg (show 0 ≤ v-n by omega) (show 0 ≤ v+n-2 by omega)
  nlinarith

 theorem finite_cutoff_reduction {ι : Type*} (nc cc ww : ι → ℤ) (u v : ℤ)
    (hviol : ∀ x, ww x < 0 → 5 ≤ nc x ∧ cc x ≤ (nc x-3)*(nc x+1)) :
    (∀ x, u ≤ nc x → nc x ≤ v → 0 ≤ ww x) ↔
    (∀ x, u ≤ nc x → nc x ≤ v → cc x ≤ (v-3)*(v+1) → 0 ≤ ww x) := by
  constructor
  · intro h x hu hv hc; exact h x hu hv
  · intro h x hu hv
    by_contra hw
    have hw' : ww x < 0 := by omega
    obtain ⟨hn,hc⟩ := hviol x hw'
    have hcut := cutoff_monotone (nc x) v hn hv
    have hp := h x hu hv (hc.trans hcut)
    omega

 theorem profile_sigma_lower (q delta rho M U : ℤ) (hq : 1 ≤ q)
    (hrho : 0 ≤ rho) (hM : delta ≤ M) (hU : delta-rho ≤ U) :
    q*delta-rho ≤ min (q*M) ((q-1)*M+U) := by
  have h := compression_sigma q delta rho M U U hq hrho hM hU hU
  simpa only [min_self] using h

 theorem profile_sigma_comparison (q M U mass : ℤ)
    (hlocal : (q-1)*M+U ≤ mass) : min (q*M) ((q-1)*M+U) ≤ mass :=
  (min_le_right _ _).trans hlocal

 theorem strict_endpoint_monotone (nu q sigma tau : ℤ)
    (hnu : 0 < nu) (hq : 0 ≤ q) (hst : sigma ≤ tau) :
    (sigma-1)/nu ≤ (tau-1)/nu ∧
      q*((sigma-1)/nu)+sigma ≤ q*((tau-1)/nu)+tau := by
  have hd : (sigma-1)/nu ≤ (tau-1)/nu :=
    Int.ediv_le_ediv (by omega) (by omega)
  have hp := mul_le_mul_of_nonneg_left hd hq
  exact ⟨hd,by omega⟩
end Partials.WilfStructural.Foundation
