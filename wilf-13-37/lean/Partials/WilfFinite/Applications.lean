import Partials.WilfFinite.ResidualCosts
import Partials.WilfStructural.PackingTargets

/-! Exact conditional applications. External imports and semigroup-to-profile
instantiations are uninhabited premises; no theorem headline or run-success
flag is a premise. All proof terms/tactics here are authored, UNEXECUTED. -/
namespace Partials.WilfFinite.Application
open Partials.WilfStructural.Foundation

/-- Two sign factors replace evaluation of the five possible r values.
The integer gap 3<r implies r>=4 and is essential to the second branch. -/
theorem thirteen_pair_polynomial (r : ℤ) (hr0 : 0 ≤ r) (hr4 : r ≤ 4) :
    r*(19-3*r) ≤ 30 := by
  by_cases hr3 : r ≤ 3
  · have hp := mul_nonneg (show 0 ≤ 3-r by omega) (show 0 ≤ 10-3*r by omega)
    nlinarith
  · have hr : 4 ≤ r := by omega
    have hp := mul_nonneg (show 0 ≤ r-3 by omega) (show 0 ≤ 3*r-10 by omega)
    nlinarith

theorem thirteen_profile_bound (a b d δ : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (hmass : 3*a+2*b+d=9)
    (hpair : 2*δ ≤ (a+b)*(a+b+1)+2*(a+b)*d) : δ ≤ 15 := by
  let r := a+b
  have hr0 : 0 ≤ r := by dsimp [r]; omega
  have hr4 : r ≤ 4 := by dsimp [r]; omega
  have hd' : d ≤ 9-2*r := by dsimp [r]; omega
  have hprod := mul_nonneg hr0 (show 0 ≤ 9-2*r-d by omega)
  have hpoly := thirteen_pair_polynomial r hr0 hr4
  dsimp [r] at hprod hpoly
  nlinarith

theorem thirteen_endpoint (e δ ρ c : ℤ)
    (hδ : δ ≤ 15) (hρ : 0 ≤ ρ) (hc : c=4*(e+δ)-ρ)
    (hstrict : 13*e < c) : e ≤ 6 ∧ c ≤ 84 := by
  have hupper : c ≤ 4*e+60 := by omega
  have he : e ≤ 6 := by omega
  exact ⟨he,by omega⟩

/-- Independently specified imports and structural maps; none assumes the
desired n=13 inequality. Pair counting is stated in its doubled integer form. -/
structure ThirteenInputs where
  embedding_three : ExternalEmbeddingThree
  depth_three : ExternalDepthThree
  graph : ExternalGraphCases
  profile : ∀ d : Data, n d=13 → depth d=4 →
    3*(alpha d 1 : ℤ)+2*(alpha d 2 : ℤ)+(alpha d 3 : ℤ)=9
  pairs : ∀ d : Data, depth d=4 →
    2*(delta d : ℤ) ≤ ((alpha d 1 : ℤ)+alpha d 2)*
      ((alpha d 1 : ℤ)+alpha d 2+1)+
      2*((alpha d 1 : ℤ)+alpha d 2)*(alpha d 3 : ℤ)
  conductor_identity : ∀ d : Data,
    (d.c : ℤ)=(depth d : ℤ)*((e d : ℤ)+delta d)-rho d

theorem thirteen_depth (H : ThirteenInputs) (d : Data)
    (hn : n d=13) (hbad : W d < 0) : 4 ≤ e d ∧ depth d=4 := by
  have he : 4 ≤ e d := by
    by_contra h
    have hw := H.embedding_three d (by omega)
    omega
  have hq : 4 ≤ depth d := by
    by_contra h
    have hw := H.depth_three d (by omega)
    omega
  have hq4 : depth d ≤ 4 := by
    by_contra h
    have hgraph := H.graph d he hq (by rw [hn]; omega)
    omega
  exact ⟨he,by omega⟩

theorem thirteen_conductor_conditional (H : ThirteenInputs) (d : Data)
    (hn : n d=13) (hbad : W d < 0) : delta d ≤ 15 ∧ e d ≤ 6 ∧ d.c ≤ 84 := by
  have hq := (thirteen_depth H d hn hbad).2
  have hδ := thirteen_profile_bound (alpha d 1 : ℤ) (alpha d 2 : ℤ)
    (alpha d 3 : ℤ) (delta d : ℤ) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) (H.profile d hn hq) (H.pairs d hq)
  have hc : (d.c : ℤ)=4*((e d : ℤ)+delta d)-rho d := by
    simpa only [hq,Nat.cast_ofNat] using H.conductor_identity d
  have hs : 13*(e d : ℤ) < d.c := by
    unfold W at hbad
    rw [hn] at hbad
    omega
  have hec := thirteen_endpoint (e d : ℤ) (delta d : ℤ) (rho d : ℤ) d.c
    hδ (Nat.cast_nonneg _) hc hs
  exact ⟨by exact_mod_cast hδ,by exact_mod_cast hec.1,by exact_mod_cast hec.2⟩

theorem thirteen_wilf_conditional (H : ThirteenInputs)
    (H200 : ExternalConductor200) (d : Data) (hn : n d=13) : 0 ≤ W d := by
  by_contra h
  have hb : W d < 0 := by omega
  have hc := (thirteen_conductor_conditional H d hn hb).2.2
  have hw := H200 d (by omega)
  omega

def Tuple921PrimitiveCondition (x : ℤ) : Prop :=
  max (56+1) (56-55) ≤ x ∧ x ≤ 2*56-55-1

/-- Endpoint calculation as a symbolic proof term. This was not executed. -/
theorem tuple921_endpoints :
    max (56+1 : ℤ) (56-55)=57 ∧ (2*56-55-1 : ℤ)=56 := by
  constructor
  · have hm : (56-55 : ℤ) ≤ 56+1 := by omega
    rw [max_eq_left hm]
    omega
  · omega

theorem tuple921_empty (x : ℤ) : ¬Tuple921PrimitiveCondition x := by
  unfold Tuple921PrimitiveCondition
  rw [tuple921_endpoints.1,tuple921_endpoints.2]
  omega

/-- Ranked eligibility zero contradicts h[2,3]=1. The exact map from the
empty primitive interval to eligibility zero remains a separate duty. -/
theorem tuple921_selected_prefix_empty (eligible selected : ℕ)
    (he : eligible=0) (hs : selected=1) : ¬selected ≤ eligible := by omega

inductive ExclusionReason
  | emptyPrimitiveBox
  | selectedPrefix
  deriving DecidableEq

theorem tuple921_reason_codes_distinct :
    ExclusionReason.emptyPrimitiveBox ≠ ExclusionReason.selectedPrefix := by
  intro h
  cases h

end Partials.WilfFinite.Application
