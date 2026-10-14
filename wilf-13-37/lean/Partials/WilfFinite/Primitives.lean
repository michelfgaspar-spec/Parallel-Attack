import Partials.WilfFinite.Canonical
import Mathlib.Data.List.Sort

/-! Complete primitive domain [1,c+m), including right primitives. Positive
summands are compulsory on the left; zero in L+L cannot hit [c,c+m). -/
namespace Partials.WilfFinite.Prefix
open Partials.Interface
abbrev FData := Partials.WilfStructural.Foundation.Data
open Partials.WilfStructural.Foundation
attribute [local instance] Classical.propDecidable

noncomputable def sourceData (a : Core.CanonicalState) : FData where
  S := Core.semigroup a
  c := Core.conductor a
  m := reconstructedMultiplicity a
  conductor := Core.actual_conductor a
  multiplicity := reconstructedMultiplicity_spec a
  c_pos := by have := a.2.c_two; change 0<a.1; omega

theorem primitive_cutoff_full (d : FData) {x : ℕ} (hx : IsPrimitive d.S x) :
    x<d.c+d.m := by
  by_contra hcut
  have hrem : d.c≤x-d.m := by omega
  have hremS := d.conductor.1 (x-d.m) hrem
  have hm := d.multiplicity.1
  have hc := d.c_pos
  exact hx.2.2 ⟨d.m,x-d.m,hm,by omega,d.multiplicity.2.1,hremS,by omega⟩

theorem left_decomposition_iff (d : FData) {x : ℕ} (hx : x<d.c) :
    IsDecomposable d.S x ↔
      ∃ u∈L d, ∃ v∈L d, 0<u ∧ 0<v ∧ x=u+v := by
  constructor
  · rintro ⟨u,v,hu,hv,huS,hvS,heq⟩
    exact ⟨u,(mem_L d u).2 ⟨by omega,huS⟩,
      v,(mem_L d v).2 ⟨by omega,hvS⟩,hu,hv,heq⟩
  · rintro ⟨u,hu,v,hv,hup,hvp,heq⟩
    exact ⟨u,v,hup,hvp,((mem_L d u).1 hu).2,((mem_L d v).1 hv).2,heq⟩

theorem threshold_decomposition_iff (d : FData) {x : ℕ}
    (hlo : d.c≤x) (hhi : x<d.c+d.m) :
    IsDecomposable d.S x ↔ ∃ u∈L d, ∃ v∈L d, x=u+v := by
  constructor
  · rintro ⟨u,v,hu,hv,huS,hvS,heq⟩
    have hmu := d.multiplicity.2.2 u hu huS
    have hmv := d.multiplicity.2.2 v hv hvS
    exact ⟨u,(mem_L d u).2 ⟨by omega,huS⟩,
      v,(mem_L d v).2 ⟨by omega,hvS⟩,heq⟩
  · rintro ⟨u,hu,v,hv,heq⟩
    obtain ⟨huc,huS⟩ := (mem_L d u).1 hu
    obtain ⟨hvc,hvS⟩ := (mem_L d v).1 hv
    exact ⟨u,v,by omega,by omega,huS,hvS,heq⟩

noncomputable def sumset (X : Finset ℕ) : Finset ℕ :=
  (X ×ˢ X).image (fun p : ℕ×ℕ => p.1+p.2)
noncomputable def thresholdDecomposables (d : FData) : Finset ℕ := by
  classical
  exact (Finset.Ico d.c (d.c+d.m)).filter (IsDecomposable d.S)

theorem threshold_set_exact (d : FData) :
    thresholdDecomposables d = sumset (L d) ∩ Finset.Ico d.c (d.c+d.m) := by
  classical
  ext x
  simp only [thresholdDecomposables,Finset.mem_filter,Finset.mem_Ico,
    Finset.mem_inter]
  constructor
  · rintro ⟨⟨hlo,hhi⟩,hd⟩
    obtain ⟨u,hu,v,hv,heq⟩ := (threshold_decomposition_iff d hlo hhi).1 hd
    exact ⟨Finset.mem_image.mpr ⟨(u,v),by simp [hu,hv],heq.symm⟩,hlo,hhi⟩
  · rintro ⟨hs,hlo,hhi⟩
    obtain ⟨p,hp,hpEq⟩ := Finset.mem_image.mp hs
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp hp
    exact ⟨⟨hlo,hhi⟩,(threshold_decomposition_iff d hlo hhi).2
      ⟨p.1,hu,p.2,hv,hpEq.symm⟩⟩

theorem right_complement_exact (d : FData) :
    rightPrimitives d = (Finset.Ico d.c (d.c+d.m)).filter
      (fun x => ¬IsDecomposable d.S x) := by
  classical
  ext x
  simp only [rightPrimitives,Finset.mem_filter,mem_P,Finset.mem_Ico]
  constructor
  · rintro ⟨hp,hxc⟩
    exact ⟨⟨hxc,primitive_cutoff_full d hp⟩,hp.2.2⟩
  · rintro ⟨⟨hxc,hhi⟩,hnd⟩
    exact ⟨⟨d.conductor.1 x hxc,by have := d.c_pos; omega,hnd⟩,hxc⟩

theorem right_count_exact (d : FData) :
    rP d = d.m-(sumset (L d) ∩ Finset.Ico d.c (d.c+d.m)).card := by
  classical
  have hpart := Finset.card_filter_add_card_filter_not
    (s := Finset.Ico d.c (d.c+d.m)) (p := IsDecomposable d.S)
  have hright := right_complement_exact d
  have hthreshold := threshold_set_exact d
  have htotal : (Finset.Ico d.c (d.c+d.m)).card=d.m := by simp
  unfold rP
  rw [hright]
  change (thresholdDecomposables d).card +
    ((Finset.Ico d.c (d.c+d.m)).filter (fun x => ¬IsDecomposable d.S x)).card =
      (Finset.Ico d.c (d.c+d.m)).card at hpart
  rw [hthreshold,htotal] at hpart
  omega

theorem data_left_exact (s : PrefixState) : L (data s)=Core.left s.canonical :=
  Core.complete_left s.canonical
theorem data_n_exact (s : PrefixState) : n (data s)=k s := by
  unfold n k Core.leftCount
  rw [data_left_exact]

theorem left_primitive_list_exact (s : PrefixState) :
    leftPrimitives (data s) = s.G.toFinset := by
  classical
  ext x
  simp only [leftPrimitives, Finset.mem_filter, mem_P, List.mem_toFinset]
  exact (s.primitive_exact x).symm

theorem ell_list_length (s : PrefixState) : ell s = s.G.length := by
  unfold ell ellP
  rw [left_primitive_list_exact]
  exact List.toFinset_card_of_nodup s.increasing.nodup

/-- Division supplies the upper ceil-product bound; strict j<q then gives
j*m<c, including j=0. No counting conclusion is an arithmetic premise. -/
theorem ceiling_multiple_below (s : PrefixState) {j : ℕ} (hj : j<q s) : j*s.m<c s := by
  have hdiv : q s*s.m≤c s+s.m-1 := Nat.div_mul_le_self _ _
  have hmul : (j+1)*s.m≤q s*s.m := Nat.mul_le_mul_right s.m (by omega)
  have hm := s.m_two
  have hc := s.m_left
  have hcut : 1≤c s+s.m := by omega
  have hsub : c s+s.m-1+1=c s+s.m := by omega
  nlinarith

theorem depth_le_left_count (s : PrefixState) : q s≤k s := by
  classical
  have hcard : (Finset.range (q s)).card≤(Core.left s.canonical).card := by
    apply Finset.card_le_card_of_injOn (fun j => j*s.m)
    · intro j hj
      rw [←data_left_exact s]
      exact (mem_L (data s) _).2
        ⟨ceiling_multiple_below s (Finset.mem_range.mp hj),multiple_mem (data s) j⟩
    · intro i hi j hj heq
      have hm := s.m_two
      by_contra hne
      have hcases : i < j ∨ j < i := by omega
      rcases hcases with hij | hji
      · have hmul : (i+1)*s.m ≤ j*s.m := Nat.mul_le_mul_right s.m (by omega)
        nlinarith
      · have hmul : (j+1)*s.m ≤ i*s.m := Nat.mul_le_mul_right s.m (by omega)
        nlinarith
  simpa [k,Core.leftCount] using hcard

theorem full_embedding_dimension (s : PrefixState) : e s=ell s+r s :=
  primitive_partition (data s)

theorem full_W_difference (s : PrefixState) :
    W s-W0 s=((k s : ℤ)-q s)*r s := by
  have he : (e s : ℤ)=(ell s : ℤ)+r s := by
    exact_mod_cast full_embedding_dimension s
  unfold W W0
  rw [he]
  ring

theorem W_ge_W0 (s : PrefixState) : W0 s≤W s := by
  have hq : (q s : ℤ)≤k s := by exact_mod_cast depth_le_left_count s
  have hprod := mul_nonneg (show 0≤(k s : ℤ)-q s by omega)
    (show (0 : ℤ)≤r s from Nat.cast_nonneg _)
  have hdiff := full_W_difference s
  omega

/-- Original exact finite left primitive interface, with zero erased before
forming the left sumset. P4 supplies its inhabitant immediately below. -/
def LeftPrimitiveSetTarget : Prop := ∀ d : FData,
  leftPrimitives d = (L d).erase 0 \ sumset ((L d).erase 0)

/-- Exact positive-summand correspondence. Erasing zero is essential here:
otherwise every left member appears in the sumset through its zero summand. -/
theorem left_primitive_set_exact : LeftPrimitiveSetTarget := by
  classical
  intro d
  ext x
  simp only [leftPrimitives, Finset.mem_filter, mem_P, Finset.mem_sdiff,
    Finset.mem_erase]
  constructor
  · rintro ⟨hp, hxc⟩
    refine ⟨⟨by have := hp.2.1; omega, (mem_L d x).2 ⟨hxc, hp.1⟩⟩, ?_⟩
    intro hsum
    obtain ⟨p, hpairs, heq⟩ := Finset.mem_image.mp hsum
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hpairs
    obtain ⟨hu0, huL⟩ := Finset.mem_erase.mp hu
    obtain ⟨hv0, hvL⟩ := Finset.mem_erase.mp hv
    exact hp.2.2 ⟨p.1, p.2, by omega, by omega,
      ((mem_L d p.1).1 huL).2, ((mem_L d p.2).1 hvL).2, heq.symm⟩
  · rintro ⟨⟨hx0, hxL⟩, hsum⟩
    obtain ⟨hxc, hxS⟩ := (mem_L d x).1 hxL
    refine ⟨⟨hxS, by omega, ?_⟩, hxc⟩
    intro hd
    obtain ⟨u, hu, v, hv, hup, hvp, heq⟩ := (left_decomposition_iff d hxc).1 hd
    exact hsum (Finset.mem_image.mpr ⟨(u,v),
      Finset.mem_product.mpr ⟨Finset.mem_erase.mpr ⟨by omega,hu⟩,
        Finset.mem_erase.mpr ⟨by omega,hv⟩⟩, heq.symm⟩)

end Partials.WilfFinite.Prefix
