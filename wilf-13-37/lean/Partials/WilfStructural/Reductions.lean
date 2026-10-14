import Partials.WilfStructural.Apery
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Exact finite-pair/profile definitions, compression/endpoints arithmetic,
and the canonical left-set construction. No execution or external theorem imports. -/
namespace Partials.WilfStructural.Foundation
open Partials.Interface

noncomputable def eligiblePairs (d : Data) : Finset (ℕ × ℕ) :=
  (unorderedPairs (T d)).filter (fun p => level d p.1 + level d p.2 ≤ depth d + 1)
noncomputable def normalPairs (d : Data) : Finset (ℕ × ℕ) :=
  (unorderedPairs (T d)).filter (fun p => level d p.1 + level d p.2 ≤ depth d)
noncomputable def sumEdges (d : Data) : Finset (ℕ × ℕ) := by
  classical
  exact (unorderedPairs (T d)).filter (fun p => IsAperyAt d.S d.m (p.1+p.2))
noncomputable def compressed (d : Data) : Finset ℕ := by
  classical
  exact (D d).filter (fun z => ∃ x y : ℕ, 0 < x ∧ 0 < y ∧
    x ∈ d.S.carrier ∧ y ∈ d.S.carrier ∧ z = x+y ∧
    level d z + 1 = level d x + level d y)

def pairCap (Q : ℕ) (z : ℕ → ℕ) : ℕ :=
  (∑ i ∈ Finset.Icc 1 (Q-1), ∑ j ∈ Finset.Icc 1 (Q-1),
    if i < j ∧ i+j ≤ Q+1 then z i * z j else 0) +
  ∑ i ∈ Finset.Icc 1 (Q-1), if 2*i ≤ Q+1 then Nat.choose (z i+1) 2 else 0

def normalCap (Q : ℕ) (z : ℕ → ℕ) : ℕ :=
  (∑ i ∈ Finset.Icc 1 (Q-1), ∑ j ∈ Finset.Icc 1 (Q-1),
    if i < j ∧ i+j ≤ Q then z i * z j else 0) +
  ∑ i ∈ Finset.Icc 1 (Q-1), if 2*i ≤ Q then Nat.choose (z i+1) 2 else 0

/-- One chosen pair per numerical value; surjectivity is obtained without
requiring unique factorizations. -/
 theorem decomposable_has_left_pair (d : Data) {z : ℕ} (hz : z ∈ D d) :
    ∃ p ∈ unorderedPairs (T d), z = p.1+p.2 := by
  classical
  obtain ⟨hzA,hzd⟩ := Finset.mem_filter.mp hz
  have ha := (mem_A d z).1 hzA
  obtain ⟨x,y,hxp,hyp,hxS,hyS,heq⟩ := hzd
  have hx := proper_subsum d ha hxS hyS hyp heq
  have hy := proper_subsum d ha hyS hxS hxp (by omega)
  have hxT : x ∈ T d := by
    simp only [T, Finset.mem_filter]
    exact ⟨(mem_A d x).2 hx.1,hxp,hx.2⟩
  have hyT : y ∈ T d := by
    simp only [T, Finset.mem_filter]
    exact ⟨(mem_A d y).2 hy.1,hyp,hy.2⟩
  by_cases hxy : x ≤ y
  · exact ⟨(x,y),by simp [unorderedPairs,hxT,hyT,hxy],heq⟩
  · exact ⟨(y,x),by simp [unorderedPairs,hxT,hyT,show y ≤ x by omega],by omega⟩

 theorem selected_pair_injective {F : Finset ℕ} (choosePair : ℕ → ℕ × ℕ)
    (hvalue : ∀ z ∈ F, z = (choosePair z).1 + (choosePair z).2) :
    Set.InjOn choosePair (↑F : Set ℕ) := by
  intro x hx y hy hxy
  rw [hvalue x hx,hvalue y hy,hxy]

 theorem compression_sigma (q delta rho F U N : ℤ)
    (hq : 1 ≤ q) (hrho : 0 ≤ rho) (hF : delta ≤ F)
    (hU : delta-rho ≤ U) (hN : delta-rho ≤ N) :
    q*delta-rho ≤ min (q*F) (min ((q-1)*F+U) ((q-1)*F+N)) := by
  have hp := mul_le_mul_of_nonneg_left hF (show 0 ≤ q-1 by omega)
  have hp' := mul_le_mul_of_nonneg_left hF (show 0 ≤ q by omega)
  apply le_min
  · nlinarith
  · apply le_min <;> nlinarith

 theorem strict_integer_endpoint (nu e sigma : ℤ) (hnu : 0 < nu)
    (hstrict : nu*e < sigma) : e ≤ (sigma-1)/nu := by
  apply (Int.le_ediv_iff_mul_le hnu).2
  rw [mul_comm]
  omega

 theorem strict_conductor_endpoint (q e sigma c : ℤ) (hq : 0 ≤ q)
    (E : ℤ) (he : e ≤ E) (hc : c ≤ q*e+sigma) : c ≤ q*E+sigma := by
  have := mul_le_mul_of_nonneg_left he hq
  omega

 theorem endpoint_exclusion (e E emin : ℤ) (he : emin ≤ e)
    (hE : e ≤ E) (hbad : E < emin) : False := by omega

 theorem conductor_cutoff_exclusion (c C H W : ℤ)
    (hc : c ≤ C) (hCH : C ≤ H)
    (hknown : c ≤ H → 0 ≤ W) (hviol : W < 0) : False := by
  have := hknown (by omega)
  omega

/-- Local collision arithmetic is separate from proving a collision exists. -/
 theorem missing_or_collision (delta M E r a : ℤ)
    (hE : E ≤ M-r+a) (hdelta : delta ≤ E) (hr : 2 ≤ r)
    (ha : a ≤ r) (hcollision : 2 ≤ a → delta ≤ E-1) : delta ≤ M-1 := by
  by_cases haa : 2 ≤ a
  · have := hcollision haa
    omega
  · omega

 theorem shallow_two_arithmetic (n m c d r : ℤ)
    (hpairs : 2*d ≤ n*(n-1)) (hr : r=m-d) (hc : c ≤ 2*m) :
    0 ≤ n*(n-1)+2*r-c := by nlinarith

/-- Canonical left data impose actual, not merely upper, conductor. -/
structure CanonicalLeft (c : ℕ) where
  left : Finset ℕ
  c_two : 2 ≤ c
  below : ∀ x ∈ left, x < c
  zero : 0 ∈ left
  gap : c-1 ∉ left
  closed : ∀ x ∈ left, ∀ y ∈ left, x+y < c → x+y ∈ left

noncomputable def canonicalSemigroup {c : ℕ} (a : CanonicalLeft c) : NumericalSemigroup where
  carrier := {
    carrier := {x | x ∈ a.left ∨ c ≤ x}
    zero_mem' := Or.inl a.zero
    add_mem' := by
      intro x y hx hy
      by_cases hxy : x+y < c
      · left
        have hxl : x ∈ a.left := by rcases hx with h | h; exact h; omega
        have hyl : y ∈ a.left := by rcases hy with h | h; exact h; omega
        exact a.closed x hxl y hyl hxy
      · exact Or.inr (by omega) }
  finiteGaps := by
    apply (Finset.range c).finite_toSet.subset
    intro x hx
    simp only [Finset.mem_coe, Finset.mem_range]
    change ¬(x ∈ a.left ∨ c ≤ x) at hx
    omega

 theorem canonical_conductor {c : ℕ} (a : CanonicalLeft c) :
    IsConductor (canonicalSemigroup a) c := by
  constructor
  · intro x hx; exact Or.inr hx
  · intro b hb
    refine ⟨c-1,by omega,?_⟩
    change ¬(c-1 ∈ a.left ∨ c ≤ c-1)
    simp only [not_or]
    exact ⟨a.gap,by omega⟩

 theorem canonical_left_exact {c : ℕ} (a : CanonicalLeft c) :
    LeftBelow (canonicalSemigroup a) c = a.left := by
  classical
  ext x
  simp only [LeftBelow, Finset.mem_filter, Finset.mem_range]
  change (x < c ∧ (x ∈ a.left ∨ c ≤ x)) ↔ x ∈ a.left
  constructor
  · rintro ⟨hx,hl | ht⟩
    · exact hl
    · omega
  · intro hx
    exact ⟨a.below x hx,Or.inl hx⟩

noncomputable def canonicalOfData (d : Data) (hc : 2 ≤ d.c) : CanonicalLeft d.c where
  left := L d
  c_two := hc
  below := by intro x hx; exact ((mem_L d x).1 hx).1
  zero := zero_left d
  gap := by intro h; exact conductor_predecessor_gap d (((mem_L d _).1 h).2)
  closed := by
    intro x hx y hy hxy
    exact (mem_L d _).2 ⟨hxy,d.S.carrier.add_mem
      (((mem_L d x).1 hx).2) (((mem_L d y).1 hy).2)⟩

 theorem canonical_reconstruction_membership (d : Data) (hc : 2 ≤ d.c) (x : ℕ) :
    x ∈ (canonicalSemigroup (canonicalOfData d hc)).carrier ↔ x ∈ d.S.carrier := by
  change (x ∈ L d ∨ d.c ≤ x) ↔ x ∈ d.S.carrier
  constructor
  · rintro (h | h)
    · exact ((mem_L d x).1 h).2
    · exact d.conductor.1 x h
  · intro hx
    by_cases hxc : x < d.c
    · exact Or.inl ((mem_L d x).2 ⟨hxc,hx⟩)
    · exact Or.inr (by omega)
/-- The local compressed-split calculation, including the actual residue strip.
The four equalities are Euclidean quotient/remainder identities of the factors
and the compressed target; no compressed-count conclusion is a premise. -/
 theorem compressed_split_strip (m rho x y z i j rx ry rz : ℕ)
    (hrho : rho < m) (hrz : rz < m)
    (hx : x+rho=i*m+rx) (hy : y+rho=j*m+ry)
    (hz : z=x+y) (hcompressed : z+rho+m=(i+j)*m+rz) :
    (z+2*rho)%m < rho := by
  have heq : z+2*rho=(i+j)*m+(rx+ry) := by nlinarith
  have hsmall : rx+ry < rho := by nlinarith
  have hrem : rx+ry < m := by omega
  simpa [heq, Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hrem] using hsmall

/-- The one global allowance. The residue-separation premise concerns ALL
Apéry values, independently of which split witnesses compression. -/
 theorem global_compression_count (d : Data)
    (hstrip : ∀ z ∈ compressed d, (z+2*rho d)%d.m < rho d)
    (hsep : ∀ x ∈ A d, ∀ y ∈ A d,
      (x+2*rho d)%d.m=(y+2*rho d)%d.m → x=y) :
    (compressed d).card ≤ rho d := by
  classical
  have hc : (compressed d).card ≤ (Finset.range (rho d)).card := by
    apply Finset.card_le_card_of_injOn (fun z => (z+2*rho d)%d.m)
    · intro z hz
      exact Finset.mem_range.mpr (hstrip z hz)
    · intro x hx y hy heq
      have hxD : x ∈ D d := (Finset.mem_filter.mp hx).1
      have hyD : y ∈ D d := (Finset.mem_filter.mp hy).1
      exact hsep x (Finset.mem_filter.mp hxD).1 y (Finset.mem_filter.mp hyD).1 heq
  simpa using hc
end Partials.WilfStructural.Foundation
