import Partials.WilfFinite.Core

/-! R10 source only, UNCOMPILED and API-unverified. Exact full-primitive
reconstruction is separated from the bit-machine realization. A width is a
binary length; none of these cost expressions uses unbounded unit-cost words. -/
namespace Partials.WilfFinite.Application
open Partials.Interface
open Partials.WilfStructural.Foundation
open scoped BigOperators

noncomputable def sparsePositive (d : Data) : Finset ℕ := (L d).erase 0
noncomputable def sparsePairSums (d : Data) : Finset ℕ :=
  (sparsePositive d ×ˢ sparsePositive d).image (fun p => p.1+p.2)
noncomputable def sparseLeftPrimitive (d : Data) : Finset ℕ :=
  sparsePositive d \ sparsePairSums d
noncomputable def sparseRightForbidden (d : Data) : Finset ℕ :=
  sparsePairSums d ∩ Finset.Ico d.c (d.c+d.m)
noncomputable def sparseRightPrimitive (d : Data) : Finset ℕ :=
  Finset.Ico d.c (d.c+d.m) \ sparseRightForbidden d

theorem sparse_pair_mem (d : Data) (x : ℕ) :
    x ∈ sparsePairSums d ↔ ∃ a b, a ∈ L d ∧ b ∈ L d ∧
      0 < a ∧ 0 < b ∧ x=a+b := by
  classical
  constructor
  · intro hx
    obtain ⟨⟨a,b⟩,hab,heq⟩ := Finset.mem_image.mp hx
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hab
    obtain ⟨ha0,haL⟩ := Finset.mem_erase.mp ha
    obtain ⟨hb0,hbL⟩ := Finset.mem_erase.mp hb
    exact ⟨a,b,haL,hbL,by omega,by omega,heq.symm⟩
  · rintro ⟨a,b,ha,hb,hap,hbp,hx⟩
    apply Finset.mem_image.mpr
    refine ⟨(a,b),Finset.mem_product.mpr ⟨?_,?_⟩,hx.symm⟩
    · exact Finset.mem_erase.mpr ⟨by omega,ha⟩
    · exact Finset.mem_erase.mpr ⟨by omega,hb⟩

/-- A positive summand in the conductor tail forces the sum above the
primitive ceiling. This is why pair sums of the complete left set suffice. -/
theorem sparse_decomposable_iff (d : Data) {x : ℕ} (hx : x < d.c+d.m) :
    IsDecomposable d.S x ↔ x ∈ sparsePairSums d := by
  constructor
  · rintro ⟨a,b,hap,hbp,haS,hbS,hxsum⟩
    have hma := d.multiplicity.2.2 a hap haS
    have hmb := d.multiplicity.2.2 b hbp hbS
    have hac : a < d.c := by omega
    have hbc : b < d.c := by omega
    exact (sparse_pair_mem d x).2 ⟨a,b,(mem_L d a).2 ⟨hac,haS⟩,
      (mem_L d b).2 ⟨hbc,hbS⟩,hap,hbp,hxsum⟩
  · intro hp
    obtain ⟨a,b,ha,hb,hap,hbp,hxsum⟩ := (sparse_pair_mem d x).1 hp
    exact ⟨a,b,hap,hbp,((mem_L d a).1 ha).2,
      ((mem_L d b).1 hb).2,hxsum⟩

/-- This describes ALL primitives, including the complement in [c,c+m). -/
theorem primitive_iff_sparse (d : Data) (x : ℕ) :
    IsPrimitive d.S x ↔ 0 < x ∧ x < d.c+d.m ∧
      (x ∈ L d ∨ d.c ≤ x) ∧ x ∉ sparsePairSums d := by
  constructor
  · rintro ⟨hxS,hxp,hnd⟩
    have hcut := primitive_cutoff d ⟨hxS,hxp,hnd⟩
    refine ⟨hxp,hcut,?_,?_⟩
    · by_cases hxc : x < d.c
      · exact Or.inl ((mem_L d x).2 ⟨hxc,hxS⟩)
      · exact Or.inr (by omega)
    · intro hp; exact hnd ((sparse_decomposable_iff d hcut).2 hp)
  · rintro ⟨hxp,hcut,hleft,hnot⟩
    have hxS : x ∈ d.S.carrier := by
      rcases hleft with hl | ht
      · exact ((mem_L d x).1 hl).2
      · exact d.conductor.1 x ht
    exact ⟨hxS,hxp,fun hd => hnot ((sparse_decomposable_iff d hcut).1 hd)⟩

theorem primitive_compact_exact (d : Data) (x : ℕ) :
    IsPrimitive d.S x ↔
      x ∈ sparseLeftPrimitive d ∨ x ∈ sparseRightPrimitive d := by
  classical
  rw [primitive_iff_sparse]
  simp only [sparseLeftPrimitive,sparseRightPrimitive,sparseRightForbidden,
    sparsePositive,Finset.mem_sdiff,Finset.mem_erase,Finset.mem_inter,
    Finset.mem_Ico]
  have hm : 0 < d.m := d.multiplicity.1
  have hc : 0 < d.c := d.c_pos
  constructor
  · rintro ⟨hp,hcut,hl | ht,hn⟩
    · exact Or.inl ⟨⟨by omega,hl⟩,hn⟩
    · exact Or.inr ⟨⟨ht,hcut⟩,by tauto⟩
  · rintro (⟨⟨hne,hl⟩,hn⟩ | ⟨⟨ht,hcut⟩,hn⟩)
    · have hbelow := ((mem_L d x).1 hl).1
      exact ⟨by omega,by omega,Or.inl hl,hn⟩
    · exact ⟨by omega,hcut,Or.inr ht,by tauto⟩

theorem same_progression_decomposes (d : Data) {x y k : ℕ}
    (hx : x ∈ d.S.carrier) (hxp : 0 < x) (hk : 0 < k)
    (hy : y=x+k*d.m) : IsDecomposable d.S y := by
  have hkm : k*d.m ∈ d.S.carrier := by
    clear hk hy
    induction k with
    | zero => simpa using d.S.carrier.zero_mem
    | succ k ih =>
      simpa [Nat.succ_mul,Nat.add_comm] using d.S.carrier.add_mem d.multiplicity.2.1 ih
  exact ⟨x,k*d.m,hxp,Nat.mul_pos hk d.multiplicity.1,hx,hkm,hy⟩

/-- Validation precedes extraction. The list must have distinct entries,
contain zero, omit c-1, lie below c and be closed for sums below c. -/
def SparseValidation (c : ℕ) (xs : List ℕ) : Prop :=
  2 ≤ c ∧ xs.Nodup ∧ 0 ∈ xs ∧ c-1 ∉ xs ∧
  (∀ x ∈ xs, x < c) ∧
  (∀ x ∈ xs, ∀ y ∈ xs, x+y < c → x+y ∈ xs)

def invariantTimeScale (b : ℕ) : ℕ := b^2
def invariantSpaceScale (b : ℕ) : ℕ := b
def sparseTimeScale (I k bitWidth logk : ℕ) : ℕ := I+k^2*logk*bitWidth+bitWidth^2
def sparseSpaceScale (k bitWidth : ℕ) : ℕ := (k+1)^2*bitWidth
def primitiveOutputScale (e bitWidth : ℕ) : ℕ := e*bitWidth

/-- Independent charging laws: read input, sort/deduplicate pair records,
then do bounded-width scalar arithmetic. Their machine instantiation is open. -/
theorem sparse_charging (I k bitWidth logk A read pairs arithmetic : ℕ)
    (hr : read ≤ A*I) (hp : pairs ≤ A*(k^2*logk*bitWidth))
    (ha : arithmetic ≤ A*bitWidth^2) :
    read+pairs+arithmetic ≤ A*sparseTimeScale I k bitWidth logk := by
  unfold sparseTimeScale
  nlinarith

def SparseChargingLaw : Prop :=
  ∃ A : ℕ, 0 < A ∧ ∀ I k bitWidth logk : ℕ,
    ∀ read pairs arithmetic : ℕ,
    read ≤ A*I → pairs ≤ A*(k^2*logk*bitWidth) → arithmetic ≤ A*bitWidth^2 →
    read+pairs+arithmetic ≤ A*sparseTimeScale I k bitWidth logk

theorem sparse_bit_charging_exists : SparseChargingLaw := by
  refine ⟨1,by omega,?_⟩
  intro I k bitWidth logk read pairs arithmetic hr hp ha
  exact sparse_charging I k bitWidth logk 1 read pairs arithmetic hr hp ha

end Partials.WilfFinite.Application
