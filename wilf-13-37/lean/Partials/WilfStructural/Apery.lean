import Partials.WilfStructural.Model

/-! Universal subsums, primitive factorizations, residue minimality and the
reflection injection. All proof source is unexecuted. -/
namespace Partials.WilfStructural.Foundation
open Partials.Interface

 theorem multiple_mem (d : Data) (k : ℕ) : k * d.m ∈ d.S.carrier := by
  induction k with
  | zero => simpa using d.S.carrier.zero_mem
  | succ k ih => simpa [Nat.succ_mul] using d.S.carrier.add_mem ih d.multiplicity.2.1

 theorem apery_summands (d : Data) {a x y : ℕ}
    (ha : IsAperyAt d.S d.m a) (hx : x ∈ d.S.carrier)
    (hy : y ∈ d.S.carrier) (hs : a = x + y) :
    IsAperyAt d.S d.m x ∧ IsAperyAt d.S d.m y := by
  constructor
  · refine ⟨hx, ?_⟩
    rintro ⟨z,hz,hzEq⟩
    exact ha.2 ⟨z+y,d.S.carrier.add_mem hz hy,by omega⟩
  · refine ⟨hy, ?_⟩
    rintro ⟨z,hz,hzEq⟩
    exact ha.2 ⟨x+z,d.S.carrier.add_mem hx hz,by omega⟩

/-- Any grouped subsum works, independently of any choice of factorization. -/
 theorem proper_subsum (d : Data) {a x y : ℕ}
    (ha : IsAperyAt d.S d.m a) (hx : x ∈ d.S.carrier)
    (hy : y ∈ d.S.carrier) (hyp : 0 < y) (hs : a = x + y) :
    IsAperyAt d.S d.m x ∧ x < d.c := by
  have hm := d.multiplicity.2.2 y hyp hy
  have hcut := apery_cutoff d ha
  exact ⟨(apery_summands d ha hx hy hs).1, by omega⟩

 theorem list_sum_mem (d : Data) (xs : List ℕ)
    (h : ∀ x ∈ xs, x ∈ d.S.carrier) : xs.sum ∈ d.S.carrier := by
  induction xs with
  | nil => simpa using d.S.carrier.zero_mem
  | cons x xs ih =>
    have hx := h x (by simp)
    have ht : xs.sum ∈ d.S.carrier := ih (by intro y hy; exact h y (by simp [hy]))
    simpa using d.S.carrier.add_mem hx ht

 theorem primitive_factorization (d : Data) (x : ℕ)
    (hx : x ∈ d.S.carrier) (hpos : 0 < x) :
    ∃ xs : List ℕ, xs.sum = x ∧ ∀ a ∈ xs, IsPrimitive d.S a := by
  classical
  revert hx hpos
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro hx hpos
    by_cases hp : IsPrimitive d.S x
    · exact ⟨[x],by simp,by simpa using hp⟩
    · have hd : IsDecomposable d.S x := by
        by_contra hn
        exact hp ⟨hx,hpos,hn⟩
      obtain ⟨a,b,ha,hb,haS,hbS,heq⟩ := hd
      obtain ⟨as,has,hpa⟩ := ih a (by omega) haS ha
      obtain ⟨bs,hbs,hpb⟩ := ih b (by omega) hbS hb
      refine ⟨as ++ bs, by simp [has,hbs,heq], ?_⟩
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hpa z hz
      · exact hpb z hz

 theorem apery_minimal_in_progression (d : Data) {a b k : ℕ}
    (ha : IsAperyAt d.S d.m a) (hb : b ∈ d.S.carrier)
    (heq : a = b + k * d.m) : k = 0 := by
  by_contra hk
  have hkpos : 0 < k := by omega
  have hpred : b + (k-1)*d.m ∈ d.S.carrier :=
    d.S.carrier.add_mem hb (multiple_mem d (k-1))
  have hmul : k*d.m = (k-1)*d.m + d.m := by
    have hk' : k = (k-1)+1 := by omega
    conv_lhs => rw [hk']
    ring
  exact ha.2 ⟨b+(k-1)*d.m,hpred,by omega⟩

/-- A least semigroup representative of a residue is Apéry. The existence of
least representatives uses only cofiniteness, independently of cardinality laws. -/
 theorem least_residue_is_apery (d : Data) {a r : ℕ}
    (ha : a ∈ d.S.carrier) (har : a % d.m = r)
    (hmin : ∀ b, b ∈ d.S.carrier → b % d.m = r → a ≤ b) :
    IsAperyAt d.S d.m a := by
  refine ⟨ha, ?_⟩
  rintro ⟨b,hb,heq⟩
  have hbr : b % d.m = r := by simpa [heq, Nat.add_mod] using har
  have hab := hmin b hb hbr
  have hm := d.multiplicity.1
  omega

 theorem reflection_gap (d : Data) {x : ℕ} (hx : x ∈ L d) :
    d.c - 1 - x < d.c ∧ d.c - 1 - x ∉ d.S.carrier := by
  obtain ⟨hxc,hxS⟩ := (mem_L d x).1 hx
  refine ⟨by omega, ?_⟩
  intro hr
  have hsum := d.S.carrier.add_mem hxS hr
  have heq : x + (d.c - 1 - x) = d.c - 1 := by omega
  rw [heq] at hsum
  exact conductor_predecessor_gap d hsum

 theorem reflection_injective (d : Data) :
    Set.InjOn (fun x : ℕ => d.c - 1 - x) (↑(L d) : Set ℕ) := by
  intro x hx y hy heq
  have hxc := ((mem_L d x).1 hx).1
  have hyc := ((mem_L d y).1 hy).1
  change d.c - 1 - x = d.c - 1 - y at heq
  omega

 theorem left_count_half_conductor (d : Data) : 2 * n d ≤ d.c := by
  classical
  let gaps := (Finset.range d.c).filter (fun x => x ∉ d.S.carrier)
  have hc : (L d).card ≤ gaps.card := by
    apply Finset.card_le_card_of_injOn (fun x => d.c-1-x)
    · intro x hx
      have hg := reflection_gap d hx
      simp only [Finset.mem_coe, gaps, Finset.mem_filter, Finset.mem_range]
      exact hg
    · exact reflection_injective d
  have hpart : (L d).card + gaps.card = d.c := by
    simpa [L, LeftBelow, gaps] using
      (Finset.card_filter_add_card_filter_not
        (s := Finset.range d.c) (p := fun x => x ∈ d.S.carrier))
  unfold n
  omega

/-- Euclidean remainders give the ±1 level rule over integers, with no
assumption that shifted level is a grading. -/
 theorem level_remainder_bounds (m rho rx ry i j z : ℤ)
    (hm : 0 < m) (hrho : 0 ≤ rho ∧ rho < m)
    (hrx : 0 ≤ rx ∧ rx < m) (hry : 0 ≤ ry ∧ ry < m)
    (hz : z = (i+j)*m + rx+ry-rho) :
    (i+j-1)*m ≤ z ∧ z < (i+j+2)*m := by
  constructor <;> nlinarith

 theorem level_strict_increment (m rho x y i : ℤ) (hm : 0 < m)
    (hy : m ≤ y) (hi : i*m ≤ x+rho) :
    (i+1)*m ≤ x+y+rho := by nlinarith

 theorem compressed_residue_interval (m rho rx ry : ℤ)
    (hm : 0 < m) (hrho : 0 ≤ rho ∧ rho < m)
    (hrx : 0 ≤ rx ∧ rx < m) (hry : 0 ≤ ry ∧ ry < m)
    (hcompress : rx+ry < rho) :
    0 ≤ rx+ry ∧ rx+ry < rho := by omega
end Partials.WilfStructural.Foundation
