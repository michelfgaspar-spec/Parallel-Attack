import Partials.WilfStructural.WeightedPairs

/-! Exact mixed family and exponent-weighted cubic incidence. The semigroup to
selected-order-ideal/cardinality construction is explicitly still a duty; the
finite counting and final polynomial argument are authored here. -/
namespace Partials.WilfStructural.Foundation
open Partials.Interface
open scoped BigOperators

structure MixedFamily (d : Data) where
  X : Finset ℕ
  y : ℕ
  nonempty : X.Nonempty
  offsets : ∀ x ∈ X, 1 ≤ x ∧ x < d.m
  y_range : 1 ≤ y ∧ y < d.m
  y_not_X : y ∉ X
  rho_pos : 0 < rho d
  rho_lt : rho d < d.m
  conductor_six : d.c + rho d = 6*d.m
  left_primitives : ∀ z : ℕ, IsPrimitive d.S z ∧ z < d.c ↔
    z=d.m ∨ (∃ x ∈ X, z=2*d.m+x) ∨ z=3*d.m+y

noncomputable def mixedLowCount {d : Data} (h : MixedFamily d) : ℕ :=
  ((insert h.y h.X).filter (fun x => x < d.m-rho d)).card

def exponentDegree {k : ℕ} (gamma : Fin k → ℕ) : ℕ := ∑ i, gamma i
/-- One coordinate removed; supports repeated factors and cubes. -/
def deleteVariable {k : ℕ} (gamma : Fin k → ℕ) (i : Fin k) : Fin k → ℕ :=
  fun j => gamma j - if j=i then 1 else 0

def cubicIncidence {k : ℕ} (gamma theta : Fin k → ℕ) : ℕ :=
  ∑ i, if 0 < gamma i ∧ deleteVariable gamma i = theta then gamma i else 0

 theorem quadratic_parent_mass (k : ℕ) (theta : Fin k → ℕ)
    (hdegree : exponentDegree theta = 2) :
    (∑ i, (theta i+1)) = k+2 := by
  unfold exponentDegree at hdegree
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, Nat.nsmul_eq_mul, mul_one]
  omega

/-- Rows count each cubic three times with exponent weights. A column is
bounded by sum_i(theta_i+1)=k+2. Counting distinct divisors would fail on cubes. -/
 theorem weighted_cubic_double_count {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
    (cubics : Finset ι) (lowPairs : Finset κ) (inc : ι → κ → ℕ) (k : ℕ)
    (hrow : ∀ g ∈ cubics, ∑ t ∈ lowPairs, inc g t = 3)
    (hcol : ∀ t ∈ lowPairs, ∑ g ∈ cubics, inc g t ≤ k+2) :
    3*cubics.card ≤ (k+2)*lowPairs.card := by
  have hsum : (∑ g ∈ cubics, ∑ t ∈ lowPairs, inc g t) = 3*cubics.card := by
    calc
      _ = ∑ g ∈ cubics, 3 := Finset.sum_congr rfl hrow
      _ = _ := by simp [mul_comm]
  rw [Finset.sum_comm] at hsum
  have hbound := Finset.sum_le_sum hcol
  simp only [Finset.sum_const, Nat.nsmul_eq_mul] at hbound
  nlinarith

 theorem mixed_degree_exclusions (m rho : ℤ) (hm : 0 < m) (hrho : 0 < rho) :
    7*m-rho-1 < 8*m+4 ∧ 7*m-rho-1 < 7*m+3 := by omega

 theorem cubic_divisor_low (x y z cutoff : ℤ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hs : x+y+z < cutoff) : x+y < cutoff ∧ x+z < cutoff ∧ y+z < cutoff := by omega

 theorem no_high_type33 (m rho y : ℤ) (hcut : 0 < m-rho)
    (hy : m-rho ≤ y) : ¬ 2*y < m-rho := by omega

/-- The inputs are independent counts and per-degree capacities, not the
claimed W0 bound. p33 is kept visible until the two low-offset cases split. -/
 theorem mixed_master (k n m r rho ell t p22 p23 p33 h3 : ℤ)
    (hk : 1 ≤ k)
    (hsize : m-r=k+2+p22+p23+p33+h3)
    (hrows : 3*k+8+ell+2*t ≤ n)
    (hp22 : 2*p22 ≤ k*(k+1)) (hp23 : p23 ≤ k)
    (hcubic : 3*h3 ≤ (k+2)*t) :
    rho-k-2+(k+2)*ell+6*(1-p33) ≤ (k+2)*n-6*(m-r)+rho := by
  have hrowmul := mul_le_mul_of_nonneg_left hrows (show 0 ≤ k+2 by omega)
  nlinarith

 theorem mixed_positive_cases (k n m r rho ell t p22 p23 p33 h3 : ℤ)
    (hk : 1 ≤ k) (hrho : 0 < rho) (hell : 0 ≤ ell)
    (hsize : m-r=k+2+p22+p23+p33+h3)
    (hrows : 3*k+8+ell+2*t ≤ n)
    (hp22 : 2*p22 ≤ k*(k+1)) (hp23 : p23 ≤ k) (hp33 : p33 ≤ 1)
    (hcubic : 3*h3 ≤ (k+2)*t)
    (hempty : ell=0 → k+1 ≤ rho ∧ p33=0) :
    (1 ≤ ell → rho ≤ (k+2)*n-6*(m-r)+rho) ∧
    (ell=0 → rho-k+4 ≤ (k+2)*n-6*(m-r)+rho ∧ 5 ≤ rho-k+4) ∧
    0 < (k+2)*n-6*(m-r)+rho := by
  have hm := mixed_master k n m r rho ell t p22 p23 p33 h3 hk hsize hrows hp22 hp23 hcubic
  have hfirst : 1 ≤ ell → rho ≤ (k+2)*n-6*(m-r)+rho := by
    intro he
    have hp := mul_nonneg (show 0 ≤ k+2 by omega) (show 0 ≤ ell-1 by omega)
    nlinarith
  have hsecond : ell=0 → rho-k+4 ≤ (k+2)*n-6*(m-r)+rho ∧ 5 ≤ rho-k+4 := by
    intro he
    obtain ⟨hr,hp⟩ := hempty he
    rw [he,hp] at hm
    constructor <;> nlinarith
  refine ⟨hfirst,hsecond,?_⟩
  by_cases he : ell=0
  · obtain ⟨h1,h2⟩ := hsecond he
    omega
  · have h1 := hfirst (by omega)
    omega

 theorem mixed_wilf_from_positive (d : Data) (hpos : 0 < W0 d)
    (hq : depth d ≤ n d) : 0 < W d :=
  lt_of_lt_of_le hpos (wilf_ge_w0 d hq)

 theorem mixed_w0_identity (d : Data)
    (hc : (d.c : ℤ) = (depth d : ℤ)*d.m-rho d) :
    W0 d = ((e d : ℤ)-rP d)*n d - (depth d : ℤ)*(d.m-rP d)+rho d := by
  have he : (e d : ℤ) = (ellP d : ℤ)+rP d := by exact_mod_cast primitive_partition d
  unfold W0
  rw [hc,he]
  ring
end Partials.WilfStructural.Foundation
