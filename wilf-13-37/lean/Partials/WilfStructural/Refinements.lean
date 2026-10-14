import Partials.WilfStructural.Shadows
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith

/-! R9 blind source. Signed arithmetic preserves impossible negative capacities.
These primitive consequences do not assume any Wilf or shadow headline. -/
namespace Partials.WilfStructural.Shadow

/-- Lower factor sum and strict upper layer endpoint yield the strict cutoff. -/
theorem cutoff_pattern_strict (L Q m rho r z : ℤ)
    (hlo : L * m - r * rho ≤ z) (hhi : z < (Q + 1) * m - rho) :
    (L - Q - 1) * m < (r - 1) * rho := by nlinarith

 theorem cutoff_few_high_impossible (L Q m rho r : ℤ)
    (hm : 0 < m) (hrho : 0 ≤ rho) (hr : r ≤ 1) (hL : Q + 1 ≤ L)
    (hstrict : (L - Q - 1) * m < (r - 1) * rho) : False := by
  have hl : 0 ≤ (L - Q - 1) * m := mul_nonneg (by omega) (by omega)
  have hh : (r - 1) * rho ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) hrho
  omega

/-- Denominator-free version of rho/m ≤ q-(H+1)/M; no sign ambiguity. -/
theorem cutoff_ratio_cross (q m rho H M : ℤ)
    (hm : 0 < m) (hmM : m ≤ M) (hH : 0 ≤ H + 1)
    (hc : H + 1 ≤ q * m - rho) :
    rho * M ≤ m * (q * M - (H + 1)) := by
  have hM : 0 ≤ M := by omega
  have hscaled := mul_le_mul_of_nonneg_right hc hM
  have hcompare := mul_le_mul_of_nonneg_left hmM hH
  nlinarith

 theorem cutoff_scaled_impossible (L Q m rho r q H M : ℤ)
    (hm : 0 < m) (hM : 0 < M) (hr : 0 ≤ r - 1)
    (hstrict : (L - Q - 1) * m < (r - 1) * rho)
    (hratio : rho * M ≤ m * (q * M - (H + 1)))
    (hexclude : (r - 1) * (q * M - (H + 1)) ≤ (L - Q - 1) * M) : False := by
  have h1 := mul_lt_mul_of_pos_right hstrict hM
  have h2 := mul_le_mul_of_nonneg_left hratio hr
  have h3 := mul_le_mul_of_nonneg_left hexclude (le_of_lt hm)
  nlinarith

structure Caps where
  F : ℕ
  N : ℕ
  sigma : ℕ
  E : ℕ
  deriving DecidableEq

def capMass (x : Caps) : ℕ := x.F + x.N + x.sigma + x.E

def tighten (x y : Caps) : Caps :=
  ⟨min x.F y.F, min x.N y.N, min x.sigma y.sigma, min x.E y.E⟩

/-- Validity is pointwise for the SAME putative violator. -/
def CapsValid (delta nc sigmaValue embedding : ℕ) (x : Caps) : Prop :=
  delta ≤ x.F ∧ nc ≤ x.N ∧ sigmaValue ≤ x.sigma ∧ embedding ≤ x.E

 theorem tighten_valid (delta nc sigmaValue embedding : ℕ) (x y : Caps)
    (hx : CapsValid delta nc sigmaValue embedding x)
    (hy : CapsValid delta nc sigmaValue embedding y) :
    CapsValid delta nc sigmaValue embedding (tighten x y) := by
  simp only [CapsValid, tighten] at *
  omega

 theorem tighten_mass_lt (x y : Caps) (h : tighten x y ≠ x) :
    capMass (tighten x y) < capMass x := by
  rcases x with ⟨f, n, a, e⟩
  rcases y with ⟨g, p, b, d⟩
  simp only [tighten, Caps.mk.injEq, ne_eq] at h
  simp only [capMass, tighten]
  omega

/-- At most f(0) strict decreases; a stationary result does not imply rejection. -/
theorem no_infinite_strict_descent (f : ℕ → ℕ) : ¬∀ n, f (n + 1) < f n := by
  intro hs
  have hbound : ∀ n, f n + n ≤ f 0 := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have := hs n; omega
  have := hbound (f 0 + 1)
  omega

/-- A pair at top-left level followed by at least two positive factors is
already too high. This excludes all lengths ≥4 in L16's top-only case. -/
theorem top_left_four_impossible (q pairLevel targetLevel : ℤ)
    (hp : pairLevel = q - 1) (hinc : pairLevel + 2 ≤ targetLevel)
    (ht : targetLevel ≤ q) : False := by omega

 theorem top_left_cubic_factor (q pairLevel factorLevel targetLevel : ℤ)
    (hp : pairLevel = q - 1)
    (hs : factorLevel + pairLevel - 1 ≤ targetLevel)
    (ht : targetLevel ≤ q) : factorLevel ≤ 2 := by omega

 theorem cubic_five_factor (pairLevel factorLevel targetLevel : ℤ)
    (hp : 3 ≤ pairLevel) (hs : factorLevel + pairLevel - 1 ≤ targetLevel)
    (ht : targetLevel ≤ 5) : factorLevel ≤ 3 := by omega

 theorem cubic_five_level_three_complement (pairLevel targetLevel : ℤ)
    (hp : 3 ≤ pairLevel) (hs : 3 + pairLevel - 1 ≤ targetLevel)
    (ht : targetLevel ≤ 5) : pairLevel = 3 := by omega

 theorem nc_cubic_complement (factorLevel pairLevel targetLevel : ℤ)
    (hp : 2 ≤ pairLevel) (hs : factorLevel + pairLevel ≤ targetLevel)
    (ht : targetLevel ≤ 5) : pairLevel ≤ 5 - factorLevel := by omega

/-- Both marked quartic exclusions produce complementary pairs of level ≥3. -/
theorem nc_marked_quartic_impossible (leftPair rightPair targetLevel : ℤ)
    (hl : 3 ≤ leftPair) (hr : 3 ≤ rightPair)
    (hnc : leftPair + rightPair ≤ targetLevel) (ht : targetLevel ≤ 5) : False := by
  omega

/-- Exactly one compression allowance on VALUES, after partitioning D. -/
theorem compression_debit (delta compressed nc rho : ℤ)
    (hpartition : delta = compressed + nc) (hcompression : compressed ≤ rho) :
    delta - rho ≤ nc := by omega

 theorem compression_cap (q delta rho F nc N : ℤ)
    (hq : 1 ≤ q) (hF : delta ≤ F) (hdebit : delta - rho ≤ nc)
    (hN : nc ≤ N) : q * delta - rho ≤ (q - 1) * F + N := by
  have hh := mul_le_mul_of_nonneg_left hF (show 0 ≤ q - 1 by omega)
  nlinarith

/-- Consumed left pair representatives and top representatives are disjoint.
The signed form exposes impossible P0<k rather than truncating subtraction. -/
theorem pair_remainder_bound (P0 k top : ℤ) (hpair : k + top ≤ P0) :
    top ≤ P0 - k := by omega

 theorem pair_capacity_rejection (P0 k top : ℤ) (htop : 0 ≤ top)
    (hpair : k + top ≤ P0) (hbad : P0 < k) : False := by omega

/-- Last arithmetic step of L19; the three premises have independent set origins:
partition of D, a formal A2-pair injection, and disjoint compressed subsets. -/
theorem empty_first_depth_four_debit (delta k ell h0 rho b : ℤ)
    (hpartition : delta = k + ell + h0)
    (hpairs : 2 * (k + ell) ≤ b * (b + 1))
    (hcompressed : k + h0 ≤ rho) :
    4 * delta - rho ≤ 2 * b * (b + 1) - k + 3 * h0 := by nlinarith

/-- Surviving quartics with two loop variables consist of these exponent types;
their distinctness and exhaustive small-support proof remain a finite-set duty. -/
def twoVariableQuartics : Finset (ℕ × ℕ) :=
  {(4, 0), (3, 1), (2, 2), (1, 3), (0, 4)}

/-- Formal stars-and-bars convention, including absent levels and empty factors.
Its interpretation as an exact cardinality is a separate bijection duty. -/
def multisetFactor (beta repetitions : ℕ) : ℕ :=
  if repetitions = 0 then 1
  else if beta = 0 then 0
  else Nat.choose (beta + repetitions - 1) repetitions

 theorem multisetFactor_zero_repetitions (beta : ℕ) : multisetFactor beta 0 = 1 := by
  simp [multisetFactor]

 theorem multisetFactor_empty_level (r : ℕ) (hr : 0 < r) : multisetFactor 0 r = 0 := by
  simp [multisetFactor, Nat.ne_of_gt hr]

end Partials.WilfStructural.Shadow
