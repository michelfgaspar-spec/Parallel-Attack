import Partials.Covering.Model

noncomputable section
namespace Partials.Covering.Support

/-! Exact logical support mechanism from the supplement. None of the retained
point admissions, selected cycles or Bernstein data has been replayed. Primitive
geometry and data interpretations remain explicit duties, not custom axioms. -/

abbrev Parameters := ℝ × ℝ

def segment (t : ℝ) (x y : Parameters) : Parameters :=
  ((1 - t) * x.1 + t * y.1, (1 - t) * x.2 + t * y.2)

def AlongSegmentsConvex (f : Parameters → ℝ) : Prop :=
  ∀ x y t, 0 ≤ t → t ≤ 1 →
    f (segment t x y) ≤ (1 - t) * f x + t * f y

structure AffinePlane where
  a : ℝ
  b : ℝ
  c : ℝ

def AffinePlane.eval (p : AffinePlane) (z : Parameters) : ℝ :=
  p.a * z.1 + p.b * z.2 + p.c

def AffinePlane.Supports (p : AffinePlane) (f : Parameters → ℝ) : Prop :=
  ∀ z, p.eval z ≤ f z

theorem affine_segment (p : AffinePlane) (t : ℝ) (x y : Parameters) :
    p.eval (segment t x y) = (1 - t) * p.eval x + t * p.eval y := by
  unfold AffinePlane.eval segment
  ring

/-- Local equality along a short positive part of every ray is the precise
local persistence input; it is weaker than assuming a global supporting plane. -/
def LocalRayAffine (f : Parameters → ℝ) (p : AffinePlane) (anchor : Parameters) : Prop :=
  f anchor = p.eval anchor ∧
    ∀ z, ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ f (segment t anchor z) = p.eval (segment t anchor z)

theorem support_of_local_ray (f : Parameters → ℝ) (p : AffinePlane)
    (anchor : Parameters) (hconv : AlongSegmentsConvex f)
    (hlocal : LocalRayAffine f p anchor) : p.Supports f := by
  intro z
  obtain ⟨t, ht, ht1, he⟩ := hlocal.2 z
  have h := hconv anchor z t (le_of_lt ht) ht1
  rw [he, affine_segment, hlocal.1] at h
  nlinarith

theorem weighted_eval (p : Fin n → AffinePlane) (w : Fin n → ℝ) (z : Parameters) :
    (∑ i, w i * (p i).eval z) =
      (∑ i, w i * (p i).a) * z.1 + (∑ i, w i * (p i).b) * z.2 +
      ∑ i, w i * (p i).c := by
  calc
    _ = ∑ i, ((w i * (p i).a) * z.1 + (w i * (p i).b) * z.2 + w i * (p i).c) := by
      apply Finset.sum_congr rfl
      intro i hi
      unfold AffinePlane.eval
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_mul]

/-- Nonnegative exact weights eliminate both unrestricted horizontal variables.
The plane supports must be derived from geometry/local persistence separately. -/
theorem weighted_support_bound (f : Parameters → ℝ) (p : Fin n → AffinePlane)
    (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (ha : ∑ i, w i * (p i).a = 0) (hb : ∑ i, w i * (p i).b = 0)
    (hs : ∀ i, (p i).Supports f) (z : Parameters) :
    (∑ i, w i * (p i).c) ≤ f z := by
  have h : (∑ i, w i * (p i).eval z) ≤ ∑ i, w i * f z := by
    apply Finset.sum_le_sum
    intro i hi
    exact mul_le_mul_of_nonneg_left (hs i z) (hw i)
  rw [weighted_eval, ha, hb] at h
  have hr : (∑ i, w i * f z) = f z := by
    rw [← Finset.sum_mul, hsum, one_mul]
  simpa [hr] using h

def cramerN (p : Fin 3 → AffinePlane) : Fin 3 → ℝ :=
  ![(p 1).a * (p 2).b - (p 2).a * (p 1).b,
    (p 2).a * (p 0).b - (p 0).a * (p 2).b,
    (p 0).a * (p 1).b - (p 1).a * (p 0).b]

def cramerDelta (p : Fin 3 → AffinePlane) : ℝ := ∑ i, cramerN p i

theorem cramer_slope_cancellation (p : Fin 3 → AffinePlane) :
    (∑ i, cramerN p i * (p i).a) = 0 ∧
    (∑ i, cramerN p i * (p i).b) = 0 := by
  constructor <;> simp [cramerN, Fin.sum_univ_succ] <;> ring

def cramerWeights (p : Fin 3 → AffinePlane) (i : Fin 3) : ℝ :=
  cramerN p i / cramerDelta p

theorem cramer_weights_valid (p : Fin 3 → AffinePlane)
    (hd : 0 < cramerDelta p) (hn : ∀ i, 0 ≤ cramerN p i) :
    (∀ i, 0 ≤ cramerWeights p i) ∧ (∑ i, cramerWeights p i) = 1 ∧
    (∑ i, cramerWeights p i * (p i).a) = 0 ∧
    (∑ i, cramerWeights p i * (p i).b) = 0 := by
  have hd0 : cramerDelta p ≠ 0 := ne_of_gt hd
  have hc := cramer_slope_cancellation p
  refine ⟨fun i => div_nonneg (hn i) (le_of_lt hd), ?_, ?_, ?_⟩
  · simp only [cramerWeights, ← Finset.sum_div]
    exact div_self hd0
  · calc
      _ = (∑ i, cramerN p i * (p i).a) / cramerDelta p := by
        simp only [cramerWeights, div_mul_eq_mul_div, Finset.sum_div]
      _ = 0 := by rw [hc.1]; simp
  · calc
      _ = (∑ i, cramerN p i * (p i).b) / cramerDelta p := by
        simp only [cramerWeights, div_mul_eq_mul_div, Finset.sum_div]
      _ = 0 := by rw [hc.2]; simp

structure ParameterizedPlane where
  a0 : ℝ
  b0 : ℝ
  c0 : ℝ
  k : ℝ
  d3 : ℝ
  d5 : ℝ

def ParameterizedPlane.at (p : ParameterizedPlane) (y : Parameters) : AffinePlane :=
  ⟨p.a0 + p.k * y.2, p.b0 - p.k * y.1, p.c0 + p.d3 * y.1 + p.d5 * y.2⟩

theorem numerator_affine (p q : ParameterizedPlane) (y : Parameters) :
    (p.at y).a * (q.at y).b - (q.at y).a * (p.at y).b =
      p.a0 * q.b0 - q.a0 * p.b0 +
      (q.a0 * p.k - p.a0 * q.k) * y.1 +
      (p.k * q.b0 - q.k * p.b0) * y.2 := by
  unfold ParameterizedPlane.at
  ring

/-- Abstract finite partition-of-unity soundness, independent of geometric
admission and the unexecuted exact coefficient checks. -/
theorem positive_partition_bound (basis coeff : Fin n → ℝ) (μ : ℝ)
    (hb : ∀ i, 0 ≤ basis i) (hs : ∑ i, basis i = 1)
    (hc : ∀ i, μ ≤ coeff i) : μ ≤ ∑ i, coeff i * basis i := by
  calc
    μ = ∑ i, μ * basis i := by rw [← Finset.mul_sum, hs, mul_one]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_right (hc i) (hb i)

def bernstein (n : ℕ) (i : Fin (n + 1)) (u : ℝ) : ℝ :=
  (Nat.choose n i.val : ℝ) * u ^ i.val * (1 - u) ^ (n - i.val)

theorem bernstein_nonnegative (n : ℕ) (i : Fin (n + 1)) (u : ℝ)
    (hu : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ bernstein n i u := by
  unfold bernstein
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hu _))
    (pow_nonneg (by linarith) _)

def TensorPartitionDuty (m n : ℕ) : Prop :=
  ∀ u v : ℝ, u ∈ Set.Icc 0 1 → v ∈ Set.Icc 0 1 →
    (∑ i : Fin (m + 1) × Fin (n + 1), bernstein m i.1 u * bernstein n i.2 v) = 1

theorem reflection_jensen (f : Parameters → ℝ) (hc : AlongSegmentsConvex f)
    (he : ∀ y, f (-y.1, -y.2) = f y) (y : Parameters) : f (0, 0) ≤ f y := by
  have h := hc y (-y.1, -y.2) (1 / 2) (by norm_num) (by norm_num)
  have hs : segment (1 / 2) y (-y.1, -y.2) = (0, 0) := by
    apply Prod.ext <;> simp [segment] <;> ring
  rw [hs, he y] at h
  linarith

def finiteHull (P0 P3 P5 : Finset Plane) (x3 y3 x5 y5 : ℝ) : Set Plane :=
  convexHull ℝ ((↑P0 : Set Plane) ∪ translate (↑P3) (point x3 y3) ∪
    translate (↑P5) (point x5 y5))

def horizontalArea (P0 P3 P5 : Finset Plane) (y3 y5 : ℝ) (x : Parameters) : ℝ :=
  setArea (finiteHull P0 P3 P5 x.1 y3 x.2 y5)

def verticalArea (P0 P3 P5 : Finset Plane) (x3 x5 : ℝ) (y : Parameters) : ℝ :=
  setArea (finiteHull P0 P3 P5 x3 y.1 x5 y.2)

/-- OPEN adaptation of the cited common-direction shadow-system volume
theorem to finite labelled point sets, including coincidences and degeneracy. -/
def CommonDirectionConvexityDuty : Prop :=
  (∀ P0 P3 P5 y3 y5, AlongSegmentsConvex (horizontalArea P0 P3 P5 y3 y5)) ∧
    (∀ P0 P3 P5 x3 x5, AlongSegmentsConvex (verticalArea P0 P3 P5 x3 x5))

def PointAdmissions (P0 P3 P5 : Finset Plane) (I : Set ℝ) : Prop :=
  (↑P0 : Set Plane) ⊆ D ∧ (↑P3 : Set Plane) ⊆ B3 ∧
    ∀ φ ∈ I, (↑P5 : Set Plane) ⊆ rotate φ '' B5

/-- OPEN: chosen cycles persist on their stated closed vertical cells and
give local shoelace equality for the selected hull. No global H lower bound
is placed in this duty. Literal selected points/cycles need exact decoding. -/
def LocalCycleDuty (P0 P3 P5 : Finset Plane) (Y : Set Parameters)
    (p : Fin 3 → ParameterizedPlane) (anchors : Fin 3 → Parameters) : Prop :=
  ∀ y ∈ Y, ∀ i, LocalRayAffine (horizontalArea P0 P3 P5 y.1 y.2) ((p i).at y) (anchors i)

/-- OPEN actual finite-hull inclusion and finite-volume area monotonicity. -/
def FiniteHullAreaBridgeDuty (P0 P3 P5 : Finset Plane) (I : Set ℝ) : Prop :=
  PointAdmissions P0 P3 P5 I →
    ∀ φ ∈ I, ∀ x3 y3 x5 y5,
      setArea (finiteHull P0 P3 P5 x3 y3 x5 y5) ≤
        H (point x3 y3) (point x5 y5) φ

/-- Pointwise soundness of the exact determinant certificate. Polynomial
checks are inputs with their own provenance, not an asserted H lower bound. -/
theorem cramer_certificate_bound (f : Parameters → ℝ) (p : Fin 3 → AffinePlane)
    (threshold : ℝ) (hd : 0 < cramerDelta p) (hn : ∀ i, 0 ≤ cramerN p i)
    (hs : ∀ i, (p i).Supports f)
    (hT : threshold * cramerDelta p ≤ ∑ i, cramerN p i * (p i).c)
    (z : Parameters) : threshold ≤ f z := by
  obtain ⟨hw, hsum, ha, hb⟩ := cramer_weights_valid p hd hn
  have hbound := weighted_support_bound f p (cramerWeights p) hw hsum ha hb hs z
  have hc : (∑ i, cramerWeights p i * (p i).c) =
      (∑ i, cramerN p i * (p i).c) / cramerDelta p := by
    simp only [cramerWeights, div_mul_eq_mul_div, Finset.sum_div]
  rw [hc] at hbound
  exact ((le_div_iff₀ hd).2 hT).trans hbound

/-- Unrestricted horizontal translations, exactly the supplied vertical/angle
domains. Actual stored point/cycle/polynomial data have not been decoded or
checked. This implication cannot enlarge Y or I. -/
theorem restricted_cell_from_ingredients (P0 P3 P5 : Finset Plane)
    (Y : Set Parameters) (I : Set ℝ) (p : Fin 3 → ParameterizedPlane)
    (anchors : Fin 3 → Parameters) (threshold : ℝ)
    (convexity : CommonDirectionConvexityDuty)
    (admissions : PointAdmissions P0 P3 P5 I)
    (cycles : LocalCycleDuty P0 P3 P5 Y p anchors)
    (areaBridge : FiniteHullAreaBridgeDuty P0 P3 P5 I)
    (checks : ∀ y ∈ Y, 0 < cramerDelta (fun i => (p i).at y) ∧
      (∀ i, 0 ≤ cramerN (fun i => (p i).at y) i) ∧
      threshold * cramerDelta (fun i => (p i).at y) ≤
        ∑ i, cramerN (fun j => (p j).at y) i * ((p i).at y).c) :
    ∀ y ∈ Y, ∀ φ ∈ I, ∀ x3 x5 : ℝ,
      threshold ≤ H (point x3 y.1) (point x5 y.2) φ := by
  intro y hy φ hφ x3 x5
  obtain ⟨hd, hn, hT⟩ := checks y hy
  have hs : ∀ i, ((p i).at y).Supports (horizontalArea P0 P3 P5 y.1 y.2) := by
    intro i
    exact support_of_local_ray _ _ (anchors i) (convexity.1 P0 P3 P5 y.1 y.2)
      (cycles y hy i)
  have hb := cramer_certificate_bound _ (fun i => (p i).at y) threshold hd hn hs hT (x3, x5)
  exact hb.trans (areaBridge admissions φ hφ x3 y.1 x5 y.2)

/-- Uniform dot-product bound retains possible interior stationary extrema;
endpoint-only admission is not substituted for a continuous-angle premise. -/
theorem rotating_dot_lower (A B s : ℝ) :
    -Real.sqrt (A ^ 2 + B ^ 2) ≤ A * Real.cos s + B * Real.sin s := by
  have hr : 0 ≤ A ^ 2 + B ^ 2 := by positivity
  have hs := Real.sq_sqrt hr
  have ht := Real.sin_sq_add_cos_sq s
  have hi : (A * Real.cos s + B * Real.sin s) ^ 2 +
      (A * Real.sin s - B * Real.cos s) ^ 2 =
      (A ^ 2 + B ^ 2) * (Real.sin s ^ 2 + Real.cos s ^ 2) := by ring
  rw [ht, mul_one] at hi
  have hp : (A * Real.cos s + B * Real.sin s) ^ 2 ≤ A ^ 2 + B ^ 2 := by
    nlinarith [sq_nonneg (A * Real.sin s - B * Real.cos s)]
  have hroot := Real.sqrt_nonneg (A ^ 2 + B ^ 2)
  by_contra h
  have h1 : A * Real.cos s + B * Real.sin s + Real.sqrt (A ^ 2 + B ^ 2) < 0 := by linarith
  have h2 : A * Real.cos s + B * Real.sin s - Real.sqrt (A ^ 2 + B ^ 2) < 0 := by linarith
  have hprod := mul_pos_of_neg_of_neg h1 h2
  nlinarith

end Partials.Covering.Support
end
