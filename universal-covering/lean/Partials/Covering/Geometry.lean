import Partials.Covering.Model

open scoped ENNReal

noncomputable section

/-! Blind R4 source. The explicit duties below are unproved inputs, not axioms,
instances, or a supplied confinement conclusion. See GEOMETRY_PROOF.md. -/
namespace Partials.Covering

/-- OPEN coordinate identification of the EuclideanSpace norm. This is the
only norm-coordinate input; rotations and coordinate bounds are derived. -/
def EuclideanCoordinateDuty : Prop :=
  ∀ x : Plane, ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2

/-- P1 checks the concrete Euclidean coordinate identity in the pinned library. -/
theorem euclideanCoordinate_verified : EuclideanCoordinateDuty := by
  intro x
  simpa only [Fin.sum_univ_two] using EuclideanSpace.real_norm_sq_eq x

theorem point_zero (x y : ℝ) : point x y 0 = x := by simp [point]
theorem point_one (x y : ℝ) : point x y 1 = y := by simp [point]

theorem point_coordinates (x : Plane) : point (x 0) (x 1) = x := by
  ext i
  fin_cases i <;> simp [point]

theorem point_norm_sq (h : EuclideanCoordinateDuty) (x y : ℝ) :
    ‖point x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  simpa [point] using h (point x y)

theorem coordinate_abs_le_norm (h : EuclideanCoordinateDuty) (x : Plane) :
    |x 1| ≤ ‖x‖ := by
  have hs := h x
  have ha : |x 1| ^ 2 = (x 1) ^ 2 := by rw [sq_abs]
  nlinarith [sq_nonneg (x 0), abs_nonneg (x 1), norm_nonneg x]

theorem unit_point_norm (h : EuclideanCoordinateDuty) (θ : ℝ) :
    ‖point (Real.cos θ) (Real.sin θ)‖ = 1 := by
  have hs := point_norm_sq h (Real.cos θ) (Real.sin θ)
  have ht := Real.cos_sq_add_sin_sq θ
  nlinarith [norm_nonneg (point (Real.cos θ) (Real.sin θ))]

theorem rotate_add (θ : ℝ) (x y : Plane) :
    rotate θ (x + y) = rotate θ x + rotate θ y := by
  ext i
  fin_cases i <;> simp [rotate, point] <;> ring

theorem rotate_sub (θ : ℝ) (x y : Plane) :
    rotate θ (x - y) = rotate θ x - rotate θ y := by
  ext i
  fin_cases i <;> simp [rotate, point] <;> ring

theorem rotate_zero_angle (x : Plane) : rotate 0 x = x := by
  ext i
  fin_cases i <;> simp [rotate, point]

theorem rotate_origin (θ : ℝ) : rotate θ (0 : Plane) = 0 := by
  ext i
  fin_cases i <;> simp [rotate, point]

theorem rotate_compose (θ φ : ℝ) (x : Plane) :
    rotate θ (rotate φ x) = rotate (θ + φ) x := by
  ext i
  fin_cases i <;> simp [rotate, point, Real.cos_add, Real.sin_add] <;> ring

theorem rotate_inverse (θ : ℝ) (x : Plane) :
    rotate (-θ) (rotate θ x) = x := by
  rw [rotate_compose]
  simp [rotate_zero_angle]

theorem rotate_norm (h : EuclideanCoordinateDuty) (θ : ℝ) (x : Plane) :
    ‖rotate θ x‖ = ‖x‖ := by
  have hs : ‖rotate θ x‖ ^ 2 = ‖x‖ ^ 2 := by
    calc
      ‖rotate θ x‖ ^ 2 =
          (Real.cos θ * x 0 - Real.sin θ * x 1) ^ 2 +
          (Real.sin θ * x 0 + Real.cos θ * x 1) ^ 2 := by
            simpa [rotate, point] using h (rotate θ x)
      _ = (Real.cos θ ^ 2 + Real.sin θ ^ 2) *
          ((x 0) ^ 2 + (x 1) ^ 2) := by ring
      _ = ‖x‖ ^ 2 := by rw [Real.cos_sq_add_sin_sq, one_mul, h x]
  nlinarith [norm_nonneg x, norm_nonneg (rotate θ x)]

theorem rotate_surjective (θ : ℝ) : Function.Surjective (rotate θ) := by
  intro x
  refine ⟨rotate (-θ) x, ?_⟩
  rw [rotate_compose]
  simp [rotate_zero_angle]

theorem reflect_involutive : Function.Involutive reflect := by
  intro x
  ext i
  fin_cases i <;> simp [reflect, point]

@[simp] theorem reflect_reflect (x : Plane) : reflect (reflect x) = x :=
  reflect_involutive x

theorem reflect_sub (x y : Plane) : reflect (x - y) = reflect x - reflect y := by
  ext i
  fin_cases i <;> simp [reflect, point] <;> ring

theorem reflect_norm (h : EuclideanCoordinateDuty) (x : Plane) :
    ‖reflect x‖ = ‖x‖ := by
  have hs : ‖reflect x‖ ^ 2 = ‖x‖ ^ 2 := by
    calc
      ‖reflect x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
        simpa [reflect, point] using h (reflect x)
      _ = ‖x‖ ^ 2 := (h x).symm
  nlinarith [norm_nonneg x, norm_nonneg (reflect x)]

theorem reflect_rotate (φ : ℝ) (x : Plane) :
    reflect (rotate φ x) = rotate (-φ) (reflect x) := by
  ext i
  fin_cases i <;> simp [reflect, rotate, point, Real.cos_neg, Real.sin_neg] <;> ring

theorem rotate_disk (h : EuclideanCoordinateDuty) (θ r : ℝ) :
    rotate θ '' disk 0 r = disk 0 r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [Partials.Interface.ClosedDisk, rotate_norm h] using hy
  · intro hx
    refine ⟨rotate (-θ) x, ?_, ?_⟩
    · simpa [Partials.Interface.ClosedDisk, rotate_norm h] using hx
    · rw [rotate_compose]
      simp [rotate_zero_angle]

theorem rho_positive (n : ℕ)
    (hc : 0 < Real.cos (Real.pi / (2 * (n : ℝ)))) : 0 < rho n := by
  exact div_pos (by norm_num) (mul_pos (by norm_num) hc)

theorem rho_square_identity (n : ℕ)
    (hc : Real.cos (Real.pi / (2 * (n : ℝ))) ≠ 0) :
    (rho n) ^ 2 * (4 * Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2) = 1 := by
  unfold rho
  field_simp [hc]
  <;> ring

theorem center_norm (h : EuclideanCoordinateDuty) (n : ℕ)
    (hc : 0 < Real.cos (Real.pi / (2 * (n : ℝ)))) (j : Fin n) :
    ‖center n j‖ = rho n := by
  have hp := rho_positive n hc
  simp [center, norm_smul, Real.norm_eq_abs, abs_of_pos hp, unit_point_norm h]

theorem inner_disk_sandwich (n : ℕ)
    (hn : ∀ j : Fin n, ‖center n j‖ = rho n) :
    disk 0 (1 - rho n) ⊆ reuleaux n := by
  intro x hx j
  have hx' : ‖x‖ ≤ 1 - rho n := by
    simpa [Partials.Interface.ClosedDisk] using hx
  show ‖x - center n j‖ ≤ 1
  calc
    ‖x - center n j‖ ≤ ‖x‖ + ‖center n j‖ := norm_sub_le _ _
    _ ≤ 1 := by rw [hn j]; linarith

/-- OPEN finite angular mesh bridge: choose a defining center within π/n
of the direction opposite x and expand the squared Euclidean distance.
This supplies neither a sandwich conclusion nor an area lower bound. -/
def CenterDirectionDuty (n : ℕ) : Prop :=
  ∀ x : Plane, rho n < ‖x‖ → ∃ j : Fin n,
    ‖x‖ ^ 2 + (rho n) ^ 2 +
      2 * ‖x‖ * rho n * Real.cos (Real.pi / (n : ℝ)) ≤ ‖x - center n j‖ ^ 2

theorem outer_disk_sandwich (n : ℕ) (hdir : CenterDirectionDuty n)
    (hr : 0 < rho n) (hc : 0 < Real.cos (Real.pi / (n : ℝ)))
    (hid : 2 * (rho n) ^ 2 * (1 + Real.cos (Real.pi / (n : ℝ))) = 1) :
    reuleaux n ⊆ disk 0 (rho n) := by
  intro x hx
  show ‖x - 0‖ ≤ rho n
  simp only [sub_zero]
  by_contra hbad
  have hgt : rho n < ‖x‖ := lt_of_not_ge hbad
  obtain ⟨j, hj⟩ := hdir x hgt
  have hdist : ‖x - center n j‖ ≤ 1 := hx j
  have hprod : rho n * Real.cos (Real.pi / (n : ℝ)) > 0 := mul_pos hr hc
  have hcross : 2 * ‖x‖ * rho n * Real.cos (Real.pi / (n : ℝ)) ≥
      2 * rho n * rho n * Real.cos (Real.pi / (n : ℝ)) := by
    have hm := mul_le_mul_of_nonneg_right (le_of_lt hgt)
      (le_of_lt (mul_pos (by norm_num : (0 : ℝ) < 2) hprod))
    nlinarith
  have hsq := mul_pos (sub_pos.mpr hgt)
    (show 0 < ‖x‖ + rho n by linarith)
  nlinarith [norm_nonneg (x - center n j), norm_nonneg x]

/-- OPEN exact classical trigonometry at π/6, π/10, π/3 and π/5.
All fields are identities/signs; the rational rho cutoffs are derived below. -/
structure RadiusTrigonometryDuty : Prop where
  cos3_pos : 0 < Real.cos (Real.pi / (2 * (3 : ℝ)))
  cos5_pos : 0 < Real.cos (Real.pi / (2 * (5 : ℝ)))
  cos3_square : Real.cos (Real.pi / (2 * (3 : ℝ))) ^ 2 = 3 / 4
  cos5_square : Real.cos (Real.pi / (2 * (5 : ℝ))) ^ 2 = (5 + Real.sqrt 5) / 8
  double3 : Real.cos (Real.pi / 3) =
    2 * Real.cos (Real.pi / (2 * (3 : ℝ))) ^ 2 - 1
  double5 : Real.cos (Real.pi / 5) =
    2 * Real.cos (Real.pi / (2 * (5 : ℝ))) ^ 2 - 1

/-- P1 supplies the exact scalar trigonometric fields; angular mesh geometry
is still a separate duty. -/
theorem radiusTrigonometry_verified : RadiusTrigonometryDuty := by
  have h3 : 0 < Real.cos (Real.pi / (2 * (3 : ℝ))) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have h5 : 0 < Real.cos (Real.pi / (2 * (5 : ℝ))) := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  have d3 : Real.cos (Real.pi / 3) =
      2 * Real.cos (Real.pi / (2 * (3 : ℝ))) ^ 2 - 1 := by
    convert Real.cos_two_mul (Real.pi / (2 * (3 : ℝ))) using 1 <;> congr 1 <;> ring
  have d5 : Real.cos (Real.pi / 5) =
      2 * Real.cos (Real.pi / (2 * (5 : ℝ))) ^ 2 - 1 := by
    convert Real.cos_two_mul (Real.pi / (2 * (5 : ℝ))) using 1 <;> congr 1 <;> ring
  refine ⟨h3, h5, ?_, ?_, d3, d5⟩
  · convert Real.sq_cos_pi_div_six using 1 <;> norm_num
  · rw [Real.cos_pi_div_five] at d5
    linarith

theorem sqrt_five_lower : (223 : ℝ) / 100 < Real.sqrt 5 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  nlinarith [Real.sqrt_nonneg (5 : ℝ)]

theorem rho3_rational_bound (h : RadiusTrigonometryDuty) : rho 3 < 289 / 500 := by
  have hp := rho_positive 3 h.cos3_pos
  have hs := rho_square_identity 3 (ne_of_gt h.cos3_pos)
  norm_num only [Nat.cast_ofNat] at hs
  have hcos : Real.cos (Real.pi / 6) ^ 2 = 3 / 4 := by
    convert h.cos3_square using 1 <;> norm_num
  rw [hcos] at hs
  nlinarith

theorem rho5_rational_bound (h : RadiusTrigonometryDuty) : rho 5 < 263 / 500 := by
  have hc : (250 : ℝ) / 263 < Real.cos (Real.pi / (2 * (5 : ℝ))) := by
    have hs := h.cos5_square
    have hr := sqrt_five_lower
    nlinarith [h.cos5_pos]
  unfold rho
  apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) h.cos5_pos)).2
  nlinarith

theorem rho_width_identity (n : ℕ)
    (hc : Real.cos (Real.pi / (2 * (n : ℝ))) ≠ 0)
    (hd : Real.cos (Real.pi / (n : ℝ)) =
      2 * Real.cos (Real.pi / (2 * (n : ℝ))) ^ 2 - 1) :
    2 * (rho n) ^ 2 * (1 + Real.cos (Real.pi / (n : ℝ))) = 1 := by
  have hs := rho_square_identity n hc
  rw [hd]
  nlinarith

theorem concrete_inner_disks (he : EuclideanCoordinateDuty)
    (ht : RadiusTrigonometryDuty) : (disk 0 r3 ⊆ B3) ∧ (disk 0 r5 ⊆ B5) := by
  have hi3 := inner_disk_sandwich 3 (center_norm he 3 ht.cos3_pos)
  have hi5 := inner_disk_sandwich 5 (center_norm he 5 ht.cos5_pos)
  have hr3 : r3 ≤ 1 - rho 3 := by
    have h := rho3_rational_bound ht
    norm_num [r3] at *
    linarith
  have hr5 : r5 ≤ 1 - rho 5 := by
    have h := rho5_rational_bound ht
    norm_num [r5] at *
    linarith
  constructor
  · intro x hx
    apply hi3
    exact le_trans hx hr3
  · intro x hx
    apply hi5
    exact le_trans hx hr5

theorem concrete_sandwiches (he : EuclideanCoordinateDuty)
    (ht : RadiusTrigonometryDuty) (hd3 : CenterDirectionDuty 3)
    (hd5 : CenterDirectionDuty 5) :
    (disk 0 r3 ⊆ B3) ∧ (B3 ⊆ disk 0 (rho 3)) ∧
    (disk 0 r5 ⊆ B5) ∧ (B5 ⊆ disk 0 (rho 5)) := by
  obtain ⟨hi3, hi5⟩ := concrete_inner_disks he ht
  have ho3 := outer_disk_sandwich 3 hd3 (rho_positive 3 ht.cos3_pos)
    (by norm_num only [Nat.cast_ofNat]; rw [ht.double3, ht.cos3_square]; norm_num)
    (rho_width_identity 3 (ne_of_gt ht.cos3_pos) ht.double3)
  have ho5 := outer_disk_sandwich 5 hd5 (rho_positive 5 ht.cos5_pos)
    (by norm_num only [Nat.cast_ofNat]; rw [ht.double5, ht.cos5_square]; nlinarith [sqrt_five_lower])
    (rho_width_identity 5 (ne_of_gt ht.cos5_pos) ht.double5)
  exact ⟨hi3, ho3, hi5, ho5⟩

def diskHull (R r d : ℝ) : Set Plane :=
  convexHull ℝ (disk 0 R ∪ disk (point d 0) r)

noncomputable def diskHullArea (R r d : ℝ) : ℝ := setArea (diskHull R r d)

def diskAreaExpression (R r d : ℝ) : ℝ :=
  Real.pi / 2 * (R ^ 2 + r ^ 2) +
  (R ^ 2 - r ^ 2) * Real.arcsin ((R - r) / d) +
  (R + r) * Real.sqrt (d ^ 2 - (R - r) ^ 2)

/-- Proven real-area monotonicity requires finite volume of the larger set;
measurability is not needed for the outer-measure inequality itself. -/
theorem setArea_mono {S U : Set Plane} (hsub : S ⊆ U)
    (hfinite : MeasureTheory.volume U ≠ ∞) : setArea S ≤ setArea U := by
  exact ENNReal.toReal_mono hfinite (MeasureTheory.measure_mono hsub)

/-- OPEN boundary/Green bridge, including the contained-disk branch.
The four arc/segment integrals in main.tex Lemma two-disks must be proved
for the actual volume.toReal area before this duty can be discharged. -/
def DiskHullAreaFormulaDuty : Prop :=
  ∀ R r d : ℝ, 0 < r → r ≤ R → 0 ≤ d →
    (d ≤ R - r → diskHullArea R r d = Real.pi * R ^ 2) ∧
    (R - r < d → diskHullArea R r d = diskAreaExpression R r d)

/-- OPEN boundary correspondence plus Green's theorem for the actual disk
hull, with θ=arccos((R-r)/d). The four terms retain the manuscript's large
arc, bottom segment, small arc and top segment in that order. -/
def DiskHullBoundaryGreenDuty : Prop :=
  ∀ R r d : ℝ, 0 < r → r ≤ R → R - r < d →
    let θ := Real.arccos ((R - r) / d)
    diskHullArea R r d = R ^ 2 * (Real.pi - θ) + d * R * Real.sin θ / 2 +
      (r ^ 2 * θ + d * r * Real.sin θ) + d * R * Real.sin θ / 2

/-- OPEN analytic substitutions for the contact angle; these are scalar
identities independent of area or convex-hull conclusions. -/
def DiskTangentTrigonometryDuty : Prop :=
  ∀ R r d : ℝ, 0 < r → r ≤ R → R - r < d →
    Real.arccos ((R - r) / d) = Real.pi / 2 - Real.arcsin ((R - r) / d) ∧
    d * Real.sin (Real.arccos ((R - r) / d)) = Real.sqrt (d ^ 2 - (R - r) ^ 2)

/-- OPEN contained-case area bridge, separated from the noncontained Green
argument so neither an overlapping nor a disjoint case is silently dropped. -/
def DiskHullContainedAreaDuty : Prop :=
  ∀ R r d : ℝ, 0 < r → r ≤ R → 0 ≤ d → d ≤ R - r →
    diskHullArea R r d = Real.pi * R ^ 2

theorem unequal_disk_formula_from_boundary (hg : DiskHullBoundaryGreenDuty)
    (ht : DiskTangentTrigonometryDuty) {R r d : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hd : R - r < d) :
    diskHullArea R r d = diskAreaExpression R r d := by
  obtain ⟨hθ, hs⟩ := ht R r d hr hrR hd
  calc
    diskHullArea R r d = Real.pi * R ^ 2 - (R ^ 2 - r ^ 2) *
        Real.arccos ((R - r) / d) + (R + r) *
        (d * Real.sin (Real.arccos ((R - r) / d))) := by
          rw [hg R r d hr hrR hd]
          ring
    _ = diskAreaExpression R r d := by
      rw [hθ] at hs ⊢
      rw [hs]
      unfold diskAreaExpression
      ring

theorem diskHullAreaFormula_of_bridges (hc : DiskHullContainedAreaDuty)
    (hg : DiskHullBoundaryGreenDuty) (ht : DiskTangentTrigonometryDuty) :
    DiskHullAreaFormulaDuty := by
  intro R r d hr hrR hd
  exact ⟨hc R r d hr hrR hd, unequal_disk_formula_from_boundary hg ht hr hrR⟩

/-- The same radius-r offset z is used at both endpoints. This proves the
segment step in the manuscript; only area finiteness remains an input. -/
theorem diskHull_segment {R r d1 d2 : ℝ}
    (hrR : r ≤ R) (h0 : 0 ≤ d1) (h12 : d1 ≤ d2) :
    disk (point d1 0) r ⊆ diskHull R r d2 := by
  intro x hx
  by_cases h2 : d2 = 0
  · have h1 : d1 = 0 := by linarith
    apply subset_convexHull ℝ _
    right
    simpa [h1, h2] using hx
  · have h2pos : 0 < d2 := lt_of_le_of_ne (le_trans h0 h12) (Ne.symm h2)
    let z : Plane := x - point d1 0
    let weight : ℝ := d1 / d2
    have hzbound : ‖z‖ ≤ r := hx
    have hz : z ∈ disk 0 R := by
      show ‖z - 0‖ ≤ R
      simpa using le_trans hzbound hrR
    have hy : z + point d2 0 ∈ disk (point d2 0) r := by
      show ‖(z + point d2 0) - point d2 0‖ ≤ r
      simpa using hzbound
    have hweight0 : 0 ≤ weight := div_nonneg h0 (le_of_lt h2pos)
    have hweight1 : weight ≤ 1 := (div_le_one h2pos).2 h12
    have hc := convex_convexHull ℝ (disk 0 R ∪ disk (point d2 0) r)
    have hm : (1 - weight) • z + weight • (z + point d2 0) ∈ diskHull R r d2 :=
      hc (subset_convexHull ℝ _ (Or.inl hz))
        (subset_convexHull ℝ _ (Or.inr hy)) (by linarith) hweight0 (by ring)
    have heq : (1 - weight) • z + weight • (z + point d2 0) = x := by
      ext i
      fin_cases i <;> simp [z, weight, point] <;> field_simp [h2] <;> ring
    rwa [heq] at hm

theorem diskHull_mono {R r d1 d2 : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (h0 : 0 ≤ d1) (h12 : d1 ≤ d2) :
    diskHull R r d1 ⊆ diskHull R r d2 := by
  apply convexHull_min
  · intro x hx
    rcases hx with hx | hx
    · exact subset_convexHull ℝ _ (Or.inl hx)
    · exact diskHull_segment hrR h0 h12 hx
  · exact convex_convexHull ℝ _

theorem diskHullArea_mono {R r d1 d2 : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (h0 : 0 ≤ d1) (h12 : d1 ≤ d2)
    (hf : MeasureTheory.volume (diskHull R r d2) ≠ ∞) :
    diskHullArea R r d1 ≤ diskHullArea R r d2 := by
  exact setArea_mono (diskHull_mono hr hrR h0 h12) hf

end Partials.Covering

end
