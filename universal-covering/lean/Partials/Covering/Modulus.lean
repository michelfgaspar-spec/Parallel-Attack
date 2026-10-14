import Partials.Covering.Infima

noncomputable section

/-! Blind, uncompiled R4 source. The radius and displacement estimates feed a
generic Steiner/Cauchy area implication. The equal-step argument and transfer
to infima/clipping are mathematical proof source, not numerical replay. -/
namespace Partials.Covering

def angularLinearCoefficient : ℝ :=
  2 * Real.pi * hullRadius * pentagonRadius

def angularQuadraticCoefficient : ℝ := Real.pi * pentagonRadius ^ 2

def QAngularAreaBound : Prop :=
  ∀ t ∈ Q, ∀ φ ψ : ℝ,
    |placementArea t φ - placementArea t ψ| ≤ C * |φ - ψ|

def ClippedAngularModulus : Prop :=
  ∀ φ ψ : ℝ, |clippedG φ - clippedG ψ| ≤ C * |φ - ψ|

/-- Concrete lower-level obligations: rational sandwich bounds and the
pointwise rotation estimate. None of the fields supplies an area estimate. -/
structure QHullInputs : Prop where
  B3_outer_rational : B3 ⊆ disk 0 (289 / 500)
  B5_outer_rational : B5 ⊆ disk 0 pentagonRadius
  rotate_norm : ∀ φ x, ‖rotate φ x‖ = ‖x‖
  rotate_displacement : ∀ φ ψ x,
    ‖rotate φ x - rotate ψ x‖ ≤ ‖x‖ * |φ - ψ|

def DiskInteriorDuty : Prop := (interior D).Nonempty

/-- P1 supplies a concrete interior point of the exact radius-one-half disk. -/
theorem diskInterior_verified : DiskInteriorDuty := by
  refine ⟨0, ?_⟩
  change (0 : Plane) ∈ interior (disk 0 (1 / 2))
  rw [disk_eq_closedBall]
  apply Metric.ball_subset_interior_closedBall
  norm_num

theorem hull_interior_of_disk (hd : DiskInteriorDuty)
    (t3 t5 : Plane) (φ : ℝ) : (interior (K t3 t5 φ)).Nonempty :=
  hd.mono (interior_mono (D_subset_K t3 t5 φ))

theorem Q_hull_radius (b : QHullInputs) {t : Translations} (ht : t ∈ Q)
    (φ : ℝ) : K t.1 t.2 φ ⊆ disk 0 hullRadius := by
  apply convexHull_min _ (disk_convex 0 hullRadius)
  rintro x ((hx | hx) | hx)
  · change ‖x - 0‖ ≤ hullRadius
    exact le_trans hx (by norm_num [hullRadius])
  · have hb := b.B3_outer_rational hx
    change ‖x - t.1 - 0‖ ≤ (289 / 500 : ℝ) at hb
    simp only [sub_zero] at hb
    have hn : ‖x‖ ≤ ‖x - t.1‖ + ‖t.1‖ := by
      calc
        ‖x‖ = ‖(x - t.1) + t.1‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - t.1‖ + ‖t.1‖ := norm_add_le _ _
    change ‖x - 0‖ ≤ hullRadius
    simp only [sub_zero]
    have ht3 := ht.1
    norm_num [d3, hullRadius] at ht3 ⊢
    linarith
  · change x - t.2 ∈ rotate φ '' B5 at hx
    rcases hx with ⟨y, hy, hxy⟩
    have hb := b.B5_outer_rational hy
    change ‖y - 0‖ ≤ pentagonRadius at hb
    simp only [sub_zero] at hb
    have hn : ‖x‖ ≤ ‖y‖ + ‖t.2‖ := by
      calc
        ‖x‖ = ‖(x - t.2) + t.2‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - t.2‖ + ‖t.2‖ := norm_add_le _ _
        _ = ‖y‖ + ‖t.2‖ := by rw [← hxy, b.rotate_norm]
    change ‖x - 0‖ ≤ hullRadius
    simp only [sub_zero]
    have ht5 := ht.2
    norm_num [d5, hullRadius, pentagonRadius] at ht5 hb ⊢
    linarith

theorem convex_parallelBody {S : Set Plane} (hS : Convex ℝ S) (ε : ℝ) :
    Convex ℝ (parallelBody S ε) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨sx, hsx, ux, hux, rfl⟩
  rcases hy with ⟨sy, hsy, uy, huy, rfl⟩
  refine ⟨a • sx + b • sy, hS hsx hsy ha hb hab,
    a • ux + b • uy, ?_, ?_⟩
  · calc
      ‖a • ux + b • uy‖ ≤ ‖a • ux‖ + ‖b • uy‖ := norm_add_le _ _
      _ = a * ‖ux‖ + b * ‖uy‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      _ ≤ a * ε + b * ε := add_le_add
        (mul_le_mul_of_nonneg_left hux ha) (mul_le_mul_of_nonneg_left huy hb)
      _ = ε := by rw [← add_mul, hab, one_mul]
  · simp only [smul_add]
    abel

/-- Finite convex-combination replacement, proved as convexity of the
parallel body; this is the convex-hull nonexpansion step in the paper. -/
theorem convexHull_parallel_transport {S U : Set Plane} {ε : ℝ}
    (hnear : S ⊆ parallelBody U ε) :
    convexHull ℝ S ⊆ parallelBody (convexHull ℝ U) ε := by
  apply convexHull_min _ (convex_parallelBody (convex_convexHull ℝ U) ε)
  intro x hx
  rcases hnear hx with ⟨y, hy, u, hu, hxy⟩
  exact ⟨y, subset_convexHull ℝ U hy, u, hu, hxy⟩

def constituents (t : Translations) (φ : ℝ) : Set Plane :=
  D ∪ translate B3 t.1 ∪ translate (rotate φ '' B5) t.2

theorem constituents_rotation_transport (b : QHullInputs)
    (t : Translations) (φ ψ : ℝ) :
    constituents t φ ⊆ parallelBody (constituents t ψ)
      (pentagonRadius * |φ - ψ|) := by
  have hc : 0 ≤ pentagonRadius * |φ - ψ| := by
    unfold pentagonRadius
    positivity
  rintro x ((hx | hx) | hx)
  · exact ⟨x, Or.inl (Or.inl hx), 0, by simpa using hc, by simp⟩
  · exact ⟨x, Or.inl (Or.inr hx), 0, by simpa using hc, by simp⟩
  · change x - t.2 ∈ rotate φ '' B5 at hx
    rcases hx with ⟨y, hy, hxy⟩
    have hB := b.B5_outer_rational hy
    change ‖y - 0‖ ≤ pentagonRadius at hB
    simp only [sub_zero] at hB
    have hdisp : ‖rotate φ y - rotate ψ y‖ ≤ pentagonRadius * |φ - ψ| :=
      le_trans (b.rotate_displacement φ ψ y)
        (mul_le_mul_of_nonneg_right hB (abs_nonneg _))
    refine ⟨rotate ψ y + t.2, Or.inr ?_, rotate φ y - rotate ψ y, hdisp, ?_⟩
    · change (rotate ψ y + t.2) - t.2 ∈ rotate ψ '' B5
      simp only [add_sub_cancel_right]
      exact ⟨y, hy, rfl⟩
    · have hx : x = rotate φ y + t.2 := by
        rw [hxy]
        exact (sub_add_cancel x t.2).symm
      rw [hx]
      abel

theorem hull_rotation_transport (b : QHullInputs)
    (t : Translations) (φ ψ : ℝ) :
    HausdorffWithin (K t.1 t.2 φ) (K t.1 t.2 ψ)
      (pentagonRadius * |φ - ψ|) := by
  constructor
  · exact convexHull_parallel_transport (constituents_rotation_transport b t φ ψ)
  · have h := convexHull_parallel_transport (constituents_rotation_transport b t ψ φ)
    simpa only [abs_sub_comm ψ φ, K, constituents] using h

/-- Radius inclusion for arbitrary translations; Q is not required here. -/
theorem hull_radius_of_translation_bounds (b : QHullInputs)
    (t : Translations) (φ R : ℝ) (hD : (1 / 2 : ℝ) ≤ R)
    (h3 : ‖t.1‖ + 289 / 500 ≤ R)
    (h5 : ‖t.2‖ + pentagonRadius ≤ R) : K t.1 t.2 φ ⊆ disk 0 R := by
  apply convexHull_min _ (disk_convex 0 R)
  rintro x ((hx | hx) | hx)
  · exact le_trans hx hD
  · have hb := b.B3_outer_rational hx
    change ‖x - t.1 - 0‖ ≤ (289 / 500 : ℝ) at hb
    simp only [sub_zero] at hb
    have hn : ‖x‖ ≤ ‖x - t.1‖ + ‖t.1‖ := by
      calc
        ‖x‖ = ‖(x - t.1) + t.1‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - t.1‖ + ‖t.1‖ := norm_add_le _ _
    change ‖x - 0‖ ≤ R
    simp only [sub_zero]
    linarith
  · change x - t.2 ∈ rotate φ '' B5 at hx
    rcases hx with ⟨y, hy, hxy⟩
    have hb := b.B5_outer_rational hy
    change ‖y - 0‖ ≤ pentagonRadius at hb
    simp only [sub_zero] at hb
    have hn : ‖x‖ ≤ ‖y‖ + ‖t.2‖ := by
      calc
        ‖x‖ = ‖(x - t.2) + t.2‖ := by rw [sub_add_cancel]
        _ ≤ ‖x - t.2‖ + ‖t.2‖ := norm_add_le _ _
        _ = ‖y‖ + ‖t.2‖ := by rw [← hxy, b.rotate_norm]
    change ‖x - 0‖ ≤ R
    simp only [sub_zero]
    linarith

theorem constituents_placement_transport (b : QHullInputs)
    (w z : Translations × ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (h3 : ‖w.1.1 - z.1.1‖ ≤ ε)
    (h5 : ‖w.1.2 - z.1.2‖ + pentagonRadius * |w.2 - z.2| ≤ ε) :
    constituents w.1 w.2 ⊆ parallelBody (constituents z.1 z.2) ε := by
  rintro x ((hx | hx) | hx)
  · exact ⟨x, Or.inl (Or.inl hx), 0, by simpa using hε, by simp⟩
  · refine ⟨(x - w.1.1) + z.1.1, Or.inl (Or.inr ?_),
      w.1.1 - z.1.1, h3, ?_⟩
    · change ((x - w.1.1) + z.1.1) - z.1.1 ∈ B3
      change x - w.1.1 ∈ B3 at hx
      simpa only [add_sub_cancel_right] using hx
    · abel
  · change x - w.1.2 ∈ rotate w.2 '' B5 at hx
    rcases hx with ⟨y, hy, hxy⟩
    have hB := b.B5_outer_rational hy
    change ‖y - 0‖ ≤ pentagonRadius at hB
    simp only [sub_zero] at hB
    have hd := le_trans (b.rotate_displacement w.2 z.2 y)
      (mul_le_mul_of_nonneg_right hB (abs_nonneg _))
    have hu : ‖(rotate w.2 y - rotate z.2 y) + (w.1.2 - z.1.2)‖ ≤ ε := by
      have hn := norm_add_le (rotate w.2 y - rotate z.2 y) (w.1.2 - z.1.2)
      linarith
    refine ⟨rotate z.2 y + z.1.2, Or.inr ?_,
      (rotate w.2 y - rotate z.2 y) + (w.1.2 - z.1.2), hu, ?_⟩
    · change (rotate z.2 y + z.1.2) - z.1.2 ∈ rotate z.2 '' B5
      simp only [add_sub_cancel_right]
      exact ⟨y, hy, rfl⟩
    · have hx : x = rotate w.2 y + w.1.2 := by
        rw [hxy]
        exact (sub_add_cancel x w.1.2).symm
      rw [hx]
      abel

theorem placement_component_distance (w z : Translations × ℝ) :
    ‖w.1.1 - z.1.1‖ ≤ dist w z ∧
    ‖w.1.2 - z.1.2‖ ≤ dist w z ∧ |w.2 - z.2| ≤ dist w z := by
  have htrans : dist w.1 z.1 ≤ dist w z := by
    simpa only [Prod.dist_eq] using
      (le_max_left (dist w.1 z.1) (dist w.2 z.2))
  have hfirst : dist w.1.1 z.1.1 ≤ dist w.1 z.1 := by
    simpa only [Prod.dist_eq] using
      (le_max_left (dist w.1.1 z.1.1) (dist w.1.2 z.1.2))
  have hsecond : dist w.1.2 z.1.2 ≤ dist w.1 z.1 := by
    simpa only [Prod.dist_eq] using
      (le_max_right (dist w.1.1 z.1.1) (dist w.1.2 z.1.2))
  have hangle : dist w.2 z.2 ≤ dist w z := by
    simpa only [Prod.dist_eq] using
      (le_max_right (dist w.1 z.1) (dist w.2 z.2))
  exact ⟨by simpa only [dist_eq_norm] using le_trans hfirst htrans,
    by simpa only [dist_eq_norm] using le_trans hsecond htrans,
    by simpa only [Real.dist_eq] using hangle⟩

/-- The local hull-continuity bridge is derived from the concrete body inputs.
This controls all nearby placements with a radius chosen before ε. -/
theorem local_hull_transport_of_body_inputs (b : QHullInputs)
    (hd : DiskInteriorDuty) : LocalHullTransportDuty := by
  intro z
  let R : ℝ := 3 + ‖z.1.1‖ + ‖z.1.2‖
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hD : (1 / 2 : ℝ) ≤ R := by
    dsimp [R]
    have h1 := norm_nonneg z.1.1
    have h2 := norm_nonneg z.1.2
    linarith
  have hz3 : ‖z.1.1‖ + 289 / 500 ≤ R := by
    dsimp [R]
    have hn := norm_nonneg z.1.2
    linarith
  have hz5 : ‖z.1.2‖ + pentagonRadius ≤ R := by
    dsimp [R, pentagonRadius]
    have hn := norm_nonneg z.1.1
    linarith
  refine ⟨R, hR, hull_interior_of_disk hd _ _ _,
    hull_radius_of_translation_bounds b z.1 z.2 R hD hz3 hz5, ?_⟩
  intro ε hε
  let δ : ℝ := min 1 (ε / 3)
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by norm_num) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  have hd1 : dist w z < 1 := lt_of_lt_of_le hw (min_le_left _ _)
  have hdε : dist w z < ε / 3 := lt_of_lt_of_le hw (min_le_right _ _)
  rcases placement_component_distance w z with ⟨hw3, hw5, hwφ⟩
  have hn3 : ‖w.1.1‖ ≤ ‖z.1.1‖ + dist w z := by
    have hn := norm_add_le (w.1.1 - z.1.1) z.1.1
    rw [sub_add_cancel] at hn
    linarith
  have hn5 : ‖w.1.2‖ ≤ ‖z.1.2‖ + dist w z := by
    have hn := norm_add_le (w.1.2 - z.1.2) z.1.2
    rw [sub_add_cancel] at hn
    linarith
  have hw3R : ‖w.1.1‖ + 289 / 500 ≤ R := by
    dsimp [R]
    have hn := norm_nonneg z.1.2
    linarith
  have hw5R : ‖w.1.2‖ + pentagonRadius ≤ R := by
    dsimp [R, pentagonRadius]
    have hn := norm_nonneg z.1.1
    linarith
  have he3 : ‖w.1.1 - z.1.1‖ ≤ ε := by linarith
  have he5 : ‖w.1.2 - z.1.2‖ + pentagonRadius * |w.2 - z.2| ≤ ε := by
    have hm := mul_le_mul_of_nonneg_left hwφ
      (show 0 ≤ pentagonRadius by norm_num [pentagonRadius])
    norm_num [pentagonRadius] at hm ⊢
    linarith
  have hz3w : ‖z.1.1 - w.1.1‖ ≤ ε := by
    simpa only [norm_sub_rev] using he3
  have hz5w : ‖z.1.2 - w.1.2‖ + pentagonRadius * |z.2 - w.2| ≤ ε := by
    simpa only [norm_sub_rev, abs_sub_comm z.2 w.2] using he5
  refine ⟨hull_interior_of_disk hd _ _ _,
    hull_radius_of_translation_bounds b w.1 w.2 R hD hw3R hw5R, ?_, ?_⟩
  · exact convexHull_parallel_transport
      (constituents_placement_transport b w z ε (le_of_lt hε) he3 he5)
  · exact convexHull_parallel_transport
      (constituents_placement_transport b z w ε (le_of_lt hε) hz3w hz5w)

theorem placement_continuity_of_body_inputs (c : CompactPlanarImports)
    (hrot : RotationContinuityDuty) (i : ClassicalAreaImports)
    (b : QHullInputs) (hd : DiskInteriorDuty) : PlacementContinuityDuty :=
  placement_continuity_of_local_transport c hrot i
    (local_hull_transport_of_body_inputs b hd)

theorem Q_angular_quadratic_estimate (c : CompactPlanarImports)
    (hrot : RotationContinuityDuty) (i : ClassicalAreaImports)
    (b : QHullInputs) (hd : DiskInteriorDuty) {t : Translations} (ht : t ∈ Q)
    (φ ψ : ℝ) :
    |placementArea t φ - placementArea t ψ| ≤
      angularLinearCoefficient * |φ - ψ| + angularQuadraticCoefficient * (φ - ψ) ^ 2 := by
  have hε : 0 ≤ pentagonRadius * |φ - ψ| := by
    unfold pentagonRadius
    positivity
  have hR : 0 ≤ hullRadius := by norm_num [hullRadius]
  have hb := area_hausdorff_radius_bound i
    (hull_compact_of_imports c hrot t.1 t.2 φ)
    (hull_compact_of_imports c hrot t.1 t.2 ψ)
    (K_convex _ _ _) (K_convex _ _ _)
    (hull_interior_of_disk hd _ _ _) (hull_interior_of_disk hd _ _ _)
    hε hR (Q_hull_radius b ht φ) (Q_hull_radius b ht ψ)
    (hull_rotation_transport b t φ ψ)
  calc
    |placementArea t φ - placementArea t ψ| ≤
        2 * Real.pi * hullRadius * (pentagonRadius * |φ - ψ|) +
        Real.pi * (pentagonRadius * |φ - ψ|) ^ 2 := hb
    _ = angularLinearCoefficient * |φ - ψ| +
        angularQuadraticCoefficient * (φ - ψ) ^ 2 := by
      simp only [angularLinearCoefficient, angularQuadraticCoefficient, mul_pow, sq_abs]
      ring

/-- Explicit finite equal-step telescoping. No limiting area estimate is
assumed: a quadratic estimate on every pair supplies the finite bound. -/
theorem equal_step_quadratic_estimate (f : ℝ → ℝ) (A B : ℝ)
    (hpair : ∀ x y : ℝ, |f x - f y| ≤ A * |x - y| + B * (x - y) ^ 2)
    (φ ψ : ℝ) (m : ℕ) (hm : 0 < m) :
    |f φ - f ψ| ≤ A * |ψ - φ| + B * (ψ - φ) ^ 2 / (m : ℝ) := by
  let s : ℝ := (ψ - φ) / (m : ℝ)
  have hchain : ∀ k : ℕ,
      |f φ - f (φ + (k : ℝ) * s)| ≤ (k : ℝ) * (A * |s| + B * s ^ 2) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hstep := hpair (φ + (k : ℝ) * s) (φ + ((k + 1 : ℕ) : ℝ) * s)
      have hdiff : (φ + (k : ℝ) * s) - (φ + ((k + 1 : ℕ) : ℝ) * s) = -s := by
        push_cast
        ring
      rw [hdiff, abs_neg, neg_sq] at hstep
      calc
        |f φ - f (φ + ((k + 1 : ℕ) : ℝ) * s)| ≤
            |f φ - f (φ + (k : ℝ) * s)| +
            |f (φ + (k : ℝ) * s) - f (φ + ((k + 1 : ℕ) : ℝ) * s)| :=
          abs_sub_le _ _ _
        _ ≤ (k : ℝ) * (A * |s| + B * s ^ 2) + (A * |s| + B * s ^ 2) :=
          add_le_add ih hstep
        _ = ((k + 1 : ℕ) : ℝ) * (A * |s| + B * s ^ 2) := by
          push_cast
          ring
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hendpoint : φ + (m : ℝ) * s = ψ := by
    dsimp [s]
    field_simp [ne_of_gt hmR] <;> ring
  have hsum : (m : ℝ) * (A * |s| + B * s ^ 2) =
      A * |ψ - φ| + B * (ψ - φ) ^ 2 / (m : ℝ) := by
    dsimp [s]
    rw [abs_div, abs_of_pos hmR]
    field_simp [ne_of_gt hmR] <;> ring
  have h := hchain m
  rw [hendpoint, hsum] at h
  exact h

/-- Archimedean removal of the 1/m remainder. This is the exact equal-step
limit argument, with arbitrary real remainder coefficient. -/
theorem quadratic_remainder_vanishes (a ℓ b : ℝ)
    (h : ∀ m : ℕ, 0 < m → a ≤ ℓ + b / (m : ℝ)) : a ≤ ℓ := by
  by_contra hn
  have hε : 0 < a - ℓ := sub_pos.mpr (lt_of_not_ge hn)
  rcases exists_nat_gt (max 0 (b / (a - ℓ))) with ⟨m, hm⟩
  have hmR : 0 < (m : ℝ) := lt_of_le_of_lt (le_max_left _ _) hm
  have hmN : 0 < m := by exact_mod_cast hmR
  have hb : b / (a - ℓ) < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
  have hbprod : b < (m : ℝ) * (a - ℓ) := (div_lt_iff₀ hε).mp hb
  have hbdiv : b / (m : ℝ) < a - ℓ := (div_lt_iff₀ hmR).mpr (by nlinarith)
  have ha := h m hmN
  linarith

theorem quadratic_pair_estimate_implies_linear (f : ℝ → ℝ) (A B : ℝ)
    (hpair : ∀ x y : ℝ, |f x - f y| ≤ A * |x - y| + B * (x - y) ^ 2) :
    ∀ φ ψ : ℝ, |f φ - f ψ| ≤ A * |φ - ψ| := by
  intro φ ψ
  have h := quadratic_remainder_vanishes (|f φ - f ψ|)
    (A * |ψ - φ|) (B * (ψ - φ) ^ 2)
    (fun m hm => equal_step_quadratic_estimate f A B hpair φ ψ m hm)
  simpa only [abs_sub_comm ψ φ] using h

def PiUpperDuty : Prop := Real.pi < (22 / 7 : ℝ)

theorem piUpper_verified : PiUpperDuty := by
  unfold PiUpperDuty
  linarith [Real.pi_lt_d6]

theorem angularLinearCoefficient_lt_C (hpi : PiUpperDuty) :
    angularLinearCoefficient < C := by
  unfold PiUpperDuty at hpi
  unfold angularLinearCoefficient hullRadius pentagonRadius C
  nlinarith

theorem Q_angular_linear_estimate (c : CompactPlanarImports)
    (hrot : RotationContinuityDuty) (i : ClassicalAreaImports)
    (b : QHullInputs) (hd : DiskInteriorDuty) (hpi : PiUpperDuty) : QAngularAreaBound := by
  intro t ht φ ψ
  have hlin := quadratic_pair_estimate_implies_linear
    (placementArea t) angularLinearCoefficient angularQuadraticCoefficient
    (Q_angular_quadratic_estimate c hrot i b hd ht) φ ψ
  exact le_trans hlin (mul_le_mul_of_nonneg_right
    (le_of_lt (angularLinearCoefficient_lt_C hpi)) (abs_nonneg _))

/-- Common Lipschitz constants pass to real infima even when not attained.
The nonempty and lower-bound premises are exposed for each value set. -/
theorem uniform_sInf_lipschitz {α : Type*} (f : α → ℝ → ℝ)
    (S : Set α) (hS : S.Nonempty) (L : ℝ)
    (hbelow : ∀ φ, BddBelow ((fun t => f t φ) '' S))
    (hbound : ∀ t ∈ S, ∀ φ ψ, |f t φ - f t ψ| ≤ L * |φ - ψ|) :
    ∀ φ ψ, |sInf ((fun t => f t φ) '' S) - sInf ((fun t => f t ψ) '' S)| ≤
      L * |φ - ψ| := by
  intro φ ψ
  have hφne : ((fun t => f t φ) '' S).Nonempty := hS.image _
  have hψne : ((fun t => f t ψ) '' S).Nonempty := hS.image _
  have h1 : sInf ((fun t => f t φ) '' S) - L * |φ - ψ| ≤
      sInf ((fun t => f t ψ) '' S) := by
    apply le_csInf hψne
    rintro v ⟨t, ht, rfl⟩
    have hle := csInf_le (hbelow φ) (show f t φ ∈ (fun t => f t φ) '' S from ⟨t, ht, rfl⟩)
    have hb := (abs_le.mp (hbound t ht φ ψ)).2
    linarith
  have h2 : sInf ((fun t => f t ψ) '' S) - L * |φ - ψ| ≤
      sInf ((fun t => f t φ) '' S) := by
    apply le_csInf hφne
    rintro v ⟨t, ht, rfl⟩
    have hle := csInf_le (hbelow ψ) (show f t ψ ∈ (fun t => f t ψ) '' S from ⟨t, ht, rfl⟩)
    have hb := (abs_le.mp (hbound t ht φ ψ)).1
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem uniform_minimum_lipschitz {α : Type*} (f : α → ℝ → ℝ)
    (S : Set α) (g : ℝ → ℝ) (L : ℝ)
    (hmin : ∀ φ, ∃ t ∈ S, f t φ = g φ ∧ ∀ u ∈ S, g φ ≤ f u φ)
    (hbound : ∀ t ∈ S, ∀ φ ψ, |f t φ - f t ψ| ≤ L * |φ - ψ|) :
    ∀ φ ψ, |g φ - g ψ| ≤ L * |φ - ψ| := by
  intro φ ψ
  rcases hmin φ with ⟨tφ, htφ, hvφ, hmφ⟩
  rcases hmin ψ with ⟨tψ, htψ, hvψ, hmψ⟩
  have hp := hmφ tψ htψ
  have hq := hmψ tφ htφ
  have hbψ := (abs_le.mp (hbound tψ htψ φ ψ)).2
  have hbφ := (abs_le.mp (hbound tφ htφ φ ψ)).1
  rw [hvψ] at hbψ
  rw [hvφ] at hbφ
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem clipping_one_lipschitz (L x y : ℝ) :
    |min L x - min L y| ≤ |x - y| := by
  rcases le_total x L with hx | hx <;> rcases le_total y L with hy | hy
  · rw [min_eq_right hx, min_eq_right hy]
  · rw [min_eq_right hx, min_eq_left hy,
      abs_of_nonpos (sub_nonpos.mpr hx),
      abs_of_nonpos (sub_nonpos.mpr (le_trans hx hy))]
    linarith
  · rw [min_eq_left hx, min_eq_right hy,
      abs_of_nonneg (sub_nonneg.mpr hy),
      abs_of_nonneg (sub_nonneg.mpr (le_trans hy hx))]
    linarith
  · rw [min_eq_left hx, min_eq_left hy]
    simp

theorem F_angular_lipschitz (hQ : QAngularAreaBound) :
    ∀ φ ψ, |F φ - F ψ| ≤ C * |φ - ψ| :=
  uniform_sInf_lipschitz placementArea Q ⟨(0, 0), zero_in_Q⟩ C
    Q_image_bddBelow hQ

theorem F_angular_lipschitz_by_minimum
    (hcont : PlacementContinuityDuty) (hQ : QAngularAreaBound) :
    ∀ φ ψ, |F φ - F ψ| ≤ C * |φ - ψ| := by
  apply uniform_minimum_lipschitz placementArea Q F C
  · intro φ
    rcases F_attained_on_Q hcont φ with ⟨t, ht, hv, hmin⟩
    refine ⟨t, ht, hv, ?_⟩
    intro u hu
    rw [← hv]
    exact hmin u hu
  · exact hQ

theorem clipped_modulus_of_Q_bound (hext : ExteriorQCutoffDuty)
    (hQ : QAngularAreaBound) : ClippedAngularModulus := by
  intro φ ψ
  rw [clipped_infimum_identity hext φ, clipped_infimum_identity hext ψ]
  exact le_trans (clipping_one_lipschitz L3 (F φ) (F ψ))
    (F_angular_lipschitz hQ φ ψ)

theorem clipped_modulus_of_geometric_imports (c : CompactPlanarImports)
    (hrot : RotationContinuityDuty) (i : ClassicalAreaImports)
    (b : QHullInputs) (hd : DiskInteriorDuty) (hpi : PiUpperDuty)
    (hext : ExteriorQCutoffDuty) : ClippedAngularModulus :=
  clipped_modulus_of_Q_bound hext (Q_angular_linear_estimate c hrot i b hd hpi)

end Partials.Covering
end
