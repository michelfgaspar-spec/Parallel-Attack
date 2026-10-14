import Partials.Covering.Geometry
import Mathlib.Algebra.Order.Floor.Ring

open scoped ENNReal

noncomputable section

namespace Partials.Covering

/-- OPEN finite center-permutation consequences. Discharge by cyclic j↦j+1
and reflection j↦-j modulo n in the exact center definition; no infimum or
placement theorem is supplied by this duty. -/
structure CenteredBodySymmetryDuty : Prop where
  triangle_rotation : rotate (2 * Real.pi / 3) '' B3 = B3
  pentagon_rotation : rotate (2 * Real.pi / 5) '' B5 = B5
  triangle_reflection : reflect '' B3 = B3
  pentagon_reflection : reflect '' B5 = B5

/-- OPEN finite center relabeling, a finer bridge than body invariance.
The concrete witness is cyclic addition for rotation and negation for
reflection, both modulo n, using exact trigonometric periodicity. -/
structure CenterRelabelDuty (n : ℕ) : Prop where
  rotation : ∃ e : Fin n ≃ Fin n, ∀ j,
    rotate (2 * Real.pi / (n : ℝ)) (center n j) = center n (e j)
  reflection : ∃ e : Fin n ≃ Fin n, ∀ j, reflect (center n j) = center n (e j)

theorem reuleaux_rotation (he : EuclideanCoordinateDuty) (n : ℕ)
    (hp : CenterRelabelDuty n) :
    rotate (2 * Real.pi / (n : ℝ)) '' reuleaux n = reuleaux n := by
  obtain ⟨e, hcent⟩ := hp.rotation
  let θ : ℝ := 2 * Real.pi / (n : ℝ)
  have hm : ∀ x : Plane, rotate θ x ∈ reuleaux n ↔ x ∈ reuleaux n := by
    intro x
    constructor
    · intro hx j
      have hj := hx (e j)
      change ‖rotate θ x - center n (e j)‖ ≤ 1 at hj
      show ‖x - center n j‖ ≤ 1
      rw [← hcent j] at hj
      change ‖rotate θ x - rotate θ (center n j)‖ ≤ 1 at hj
      rwa [← rotate_sub, rotate_norm he] at hj
    · intro hx j
      have hc : center n j = rotate θ (center n (e.symm j)) := by
        simpa [θ] using (hcent (e.symm j)).symm
      show ‖rotate θ x - center n j‖ ≤ 1
      rw [hc, ← rotate_sub, rotate_norm he]
      exact hx (e.symm j)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hm y).2 hy
  · intro hx
    obtain ⟨y, rfl⟩ := rotate_surjective θ x
    exact ⟨y, (hm y).1 hx, rfl⟩

theorem reuleaux_reflection (he : EuclideanCoordinateDuty) (n : ℕ)
    (hp : CenterRelabelDuty n) : reflect '' reuleaux n = reuleaux n := by
  obtain ⟨e, hcent⟩ := hp.reflection
  have hm : ∀ x : Plane, reflect x ∈ reuleaux n ↔ x ∈ reuleaux n := by
    intro x
    constructor
    · intro hx j
      have hj := hx (e j)
      change ‖reflect x - center n (e j)‖ ≤ 1 at hj
      show ‖x - center n j‖ ≤ 1
      simpa [← hcent j, ← reflect_sub, reflect_norm he] using hj
    · intro hx j
      have hc : center n j = reflect (center n (e.symm j)) := by
        simpa using (hcent (e.symm j)).symm
      show ‖reflect x - center n j‖ ≤ 1
      rw [hc, ← reflect_sub, reflect_norm he]
      exact hx (e.symm j)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (hm y).2 hy
  · intro hx
    refine ⟨reflect x, ?_, reflect_involutive x⟩
    apply (hm (reflect x)).1
    simpa only [reflect_reflect] using hx

theorem centeredBodySymmetry_of_relabel (he : EuclideanCoordinateDuty)
    (h3 : CenterRelabelDuty 3) (h5 : CenterRelabelDuty 5) :
    CenteredBodySymmetryDuty := by
  exact ⟨reuleaux_rotation he 3 h3, reuleaux_rotation he 5 h5,
    reuleaux_reflection he 3 h3, reuleaux_reflection he 5 h5⟩

/-- OPEN affine image/convex-hull transport theorem for the concrete maps. -/
structure RigidHullTransportDuty : Prop where
  rotation : ∀ θ S, rotate θ '' convexHull ℝ S = convexHull ℝ (rotate θ '' S)
  reflection : ∀ S, reflect '' convexHull ℝ S = convexHull ℝ (reflect '' S)

/-- OPEN Lebesgue measure invariance. This is a generic all-set identity,
independent of the chosen test family and its desired bounds. -/
structure RigidAreaDuty : Prop where
  rotation : ∀ θ S, setArea (rotate θ '' S) = setArea S
  reflection : ∀ S, setArea (reflect '' S) = setArea S

theorem rotation_image_add (θ φ : ℝ) (S : Set Plane) :
    rotate (θ + φ) '' S = rotate θ '' (rotate φ '' S) := by
  rw [Set.image_image]
  congr 1
  funext x
  exact (rotate_compose θ φ x).symm

theorem reflection_rotation_image (φ : ℝ) (S : Set Plane) :
    reflect '' (rotate φ '' S) = rotate (-φ) '' (reflect '' S) := by
  rw [Set.image_image, Set.image_image]
  congr 1
  funext x
  exact reflect_rotate φ x

theorem reflect_disk (he : EuclideanCoordinateDuty) (r : ℝ) :
    reflect '' disk 0 r = disk 0 r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [Partials.Interface.ClosedDisk, reflect_norm he] using hy
  · intro hx
    refine ⟨reflect x, ?_, reflect_involutive x⟩
    simpa [Partials.Interface.ClosedDisk, reflect_norm he] using hx

theorem rotation_translate_image (θ : ℝ) (S : Set Plane) (t : Plane) :
    rotate θ '' translate S t = translate (rotate θ '' S) (rotate θ t) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y - t, hy, rotate_sub θ y t⟩
  · rintro ⟨z, hz, heq⟩
    refine ⟨z + t, ?_, ?_⟩
    · simpa [Partials.Interface.Translate] using hz
    · rw [rotate_add, heq]
      simp

theorem reflection_translate_image (S : Set Plane) (t : Plane) :
    reflect '' translate S t = translate (reflect '' S) (reflect t) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y - t, hy, reflect_sub y t⟩
  · rintro ⟨z, hz, heq⟩
    refine ⟨reflect x, ?_, reflect_involutive x⟩
    have hdiff : reflect x - t = z := by
      have hh := congrArg reflect heq
      rw [reflect_sub] at hh
      simpa only [reflect_reflect] using hh.symm
    simpa [Partials.Interface.Translate, hdiff] using hz

theorem H_pentagon_period (hb : CenteredBodySymmetryDuty)
    (t3 t5 : Plane) (φ : ℝ) :
    H t3 t5 (φ + 2 * Real.pi / 5) = H t3 t5 φ := by
  unfold H K
  rw [rotation_image_add, hb.pentagon_rotation]

theorem K_common_rotation (he : EuclideanCoordinateDuty)
    (hb : CenteredBodySymmetryDuty) (hh : RigidHullTransportDuty)
    (t3 t5 : Plane) (φ : ℝ) :
    rotate (2 * Real.pi / 3) '' K t3 t5 φ =
      K (rotate (2 * Real.pi / 3) t3) (rotate (2 * Real.pi / 3) t5)
        (φ + 2 * Real.pi / 3) := by
  unfold K
  rw [hh.rotation, Set.image_union, Set.image_union,
    rotation_translate_image, rotation_translate_image, hb.triangle_rotation]
  rw [show rotate (2 * Real.pi / 3) '' D = D by exact rotate_disk he _ _]
  rw [← rotation_image_add]
  rw [add_comm (2 * Real.pi / 3) φ]

theorem H_common_rotation (he : EuclideanCoordinateDuty)
    (hb : CenteredBodySymmetryDuty) (hh : RigidHullTransportDuty)
    (ha : RigidAreaDuty) (t3 t5 : Plane) (φ : ℝ) :
    H (rotate (2 * Real.pi / 3) t3) (rotate (2 * Real.pi / 3) t5)
      (φ + 2 * Real.pi / 3) = H t3 t5 φ := by
  unfold H
  rw [← K_common_rotation he hb hh]
  exact ha.rotation _ _

theorem K_reflection (he : EuclideanCoordinateDuty)
    (hb : CenteredBodySymmetryDuty) (hh : RigidHullTransportDuty)
    (t3 t5 : Plane) (φ : ℝ) :
    reflect '' K t3 t5 φ = K (reflect t3) (reflect t5) (-φ) := by
  unfold K
  rw [hh.reflection, Set.image_union, Set.image_union,
    reflection_translate_image, reflection_translate_image,
    reflection_rotation_image, hb.triangle_reflection, hb.pentagon_reflection]
  rw [show reflect '' D = D by exact reflect_disk he _]

theorem H_reflection (he : EuclideanCoordinateDuty)
    (hb : CenteredBodySymmetryDuty) (hh : RigidHullTransportDuty)
    (ha : RigidAreaDuty) (t3 t5 : Plane) (φ : ℝ) :
    H (reflect t3) (reflect t5) (-φ) = H t3 t5 φ := by
  unfold H
  rw [← K_reflection he hb hh]
  exact ha.reflection _

theorem G_pentagon_period (hb : CenteredBodySymmetryDuty) (φ : ℝ) :
    G (φ + 2 * Real.pi / 5) = G φ := by
  unfold G
  congr 1
  ext a
  constructor <;> rintro ⟨t, ht⟩ <;> refine ⟨t, ?_⟩
  · simpa [placementArea, H_pentagon_period hb] using ht
  · simpa [placementArea, H_pentagon_period hb] using ht

theorem G_triangle_period (he : EuclideanCoordinateDuty)
    (hb : CenteredBodySymmetryDuty) (hh : RigidHullTransportDuty)
    (ha : RigidAreaDuty) (φ : ℝ) : G (φ + 2 * Real.pi / 3) = G φ := by
  unfold G
  congr 1
  ext a
  constructor
  · rintro ⟨t, ht⟩
    obtain ⟨t3, h3⟩ := rotate_surjective (2 * Real.pi / 3) t.1
    obtain ⟨t5, h5⟩ := rotate_surjective (2 * Real.pi / 3) t.2
    refine ⟨(t3, t5), ?_⟩
    simpa [placementArea, ← h3, ← h5, H_common_rotation he hb hh ha] using ht
  · rintro ⟨t, ht⟩
    refine ⟨(rotate (2 * Real.pi / 3) t.1, rotate (2 * Real.pi / 3) t.2), ?_⟩
    simpa [placementArea, H_common_rotation he hb hh ha] using ht

theorem G_even (he : EuclideanCoordinateDuty)
    (hb : CenteredBodySymmetryDuty) (hh : RigidHullTransportDuty)
    (ha : RigidAreaDuty) (φ : ℝ) : G (-φ) = G φ := by
  unfold G
  congr 1
  ext a
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨(reflect t.1, reflect t.2), ?_⟩
    have heq := H_reflection he hb hh ha (reflect t.1) (reflect t.2) φ
    simp only [reflect_reflect] at heq
    simpa only [placementArea] using heq.symm.trans ht
  · rintro ⟨t, ht⟩
    refine ⟨(reflect t.1, reflect t.2), ?_⟩
    simpa [placementArea] using (H_reflection he hb hh ha t.1 t.2 φ).trans ht

theorem period_sub {f : ℝ → ℝ} {p : ℝ}
    (hp : ∀ x, f (x + p) = f x) (x : ℝ) : f (x - p) = f x := by
  have hh := hp (x - p)
  simpa using hh.symm

theorem combined_period {f : ℝ → ℝ} {a b : ℝ}
    (ha : ∀ x, f (x + a) = f x) (hb : ∀ x, f (x + b) = f x) (x : ℝ) :
    f (x + (2 * a - 3 * b)) = f x := by
  calc
    f (x + (2 * a - 3 * b)) = f (((x - b) - b) - b + a + a) := by congr 1; ring
    _ = f x := by rw [ha, ha, period_sub hb, period_sub hb, period_sub hb]

theorem G_small_period (he : EuclideanCoordinateDuty)
    (hb : CenteredBodySymmetryDuty) (hh : RigidHullTransportDuty)
    (ha : RigidAreaDuty) (φ : ℝ) : G (φ + 2 * Real.pi / 15) = G φ := by
  have hp := combined_period (G_triangle_period he hb hh ha) (G_pentagon_period hb) φ
  convert hp using 1 <;> congr 1 <;> ring

theorem period_nat_shift {f : ℝ → ℝ} {p : ℝ}
    (hp : ∀ x, f (x + p) = f x) (n : ℕ) (x : ℝ) : f (x + (n : ℝ) * p) = f x := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      f (x + ((n + 1 : ℕ) : ℝ) * p) = f ((x + (n : ℝ) * p) + p) := by
        congr 1
        push_cast
        ring
      _ = f (x + (n : ℝ) * p) := hp _
      _ = f x := ih

theorem period_nat_sub {f : ℝ → ℝ} {p : ℝ}
    (hp : ∀ x, f (x + p) = f x) (n : ℕ) (x : ℝ) : f (x - (n : ℝ) * p) = f x := by
  have hs := period_nat_shift hp n (x - (n : ℝ) * p)
  simpa using hs.symm

/-- OPEN Archimedean remainder duty, stated independently of every function.
It can be discharged by floor(x/p), split into positive/negative natural
parts. The closed upper endpoint is harmless and makes no attainment claim. -/
def RealPeriodRepresentativeDuty : Prop :=
  ∀ p : ℝ, 0 < p → ∀ x : ℝ, ∃ y : ℝ, ∃ n m : ℕ,
    0 ≤ y ∧ y ≤ p ∧ x = y + (n : ℝ) * p - (m : ℝ) * p

/-- P1 constructs the real remainder and records positive/negative integer
parts as naturals, without supplying any function or infimum equality. -/
theorem realPeriodRepresentative_verified : RealPeriodRepresentativeDuty := by
  intro p hp x
  let z : ℤ := ⌊x / p⌋
  let y : ℝ := x - (z : ℝ) * p
  have hy0 : 0 ≤ y := Int.sub_floor_div_mul_nonneg x hp
  have hyp : y ≤ p := (Int.sub_floor_div_mul_lt x hp).le
  by_cases hz : 0 ≤ z
  · refine ⟨y, z.toNat, 0, hy0, hyp, ?_⟩
    have hc : (z.toNat : ℝ) = (z : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hz
    rw [hc]
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    dsimp [y]
    ring
  · refine ⟨y, 0, (-z).toNat, hy0, hyp, ?_⟩
    have hc : ((-z).toNat : ℝ) = -(z : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg (show 0 ≤ -z by omega)
    rw [hc]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    dsimp [y]
    ring

theorem even_periodic_representative (hr : RealPeriodRepresentativeDuty)
    {f : ℝ → ℝ} {p : ℝ} (hp0 : 0 < p)
    (hp : ∀ x, f (x + p) = f x) (he : ∀ x, f (-x) = f x) (x : ℝ) :
    ∃ z ∈ Set.Icc (0 : ℝ) (p / 2), f z = f x := by
  obtain ⟨y, n, m, hy0, hyp, hx⟩ := hr p hp0 x
  have hval : f x = f y := by
    rw [hx, period_nat_sub hp, period_nat_shift hp]
  by_cases hyhalf : y ≤ p / 2
  · exact ⟨y, ⟨hy0, hyhalf⟩, hval.symm⟩
  · refine ⟨p - y, ⟨by linarith, by linarith⟩, ?_⟩
    calc
      f (p - y) = f (-y + p) := by congr 1; ring
      _ = f (-y) := hp _
      _ = f y := he _
      _ = f x := hval.symm

theorem G_fundamental_range (he : EuclideanCoordinateDuty)
    (hb : CenteredBodySymmetryDuty) (hh : RigidHullTransportDuty)
    (ha : RigidAreaDuty) (hr : RealPeriodRepresentativeDuty) :
    Set.range G = G '' fundamentalInterval := by
  ext v
  constructor
  · rintro ⟨φ, rfl⟩
    obtain ⟨ψ, hψ, hv⟩ := even_periodic_representative hr
      (by positivity : (0 : ℝ) < 2 * Real.pi / 15)
      (G_small_period he hb hh ha) (G_even he hb hh ha) φ
    refine ⟨ψ, ?_, hv⟩
    constructor
    · exact hψ.1
    · have hend : (2 * Real.pi / 15) / 2 = fundamentalEnd := by
        unfold fundamentalEnd
        ring
      simpa [hend] using hψ.2
  · rintro ⟨φ, hφ, hv⟩
    exact ⟨φ, hv⟩

theorem M_fundamental_infimum (he : EuclideanCoordinateDuty)
    (hb : CenteredBodySymmetryDuty) (hh : RigidHullTransportDuty)
    (ha : RigidAreaDuty) (hr : RealPeriodRepresentativeDuty) :
    M = sInf (G '' fundamentalInterval) := by
  unfold M
  rw [G_fundamental_range he hb hh ha hr]

/-- Matches the independently authored Infima.FundamentalRepresentativeDuty
without importing Infima or creating an import cycle. -/
theorem G_fundamental_representative (he : EuclideanCoordinateDuty)
    (hb : CenteredBodySymmetryDuty) (hh : RigidHullTransportDuty)
    (ha : RigidAreaDuty) (hr : RealPeriodRepresentativeDuty) (φ : ℝ) :
    ∃ ψ ∈ fundamentalInterval, G ψ = G φ := by
  have hm : G φ ∈ Set.range G := Set.mem_range_self φ
  rw [G_fundamental_range he hb hh ha hr] at hm
  exact hm

theorem G_bounded_below (φ : ℝ) :
    BddBelow (Set.range (fun t : Translations => placementArea t φ)) := by
  refine ⟨0, ?_⟩
  rintro v ⟨t, rfl⟩
  exact H_nonnegative _ _ _

theorem symmetry_G_nonnegative (φ : ℝ) : 0 ≤ G φ := by
  apply le_csInf
  · exact ⟨placementArea (0, 0) φ, ⟨(0, 0), rfl⟩⟩
  · rintro v ⟨t, rfl⟩
    exact H_nonnegative _ _ _

theorem M_le_placement (t3 t5 : Plane) (φ : ℝ) : M ≤ H t3 t5 φ := by
  have hG : G φ ≤ H t3 t5 φ :=
    csInf_le (G_bounded_below φ) ⟨(t3, t5), rfl⟩
  have hM : M ≤ G φ := csInf_le
    (show BddBelow (Set.range G) from ⟨0, by rintro v ⟨ψ, rfl⟩; exact symmetry_G_nonnegative ψ⟩)
    ⟨φ, rfl⟩
  exact le_trans hM hG

/-- OPEN finite-volume fact for every rigid image of a compact universal
cover. Compactness plus continuity of e.apply discharges it; it contains no
placement normalization or desired lower bound. -/
def UniversalImageFiniteDuty : Prop :=
  ∀ U : Set Plane, UniversalCover U → ∀ e : RigidMotion,
    MeasureTheory.volume (e.apply '' U) ≠ ∞

theorem D_diameter_at_most_one : DiameterAtMostOne D := by
  intro x hx y hy
  have hx' : ‖x‖ ≤ (1 / 2 : ℝ) := by
    simpa [D, Partials.Interface.ClosedDisk] using hx
  have hy' : ‖y‖ ≤ (1 / 2 : ℝ) := by
    simpa [D, Partials.Interface.ClosedDisk] using hy
  rw [dist_eq_norm]
  exact le_trans (norm_sub_le x y) (by linarith)

/-- OPEN constant-width/diameter bridge for the exact disk intersections.
This is required when deriving Model.UniversalNormalizationDuty from the
universal-cover quantifier; sandwich alone does not establish diameter one. -/
def ReuleauxDiameterDuty : Prop := DiameterAtMostOne B3 ∧ DiameterAtMostOne B5

/-- The Model normalization remains an explicit geometric duty. It must use
diameter-one D,B3,B5, three individual placements, and one common inverse
motion. Reflections are removed using centered body reflection invariance. -/
theorem universal_cover_area_lower (hn : UniversalNormalizationDuty)
    (hf : UniversalImageFiniteDuty) (U : Set Plane) (hU : UniversalCover U) :
    M ≤ setArea U := by
  obtain ⟨e, t3, t5, φ, hsub, harea⟩ := hn U hU
  have hm := setArea_mono hsub (hf U hU e)
  rw [harea] at hm
  exact le_trans (M_le_placement t3 t5 φ) hm

/-- Nonemptiness of the actual universal-cover class is explicit, avoiding
the exceptional real sInf of an empty set. No headline bound is assumed. -/
theorem M_le_aLeb (hn : UniversalNormalizationDuty)
    (hf : UniversalImageFiniteDuty)
    (hne : ∃ U : Set Plane, UniversalCover U) : M ≤ aLeb := by
  apply le_csInf
  · obtain ⟨U, hU⟩ := hne
    exact ⟨setArea U, ⟨U, hU, rfl⟩⟩
  · rintro v ⟨U, hU, rfl⟩
    exact universal_cover_area_lower hn hf U hU

end Partials.Covering

end
