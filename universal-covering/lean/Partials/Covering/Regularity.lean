import Partials.Covering.Model

open scoped ENNReal

noncomputable section

/-!
R4 blind source. All declarations in this file are uncompiled proposals.
No structure below has an asserted inhabitant. An argument of an `Imports` or
`Duty` type is an explicit open geometric/library obligation, not an axiom.
The generic imported statements are recorded, with their adequacy obligations,
in notes/INFIMUM_PROOF.md.
-/
namespace Partials.Covering

def PlacementContinuityDuty : Prop :=
  Continuous (fun z : Translations × ℝ => placementArea z.1 z.2)

def RotationContinuityDuty : Prop :=
  Continuous (fun z : ℝ × Plane => rotate z.1 z.2)

/-- P1 checks continuity of the literal sine/cosine rotation, jointly in
angle and point. This is separate from hull-area continuity. -/
theorem rotationContinuity_verified : RotationContinuityDuty := by
  unfold RotationContinuityDuty rotate point
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> fun_prop

def CoercivityDuty : Prop :=
  ∀ t3 t5 φ, (1 / 2 : ℝ) * max ‖t3‖ ‖t5‖ ≤ H t3 t5 φ

def ZeroPlacementBoundDuty : Prop :=
  ∀ φ, H 0 0 φ ≤ Real.pi / 3

theorem disk_eq_closedBall (p : Plane) (r : ℝ) :
    disk p r = Metric.closedBall p r := by
  ext x
  simp only [Partials.Interface.ClosedDisk, Set.mem_setOf_eq,
    Metric.mem_closedBall, dist_eq_norm]

theorem disk_compact (p : Plane) (r : ℝ) : IsCompact (disk p r) := by
  rw [disk_eq_closedBall]
  exact isCompact_closedBall p r

theorem disk_convex (p : Plane) (r : ℝ) : Convex ℝ (disk p r) := by
  rw [disk_eq_closedBall]
  exact convex_closedBall p r

theorem reuleaux_closed (n : ℕ) : IsClosed (reuleaux n) := by
  have heq : reuleaux n = ⋂ j : Fin n, disk (center n j) 1 := by
    ext x
    simp [reuleaux]
  rw [heq]
  exact isClosed_iInter (fun j => (disk_compact (center n j) 1).isClosed)

theorem reuleaux_compact (n : ℕ) (hn : 0 < n) : IsCompact (reuleaux n) := by
  let j : Fin n := ⟨0, hn⟩
  apply (disk_compact (center n j) 1).of_isClosed_subset (reuleaux_closed n)
  intro x hx
  exact hx j

theorem D_compact : IsCompact D := disk_compact 0 (1 / 2)
theorem B3_compact : IsCompact B3 := reuleaux_compact 3 (by norm_num)
theorem B5_compact : IsCompact B5 := reuleaux_compact 5 (by norm_num)

theorem translate_eq_image (S : Set Plane) (t : Plane) :
    translate S t = (fun x => x + t) '' S := by
  ext x
  constructor
  · intro hx
    exact ⟨x - t, hx, sub_add_cancel x t⟩
  · rintro ⟨y, hy, rfl⟩
    simpa [Partials.Interface.Translate] using hy

theorem translate_compact {S : Set Plane} (hS : IsCompact S) (t : Plane) :
    IsCompact (translate S t) := by
  rw [translate_eq_image]
  exact hS.image (continuous_id.add continuous_const)

/-- Classical finite-dimensional compact-hull theorem and local finiteness of
Lebesgue volume. These are generic statements, not regularity of this K. The
former is the Carathéodory compactness consequence; the latter also supplies
the measurability required for honest use of `volume.toReal`. -/
structure CompactPlanarImports : Prop where
  compact_convexHull : ∀ S : Set Plane, IsCompact S → IsCompact (convexHull ℝ S)
  compact_volume : ∀ S : Set Plane, IsCompact S →
    MeasurableSet S ∧ MeasureTheory.volume S ≠ ∞

/-- The volume/measurability component is supplied from concrete planar
Lebesgue instances. Compactness of arbitrary convex hulls is still separate. -/
theorem compact_volume_verified (S : Set Plane) (hS : IsCompact S) :
    MeasurableSet S ∧ MeasureTheory.volume S ≠ ∞ :=
  ⟨hS.measurableSet, hS.measure_ne_top⟩

theorem hull_compact_of_imports (i : CompactPlanarImports)
    (hrot : RotationContinuityDuty) (t3 t5 : Plane) (φ : ℝ) :
    IsCompact (K t3 t5 φ) := by
  have hr : Continuous (rotate φ) := by
    change Continuous ((fun z : ℝ × Plane => rotate z.1 z.2) ∘
      (fun x : Plane => (φ, x)))
    exact Continuous.comp hrot
      (show Continuous (fun x : Plane => (φ, x)) from
        continuous_const.prodMk continuous_id)
  unfold K
  apply i.compact_convexHull
  exact (D_compact.union (translate_compact B3_compact t3)).union
    (translate_compact (B5_compact.image hr) t5)

theorem hullRegularity_of_imports (i : CompactPlanarImports)
    (hrot : RotationContinuityDuty) : HullRegularityDuty := by
  intro t3 t5 φ
  have hc := hull_compact_of_imports i hrot t3 t5 φ
  exact ⟨hc, i.compact_volume _ hc⟩

theorem K_convex (t3 t5 : Plane) (φ : ℝ) : Convex ℝ (K t3 t5 φ) :=
  convex_convexHull ℝ _

theorem D_subset_K (t3 t5 : Plane) (φ : ℝ) : D ⊆ K t3 t5 φ := by
  intro x hx
  exact subset_convexHull ℝ _ (Or.inl (Or.inl hx))

theorem regularity_setArea_mono {S U : Set Plane}
    (hU : MeasureTheory.volume U ≠ ∞) (hSU : S ⊆ U) :
    setArea S ≤ setArea U := by
  exact ENNReal.toReal_mono hU (MeasureTheory.measure_mono hSU)

/-- A lower-level disk-plus-point theorem, independent of the three-body
family. Paper source: Zeng v1, Lemma S5.6. One direct proof places the
perpendicular diameter of D and p in a triangle of area ‖p‖/2. -/
def DiskPointAreaDuty : Prop :=
  ∀ S : Set Plane, ∀ p : Plane,
    IsCompact S → Convex ℝ S → D ⊆ S → p ∈ S → ‖p‖ / 2 ≤ setArea S

structure CenterContainmentInputs : Prop where
  zero_B3 : (0 : Plane) ∈ B3
  zero_B5 : (0 : Plane) ∈ B5
  rotate_zero : ∀ φ, rotate φ (0 : Plane) = 0

theorem centers_in_K (b : CenterContainmentInputs) (t3 t5 : Plane) (φ : ℝ) :
    t3 ∈ K t3 t5 φ ∧ t5 ∈ K t3 t5 φ := by
  constructor
  · apply subset_convexHull ℝ _
    apply Or.inl
    apply Or.inr
    simpa [Partials.Interface.Translate] using b.zero_B3
  · apply subset_convexHull ℝ _
    apply Or.inr
    change t5 - t5 ∈ rotate φ '' B5
    simp only [sub_self]
    exact ⟨0, b.zero_B5, b.rotate_zero φ⟩

theorem coercivity_of_diskPoint (i : CompactPlanarImports)
    (hrot : RotationContinuityDuty) (b : CenterContainmentInputs)
    (hpoint : DiskPointAreaDuty) : CoercivityDuty := by
  intro t3 t5 φ
  have hc := hull_compact_of_imports i hrot t3 t5 φ
  have hp := centers_in_K b t3 t5 φ
  have h3 := hpoint _ t3 hc (K_convex t3 t5 φ) (D_subset_K t3 t5 φ) hp.1
  have h5 := hpoint _ t5 hc (K_convex t3 t5 φ) (D_subset_K t3 t5 φ) hp.2
  rcases le_total ‖t3‖ ‖t5‖ with h | h
  · rw [max_eq_right h]
    simpa [H, div_eq_mul_inv, mul_comm] using h5
  · rw [max_eq_left h]
    simpa [H, div_eq_mul_inv, mul_comm] using h3

/-- These are concrete sandwich/radius/isometry inputs. The desired upper
bound on H is absent: it will be proved by hull inclusion and area monotonicity. -/
structure ZeroHullInputs : Prop where
  B3_outer : B3 ⊆ disk 0 (rho 3)
  B5_outer : B5 ⊆ disk 0 (rho 5)
  rho5_le_rho3 : rho 5 ≤ rho 3
  half_le_rho3 : (1 / 2 : ℝ) ≤ rho 3
  rho3_nonnegative : 0 ≤ rho 3
  rho3_square : rho 3 ^ 2 = 1 / 3
  rotate_norm : ∀ φ x, ‖rotate φ x‖ = ‖x‖

def EuclideanDiskAreaDuty : Prop :=
  ∀ r : ℝ, 0 ≤ r → setArea (disk 0 r) = Real.pi * r ^ 2

theorem zero_hull_subset (b : ZeroHullInputs) (φ : ℝ) :
    K 0 0 φ ⊆ disk 0 (rho 3) := by
  apply convexHull_min _ (disk_convex 0 (rho 3))
  rintro x ((hx | hx) | hx)
  · exact le_trans hx b.half_le_rho3
  · have hxB : x ∈ B3 := by
      simpa [Partials.Interface.Translate] using hx
    exact b.B3_outer hxB
  · change x - 0 ∈ rotate φ '' B5 at hx
    simp only [sub_zero] at hx
    rcases hx with ⟨y, hy, rfl⟩
    have hb := b.B5_outer hy
    change ‖y - 0‖ ≤ rho 5 at hb
    change ‖rotate φ y - 0‖ ≤ rho 3
    simpa only [sub_zero, b.rotate_norm] using le_trans hb b.rho5_le_rho3

theorem zeroPlacementBound_of_inputs (i : CompactPlanarImports)
    (b : ZeroHullInputs) (harea : EuclideanDiskAreaDuty) :
    ZeroPlacementBoundDuty := by
  intro φ
  have hd := (i.compact_volume _ (disk_compact 0 (rho 3))).2
  have hm := regularity_setArea_mono hd (zero_hull_subset b φ)
  rw [harea _ b.rho3_nonnegative, b.rho3_square] at hm
  simpa [H, div_eq_mul_inv] using hm

/-- Set-theoretic parallel body, chosen to make both inclusions visible rather
than relying on any uninspected Hausdorff-distance convention. -/
def parallelBody (S : Set Plane) (ε : ℝ) : Set Plane :=
  {z | ∃ x ∈ S, ∃ u : Plane, ‖u‖ ≤ ε ∧ z = x + u}

def HausdorffWithin (S U : Set Plane) (ε : ℝ) : Prop :=
  S ⊆ parallelBody U ε ∧ U ⊆ parallelBody S ε

/-- Named classical formulas, retained as explicit inputs. `radius_perimeter`
is Cauchy's projection formula followed by width≤2R. It concerns arbitrary
compact convex sets with interior, not H or a target angular modulus. -/
structure ClassicalAreaImports where
  perimeter : Set Plane → ℝ
  steiner : ∀ S ε, IsCompact S → Convex ℝ S →
    (interior S).Nonempty → 0 ≤ ε →
    setArea (parallelBody S ε) =
      setArea S + perimeter S * ε + Real.pi * ε ^ 2
  parallel_finite : ∀ S ε, IsCompact S → 0 ≤ ε →
    MeasureTheory.volume (parallelBody S ε) ≠ ∞
  radius_perimeter : ∀ S R, IsCompact S → Convex ℝ S →
    (interior S).Nonempty → 0 ≤ R → S ⊆ disk 0 R →
    perimeter S ≤ 2 * Real.pi * R

theorem area_hausdorff_bound (i : ClassicalAreaImports)
    {S U : Set Plane} {ε : ℝ} (hS : IsCompact S) (hU : IsCompact U)
    (cS : Convex ℝ S) (cU : Convex ℝ U)
    (nS : (interior S).Nonempty) (nU : (interior U).Nonempty)
    (hε : 0 ≤ ε) (hnear : HausdorffWithin S U ε) :
    |setArea S - setArea U| ≤
      max (i.perimeter S) (i.perimeter U) * ε + Real.pi * ε ^ 2 := by
  have h1 := regularity_setArea_mono (i.parallel_finite U ε hU hε) hnear.1
  have h2 := regularity_setArea_mono (i.parallel_finite S ε hS hε) hnear.2
  rw [i.steiner U ε hU cU nU hε] at h1
  rw [i.steiner S ε hS cS nS hε] at h2
  have hpS := mul_le_mul_of_nonneg_right (le_max_left (i.perimeter S) (i.perimeter U)) hε
  have hpU := mul_le_mul_of_nonneg_right (le_max_right (i.perimeter S) (i.perimeter U)) hε
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem area_hausdorff_radius_bound (i : ClassicalAreaImports)
    {S U : Set Plane} {ε R : ℝ} (hS : IsCompact S) (hU : IsCompact U)
    (cS : Convex ℝ S) (cU : Convex ℝ U)
    (nS : (interior S).Nonempty) (nU : (interior U).Nonempty)
    (hε : 0 ≤ ε) (hR : 0 ≤ R)
    (rS : S ⊆ disk 0 R) (rU : U ⊆ disk 0 R)
    (hnear : HausdorffWithin S U ε) :
    |setArea S - setArea U| ≤ 2 * Real.pi * R * ε + Real.pi * ε ^ 2 := by
  have h := area_hausdorff_bound i hS hU cS cU nS nU hε hnear
  have hp := max_le (i.radius_perimeter S R hS cS nS hR rS)
    (i.radius_perimeter U R hU cU nU hR rU)
  have hm := mul_le_mul_of_nonneg_right hp hε
  linarith

/-- Intermediate local geometric bridge: disk containment, nonempty
interior, and continuity in the two-sided parallel-body sense. This does not
contain continuity of area as a premise. Modulus derives it from rational
body-radius, rotation-displacement and disk-interior inputs. -/
def LocalHullTransportDuty : Prop :=
  ∀ z : Translations × ℝ, ∃ R : ℝ, 0 ≤ R ∧
    (interior (K z.1.1 z.1.2 z.2)).Nonempty ∧
    K z.1.1 z.1.2 z.2 ⊆ disk 0 R ∧
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ w : Translations × ℝ, dist w z < δ →
        (interior (K w.1.1 w.1.2 w.2)).Nonempty ∧
        K w.1.1 w.1.2 w.2 ⊆ disk 0 R ∧
        HausdorffWithin (K w.1.1 w.1.2 w.2) (K z.1.1 z.1.2 z.2) ε

theorem placement_continuity_of_local_transport
    (c : CompactPlanarImports) (hrot : RotationContinuityDuty)
    (i : ClassicalAreaImports) (ht : LocalHullTransportDuty) :
    PlacementContinuityDuty := by
  apply Metric.continuous_iff.mpr
  intro z η hη
  rcases ht z with ⟨R, hR, nz, rz, hlocal⟩
  let A : ℝ := 2 * Real.pi * R + Real.pi + 1
  have hA : 0 < A := by
    dsimp [A]
    positivity
  let ε : ℝ := min 1 (η / (2 * A))
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by norm_num) (div_pos hη (by positivity))
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεη : ε ≤ η / (2 * A) := min_le_right _ _
  rcases hlocal ε hε with ⟨δ, hδ, hδw⟩
  refine ⟨δ, hδ, ?_⟩
  intro w hw
  rcases hδw w hw with ⟨nw, rw, hnear⟩
  have hb := area_hausdorff_radius_bound i
    (hull_compact_of_imports c hrot w.1.1 w.1.2 w.2)
    (hull_compact_of_imports c hrot z.1.1 z.1.2 z.2)
    (K_convex _ _ _) (K_convex _ _ _) nw nz (le_of_lt hε) hR rw rz hnear
  have hsquare : ε ^ 2 ≤ ε := by nlinarith
  have heprod : 2 * A * ε ≤ η := by
    have hprod := (le_div_iff₀ (show 0 < 2 * A by positivity)).mp hεη
    simpa only [mul_comm ε] using hprod
  have hp : 0 < Real.pi := Real.pi_pos
  have hsquareπ := mul_le_mul_of_nonneg_left hsquare (le_of_lt hp)
  have hsmall : 2 * Real.pi * R * ε + Real.pi * ε ^ 2 < η := by
    dsimp [A] at heprod hA
    nlinarith
  change dist (H w.1.1 w.1.2 w.2) (H z.1.1 z.1.2 z.2) < η
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hb hsmall

end Partials.Covering
end
