import Partials.Covering.Geometry
import Partials.Covering.Regularity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
namespace Partials.Covering

/-- The literal Cauchy width/integral target, separate from the radius bound
already included as an explicitly unfinished classical import. -/
def projectionDirection (θ : ℝ) : Plane := point (Real.cos θ) (Real.sin θ)

def projectionValues (S : Set Plane) (θ : ℝ) : Set ℝ :=
  (fun x : Plane => inner ℝ (projectionDirection θ) x) '' S

def directionalWidth (S : Set Plane) (θ : ℝ) : ℝ :=
  sSup (projectionValues S θ) - sInf (projectionValues S θ)

def cauchyPerimeter (S : Set Plane) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi, directionalWidth S θ

def CauchyProjectionDuty (i : ClassicalAreaImports) : Prop :=
  ∀ S : Set Plane, IsCompact S → Convex ℝ S → (interior S).Nonempty →
    i.perimeter S = cauchyPerimeter S

/-- A concrete nonvacuous cover-family witness. This elementary source proof
does not settle normalization, finite-area covariance or the covering bound. -/
theorem unit_disk_universal_cover : UniversalCover (disk 0 1) := by
  refine ⟨disk_compact 0 1, disk_convex 0 1, ?_⟩
  intro S hdiam
  by_cases hS : S.Nonempty
  · obtain ⟨p, hp⟩ := hS
    let e : RigidMotion := ⟨-p, 0, false⟩
    refine ⟨e, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have h := hdiam x hx p hp
    simpa [RigidMotion.apply, e, rotate_zero_angle,
      Partials.Interface.ClosedDisk, dist_eq_norm, sub_eq_add_neg, add_comm] using h
  · refine ⟨⟨0, 0, false⟩, ?_⟩
    rintro y ⟨x, hx, hxy⟩
    exact False.elim (hS ⟨x, hx⟩)

theorem universal_cover_family_nonempty : ∃ U : Set Plane, UniversalCover U :=
  ⟨disk 0 1, unit_disk_universal_cover⟩

theorem universal_cover_area_values_nonempty :
    (setArea '' {U : Set Plane | UniversalCover U}).Nonempty :=
  ⟨setArea (disk 0 1), ⟨disk 0 1, unit_disk_universal_cover, rfl⟩⟩

end Partials.Covering
end
