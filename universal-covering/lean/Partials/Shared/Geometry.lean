import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

open scoped ENNReal

/-! R1 signatures only. Geometric lower bounds, continuity, attainment,
rotations and certified interval propagation remain R4 obligations. -/
namespace Partials.Interface

/-- Euclidean norm, avoiding the max norm of an unqualified product space. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

def ClosedDisk (center : Plane) (radius : ℝ) : Set Plane :=
  {x | ‖x - center‖ ≤ radius}

def Translate (body : Set Plane) (shift : Plane) : Set Plane :=
  {x | x - shift ∈ body}

/-- Finiteness is explicit before converting extended-valued volume to ℝ. -/
structure FinitePlanarBody where
  carrier : Set Plane
  measurable : MeasurableSet carrier
  volume_finite : MeasureTheory.volume carrier ≠ ∞

noncomputable def PlanarArea (body : FinitePlanarBody) : ℝ :=
  (MeasureTheory.volume body.carrier).toReal

/-- The exact translation and angle domains remain in every lower-bound type. -/
def RegionalLowerBound (H : Plane → Plane → ℝ → ℝ)
    (translations : Set (Plane × Plane)) (angles : Set ℝ) (threshold : ℝ) : Prop :=
  ∀ shifts ∈ translations, ∀ angle ∈ angles,
    threshold ≤ H shifts.1 shifts.2 angle

end Partials.Interface
