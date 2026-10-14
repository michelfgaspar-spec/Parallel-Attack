import Partials.Shared.Geometry
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

open scoped ENNReal

noncomputable section

/-! R4 shared exact model. Plane is EuclideanSpace, not the max norm on a
product. Real area is volume.toReal; concrete hull measurability/finiteness is
the explicit regularity duty below. Source authored blind to Lean execution. -/
namespace Partials.Covering

abbrev Plane := Partials.Interface.Plane
abbrev Translations := Plane × Plane
abbrev disk := Partials.Interface.ClosedDisk
abbrev translate := Partials.Interface.Translate

def point (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

def rotate (φ : ℝ) (x : Plane) : Plane :=
  point (Real.cos φ * x 0 - Real.sin φ * x 1)
    (Real.sin φ * x 0 + Real.cos φ * x 1)

def reflect (x : Plane) : Plane := point (x 0) (-x 1)

def rho (n : ℕ) : ℝ := 1 / (2 * Real.cos (Real.pi / (2 * (n : ℝ))))

def center (n : ℕ) (j : Fin n) : Plane :=
  rho n • point (Real.cos (2 * Real.pi * (j.val : ℝ) / n))
    (Real.sin (2 * Real.pi * (j.val : ℝ) / n))

def reuleaux (n : ℕ) : Set Plane :=
  {x | ∀ j : Fin n, x ∈ disk (center n j) 1}

def D : Set Plane := disk 0 (1 / 2)
def B3 : Set Plane := reuleaux 3
def B5 : Set Plane := reuleaux 5

def K (t3 t5 : Plane) (φ : ℝ) : Set Plane :=
  convexHull ℝ (D ∪ translate B3 t3 ∪ translate (rotate φ '' B5) t5)

noncomputable def setArea (S : Set Plane) : ℝ :=
  (MeasureTheory.volume S).toReal

noncomputable def H (t3 t5 : Plane) (φ : ℝ) : ℝ := setArea (K t3 t5 φ)
noncomputable def placementArea (t : Translations) (φ : ℝ) : ℝ := H t.1 t.2 φ
noncomputable def G (φ : ℝ) : ℝ := sInf (Set.range (fun t : Translations => placementArea t φ))
noncomputable def M : ℝ := sInf (Set.range G)

def tau : ℝ := 1669 / 2000
def d3 : ℝ := 4 / 25
def d5 : ℝ := 9 / 100
def r3 : ℝ := 211 / 500
def r5 : ℝ := 237 / 500
def L3 : ℝ := 35454253 / 42400000
def L5 : ℝ := 1995480341 / 2385000000
def C : ℝ := 4270068 / 1750000
def hullRadius : ℝ := 369 / 500
def pentagonRadius : ℝ := 263 / 500
def fundamentalEnd : ℝ := Real.pi / 15
def fundamentalInterval : Set ℝ := Set.Icc 0 fundamentalEnd

def Q : Set Translations := {t | ‖t.1‖ ≤ d3 ∧ ‖t.2‖ ≤ d5}
def strictQ : Set Translations := {t | ‖t.1‖ < d3 ∧ ‖t.2‖ < d5}
def T : Set Translations := {t | ‖t.1‖ ≤ 3 ∧ ‖t.2‖ ≤ 3}
def verticalRectangle : Set Translations :=
  {t | |t.1 1| ≤ d3 ∧ |t.2 1| ≤ d5}

noncomputable def F (φ : ℝ) : ℝ :=
  sInf ((fun t : Translations => placementArea t φ) '' Q)
noncomputable def clippedG (φ : ℝ) : ℝ := min L3 (G φ)

def RegionalPremise (lo hi threshold : ℝ) : Prop :=
  Partials.Interface.RegionalLowerBound H Set.univ (Set.Icc lo hi) threshold

def HullRegularityDuty : Prop :=
  ∀ t3 t5 φ, IsCompact (K t3 t5 φ) ∧ MeasurableSet (K t3 t5 φ) ∧
    MeasureTheory.volume (K t3 t5 φ) ≠ ∞

def DiameterAtMostOne (S : Set Plane) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1

/-- Includes reflections as well as rotations and translations. -/
structure RigidMotion where
  shift : Plane
  angle : ℝ
  reflected : Bool

def RigidMotion.apply (e : RigidMotion) (x : Plane) : Plane :=
  e.shift + rotate e.angle (if e.reflected then reflect x else x)

def UniversalCover (U : Set Plane) : Prop :=
  IsCompact U ∧ Convex ℝ U ∧
    ∀ S : Set Plane, DiameterAtMostOne S → ∃ e : RigidMotion, e.apply '' S ⊆ U

noncomputable def aLeb : ℝ :=
  sInf (setArea '' {U : Set Plane | UniversalCover U})

/-- OPEN geometric normalization: center the placed disk, fix the triangle,
and retain one relative pentagon angle and independent translations.
This target supplies a hull containment/area-preserving motion, not M<=area U. -/
def UniversalNormalizationDuty : Prop :=
  ∀ U, UniversalCover U → ∃ e : RigidMotion, ∃ t3 t5 φ,
    K t3 t5 φ ⊆ e.apply '' U ∧ setArea (e.apply '' U) = setArea U

theorem H_nonnegative (t3 t5 : Plane) (φ : ℝ) : 0 ≤ H t3 t5 φ := by
  exact ENNReal.toReal_nonneg

theorem constants_order : 0 < tau ∧ tau < L3 ∧ L3 < L5 ∧ 0 < C := by
  norm_num [tau, L3, L5, C]

theorem confinement_radii_positive : 0 < d3 ∧ 0 < d5 ∧ 0 < r3 ∧ 0 < r5 := by
  norm_num [d3, d5, r3, r5]

theorem zero_in_Q : ((0 : Plane), (0 : Plane)) ∈ Q := by
  norm_num [Q, d3, d5]

theorem zero_in_T : ((0 : Plane), (0 : Plane)) ∈ T := by simp [T]

theorem regionalPremise_iff (lo hi threshold : ℝ) :
    RegionalPremise lo hi threshold ↔
      ∀ t3 t5 φ, φ ∈ Set.Icc lo hi → threshold ≤ H t3 t5 φ := by
  constructor
  · intro h t3 t5 φ hφ
    exact h (t3, t5) (Set.mem_univ _) φ hφ
  · intro h t ht φ hφ
    exact h t.1 t.2 φ hφ

end Partials.Covering

end
