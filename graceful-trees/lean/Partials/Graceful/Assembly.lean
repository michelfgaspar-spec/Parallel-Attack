import Partials.Graceful.NumericConstruction
import Partials.Graceful.Witnesses

/-! Exhaustive parameter classification.
The route classifier, concrete profile counts, numerical difference proofs
and two literal witnesses are assembled here and included in the project build.
Executable.lean supplies the computable labeling; ManuscriptPresentation.lean,
PreSplitCorrespondence.lean and ManuscriptFormulas.lean give the graph and formula links.
-/
namespace Partials.Graceful

open Symbolic NumericConstruction

/-- Every constructor states its exact parameter domain. These are route
conditions, not graceful-labeling certificates or assumed main conclusions. -/
inductive ConstructionCase (u v : ℕ) : Prop
  | small23 (hu : u = 1) (hv : v = 1)
  | small27 (hu : u = 1) (hv : v = 3)
  | residue0 (t : ℕ) (hq : q u v = Symbolic.q0 t)
      (hcase : 0 < t ∨ 2 ≤ u)
  | residue1 (t : ℕ) (hq : q u v = Symbolic.q1 t)
  | residue2 (t : ℕ) (hq : q u v = Symbolic.q2 t) (hu : 2 ≤ u)
  | alternate (t : ℕ) (hq : q u v = Symbolic.q2 t) (hu : u = 1)

/-- Exhaustive route classification, including q0 at t=0 and both exceptions.
The conclusion contains no labeling, NumericGraceful, or ProfileFrame premise.
-/
theorem allPositiveCases (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    ConstructionCase u v := by
  rcases edge_count_cases u v hu hv with h23 | ⟨t, h1⟩ | ⟨t, h0⟩ | ⟨t, h2⟩
  · obtain ⟨hu1, hv1⟩ := q23_parameters u v hu hv h23
    exact .small23 hu1 hv1
  · exact .residue1 t (by simpa [Symbolic.q1] using h1)
  · by_cases hc : 0 < t ∨ 2 ≤ u
    · exact .residue0 t (by simpa [Symbolic.q0] using h0) hc
    · have hu1 : u = 1 := by omega
      have ht : t = 0 := by omega
      have hv3 : v = 3 := by
        dsimp [q] at h0
        omega
      exact .small27 hu1 hv3
  · by_cases hu2 : 2 ≤ u
    · exact .residue2 t (by simpa [Symbolic.q2] using h2) hu2
    · exact .alternate t (by simpa [Symbolic.q2] using h2) (by omega)

/-- Proof of the exact all-positive target, included in the project build.
The case constructions supply the labeling without assuming a desired case
conclusion. CentreZero.lean identifies zero with the unique graph-theoretic centre. -/
theorem main_root_zero : AllPositiveTarget := by
  intro u v hu hv
  cases allPositiveCases u v hu hv with
  | small23 hu1 hv1 =>
    subst u
    subst v
    exact small23_exists
  | small27 hu1 hv3 =>
    subst u
    subst v
    exact small27_exists
  | residue0 t hq hc => exact standard0_constructed u v t hu hv hq hc
  | residue1 t hq => exact standard1_constructed u v t hu hv hq
  | residue2 t hq hu2 => exact standard2_constructed u v t hu2 hv hq
  | alternate t hq hu1 =>
    subst u
    exact alternate_constructed v t hv hq

end Partials.Graceful
