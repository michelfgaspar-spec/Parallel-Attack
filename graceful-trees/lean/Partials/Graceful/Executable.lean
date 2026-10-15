import Partials.Graceful.Assembly
import Partials.Graceful.ReorderedPresentation

/-! Executable extraction of the manuscript's six-case construction.
The numerical parent functions and fiber sets are those of NumericConstruction.
Leaves receive the increasing enumeration of their actual numerical fiber. -/
namespace Partials.Graceful

namespace ProfileFrame

def labeling {u v : ℕ} (F : ProfileFrame u v) : Vertex u v → Fin (q u v + 1) :=
  fun x => F.fullMap (profileCodeEquiv u v x)

theorem labeling_eq_realization {u v : ℕ} (F : ProfileFrame u v) :
    F.labeling = F.realization := rfl

theorem labeling_graceful {u v : ℕ} (F : ProfileFrame u v)
    (h : NumericGraceful F.numericParent) : RootZeroGraceful u v F.labeling :=
  rootZeroGraceful_of_profile F h

theorem labeling_leaf_strictMono {u v : ℕ} (F : ProfileFrame u v) (c : DepthCode) :
    StrictMono (fun k => F.labeling (.leaf c.1 c.2 k)) :=
  ((F.fibers c).orderEmbOfFin (F.fiber_card c)).strictMono

theorem labeling_leaf_getElem {u v : ℕ} (F : ProfileFrame u v) (c : DepthCode)
    (k : Fin (pendantCount u v c.1 c.2)) :
    F.labeling (.leaf c.1 c.2 k) =
      (F.fibers c).sort[k.val]'(by rw [Finset.length_sort, F.fiber_card]; exact k.isLt) :=
  Finset.orderEmbOfFin_apply (F.fibers c) (F.fiber_card c) k

end ProfileFrame

namespace Executable
open Symbolic NumericConstruction

/-- Data, rather than a proposition whose witness would require choice. -/
inductive Route (u v : ℕ) : Type
  | small23 (hu : u = 1) (hv : v = 1)
  | small27 (hu : u = 1) (hv : v = 3)
  | residue0 (t : ℕ) (hq : q u v = q0 t) (hcase : 0 < t ∨ 2 ≤ u)
  | residue1 (t : ℕ) (hq : q u v = q1 t)
  | residue2 (t : ℕ) (hq : q u v = q2 t) (hu : 2 ≤ u)
  | alternate (t : ℕ) (hq : q u v = q2 t) (hu : u = 1)

/-- Arithmetic dispatch: the quotient and remainder of u+v determine t and
its residue branch, with the two literal exceptions handled explicitly. -/
def dispatch (u v : ℕ) (hu : 0 < u) (hv : 0 < v) : Route u v := by
  by_cases hsmall : u + v = 2
  · exact .small23 (by omega) (by omega)
  · have hlarge : 3 ≤ u + v := by omega
    have hmod := Nat.mod_lt (u + v) (by decide : 0 < 3)
    have hdiv := Nat.mod_add_div (u + v) 3
    let t := (u + v) / 3 - 1
    by_cases hzero : (u + v) % 3 = 0
    · exact .residue1 t (by dsimp [q, q1, t]; omega)
    · by_cases hone : (u + v) % 3 = 1
      · have hq : q u v = q0 t := by dsimp [q, q0, t]; omega
        by_cases hc : 0 < t ∨ 2 ≤ u
        · exact .residue0 t hq hc
        · exact .small27 (by omega) (by dsimp [q, q0] at hq; omega)
      · have hq : q u v = q2 t := by dsimp [q, q2, t]; omega
        by_cases hu2 : 2 ≤ u
        · exact .residue2 t hq hu2
        · exact .alternate t hq (by omega)

/-- Each route returns the actual function, without extracting an existential. -/
def labelOfRoute {u v : ℕ} (hu : 0 < u) (hv : 0 < v) :
    Route u v → Vertex u v → Fin (q u v + 1)
  | .small23 hu1 hv1 => by subst u; subst v; exact small23Label
  | .small27 hu1 hv3 => by subst u; subst v; exact small27Label
  | .residue0 t hq hc => (profile0 u v t hu hv hq hc).labeling
  | .residue1 t hq => (profile1 u v t hu hv hq).labeling
  | .residue2 t hq hu2 => (profile2 u v t hu2 hv hq).labeling
  | .alternate t hq hu1 => by subst u; exact (alternateProfile v t hv hq).labeling

theorem labelOfRoute_graceful {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (r : Route u v) : RootZeroGraceful u v (labelOfRoute hu hv r) := by
  cases r with
  | small23 hu1 hv1 => subst u; subst v; exact small23_root_zero
  | small27 hu1 hv3 => subst u; subst v; exact small27_root_zero
  | residue0 t hq hc =>
    exact ProfileFrame.labeling_graceful _ (profile0_numericGraceful u v t hu hv hq hc)
  | residue1 t hq =>
    exact ProfileFrame.labeling_graceful _ (profile1_numericGraceful u v t hu hv hq)
  | residue2 t hq hu2 =>
    exact ProfileFrame.labeling_graceful _ (profile2_numericGraceful u v t hu2 hv hq)
  | alternate t hq hu1 =>
    subst u
    exact ProfileFrame.labeling_graceful _ (alternateProfile_numericGraceful v t hv hq)

theorem labelOfRoute_leaf_strictMono {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (r : Route u v) (c : DepthCode) :
    StrictMono (fun k => labelOfRoute hu hv r (.leaf c.1 c.2 k)) := by
  cases r with
  | small23 hu1 hv1 =>
    subst u; subst v
    change StrictMono (fun k => small23Label (.leaf c.1 c.2 k))
    fin_cases c <;> decide
  | small27 hu1 hv3 =>
    subst u; subst v
    change StrictMono (fun k => small27Label (.leaf c.1 c.2 k))
    fin_cases c <;> decide
  | residue0 t hq hc => exact ProfileFrame.labeling_leaf_strictMono _ c
  | residue1 t hq => exact ProfileFrame.labeling_leaf_strictMono _ c
  | residue2 t hq hu2 => exact ProfileFrame.labeling_leaf_strictMono _ c
  | alternate t hq hu1 => subst u; exact ProfileFrame.labeling_leaf_strictMono _ c

/-- Total computable construction on exactly the positive manuscript parameters. -/
def label (u v : ℕ) (hu : 0 < u) (hv : 0 < v) : Vertex u v → Fin (q u v + 1) :=
  labelOfRoute hu hv (dispatch u v hu hv)

theorem label_graceful (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    RootZeroGraceful u v (label u v hu hv) :=
  labelOfRoute_graceful hu hv _

theorem label_leaf_strictMono (u v : ℕ) (hu : 0 < u) (hv : 0 < v) (c : DepthCode) :
    StrictMono (fun k => label u v hu hv (.leaf c.1 c.2 k)) :=
  labelOfRoute_leaf_strictMono hu hv _ c

end Executable
end Partials.Graceful
