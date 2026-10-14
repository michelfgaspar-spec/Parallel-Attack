import Partials.Graceful.Model

/-! The exact two exceptional final labelings from Table tab:small after
the source star split. `by decide` is authored source, not an executed check. -/
namespace Partials.Graceful

def small23Label : Vertex 1 1 → Fin 24
  | .root => 0
  | .levelOne i =>
      match i.val with | 0 => 22 | 1 => 1 | _ => 23
  | .levelTwo i j =>
      match i.val, j.val with
      | 0, 0 => 5 | 0, 1 => 19 | 0, _ => 4
      | 1, 0 => 21 | 1, 1 => 3 | 1, _ => 20
      | _, 0 => 9 | _, _ => 2
  | .leaf i j k =>
      match i.val, j.val, k.val with
      | 0, 0, _ => 15 | 0, 1, _ => 14
      | 0, _, 0 => 10 | 0, _, 1 => 12 | 0, _, _ => 17
      | 1, 0, _ => 6 | 1, 1, _ => 7
      | 1, _, 0 => 8 | 1, _, _ => 11
      | _, 0, _ => 16 | _, _, 0 => 13 | _, _, _ => 18

def small27Label : Vertex 1 3 → Fin 28
  | .root => 0
  | .levelOne i =>
      match i.val with | 0 => 27 | 1 => 1 | _ => 26
  | .levelTwo i j =>
      match i.val, j.val with
      | 0, 0 => 2 | 0, 1 => 3 | 0, _ => 25
      | 1, 0 => 24 | 1, 1 => 4 | 1, _ => 23
      | _, 0 => 12 | _, _ => 5
  | .leaf i j k =>
      match i.val, j.val, k.val with
      | 0, 0, _ => 22 | 0, 1, _ => 18
      | 0, _, 0 => 6 | 0, _, 1 => 7 | 0, _, _ => 20
      | 1, 0, _ => 8 | 1, 1, _ => 21
      | 1, _, 0 => 10 | 1, _, 1 => 11 | 1, _, 2 => 13
      | 1, _, 3 => 14 | 1, _, 4 => 15 | 1, _, _ => 17
      | _, 0, _ => 19 | _, _, 0 => 9 | _, _, _ => 16

/-- All quantifiers in this concrete certificate interface have finite domains.
The unbounded natural-difference iff is recovered by the theorem below. -/
def FiniteGracefulCheck (u v : ℕ) (f : Vertex u v → Fin (q u v + 1)) : Prop :=
  Function.Bijective f ∧ f .root = 0 ∧
  (∀ d : Fin (q u v), ∃ e : EdgeIndex u v,
    Partials.Interface.EdgeDifference (graph u v) (fun x => (f x).val) e = d.val + 1) ∧
  (∀ e : EdgeIndex u v,
    1 ≤ Partials.Interface.EdgeDifference (graph u v) (fun x => (f x).val) e ∧
    Partials.Interface.EdgeDifference (graph u v) (fun x => (f x).val) e ≤ q u v) ∧
  Function.Injective (Partials.Interface.EdgeDifference (graph u v) (fun x => (f x).val))

theorem rootZeroGraceful_of_finite_check {u v : ℕ}
    (f : Vertex u v → Fin (q u v + 1)) (h : FiniteGracefulCheck u v f) :
    RootZeroGraceful u v f := by
  rcases h with ⟨hbij, hroot, hcover, hbounds, hinj⟩
  refine ⟨hbij, hroot, ?_, hinj⟩
  intro d
  constructor
  · intro hd
    let index : Fin (q u v) := ⟨d - 1, by omega⟩
    obtain ⟨e, he⟩ := hcover index
    refine ⟨e, ?_⟩
    have hi : index.val + 1 = d := by dsimp [index]; omega
    exact he.trans hi
  · rintro ⟨e, he⟩
    simpa only [he] using hbounds e

set_option maxRecDepth 100000 in
/-- Checks the exact source tree, including every edge bound. -/
theorem small23_finite_check : FiniteGracefulCheck 1 1 small23Label := by
  change Function.Bijective small23Label ∧ small23Label Vertex.root = 0 ∧
    (∀ d : Fin 23, ∃ e : EdgeIndex 1 1,
      Partials.Interface.EdgeDifference (graph 1 1) (fun x => (small23Label x).val) e = d.val + 1) ∧
    (∀ e : EdgeIndex 1 1,
      1 ≤ Partials.Interface.EdgeDifference (graph 1 1) (fun x => (small23Label x).val) e ∧
      Partials.Interface.EdgeDifference (graph 1 1) (fun x => (small23Label x).val) e ≤ 23) ∧
    Function.Injective (Partials.Interface.EdgeDifference (graph 1 1) (fun x => (small23Label x).val))
  decide

set_option maxRecDepth 100000 in
theorem small27_finite_check : FiniteGracefulCheck 1 3 small27Label := by
  change Function.Bijective small27Label ∧ small27Label Vertex.root = 0 ∧
    (∀ d : Fin 27, ∃ e : EdgeIndex 1 3,
      Partials.Interface.EdgeDifference (graph 1 3) (fun x => (small27Label x).val) e = d.val + 1) ∧
    (∀ e : EdgeIndex 1 3,
      1 ≤ Partials.Interface.EdgeDifference (graph 1 3) (fun x => (small27Label x).val) e ∧
      Partials.Interface.EdgeDifference (graph 1 3) (fun x => (small27Label x).val) e ≤ 27) ∧
    Function.Injective (Partials.Interface.EdgeDifference (graph 1 3) (fun x => (small27Label x).val))
  decide

theorem small23_root_zero : RootZeroGraceful 1 1 small23Label :=
  rootZeroGraceful_of_finite_check small23Label small23_finite_check

theorem small27_root_zero : RootZeroGraceful 1 3 small27Label :=
  rootZeroGraceful_of_finite_check small27Label small27_finite_check

theorem small23_exists :
    ∃ f : Vertex 1 1 → Fin (q 1 1 + 1), RootZeroGraceful 1 1 f :=
  ⟨small23Label, small23_root_zero⟩

theorem small27_exists :
    ∃ f : Vertex 1 3 → Fin (q 1 3 + 1), RootZeroGraceful 1 3 f :=
  ⟨small27Label, small27_root_zero⟩

end Partials.Graceful
