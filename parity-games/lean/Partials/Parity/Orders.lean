import Partials.Parity.Model

/-! Blind R7 source for preliminaries and P1-D04/P1-L02/P1-D09.
The ambient priorities are naturals; finite raw domains are bounded separately.
All tactic text below is authored, not executed. -/

namespace Partials.Parity

theorem priorityLE_refl (a : Nat) : PriorityLE a a := by
  unfold PriorityLE
  omega

theorem priorityLE_antisymm {a b : Nat}
    (hab : PriorityLE a b) (hba : PriorityLE b a) : a = b := by
  unfold PriorityLE at *
  omega

theorem priorityLE_trans {a b c : Nat}
    (hab : PriorityLE a b) (hbc : PriorityLE b c) : PriorityLE a c := by
  unfold PriorityLE at *
  omega

theorem priorityLE_total (a b : Nat) : PriorityLE a b ∨ PriorityLE b a := by
  unfold PriorityLE
  omega

/-- P1-L02 uses ordinary `max`, rather than a lattice maximum for PriorityLE. -/
theorem numerical_max_priority_monotone {a b : Nat}
    (hab : PriorityLE a b) (c : Nat) :
    PriorityLE (max a c) (max b c) := by
  rcases le_total a c with hac | hca <;>
    rcases le_total b c with hbc | hcb
  · simp only [max_eq_right hac, max_eq_right hbc]
    exact priorityLE_refl c
  · simp only [max_eq_right hac, max_eq_left hcb]
    unfold PriorityLE at *
    omega
  · simp only [max_eq_left hca, max_eq_right hbc]
    unfold PriorityLE at *
    omega
  · simpa only [max_eq_left hca, max_eq_left hcb] using hab

theorem numerical_max_priority_monotone_left {a b : Nat}
    (hab : PriorityLE a b) (c : Nat) :
    PriorityLE (max c a) (max c b) := by
  simpa only [max_comm] using numerical_max_priority_monotone hab c

theorem outcomeLE_refl {Exit : Type*} (x : Outcome Exit) : OutcomeLE x x := by
  cases x with
  | bottom => trivial
  | top => trivial
  | halt o p => exact ⟨rfl, priorityLE_refl p⟩

theorem outcomeLE_trans {Exit : Type*} {x y z : Outcome Exit}
    (hxy : OutcomeLE x y) (hyz : OutcomeLE y z) : OutcomeLE x z := by
  cases x with
  | bottom => trivial
  | top => cases y <;> cases z <;> simp_all [OutcomeLE]
  | halt o p =>
    cases y with
    | bottom => exact False.elim hxy
    | top => cases z <;> simp_all [OutcomeLE]
    | halt o' q =>
      cases z with
      | bottom => exact False.elim hyz
      | top => trivial
      | halt o'' r =>
        exact ⟨hxy.1.trans hyz.1, priorityLE_trans hxy.2 hyz.2⟩

theorem outcomeLE_antisymm {Exit : Type*} {x y : Outcome Exit}
    (hxy : OutcomeLE x y) (hyx : OutcomeLE y x) : x = y := by
  cases x with
  | bottom => cases y <;> simp_all [OutcomeLE]
  | top => cases y <;> simp_all [OutcomeLE]
  | halt o p =>
    cases y with
    | bottom => exact False.elim hxy
    | top => exact False.elim hyx
    | halt o' q =>
      have ho : o = o' := hxy.1
      have hp : p = q := priorityLE_antisymm hxy.2 hyx.2
      subst o'
      subst q
      rfl

theorem halt_distinct_exits_incomparable {Exit : Type*}
    {o o' : Exit} (hne : o ≠ o') (p q : Nat) :
    ¬ OutcomeLE (.halt o p) (.halt o' q) := by
  intro h
  exact hne h.1

theorem strictProfile_irrefl {Start Exit : Type*} (p : Profile Start Exit) :
    ¬ StrictProfile p p := by
  intro h
  exact h.2 h.1

end Partials.Parity
