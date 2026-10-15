import Partials.Graceful.PreSplitCorrespondence

/-! Printed q,C,Z,h,m formulas, with their actual natural and integer domains.
These aliases identify the manuscript expressions with the unchanged affine
construction; negative anchor differences use integers, not truncated naturals. -/
namespace Partials.Graceful.ManuscriptFormulas
open Symbolic NumericConstruction

theorem anchor0_printed (t : ℕ) :
    (anchor0 t).A = q0 t - 1 ∧ (anchor0 t).B = 5 ∧
    (anchor0 t).C = (q0 t + 9) / 3 ∧ (anchor0 t).Z = (2 * q0 t + 3) / 3 ∧
    (anchor0 t).B - ((anchor0 t).C : ℤ) = (6 - (q0 t : ℤ)) / 3 := by
  simp only [anchor0, q0, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  repeat' apply And.intro
  all_goals first | trivial | omega

theorem anchor1_printed (t : ℕ) :
    (anchor1 t).A = 1 ∧ (anchor1 t).B = q1 t - 3 ∧
    (anchor1 t).C = (2 * q1 t - 5) / 3 ∧ (anchor1 t).Z = (q1 t - 1) / 3 ∧
    (anchor1 t).B - ((anchor1 t).C : ℤ) = ((q1 t : ℤ) - 4) / 3 := by
  simp only [anchor1, q1, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  repeat' apply And.intro
  all_goals first | trivial | omega

theorem anchor2_printed (t : ℕ) :
    (anchor2 t).A = q2 t ∧ (anchor2 t).B = 2 ∧
    (anchor2 t).C = (q2 t + 4) / 3 ∧ (anchor2 t).Z = (2 * q2 t + 2) / 3 ∧
    (anchor2 t).B - ((anchor2 t).C : ℤ) = (2 - (q2 t : ℤ)) / 3 := by
  simp only [anchor2, q2, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  repeat' apply And.intro
  all_goals first | trivial | omega

theorem alternateAnchor_printed (t : ℕ) :
    (alternateAnchor t).A = 2 ∧ (alternateAnchor t).B = q2 t - 3 ∧
    (alternateAnchor t).C = (2 * q2 t - 4) / 3 ∧
    (alternateAnchor t).Z = (q2 t + 1) / 3 ∧
    (alternateAnchor t).B - ((alternateAnchor t).C : ℤ) = ((q2 t : ℤ) - 5) / 3 := by
  simp only [alternateAnchor, q2, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  repeat' apply And.intro
  all_goals first | trivial | omega

theorem half_parameters (t : ℕ) :
    (q0 t + 1) / 2 = 14 + 3*t ∧ (q1 t + 1) / 2 = 13 + 3*t ∧
    (q2 t - 1) / 2 = 14 + 3*t := by
  dsimp [q0, q1, q2]; omega

theorem base0_printed (t x : ℕ) : baseParent0 t x =
    if x = q0 t - 5 then 2 else if x = 6 then q0 t - 2
    else if x = q0 t - 6 then 3 else if x = 7 then q0 t - 3
    else if x = q0 t - 7 then 4
    else if x = 8 ∨ x = (q0 t + 1) / 2 then q0 t - 4 else 5 := by
  simp only [baseParent0, q0]
  simp only [show 27 + 6*t - 2 = 25 + 6*t by omega,
    show 27 + 6*t - 3 = 24 + 6*t by omega,
    show 27 + 6*t - 4 = 23 + 6*t by omega,
    show 27 + 6*t - 5 = 22 + 6*t by omega,
    show 27 + 6*t - 6 = 21 + 6*t by omega,
    show 27 + 6*t - 7 = 20 + 6*t by omega,
    show (27+6*t+1)/2 = 14+3*t by omega]

theorem base1_printed (t x : ℕ) : baseParent1 t x =
    if x = (anchor1 t).C ∨ x = (anchor1 t).Z ∨ x = 7 ∨ x = (anchor1 t).C + 3
      then (anchor1 t).B
    else if x = q1 t - 5 then 2 else if x = 6 then q1 t - 2
    else if x = q1 t - 6 then 3 else if x = (anchor1 t).Z + 2 then q1 t - 4
    else if x = (anchor1 t).Z + 3 then 5 else 4 := by
  simp only [baseParent1, q1, anchor1]
  simp only [show 25 + 6*t - 2 = 23 + 6*t by omega,
    show 25 + 6*t - 4 = 21 + 6*t by omega,
    show 25 + 6*t - 5 = 20 + 6*t by omega,
    show 25 + 6*t - 6 = 19 + 6*t by omega,
    show 15+4*t+3 = 18+4*t by omega,
    show 8+2*t+2 = 10+2*t by omega,
    show 8+2*t+3 = 11+2*t by omega]

theorem base2_printed (t x : ℕ) : baseParent2 t x =
    if x = q2 t - 6 then 3
    else if x = q2 t - 7 ∨ x = (q2 t - 1) / 2 - 2 then q2 t - 3
    else if x = 6 then q2 t - 2 else if x = (q2 t - 1) / 2 then 4
    else if x = (q2 t - 1) / 2 + 2 then 5
    else if x = (q2 t - 1) / 2 - 1 then q2 t - 4 else 2 := by
  simp only [baseParent2, q2]
  simp only [show 29 + 6*t - 2 = 27 + 6*t by omega,
    show 29 + 6*t - 3 = 26 + 6*t by omega,
    show 29 + 6*t - 4 = 25 + 6*t by omega,
    show 29 + 6*t - 6 = 23 + 6*t by omega,
    show 29 + 6*t - 7 = 22 + 6*t by omega,
    show (29+6*t-1)/2 = 14+3*t by omega,
    show 14+3*t-2 = 12+3*t by omega,
    show 14+3*t+2 = 16+3*t by omega,
    show 14+3*t-1 = 13+3*t by omega]

theorem alternateBase_printed (t x : ℕ) : alternateBaseParent t x =
    if x = (alternateAnchor t).C ∨ x = (alternateAnchor t).Z ∨ x = 7 ∨
      x = (alternateAnchor t).Z + 2 then (alternateAnchor t).B
    else if x = q2 t - 6 then 1 else if x = 6 then q2 t - 2
    else if x = 8 then 5 else if x = (alternateAnchor t).Z - 1 then 3
    else if x = (alternateAnchor t).C + 2 then q2 t - 4 else 4 := by
  simp only [alternateBaseParent, q2, alternateAnchor]
  simp only [show 29 + 6*t - 2 = 27 + 6*t by omega,
    show 29 + 6*t - 4 = 25 + 6*t by omega,
    show 29 + 6*t - 6 = 23 + 6*t by omega,
    show 10+2*t+2 = 12+2*t by omega,
    show 10+2*t-1 = 9+2*t by omega,
    show 18+4*t+2 = 20+4*t by omega]

theorem first0_printed (t : ℕ) (ht : 0 < t) :
    afterFirst0 t = moveTwo (baseParent0 t) ((anchor0 t).C - 3)
      ((anchor0 t).Z + 2) (q0 t - 2) := by
  unfold afterFirst0
  rw [if_neg (by omega)]
  congr 1 <;> dsimp [anchor0] <;> omega

theorem first0_exception_printed :
    afterFirst0 0 = moveTwo (baseParent0 0) 13 17 25 := rfl

theorem first1_printed (t : ℕ) :
    afterFirst1 t = moveTwo (baseParent1 t) ((q1 t + 1) / 2)
      ((q1 t + 1) / 2 + 1) (q1 t - 2) := by
  unfold afterFirst1
  congr 1 <;> dsimp [q1] <;> omega

theorem first2_printed (t : ℕ) :
    afterFirst2 t = moveTwo (baseParent2 t) ((anchor2 t).C - 3)
      ((anchor2 t).Z - 1) (q2 t - 4) := by
  unfold afterFirst2
  congr 1 <;> dsimp [anchor2] <;> omega

theorem alternateFirst_printed (t : ℕ) :
    alternateAfterFirst t = moveTwo (alternateBaseParent t) ((q2 t - 1) / 2)
      ((q2 t - 1) / 2 + 3) (q2 t - 2) := by
  unfold alternateAfterFirst
  congr 1 <;> dsimp [q2] <;> omega

/-- The literal three-cycle of equation q2cycle1. -/
theorem q2_cycle1_printed (t : ℕ) :
    2 + Nat.dist (q2 t - 6) 3 = q2 t - 7 ∧
    2 + Nat.dist (q2 t - 7) (q2 t - 3) = 6 ∧
    2 + Nat.dist 6 (q2 t - 2) = q2 t - 6 := by
  simp only [q2, Nat.dist]; omega

/-- The literal four-cycle of equation q2cycle2, using m=(q-1)/2. -/
theorem q2_cycle2_printed (t : ℕ) :
    let m := (q2 t - 1) / 2
    2 + Nat.dist m 4 = m - 2 ∧
    2 + Nat.dist (m-2) (q2 t - 3) = m + 2 ∧
    2 + Nat.dist (m+2) 5 = m - 1 ∧
    2 + Nat.dist (m-1) (q2 t - 4) = m := by
  dsimp
  simp only [q2, Nat.dist]; omega

theorem alternate_cycle1_printed (t : ℕ) :
    4 + Nat.dist (alternateAnchor t).C (alternateAnchor t).B = (alternateAnchor t).Z + 2 ∧
    4 + Nat.dist ((alternateAnchor t).Z + 2) (alternateAnchor t).B = (alternateAnchor t).C := by
  simp only [alternateAnchor, Nat.dist]; omega

theorem alternate_cycle2_printed (t : ℕ) :
    4 + Nat.dist (alternateAnchor t).Z (alternateAnchor t).B = (alternateAnchor t).C + 2 ∧
    4 + Nat.dist ((alternateAnchor t).C + 2) (q2 t - 4) = (alternateAnchor t).Z - 1 ∧
    4 + Nat.dist ((alternateAnchor t).Z - 1) 3 = (alternateAnchor t).Z := by
  simp only [alternateAnchor, q2, Nat.dist]; omega

/-- The four boundary replacements in equation alternateboundary. -/
theorem alternate_boundary_printed (t : ℕ) :
    Nat.dist (q2 t - 6) 4 = q2 t - 10 ∧ Nat.dist (q2 t - 6) 1 = q2 t - 7 ∧
    Nat.dist 6 4 = 2 ∧ Nat.dist 6 (q2 t - 2) = q2 t - 8 ∧
    Nat.dist 7 4 = 3 ∧ Nat.dist 7 (alternateAnchor t).B = q2 t - 10 ∧
    Nat.dist 8 4 = 4 ∧ Nat.dist 8 5 = 3 := by
  simp only [alternateAnchor, q2, Nat.dist]
  repeat' apply And.intro
  all_goals first | trivial | omega

/-- The printed signed anchor displacement never vanishes on any symbolic route. -/
theorem signed_anchor_displacements_nonzero (t : ℕ) :
    (anchor0 t).B - ((anchor0 t).C : ℤ) ≠ 0 ∧
    (anchor1 t).B - ((anchor1 t).C : ℤ) ≠ 0 ∧
    (anchor2 t).B - ((anchor2 t).C : ℤ) ≠ 0 ∧
    (alternateAnchor t).B - ((alternateAnchor t).C : ℤ) ≠ 0 := by
  simp only [anchor0, anchor1, anchor2, alternateAnchor,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

end Partials.Graceful.ManuscriptFormulas
