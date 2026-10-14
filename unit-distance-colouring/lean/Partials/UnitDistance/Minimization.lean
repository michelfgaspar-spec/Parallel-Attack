import Partials.UnitDistance.HexWord

/-! R6 BLIND SOURCE / UNCOMPILED. Main `thm:147`, the real arrangement
argument and the integral candidate reduction. The remaining analytic duty
is stated for arbitrary finite plane polyhedra: existence of a minimum,
an extreme point of a bounded polyhedron, and two independent active normals
at a plane vertex. It assumes neither a147-candidate answer nor a shortest
root word. The bounded minimum-face to cell-vertex step is authored below. -/
namespace Partials.UnitDistance.Words

universe u v

noncomputable section

open Partials.UnitDistance

def shiftObjective (p : SevenPairs) (A B : ℤ) : ℤ :=
  ∑ k : Fin 7, hexNorm ((p k).1 + A) ((p k).2 + B)

abbrev CandidateIndex := Fin 3 × Fin 7 × Fin 7

/-- Vertical-horizontal, vertical-diagonal, horizontal-diagonal intersections.
Coincident points are deduplicated by the image finset. -/
def candidate (p : SevenPairs) (i : CandidateIndex) : ℤ × ℤ :=
  if i.1 = 0 then (-(p i.2.1).1, -(p i.2.2).2)
  else if i.1 = 1 then
    (-(p i.2.1).1, (p i.2.1).1 - (p i.2.2).1 - (p i.2.2).2)
  else ((p i.2.1).2 - (p i.2.2).1 - (p i.2.2).2, -(p i.2.1).2)

def candidatePoints (p : SevenPairs) : Finset (ℤ × ℤ) :=
  Finset.univ.image (candidate p)

theorem candidate_card_le147 (p : SevenPairs) : (candidatePoints p).card ≤ 147 := by
  calc
    (candidatePoints p).card ≤ (Finset.univ : Finset CandidateIndex).card :=
      Finset.card_image_le
    _ = 147 := by simp [CandidateIndex]

theorem candidates_nonempty (p : SevenPairs) : (candidatePoints p).Nonempty := by
  exact ⟨candidate p (0, 0, 0), Finset.mem_image.mpr ⟨(0, 0, 0), by simp, rfl⟩⟩

theorem candidate_vertical_horizontal (p : SevenPairs) (i j : Fin 7) :
    (candidate p (0, i, j)).1 = -(p i).1 ∧
      (candidate p (0, i, j)).2 = -(p j).2 := by simp [candidate]

theorem candidate_vertical_diagonal (p : SevenPairs) (i j : Fin 7) :
    (candidate p (1, i, j)).1 = -(p i).1 ∧
      (candidate p (1, i, j)).1 + (candidate p (1, i, j)).2 =
        -(p j).1 - (p j).2 := by simp [candidate]; ring

theorem candidate_horizontal_diagonal (p : SevenPairs) (i j : Fin 7) :
    (candidate p (2, i, j)).2 = -(p i).2 ∧
      (candidate p (2, i, j)).1 + (candidate p (2, i, j)).2 =
        -(p j).1 - (p j).2 := by simp [candidate]; ring

theorem shiftObjective_nonneg (p : SevenPairs) (A B : ℤ) :
    0 ≤ shiftObjective p A B :=
  Finset.sum_nonneg (fun _ _ => hexNorm_nonneg _ _)

theorem shiftObjective_coordinate_bounds (p : SevenPairs) (A B L : ℤ)
    (hL : shiftObjective p A B ≤ L) (k : Fin 7) :
    |(p k).1 + A| ≤ L ∧ |(p k).2 + B| ≤ L := by
  have ht : hexNorm ((p k).1 + A) ((p k).2 + B) ≤ shiftObjective p A B :=
    Finset.single_le_sum (fun _ _ => hexNorm_nonneg _ _) (Finset.mem_univ k)
  exact ⟨le_trans (abs_first_le_hex _ _) (le_trans ht hL),
    le_trans (abs_second_le_hex _ _) (le_trans ht hL)⟩

abbrev PlanePoint := ℝ × ℝ
structure PlaneForm where
  a : ℝ
  b : ℝ
  c : ℝ

def formValue (l : PlaneForm) (x : PlanePoint) : ℝ := l.a * x.1 + l.b * x.2 + l.c
def negateForm (l : PlaneForm) : PlaneForm := ⟨-l.a, -l.b, -l.c⟩
def scaleForm (r : ℝ) (l : PlaneForm) : PlaneForm := ⟨r * l.a, r * l.b, r * l.c⟩
def offsetForm (l : PlaneForm) (r : ℝ) : PlaneForm := ⟨l.a, l.b, l.c + r⟩
def normalDet (l m : PlaneForm) : ℝ := l.a * m.b - l.b * m.a
def midpointPoint (u v : PlanePoint) : PlanePoint :=
  ((u.1 + v.1) / 2, (u.2 + v.2) / 2)
def planePolyhedron {ι : Type*} (forms : ι → PlaneForm) : Set PlanePoint :=
  {x | ∀ i, formValue (forms i) x ≤ 0}
def InBoundedBox (C : Set PlanePoint) : Prop :=
  ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ C, |x.1| ≤ R ∧ |x.2| ≤ R
def MidpointExtreme (C : Set PlanePoint) (x : PlanePoint) : Prop :=
  x ∈ C ∧ ∀ u ∈ C, ∀ v ∈ C, x = midpointPoint u v → u = x ∧ v = x

theorem formValue_negate (l : PlaneForm) (x : PlanePoint) :
    formValue (negateForm l) x = -formValue l x := by
  simp [formValue, negateForm]; ring
theorem formValue_offset (l : PlaneForm) (r : ℝ) (x : PlanePoint) :
    formValue (offsetForm l r) x = formValue l x + r := by
  simp [formValue, offsetForm]; ring
theorem formValue_midpoint (l : PlaneForm) (u v : PlanePoint) :
    formValue l (midpointPoint u v) = (formValue l u + formValue l v) / 2 := by
  simp [formValue, midpointPoint]; ring

/-- These are general finite-dimensional analysis/polyhedral facts.
They are explicitly deferred; no local runtime or library theorem inspection
has supplied them. Midpoint-extreme is adequate for convex polyhedra. -/
structure PrimitivePlaneDuty : Prop where
  continuous_bounded_sublevels_attain : ∀ f : PlanePoint → ℝ,
    Continuous f → (∀ L, InBoundedBox {x | f x ≤ L}) →
      ∃ x, ∀ y, f x ≤ f y
  bounded_polyhedron_extreme : ∀ {ι : Type*} [Fintype ι] (forms : ι → PlaneForm),
    (planePolyhedron forms).Nonempty → InBoundedBox (planePolyhedron forms) →
      ∃ x, MidpointExtreme (planePolyhedron forms) x
  vertex_active_independent : ∀ {ι : Type*} [Fintype ι] (forms : ι → PlaneForm)
    (x : PlanePoint), MidpointExtreme (planePolyhedron forms) x →
      ∃ i j, normalDet (forms i) (forms j) ≠ 0 ∧
        formValue (forms i) x = 0 ∧ formValue (forms j) x = 0

/-- Universe transport preserves the same plane polyhedron exactly. -/
theorem planePolyhedron_ulift {ι : Type*} (forms : ι → PlaneForm) :
    planePolyhedron (fun i : ULift.{v} ι => forms i.down) = planePolyhedron forms := by
  ext x
  constructor
  · intro h i
    exact h ⟨i⟩
  · intro h i
    exact h i.down

/-- Apply the original universe-polymorphic premise to a finite Type-0 index
by lifting it; no smaller-index premise replaces the original duty. -/
theorem primitive_bounded_extreme_type0 (d : PrimitivePlaneDuty.{u, v})
    {ι : Type} [Fintype ι] (forms : ι → PlaneForm)
    (hne : (planePolyhedron forms).Nonempty)
    (hb : InBoundedBox (planePolyhedron forms)) :
    ∃ x, MidpointExtreme (planePolyhedron forms) x := by
  have hne' : (planePolyhedron (fun i : ULift.{u} ι => forms i.down)).Nonempty := by
    simpa only [planePolyhedron_ulift] using hne
  have hb' : InBoundedBox (planePolyhedron (fun i : ULift.{u} ι => forms i.down)) := by
    simpa only [planePolyhedron_ulift] using hb
  simpa only [planePolyhedron_ulift] using
    d.bounded_polyhedron_extreme (fun i : ULift.{u} ι => forms i.down) hne' hb'

theorem primitive_active_independent_type0 (d : PrimitivePlaneDuty.{u, v})
    {ι : Type} [Fintype ι] (forms : ι → PlaneForm) (x : PlanePoint)
    (hx : MidpointExtreme (planePolyhedron forms) x) :
    ∃ i j, normalDet (forms i) (forms j) ≠ 0 ∧
      formValue (forms i) x = 0 ∧ formValue (forms j) x = 0 := by
  have hx' : MidpointExtreme
      (planePolyhedron (fun i : ULift.{v} ι => forms i.down)) x := by
    simpa only [planePolyhedron_ulift] using hx
  obtain ⟨i, j, hij⟩ := d.vertex_active_independent
    (fun i : ULift.{v} ι => forms i.down) x hx'
  exact ⟨i.down, j.down, hij⟩

def realHexNorm (a b : ℝ) : ℝ := max (max |a| |b|) |a + b|
def realObjective (p : SevenPairs) (x : PlanePoint) : ℝ :=
  ∑ k : Fin 7, realHexNorm ((p k).1 + x.1) ((p k).2 + x.2)

theorem real_abs_as_if (z : ℝ) : |z| = if 0 ≤ z then z else -z := by
  split_ifs with h
  · exact abs_of_nonneg h
  · exact abs_of_nonpos (le_of_not_ge h)

theorem twice_realHexNorm (a b : ℝ) :
    2 * realHexNorm a b = |a| + |b| + |a + b| := by
  simp only [realHexNorm, real_abs_as_if, max_def]
  split_ifs <;> linarith

theorem realHexNorm_nonneg (a b : ℝ) : 0 ≤ realHexNorm a b :=
  le_trans (abs_nonneg a) (le_trans (le_max_left _ _) (le_max_left _ _))

theorem realObjective_continuous (p : SevenPairs) : Continuous (realObjective p) := by
  unfold realObjective realHexNorm
  fun_prop

theorem realObjective_coordinate_bounds (p : SevenPairs) (x : PlanePoint) :
    |x.1| ≤ realObjective p x + |((p 0).1 : ℝ)| ∧
      |x.2| ≤ realObjective p x + |((p 0).2 : ℝ)| := by
  have ht : realHexNorm ((p 0).1 + x.1) ((p 0).2 + x.2) ≤ realObjective p x :=
    Finset.single_le_sum
      (fun (k : Fin 7) _ => realHexNorm_nonneg ((p k).1 + x.1) ((p k).2 + x.2))
      (Finset.mem_univ (0 : Fin 7))
  have ha : |((p 0).1 : ℝ) + x.1| ≤ realHexNorm ((p 0).1 + x.1) ((p 0).2 + x.2) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hb : |((p 0).2 : ℝ) + x.2| ≤ realHexNorm ((p 0).1 + x.1) ((p 0).2 + x.2) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  constructor
  · calc
      |x.1| = |(((p 0).1 : ℝ) + x.1) - (p 0).1| := by congr 1; ring
      _ ≤ |((p 0).1 : ℝ) + x.1| + |((p 0).1 : ℝ)| := by
        simpa using abs_sub_le (((p 0).1 : ℝ) + x.1) 0 ((p 0).1 : ℝ)
      _ ≤ realObjective p x + |((p 0).1 : ℝ)| := by linarith
  · calc
      |x.2| = |(((p 0).2 : ℝ) + x.2) - (p 0).2| := by congr 1; ring
      _ ≤ |((p 0).2 : ℝ) + x.2| + |((p 0).2 : ℝ)| := by
        simpa using abs_sub_le (((p 0).2 : ℝ) + x.2) 0 ((p 0).2 : ℝ)
      _ ≤ realObjective p x + |((p 0).2 : ℝ)| := by linarith

/-- Coercivity is expressed as bounded sublevels, including levels below zero.
The bound uses just one pair; seven terms strengthen it. -/
theorem realObjective_bounded_sublevels (p : SevenPairs) (L : ℝ) :
    InBoundedBox {x | realObjective p x ≤ L} := by
  let R := |L| + |((p 0).1 : ℝ)| + |((p 0).2 : ℝ)|
  refine ⟨R, by dsimp [R]; positivity, ?_⟩
  intro x hx
  change realObjective p x ≤ L at hx
  have hb := realObjective_coordinate_bounds p x
  have hL : L ≤ |L| := le_abs_self L
  have ha0 := abs_nonneg ((p 0).1 : ℝ)
  have hb0 := abs_nonneg ((p 0).2 : ℝ)
  dsimp [R]
  constructor <;> linarith

abbrev LineIndex := Fin 7 × Fin 3
def baseLine (p : SevenPairs) (i : LineIndex) : PlaneForm :=
  if i.2 = 0 then ⟨1, 0, (p i.1).1⟩
  else if i.2 = 1 then ⟨0, 1, (p i.1).2⟩
  else ⟨1, 1, (p i.1).1 + (p i.1).2⟩
def cellLine (p : SevenPairs) (s : LineIndex → Bool) (i : LineIndex) : PlaneForm :=
  if s i then negateForm (baseLine p i) else baseLine p i
def signAt (p : SevenPairs) (x : PlanePoint) (i : LineIndex) : Bool :=
  decide (0 ≤ formValue (baseLine p i) x)
def objectiveLine (p : SevenPairs) (s : LineIndex → Bool) : PlaneForm :=
  ⟨(∑ i : LineIndex, if s i then (baseLine p i).a else -(baseLine p i).a) / 2,
   (∑ i : LineIndex, if s i then (baseLine p i).b else -(baseLine p i).b) / 2,
   (∑ i : LineIndex, if s i then (baseLine p i).c else -(baseLine p i).c) / 2⟩

theorem point_in_its_cell (p : SevenPairs) (x : PlanePoint) :
    x ∈ planePolyhedron (cellLine p (signAt p x)) := by
  intro i
  by_cases h : 0 ≤ formValue (baseLine p i) x
  · simp [cellLine, signAt, h, formValue_negate]
  · simp [cellLine, signAt, h]; exact le_of_not_ge h

/-- The half-sum is affine on the entire CLOSED sign cell, including its edges.
This is an equality to a concrete affine form, not a generic affinity premise. -/
theorem objective_affine_on_cell (p : SevenPairs) (s : LineIndex → Bool)
    (x : PlanePoint) (hx : x ∈ planePolyhedron (cellLine p s)) :
    realObjective p x = formValue (objectiveLine p s) x := by
  have hs : ∀ i : LineIndex,
      |formValue (baseLine p i) x| =
        if s i then formValue (baseLine p i) x else -formValue (baseLine p i) x := by
    intro i
    have hi := hx i
    cases hsi : s i
    · have hi' : formValue (baseLine p i) x ≤ 0 := by
        simpa [cellLine, hsi] using hi
      simpa only [hsi, Bool.false_eq_true, ↓reduceIte] using abs_of_nonpos hi'
    · have hi' : 0 ≤ formValue (baseLine p i) x := by
        simpa [cellLine, hsi, formValue_negate] using hi
      simpa only [hsi, ↓reduceIte] using abs_of_nonneg hi'
  have hhalf : 2 * realObjective p x =
      ∑ i : LineIndex, |formValue (baseLine p i) x| := by
    rw [realObjective, Finset.mul_sum]
    simp_rw [twice_realHexNorm]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro k hk
    simp [baseLine, formValue, Fin.sum_univ_succ, add_comm, add_left_comm, add_assoc]
  rw [Finset.sum_congr rfl (fun i _ => hs i)] at hhalf
  have hlin : 2 * formValue (objectiveLine p s) x =
      ∑ i : LineIndex, if s i then formValue (baseLine p i) x
        else -formValue (baseLine p i) x := by
    have hi : ∀ i : LineIndex,
        (if s i then formValue (baseLine p i) x else -formValue (baseLine p i) x) =
        (if s i then (baseLine p i).a else -(baseLine p i).a) * x.1 +
        (if s i then (baseLine p i).b else -(baseLine p i).b) * x.2 +
        (if s i then (baseLine p i).c else -(baseLine p i).c) := by
      intro i
      cases hsi : s i <;> simp [hsi, formValue] <;> ring
    simp_rw [hi]
    simp only [objectiveLine, formValue, Finset.sum_add_distrib, ← Finset.sum_mul]
    ring
  linarith

def minimumFaceForms {ι : Type*} (forms : ι → PlaneForm)
    (objective : PlaneForm) (L : ℝ) : Sum ι (Fin 2) → PlaneForm
  | Sum.inl i => forms i
  | Sum.inr h => if h = 0 then offsetForm objective (-L)
    else negateForm (offsetForm objective (-L))

theorem minimumFace_membership {ι : Type*} (forms : ι → PlaneForm)
    (objective : PlaneForm) (L : ℝ) (x : PlanePoint) :
    x ∈ planePolyhedron (minimumFaceForms forms objective L) ↔
      x ∈ planePolyhedron forms ∧ formValue objective x = L := by
  constructor
  · intro h
    have h0 := h (Sum.inr (0 : Fin 2))
    have h1 := h (Sum.inr (1 : Fin 2))
    simp [minimumFaceForms, formValue_offset, formValue_negate] at h0 h1
    exact ⟨fun i => h (Sum.inl i), by linarith⟩
  · rintro ⟨hx, hvalue⟩ (i | h)
    · exact hx i
    · fin_cases h <;>
        simp [minimumFaceForms, formValue_offset, formValue_negate, hvalue]

/-- An extreme point of the minimum face is a vertex of the containing cell.
This works when the minimum face is an edge or a polygon; no uniqueness of
the minimizer is assumed. -/
theorem minimum_face_extreme_is_cell_extreme {ι : Type*} (forms : ι → PlaneForm)
    (objective : PlaneForm) (L : ℝ)
    (hlower : ∀ y ∈ planePolyhedron forms, L ≤ formValue objective y)
    (x : PlanePoint)
    (hx : MidpointExtreme (planePolyhedron (minimumFaceForms forms objective L)) x) :
    MidpointExtreme (planePolyhedron forms) x := by
  have hxmem := (minimumFace_membership forms objective L x).mp hx.1
  refine ⟨hxmem.1, ?_⟩
  intro u hu v hv hmid
  have huL := hlower u hu
  have hvL := hlower v hv
  have havg := formValue_midpoint objective u v
  rw [← hmid, hxmem.2] at havg
  have hueq : formValue objective u = L := by linarith
  have hveq : formValue objective v = L := by linarith
  exact hx.2 u ((minimumFace_membership forms objective L u).mpr ⟨hu, hueq⟩)
    v ((minimumFace_membership forms objective L v).mpr ⟨hv, hveq⟩) hmid

def intersectionIndex (i j : LineIndex) : CandidateIndex :=
  if i.2 = 0 then if j.2 = 1 then (0, i.1, j.1) else (1, i.1, j.1)
  else if i.2 = 1 then if j.2 = 0 then (0, j.1, i.1) else (2, i.1, j.1)
  else if j.2 = 0 then (1, j.1, i.1) else (2, j.1, i.1)

/-- Every intersection of two nonparallel arrangement lines is the cast of
one of the explicitly integral candidates. Parallel lines are excluded. -/
theorem active_lines_are_candidate (p : SevenPairs) (i j : LineIndex)
    (hne : i.2 ≠ j.2) (x : PlanePoint)
    (hi : formValue (baseLine p i) x = 0)
    (hj : formValue (baseLine p j) x = 0) :
    x = (((candidate p (intersectionIndex i j)).1 : ℝ),
      ((candidate p (intersectionIndex i j)).2 : ℝ)) := by
  rcases i with ⟨ki, ti⟩
  rcases j with ⟨kj, tj⟩
  fin_cases ti <;> fin_cases tj
  all_goals simp [baseLine, formValue] at hi hj
  all_goals simp [intersectionIndex, candidate] at hne ⊢
  all_goals apply Prod.ext <;> push_cast <;> linarith

theorem independent_cell_lines_have_different_kinds (p : SevenPairs)
    (s : LineIndex → Bool) (i j : LineIndex)
    (hdet : normalDet (cellLine p s i) (cellLine p s j) ≠ 0) : i.2 ≠ j.2 := by
  intro he
  rcases i with ⟨ki, ti⟩
  rcases j with ⟨kj, tj⟩
  simp only [Prod.snd] at he
  subst tj
  have hz : normalDet (cellLine p s (ki, ti)) (cellLine p s (kj, ti)) = 0 := by
    unfold cellLine baseLine normalDet negateForm
    split_ifs <;> simp_all <;> ring
  exact hdet hz

/-- Conditional solely on the three general plane facts. The source derives
boundedness, closed-cell affinity, minimum-face membership and its extreme
point transfer; it then identifies the independent active lines explicitly. -/
theorem real_minimum_at_integral_candidate (d : PrimitivePlaneDuty) (p : SevenPairs) :
    ∃ c ∈ candidatePoints p, ∀ y : PlanePoint,
      realObjective p ((c.1 : ℝ), (c.2 : ℝ)) ≤ realObjective p y := by
  obtain ⟨x, hx⟩ := d.continuous_bounded_sublevels_attain (realObjective p)
    (realObjective_continuous p) (realObjective_bounded_sublevels p)
  let s := signAt p x
  let forms := cellLine p s
  let objective := objectiveLine p s
  let L := realObjective p x
  have hcell : x ∈ planePolyhedron forms := point_in_its_cell p x
  have haff : ∀ y ∈ planePolyhedron forms,
      realObjective p y = formValue objective y := objective_affine_on_cell p s
  have hface : (planePolyhedron (minimumFaceForms forms objective L)).Nonempty := by
    refine ⟨x, (minimumFace_membership forms objective L x).mpr ⟨hcell, ?_⟩⟩
    exact (haff x hcell).symm
  have hbound : InBoundedBox (planePolyhedron (minimumFaceForms forms objective L)) := by
    obtain ⟨R, hR, hbox⟩ := realObjective_bounded_sublevels p L
    refine ⟨R, hR, ?_⟩
    intro y hy
    have hm := (minimumFace_membership forms objective L y).mp hy
    exact hbox y (by change realObjective p y ≤ L; rw [haff y hm.1, hm.2])
  obtain ⟨v, hv⟩ := primitive_bounded_extreme_type0 d
    (minimumFaceForms forms objective L) hface hbound
  have hvcell : MidpointExtreme (planePolyhedron forms) v :=
    minimum_face_extreme_is_cell_extreme forms objective L
      (fun y hy => by rw [← haff y hy]; exact hx y) v hv
  obtain ⟨i, j, hdet, hi, hj⟩ := primitive_active_independent_type0 d forms v hvcell
  have hne : i.2 ≠ j.2 := independent_cell_lines_have_different_kinds p s i j hdet
  have hi' : formValue (baseLine p i) v = 0 := by
    cases hsi : s i <;> simpa [forms, cellLine, hsi, formValue_negate] using hi
  have hj' : formValue (baseLine p j) v = 0 := by
    cases hsj : s j <;> simpa [forms, cellLine, hsj, formValue_negate] using hj
  let c := candidate p (intersectionIndex i j)
  have hc : c ∈ candidatePoints p :=
    Finset.mem_image.mpr ⟨intersectionIndex i j, Finset.mem_univ _, rfl⟩
  have hvc : v = ((c.1 : ℝ), (c.2 : ℝ)) := active_lines_are_candidate p i j hne v hi' hj'
  have hvvalue : realObjective p v = L := by
    have hm := (minimumFace_membership forms objective L v).mp hv.1
    rw [haff v hm.1, hm.2]
  refine ⟨c, hc, ?_⟩
  intro y
  rw [← hvc, hvvalue]
  exact hx y

theorem realObjective_integer (p : SevenPairs) (A B : ℤ) :
    realObjective p ((A : ℝ), (B : ℝ)) = (shiftObjective p A B : ℝ) := by
  simp [realObjective, realHexNorm, shiftObjective, hexNorm, Int.cast_sum,
    Int.cast_max, Int.cast_abs, Int.cast_add, max_assoc]

theorem integer_minimum_at_candidate (d : PrimitivePlaneDuty) (p : SevenPairs) :
    ∃ c ∈ candidatePoints p, ∀ A B : ℤ,
      shiftObjective p c.1 c.2 ≤ shiftObjective p A B := by
  obtain ⟨c, hc, hmin⟩ := real_minimum_at_integral_candidate d p
  refine ⟨c, hc, ?_⟩
  intro A B
  have h := hmin ((A : ℝ), (B : ℝ))
  rw [realObjective_integer, realObjective_integer] at h
  exact_mod_cast h

end

end Partials.UnitDistance.Words
