import Partials.ParityAlgorithms.PathModel
import Mathlib.Data.Finset.Max

/-! Completed single-source pivots, fixed original anchors and finite rank
budgets. The remaining no-loose/tight-walk induction is exposed precisely;
no completed-pivot count is assumed as an algorithm hypothesis. -/
namespace Partials.ParityAlgorithms.Path

noncomputable def successors {n : Nat} {A : Arena n} (τ : OddPolicy A)
    (v : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (SelectedEdge τ v)

theorem successors_nonempty {n : Nat} {A : Arena n} (τ : OddPolicy A)
    (v : Fin n) : (successors τ v).Nonempty := by
  classical
  by_cases he : A.even v = true
  · obtain ⟨w, hw⟩ := edge_total A v
    exact ⟨w, by simp [successors, (selected_even_iff τ v w he).mpr hw]⟩
  · have ho : A.even v = false := by cases hv : A.even v <;> simp_all
    exact ⟨τ.choose ⟨v, ho⟩, by simp [successors, selected_odd_iff τ _ _ ho]⟩

def foldMin (values : List Nat) (ell : Nat) : Nat := values.foldr min ell

theorem foldMin_bounded (values : List Nat) (ell : Nat) : foldMin values ell ≤ ell := by
  induction values with
  | nil => exact le_refl ell
  | cons a xs ih => exact (min_le_right a (foldMin xs ell)).trans ih

theorem foldMin_le_member (values : List Nat) (ell a : Nat)
    (h : a ∈ values) : foldMin values ell ≤ a := by
  induction values with
  | nil => simp at h
  | cons b xs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih h)

theorem foldMin_binary (values : List Nat) (ell : Nat)
    (h : ∀ a ∈ values, a = 0 ∨ a = ell) :
    foldMin values ell = 0 ∨ foldMin values ell = ell := by
  induction values with
  | nil => exact Or.inr rfl
  | cons a xs ih =>
    have ha := h a (by simp)
    have hx := ih (fun b hb => h b (by simp [hb]))
    change min a (foldMin xs ell) = 0 ∨ min a (foldMin xs ell) = ell
    rcases ha with rfl | rfl <;> rcases hx with hx | hx <;>
      rw [hx] <;> simp

theorem foldMin_map_monotone {α : Type*} (values : List α) (f g : α → Nat)
    (ell : Nat) (h : ∀ a ∈ values, f a ≤ g a) :
    foldMin (values.map f) ell ≤ foldMin (values.map g) ell := by
  induction values with
  | nil => exact le_refl ell
  | cons a xs ih =>
    have ha := h a (by simp)
    have hx := ih (fun b hb => h b (by simp [hb]))
    exact min_le_min ha hx

theorem foldMin_le_iff (values : List Nat) (ell t : Nat) :
    foldMin values ell ≤ t ↔ ell ≤ t ∨ ∃ a ∈ values, a ≤ t := by
  induction values with
  | nil => simp [foldMin]
  | cons a xs ih =>
    change min a (foldMin xs ell) ≤ t ↔ _
    rw [min_le_iff, ih]
    simp only [List.mem_cons]
    constructor
    · rintro (ha | ht | ⟨b, hb, ht⟩)
      · exact Or.inr ⟨a, Or.inl rfl, ha⟩
      · exact Or.inl ht
      · exact Or.inr ⟨b, Or.inr hb, ht⟩
    · rintro (ht | ⟨b, rfl | hb, ht⟩)
      · exact Or.inr (Or.inl ht)
      · exact Or.inl ht
      · exact Or.inr (Or.inr ⟨b, hb, ht⟩)

noncomputable def originalF {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) (x : Vector n) (v : Fin n) : Nat :=
  max (x v) (foldMin ((successors τ v).toList.map (theta A ell x v)) ell)

def replace {n : Nat} (x : Vector n) (v : Fin n) (rank : Nat) : Vector n :=
  Function.update x v rank

theorem originalF_inflationary {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) (x : Vector n) (v : Fin n) : x v ≤ originalF ell τ x v :=
  le_max_left _ _

theorem originalF_bounded {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) {x : Vector n} (hx : ValidVector ell x) (v : Fin n) :
    originalF ell τ x v ≤ ell := by
  exact max_le (hx v) (foldMin_bounded _ ell)

theorem originalF_monotone {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) {x y : Vector n} (hxy : VectorLE x y) (v : Fin n) :
    originalF ell τ x v ≤ originalF ell τ y v := by
  apply max_le_max (hxy v)
  exact foldMin_map_monotone (successors τ v).toList
    (theta A ell x v) (theta A ell y v) ell
    (fun w _ => theta_monotone A ell hxy v w)

theorem feasible_iff_selected_witness {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) (x : Vector n) : Feasible ell τ x ↔
    ∀ v, ∃ w, SelectedEdge τ v w ∧ Satisfied A ell x v w := by
  constructor
  · intro h v
    by_cases he : A.even v = true
    · have hv := h v
      simp only [dif_pos he] at hv
      obtain ⟨w, hw, hs⟩ := hv
      exact ⟨w, (selected_even_iff τ v w he).mpr hw, hs⟩
    · have ho : A.even v = false := by cases hv : A.even v <;> simp_all
      have hv := h v
      simp only [dif_neg he] at hv
      exact ⟨τ.choose ⟨v, ho⟩, (selected_odd_iff τ v _ ho).mpr rfl, hv ho⟩
  · intro h v
    by_cases he : A.even v = true
    · simp only [dif_pos he]
      obtain ⟨w, hw, hs⟩ := h v
      exact ⟨w, hw.1, hs⟩
    · simp only [dif_neg he]
      intro ho
      obtain ⟨w, hw, hs⟩ := h v
      simpa [hw.2 ho] using hs

theorem originalF_fixed_iff_witness {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) {x : Vector n} (hx : ValidVector ell x) (v : Fin n) :
    originalF ell τ x v = x v ↔
      ∃ w, SelectedEdge τ v w ∧ Satisfied A ell x v w := by
  classical
  constructor
  · intro hf
    have hmin : foldMin ((successors τ v).toList.map (theta A ell x v)) ell ≤ x v := by
      calc
        _ ≤ originalF ell τ x v := le_max_right _ _
        _ = x v := hf
    rcases (foldMin_le_iff _ ell (x v)).mp hmin with ht | ⟨a, ha, hax⟩
    · obtain ⟨w, hw⟩ := successors_nonempty τ v
      refine ⟨w, ?_, ?_⟩
      · simpa [successors] using hw
      · apply (satisfied_iff_threshold A ell hx v w).mpr
        exact (theta_bounded A ell x v w).trans ht
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp ha
      refine ⟨w, ?_, (satisfied_iff_threshold A ell hx v w).mpr hax⟩
      simpa [successors] using hw
  · rintro ⟨w, hw, hs⟩
    have hmem : theta A ell x v w ∈ (successors τ v).toList.map (theta A ell x v) := by
      apply List.mem_map.mpr
      exact ⟨w, by simpa [successors] using hw, rfl⟩
    have hmin := (foldMin_le_member _ ell _ hmem).trans
      ((satisfied_iff_threshold A ell hx v w).mp hs)
    exact max_eq_left hmin

theorem original_fixed_iff_feasible {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) {x : Vector n} (hx : ValidVector ell x) :
    (∀ v, originalF ell τ x v = x v) ↔ Feasible ell τ x := by
  rw [feasible_iff_selected_witness]
  constructor <;> intro h v
  · exact (originalF_fixed_iff_witness ell τ hx v).mp (h v)
  · exact (originalF_fixed_iff_witness ell τ hx v).mpr (h v)

def Eligible {n : Nat} (A : Arena n) (ell : Nat) (x : Vector n)
    (v w : Fin n) : Prop :=
  A.even v = false ∧ Edge A v w ∧ ¬ Satisfied A ell x v w

def NoLoose {n : Nat} {A : Arena n} (ell : Nat) (τ : OddPolicy A)
    (x : Vector n) : Prop := ∀ v w, SelectedEdge τ v w → ¬ Loose A ell x v w

def BinaryTwo {n : Nat} (A : Arena n) (ell : Nat) (x : Vector n) : Prop :=
  ∀ v, A.priority v = .two → x v = 0 ∨ x v = ell

theorem theta_two_binary {n : Nat} (A : Arena n) (ell : Nat)
    (x : Vector n) (v w : Fin n) (hp : A.priority v = .two) :
    theta A ell x v w = 0 ∨ theta A ell x v w = ell := by
  unfold theta
  split
  · simp [hp]
  · simp only [hp]
    split <;> simp

theorem originalF_two_binary {n : Nat} {A : Arena n} (ell : Nat)
    (τ : OddPolicy A) (x : Vector n) (hbinary : BinaryTwo A ell x)
    (v : Fin n) (hp : A.priority v = .two) :
    originalF ell τ x v = 0 ∨ originalF ell τ x v = ell := by
  have hfold := foldMin_binary
    ((successors τ v).toList.map (theta A ell x v)) ell (by
      intro a ha
      obtain ⟨w, _, rfl⟩ := List.mem_map.mp ha
      exact theta_two_binary A ell x v w hp)
  rcases hbinary v hp with h | h <;> rcases hfold with hf | hf <;>
    simp [originalF, h, hf]

/-- A violated original arc cannot become satisfied while its source stays
fixed and its target only increases. Covers both endpoint loop priorities. -/
theorem violated_source_must_increase {n : Nat} (A : Arena n) (ell : Nat)
    {x y : Vector n} (hx : ValidVector ell x) (hy : ValidVector ell y)
    (hxy : VectorLE x y) (v w : Fin n)
    (hviolated : ¬ Satisfied A ell x v w)
    (hnew : Satisfied A ell y v w) : x v < y v := by
  have hold : x v < theta A ell x v w := by
    have hn := (satisfied_iff_threshold A ell hx v w).not.mp hviolated
    omega
  have htheta := theta_monotone A ell hxy v w
  have hnewle := (satisfied_iff_threshold A ell hy v w).mp hnew
  omega

/-- The new policy differs at this original Odd source only. Values at all
other original Odd vertices remain present, reachable or otherwise. -/
def IsSinglePivot {n : Nat} {A : Arena n} (ell : Nat)
    (old new : OddPolicy A) (x y : Vector n) (v w : Fin n) : Prop :=
  Eligible A ell x v w ∧
    (∀ ho : A.even v = false, new.choose ⟨v, ho⟩ = w) ∧
    (∀ u, u.val ≠ v → new.choose u = old.choose u) ∧
    IsEvaluation ell new x y

theorem single_pivot_strict_source {n : Nat} {A : Arena n} {ell : Nat}
    {old new : OddPolicy A} {x y : Vector n} {v w : Fin n}
    (hx : ValidVector ell x) (hp : IsSinglePivot ell old new x y v w) :
    x v < y v := by
  have ho := hp.1.1
  have hfeas := hp.2.2.2.2.2.1 v
  have hn : ¬ A.even v = true := by simp [ho]
  simp only [dif_neg hn] at hfeas
  have hs : Satisfied A ell y v w := by
    simpa [hp.2.1 ho] using hfeas ho
  exact violated_source_must_increase A ell hx hp.2.2.2.1
    hp.2.2.2.2.1 v w hp.1.2.2 hs

inductive Completed {n : Nat} (A : Arena n) (ell : Nat) :
    OddPolicy A → Vector n → Prop where
  | initial (τ x) : IsEvaluation ell τ (fun _ => 0) x → Completed A ell τ x
  | pivot (old new x y v w) : Completed A ell old x →
      IsSinglePivot ell old new x y v w → Completed A ell new y

def ReachableCall {n : Nat} (A : Arena n) (ell : Nat)
    (τ : OddPolicy A) (floor : Vector n) : Prop :=
  floor = (fun _ => 0) ∨
    ∃ old x v w, Completed A ell old x ∧ floor = x ∧
      Eligible A ell x v w ∧
      (∀ ho : A.even v = false, τ.choose ⟨v, ho⟩ = w) ∧
      (∀ u, u.val ≠ v → τ.choose u = old.choose u)

/-- Fixed candidates use original priority-two positions, never the current
policy or the set of finite-ranked vertices. -/
noncomputable def leftPositions {n : Nat} (A : Arena n) (v : Fin n) : Finset Nat := by
  classical
  exact (Finset.univ.filter fun u : Fin n => u.val < v.val ∧ A.priority u = .two).image Fin.val

noncomputable def rightPositions {n : Nat} (A : Arena n) (v : Fin n) : Finset Nat := by
  classical
  exact (Finset.univ.filter fun u : Fin n => v.val < u.val ∧ A.priority u = .two).image Fin.val

noncomputable def leftAnchor {n : Nat} (A : Arena n) (v : Fin n) : Option Nat := by
  classical
  exact if h : (leftPositions A v).Nonempty then some ((leftPositions A v).max' h) else none

noncomputable def rightAnchor {n : Nat} (A : Arena n) (v : Fin n) : Option Nat := by
  classical
  exact if h : (rightPositions A v).Nonempty then some ((rightPositions A v).min' h) else none

def optionSingleton (x : Option Nat) : Finset Nat :=
  match x with | none => ∅ | some a => {a}

noncomputable def anchorDistances {n : Nat} (A : Arena n) (v : Fin n) : Finset Nat :=
  optionSingleton ((leftAnchor A v).map (fun a => v.val - a)) ∪
    optionSingleton ((rightAnchor A v).map (fun a => a - v.val))

theorem optionSingleton_card (x : Option Nat) : (optionSingleton x).card ≤ 1 := by
  cases x <;> simp [optionSingleton]

theorem anchorDistances_at_most_two {n : Nat} (A : Arena n) (v : Fin n) :
    (anchorDistances A v).card ≤ 2 := by
  have hu := Finset.card_union_le
    (optionSingleton ((leftAnchor A v).map (fun a => v.val - a)))
    (optionSingleton ((rightAnchor A v).map (fun a => a - v.val)))
  have hl := optionSingleton_card ((leftAnchor A v).map (fun a => v.val - a))
  have hr := optionSingleton_card ((rightAnchor A v).map (fun a => a - v.val))
  dsimp [anchorDistances]; omega

noncomputable def completedDomain {n : Nat} (A : Arena n) (ell : Nat) (v : Fin n) : Finset Nat :=
  match A.priority v with
  | .one => insert ell (anchorDistances A v)
  | .two => {0, ell}

def rankPosition (domain : Finset Nat) (r : Nat) : Nat := (domain.filter (· < r)).card

theorem rankPosition_monotone (D : Finset Nat) {x y : Nat} (hxy : x ≤ y) :
    rankPosition D x ≤ rankPosition D y := by
  apply Finset.card_le_card
  intro z hz
  simp only [Finset.mem_filter] at hz ⊢
  exact ⟨hz.1, lt_of_lt_of_le hz.2 hxy⟩

theorem rankPosition_strict (D : Finset Nat) {x y : Nat}
    (hx : x ∈ D) (hxy : x < y) : rankPosition D x < rankPosition D y := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨?_, ?_⟩
  · intro z hz
    simp only [Finset.mem_filter] at hz ⊢
    exact ⟨hz.1, lt_trans hz.2 hxy⟩
  · intro heq
    have hy : x ∈ D.filter (· < y) := by simp [hx, hxy]
    have hx' : x ∈ D.filter (· < x) := heq.symm ▸ hy
    simpa using hx'

theorem rankPosition_member_budget (D : Finset Nat) {x : Nat} (hx : x ∈ D) :
    rankPosition D x + 1 ≤ D.card := by
  have hsub : D.filter (· < x) ⊂ D := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro heq
    have hbad : x ∈ D.filter (· < x) := heq.symm ▸ hx
    simpa using hbad
  have := Finset.card_lt_card hsub
  dsimp [rankPosition]; omega

/-- Elementary telescoping of strict completed-source potential progress.
Instantiating P by the sum of original Odd domain positions needs the
no-loose/tight-anchor primitives, explicitly retained in the duty register. -/
theorem strict_potential_telescopes (P : Nat → Nat) (I : Nat)
    (hstep : ∀ k < I, P k + 1 ≤ P (k + 1)) : P 0 + I ≤ P I := by
  induction I with
  | zero => simp
  | succ I ih =>
    have hprev := ih (fun k hk => hstep k (by omega))
    have hlast := hstep I (by omega)
    omega

theorem potential_bound_counts_pivots (P : Nat → Nat) (I budget : Nat)
    (hstep : ∀ k < I, P k + 1 ≤ P (k + 1)) (hcap : P I ≤ budget) :
    I ≤ budget := by
  have := strict_potential_telescopes P I hstep
  omega

theorem additive_bound_arithmetic (I oddOne oddTwo n ell : Nat)
    (hcount : I ≤ 2 * oddOne + oddTwo) (hodd : oddOne + oddTwo ≤ n)
    (hleaves : n ≤ ell) : I ≤ 2 * n ∧ I ≤ n + ell := by omega

end Partials.ParityAlgorithms.Path
