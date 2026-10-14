import Partials.ParityAlgorithms.TreeUpper
import Mathlib.Tactic.FinCases
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Fin

/-! P5-THRESHOLD/HEIGHT2/T31. The lower obstruction keeps original
depth-one parents and original depth-two nodes. Threshold degrees count
depth-TWO nodes; arbitrary root arity, degree-one nodes and degrees >7
are retained. This file proves the two ordered contradictions from precise
count/representation extraction primitives, not from an assumed M=31. -/

namespace Partials.ParityAlgorithms.Trees

structure DegreeSystem (nodeCount : Nat) where
  parent : Fin nodeCount → Nat
  sibling : Fin nodeCount → Nat
  degree : Fin nodeCount → Nat
  positive : ∀ x, 0 < degree x
  address_unique : ∀ x y, parent x = parent y → sibling x = sibling y → x = y

def LargeNodes {N : Nat} (D : DegreeSystem N) (delta : Nat) : Finset (Fin N) :=
  Finset.univ.filter (fun x => delta ≤ D.degree x)

def ThresholdCount {N : Nat} (D : DegreeSystem N) (delta : Nat) : Nat :=
  (LargeNodes D delta).card

def OriginalLeafSum {N : Nat} (D : DegreeSystem N) : Nat :=
  ∑ x : Fin N, D.degree x

def FirstSevenCountSum {N : Nat} (D : DegreeSystem N) : Nat :=
  ThresholdCount D 1 + ThresholdCount D 2 + ThresholdCount D 3 +
    ThresholdCount D 4 + ThresholdCount D 5 + ThresholdCount D 6 + ThresholdCount D 7

theorem threshold_count_antitone {N : Nat} (D : DegreeSystem N)
    {a b : Nat} (hab : a ≤ b) : ThresholdCount D b ≤ ThresholdCount D a := by
  apply Finset.card_le_card
  intro x hx
  simp only [LargeNodes, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact le_trans hab hx

theorem threshold_count_lower_of_injection {N k delta : Nat} (D : DegreeSystem N)
    (f : Fin k → Fin N) (hinj : Function.Injective f)
    (hlarge : ∀ i, delta ≤ D.degree (f i)) : k ≤ ThresholdCount D delta := by
  let image : Finset (Fin N) := Finset.univ.image f
  have hc : image.card = k := by
    simp [image, Finset.card_image_of_injective, hinj]
  have hs : image ⊆ LargeNodes D delta := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    simp [LargeNodes, hlarge i]
  rw [← hc]
  exact Finset.card_le_card hs

theorem three_large_lower {N : Nat} (D : DegreeSystem N) (a b c : Fin N)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : 3 ≤ D.degree a) (hb : 3 ≤ D.degree b) (hc : 3 ≤ D.degree c) :
    3 ≤ ThresholdCount D 3 := by
  apply threshold_count_lower_of_injection D (![a, b, c] : Fin 3 → Fin N)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  · intro i; fin_cases i <;> simp_all

theorem four_large_lower {N : Nat} (D : DegreeSystem N) (a b c d : Fin N)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : 3 ≤ D.degree a) (hb : 3 ≤ D.degree b)
    (hc : 3 ≤ D.degree c) (hd : 3 ≤ D.degree d) :
    4 ≤ ThresholdCount D 3 := by
  apply threshold_count_lower_of_injection D (![a, b, c, d] : Fin 4 → Fin N)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  · intro i; fin_cases i <;> simp_all

theorem five_large_lower {N : Nat} (D : DegreeSystem N) (a b c d e : Fin N)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (ha : 3 ≤ D.degree a) (hb : 3 ≤ D.degree b)
    (hc : 3 ≤ D.degree c) (hd : 3 ≤ D.degree d) (he : 3 ≤ D.degree e) :
    5 ≤ ThresholdCount D 3 := by
  apply threshold_count_lower_of_injection D (![a, b, c, d, e] : Fin 5 → Fin N)
  · intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  · intro i; fin_cases i <;> simp_all

def WithinPattern {N : Nat} (D : DegreeSystem N) (a b : Nat) : Prop :=
  ∃ u v, D.parent u = D.parent v ∧ D.sibling u < D.sibling v ∧
    a ≤ D.degree u ∧ b ≤ D.degree v

def AcrossPattern {N : Nat} (D : DegreeSystem N) (a b : Nat) : Prop :=
  ∃ u v, D.parent u < D.parent v ∧ a ≤ D.degree u ∧ b ≤ D.degree v

def MixedPairBefore {N : Nat} (D : DegreeSystem N) : Prop :=
  ∃ u v w, u ≠ v ∧ D.parent u = D.parent v ∧
    D.parent u < D.parent w ∧ 2 ≤ D.degree u ∧ 2 ≤ D.degree v ∧ 3 ≤ D.degree w

def MixedPairAfter {N : Nat} (D : DegreeSystem N) : Prop :=
  ∃ w u v, u ≠ v ∧ D.parent u = D.parent v ∧
    D.parent w < D.parent u ∧ 3 ≤ D.degree w ∧ 2 ≤ D.degree u ∧ 2 ≤ D.degree v

structure RequiredOrderedPatterns {N : Nat} (D : DegreeSystem N) : Prop where
  within34 : WithinPattern D 3 4
  within43 : WithinPattern D 4 3
  across33 : AcrossPattern D 3 3
  pairThenThree : MixedPairBefore D
  threeThenPair : MixedPairAfter D
  across34 : AcrossPattern D 3 4
  across43 : AcrossPattern D 4 3

def UniqueMultiParent {N : Nat} (D : DegreeSystem N) (C : Nat) : Prop :=
  ∀ u v, u ≠ v → 2 ≤ D.degree u → 2 ≤ D.degree v →
    D.parent u = D.parent v → D.parent u = C

structure ThreeOrderedChildren {N : Nat} (D : DegreeSystem N) where
  left : Fin N
  center : Fin N
  right : Fin N
  commonLeft : D.parent left = D.parent center
  commonRight : D.parent right = D.parent center
  before : D.sibling left < D.sibling center
  after : D.sibling center < D.sibling right
  leftLarge : 3 ≤ D.degree left
  centerLarge : 4 ≤ D.degree center
  rightLarge : 3 ≤ D.degree right

theorem case_one_forces_four {N : Nat} (D : DegreeSystem N)
    (triple : ThreeOrderedChildren D) (across : AcrossPattern D 3 3) :
    4 ≤ ThresholdCount D 3 := by
  obtain ⟨a, b, hab, ha, hb⟩ := across
  have hxy : triple.left ≠ triple.center := by
    intro h; have := triple.before; simp [h] at this
  have hxz : triple.left ≠ triple.right := by
    intro h; have h1 := triple.before; have h2 := triple.after; simp [h] at h1; omega
  have hyz : triple.center ≠ triple.right := by
    intro h; have := triple.after; simp [h] at this
  have useOutside : ∀ w, D.parent w ≠ D.parent triple.center → 3 ≤ D.degree w →
      4 ≤ ThresholdCount D 3 := by
    intro w hw hd
    have hn1 : triple.left ≠ w := by intro he; apply hw; rw [← he]; exact triple.commonLeft
    have hn2 : triple.center ≠ w := by intro he; apply hw; rw [← he]
    have hn3 : triple.right ≠ w := by intro he; apply hw; rw [← he]; exact triple.commonRight
    exact four_large_lower D triple.left triple.center triple.right w
      hxy hxz hn1 hyz hn2 hn3 triple.leftLarge (by have := triple.centerLarge; omega)
      triple.rightLarge hd
  by_cases hap : D.parent a = D.parent triple.center
  · apply useOutside b _ hb
    intro hbp
    omega
  · exact useOutside a hap ha

theorem case_one_middle_forces_five {N : Nat} (D : DegreeSystem N)
    (triple : ThreeOrderedChildren D) {C : Nat}
    (middle : UniqueMultiParent D C)
    (beforePattern : MixedPairBefore D) (afterPattern : MixedPairAfter D) :
    5 ≤ ThresholdCount D 3 := by
  obtain ⟨u, v, after, huv, hparent, hafter, hu, hv, ha⟩ := beforePattern
  obtain ⟨before, x, y, hxy, hp, hbefore, hb, hx, hy⟩ := afterPattern
  have hC : D.parent triple.center = C := by
    have hne : triple.left ≠ triple.center := by
      intro he; have := triple.before; simp [he] at this
    have hm := middle triple.left triple.center hne
      (by have := triple.leftLarge; omega) (by have := triple.centerLarge; omega)
      triple.commonLeft
    exact triple.commonLeft.symm.trans hm
  have huC := middle u v huv hu hv hparent
  have hxC := middle x y hxy hx hy hp
  have beforeC : D.parent before < C := by omega
  have afterC : C < D.parent after := by omega
  have leftC : D.parent triple.left = C := triple.commonLeft.trans hC
  have rightC : D.parent triple.right = C := triple.commonRight.trans hC
  have h12 : triple.left ≠ triple.center := by
    intro he; have := triple.before; simp [he] at this
  have h13 : triple.left ≠ triple.right := by
    intro he; have := triple.before; have := triple.after; simp_all; omega
  have h23 : triple.center ≠ triple.right := by
    intro he; have := triple.after; simp [he] at this
  have unequalParent : ∀ a b : Fin N, D.parent a ≠ D.parent b → a ≠ b := by
    intro a b hab he; exact hab (congrArg D.parent he)
  exact five_large_lower D triple.left triple.center triple.right before after
    h12 h13 (unequalParent _ _ (by omega)) (unequalParent _ _ (by omega))
    h23 (unequalParent _ _ (by omega)) (unequalParent _ _ (by omega))
    (unequalParent _ _ (by omega)) (unequalParent _ _ (by omega))
    (unequalParent _ _ (by omega))
    triple.leftLarge (by have := triple.centerLarge; omega) triple.rightLarge hb ha

/-- Cardinal-three extraction retains exactly two >=3 children in C and
one outside. The two >=4 children are forced to be the two inside by the
opposite ordered within-parent patterns. The interface keeps original nodes. -/
structure CaseTwoClassification {N : Nat} (D : DegreeSystem N) where
  middle : Nat
  outside : Fin N
  outsideParent : D.parent outside ≠ middle
  allHighInMiddle : ∀ x, 4 ≤ D.degree x → D.parent x = middle
  onlyOutside : ∀ x, 3 ≤ D.degree x → D.parent x ≠ middle → x = outside

theorem case_two_order_impossible {N : Nat} (D : DegreeSystem N)
    (classification : CaseTwoClassification D)
    (leftPattern : AcrossPattern D 3 4)
    (rightPattern : AcrossPattern D 4 3) : False := by
  obtain ⟨a, b, hab, ha, hb⟩ := leftPattern
  obtain ⟨c, d, hcd, hc, hd⟩ := rightPattern
  have hbC := classification.allHighInMiddle b hb
  have hcC := classification.allHighInMiddle c hc
  have haOutside : D.parent a ≠ classification.middle := by omega
  have hdOutside : D.parent d ≠ classification.middle := by omega
  have hae := classification.onlyOutside a ha haOutside
  have hde := classification.onlyOutside d hd hdOutside
  have hleft : D.parent classification.outside < classification.middle := by
    rw [← hae]; omega
  have hright : classification.middle < D.parent classification.outside := by
    rw [← hde]; omega
  omega

/-! Precise unfinished count-to-layout extraction, not a lower-bound
conclusion. Cardinal equality and the two listed within-parent patterns
construct each layout; the subsequent contradictions are proved above. -/
structure CountOrderExtractionDuty where
  oneHigh : ∀ N (D : DegreeSystem N), ThresholdCount D 4 = 1 →
    WithinPattern D 3 4 → WithinPattern D 4 3 → Nonempty (ThreeOrderedChildren D)
  twoHigh : ∀ N (D : DegreeSystem N), ThresholdCount D 3 = 3 → ThresholdCount D 4 = 2 →
    (∃ C, UniqueMultiParent D C) → WithinPattern D 3 4 → WithinPattern D 4 3 →
    AcrossPattern D 3 3 → Nonempty (CaseTwoClassification D)

/-! R8-TREE-THRESHOLD-REPRESENTATION: flattening/pruning full-node
embeddings, height-two minima, and equality extraction have not been admitted.
The field middleFive must be derived from an exact retained-parent 1,3,1
threshold row with arbitrary original parent indices retained. -/
structure UniversalThresholdPrimitives where
  encode : (target : HeightThree) → PositiveThree target →
    Σ N, DegreeSystem N
  leaf_sum : ∀ t ht, OriginalLeafSum (encode t ht).2 = NestedLeafCount t
  baseline : ∀ t ht, UniversalThree 7 t →
    let D := (encode t ht).2
    17 ≤ ThresholdCount D 1 ∧ 5 ≤ ThresholdCount D 2 ∧ 3 ≤ ThresholdCount D 3 ∧
      1 ≤ ThresholdCount D 4 ∧ 1 ≤ ThresholdCount D 5 ∧
      1 ≤ ThresholdCount D 6 ∧ 1 ≤ ThresholdCount D 7
  patterns : ∀ t ht, UniversalThree 7 t → RequiredOrderedPatterns (encode t ht).2
  middleFive : ∀ t ht, UniversalThree 7 t → ThresholdCount (encode t ht).2 2 = 5 →
    ∃ C, UniqueMultiParent (encode t ht).2 C

/-! The unrestricted finite tail is stated explicitly; firstSevenCountSum
is only a lower bound and never substitutes for total leaf count. -/
def ThresholdLayerCakeDuty : Prop :=
  ∀ N (D : DegreeSystem N), ∃ maxDegree : Nat,
    (∀ x, D.degree x ≤ maxDegree) ∧
    OriginalLeafSum D = ∑ delta ∈ Finset.Icc 1 maxDegree, ThresholdCount D delta

theorem one_degree_layer_count (degree maxDegree : Nat) (hb : degree ≤ maxDegree) :
    (∑ delta ∈ Finset.Icc 1 maxDegree, if delta ≤ degree then 1 else 0) = degree := by
  have heq : (Finset.Icc 1 maxDegree).filter (fun delta => delta ≤ degree) =
      Finset.Icc 1 degree := by
    ext delta
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  calc
    (∑ delta ∈ Finset.Icc 1 maxDegree, if delta ≤ degree then 1 else 0) =
        ((Finset.Icc 1 maxDegree).filter (fun delta => delta ≤ degree)).card := by
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = (Finset.Icc 1 degree).card := by rw [heq]
    _ = degree := by simp

theorem finite_layer_cake {N : Nat} (D : DegreeSystem N) (maxDegree : Nat)
    (hb : ∀ x, D.degree x ≤ maxDegree) :
    OriginalLeafSum D = ∑ delta ∈ Finset.Icc 1 maxDegree, ThresholdCount D delta := by
  have hc : ∀ delta, ThresholdCount D delta =
      ∑ x : Fin N, if delta ≤ D.degree x then 1 else 0 := by
    intro delta
    rw [ThresholdCount, LargeNodes, Finset.card_eq_sum_ones, Finset.sum_filter]
  simp only [hc]
  rw [Finset.sum_comm]
  simp only [OriginalLeafSum]
  apply Finset.sum_congr rfl
  intro x hx
  exact (one_degree_layer_count (D.degree x) maxDegree (hb x)).symm

theorem threshold_layer_cake_source : ThresholdLayerCakeDuty := by
  intro N D
  let maxDegree := Finset.univ.sup D.degree
  have hb : ∀ x, D.degree x ≤ maxDegree := by
    intro x
    exact Finset.le_sup (Finset.mem_univ x)
  exact ⟨maxDegree, hb, finite_layer_cake D maxDegree hb⟩

theorem finite_first_seven_leaves {N : Nat} (D : DegreeSystem N) :
    FirstSevenCountSum D ≤ OriginalLeafSum D := by
  have hc : ∀ delta, ThresholdCount D delta =
      ∑ x : Fin N, if delta ≤ D.degree x then 1 else 0 := by
    intro delta
    rw [ThresholdCount, LargeNodes, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hsum : FirstSevenCountSum D =
      ∑ x : Fin N,
        ((if 1 ≤ D.degree x then 1 else 0) + (if 2 ≤ D.degree x then 1 else 0) +
         (if 3 ≤ D.degree x then 1 else 0) + (if 4 ≤ D.degree x then 1 else 0) +
         (if 5 ≤ D.degree x then 1 else 0) + (if 6 ≤ D.degree x then 1 else 0) +
         (if 7 ≤ D.degree x then 1 else 0)) := by
    simp [FirstSevenCountSum, hc, Finset.sum_add_distrib]
  rw [hsum]
  apply Finset.sum_le_sum
  intro x hx
  split_ifs <;> omega

theorem all_targets_at_least_thirty_one (primitives : UniversalThresholdPrimitives)
    (extract : CountOrderExtractionDuty) (target : HeightThree)
    (hu : UniversalThree 7 target) : 31 ≤ NestedLeafCount target := by
  by_contra hnot
  have hL : NestedLeafCount target ≤ 30 := by omega
  let D := (primitives.encode target hu.1).2
  have hbaseline : 17 ≤ ThresholdCount D 1 ∧ 5 ≤ ThresholdCount D 2 ∧
      3 ≤ ThresholdCount D 3 ∧ 1 ≤ ThresholdCount D 4 ∧
      1 ≤ ThresholdCount D 5 ∧ 1 ≤ ThresholdCount D 6 ∧ 1 ≤ ThresholdCount D 7 :=
    primitives.baseline target hu.1 hu
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hbaseline
  have hsum : FirstSevenCountSum D ≤ NestedLeafCount target := by
    rw [← primitives.leaf_sum target hu.1]
    exact finite_first_seven_leaves D
  have pat := primitives.patterns target hu.1 hu
  have hsum' : ThresholdCount D 1 + ThresholdCount D 2 + ThresholdCount D 3 +
      ThresholdCount D 4 + ThresholdCount D 5 + ThresholdCount D 6 + ThresholdCount D 7 ≤ 30 := by
    simpa [D, FirstSevenCountSum] using le_trans hsum hL
  by_cases hc4 : ThresholdCount D 4 = 1
  · obtain ⟨triple⟩ := extract.oneHigh _ D hc4 pat.within34 pat.within43
    have hfour := case_one_forces_four D triple pat.across33
    have hc2 : ThresholdCount D 2 = 5 := by omega
    obtain ⟨C, hmiddle⟩ := primitives.middleFive target hu.1 hu hc2
    have hfive := case_one_middle_forces_five D triple hmiddle pat.pairThenThree pat.threeThenPair
    omega
  · have hc4two : ThresholdCount D 4 = 2 := by omega
    have hc3 : ThresholdCount D 3 = 3 := by omega
    have hc2 : ThresholdCount D 2 = 5 := by omega
    have hmiddle := primitives.middleFive target hu.1 hu hc2
    obtain ⟨classification⟩ := extract.twoHigh _ D hc3 hc4two hmiddle
      pat.within34 pat.within43 pat.across33
    exact case_two_order_impossible D classification pat.across34 pat.across43


def ThresholdDeletion (target : HeightThree) (delta : Nat) : DegreeRow :=
  (target.map (fun row => (row.filter (fun d => delta ≤ d)).length)).filter (fun d => 0 < d)

def ThresholdUniversalityDuty : Prop :=
  ∀ target, UniversalThree 7 target → ∀ delta, 1 ≤ delta → delta ≤ 7 →
    UniversalTwo (7 / delta) (ThresholdDeletion target delta)

def ExactHeightTwoMinimum (n leaves : Nat) : Prop :=
  (∃ target, UniversalTwo n target ∧ RowLeafCount target = leaves) ∧
    ∀ target, UniversalTwo n target → leaves ≤ RowLeafCount target

def RowDegreeSystem (row : DegreeRow) (hr : PositiveRow row) : DegreeSystem row.length where
  parent := fun _ => 0
  sibling := Fin.val
  degree := fun i => row[i]
  positive := by intro i; exact hr.2 row[i] (List.getElem_mem i.isLt)
  address_unique := by intro x y _ hxy; exact Fin.ext hxy

/-! Repeated uniform degree-delta sources force floor(n/delta) selected
children. This generic extraction has no desired minimum as a premise. -/
def HeightTwoUniformExtractionDuty : Prop :=
  ∀ n row (hu : UniversalTwo n row), ∀ delta, 1 ≤ delta → delta ≤ n →
    n / delta ≤ ThresholdCount (RowDegreeSystem row hu.1) delta

def RowDegreeSumBridgeDuty : Prop :=
  ∀ row hr, OriginalLeafSum (RowDegreeSystem row hr) = RowLeafCount row

/-- The original finite index sum counts every list occurrence once. -/
theorem row_degree_sum_bridge_source : RowDegreeSumBridgeDuty := by
  intro row hr
  change (∑ i : Fin row.length, row[i.val]) = row.sum
  rw [← List.sum_ofFn, List.ofFn_getElem]

theorem height_two_three_lower (uniform : HeightTwoUniformExtractionDuty)
    (sumBridge : RowDegreeSumBridgeDuty) (row : DegreeRow) (hu : UniversalTwo 3 row) :
    5 ≤ RowLeafCount row := by
  have h1 := uniform 3 row hu 1 (by omega) (by omega)
  have h2 := uniform 3 row hu 2 (by omega) (by omega)
  have h3 := uniform 3 row hu 3 (by omega) (by omega)
  have hs := finite_first_seven_leaves (RowDegreeSystem row hu.1)
  rw [sumBridge] at hs
  norm_num at h1 h2 h3
  simp only [FirstSevenCountSum] at hs
  omega

theorem height_two_two_lower (uniform : HeightTwoUniformExtractionDuty)
    (sumBridge : RowDegreeSumBridgeDuty) (row : DegreeRow) (hu : UniversalTwo 2 row) :
    3 ≤ RowLeafCount row := by
  have h1 := uniform 2 row hu 1 (by omega) (by omega)
  have h2 := uniform 2 row hu 2 (by omega) (by omega)
  have hs := finite_first_seven_leaves (RowDegreeSystem row hu.1)
  rw [sumBridge] at hs
  norm_num at h1 h2
  simp only [FirstSevenCountSum] at hs
  omega

structure HeightTwoSevenLayout (target : DegreeRow) where
  big : Fin target.length
  other : Fin target.length
  distinct : big ≠ other
  big_degree : 4 ≤ target[big]
  other_degree : 3 ≤ target[other]
  unique_four : ∀ i, 4 ≤ target[i] → i = big
  exactly_three : ∀ i, 3 ≤ target[i] → i = big ∨ i = other

def HeightTwoSevenLayoutDuty : Prop :=
  ∀ target, UniversalTwo 7 target → RowLeafCount target ≤ 16 →
    Nonempty (HeightTwoSevenLayout target)

theorem pair34_forces_other_before {target : DegreeRow}
    (layout : HeightTwoSevenLayout target) (embed : DegreeRowEmbeds [3, 4] target) :
    layout.other < layout.big := by
  obtain ⟨f, hf, hd⟩ := embed
  let lo : Fin 2 := ⟨0, by omega⟩
  let hi : Fin 2 := ⟨1, by omega⟩
  have hlt : f lo < f hi := hf (by simp [lo, hi])
  have hlow : 3 ≤ target[f lo] := by simpa [lo] using hd lo
  have hhigh : 4 ≤ target[f hi] := by simpa [hi] using hd hi
  have hbig := layout.unique_four (f hi) hhigh
  rcases layout.exactly_three (f lo) hlow with hsame | hother
  · rw [hsame, hbig] at hlt
    exact False.elim (lt_irrefl _ hlt)
  · simpa [hother, hbig] using hlt

theorem pair43_forces_big_before {target : DegreeRow}
    (layout : HeightTwoSevenLayout target) (embed : DegreeRowEmbeds [4, 3] target) :
    layout.big < layout.other := by
  obtain ⟨f, hf, hd⟩ := embed
  let lo : Fin 2 := ⟨0, by omega⟩
  let hi : Fin 2 := ⟨1, by omega⟩
  have hlt : f lo < f hi := hf (by simp [lo, hi])
  have hhigh : 4 ≤ target[f lo] := by simpa [lo] using hd lo
  have hlow : 3 ≤ target[f hi] := by simpa [hi] using hd hi
  have hbig := layout.unique_four (f lo) hhigh
  rcases layout.exactly_three (f hi) hlow with hsame | hother
  · rw [hsame, hbig] at hlt
    exact False.elim (lt_irrefl _ hlt)
  · simpa [hother, hbig] using hlt

theorem height_two_seven_lower (layoutDuty : HeightTwoSevenLayoutDuty)
    (target : DegreeRow) (hu : UniversalTwo 7 target) : 17 ≤ RowLeafCount target := by
  by_contra hn
  have h16 : RowLeafCount target ≤ 16 := by omega
  obtain ⟨layout⟩ := layoutDuty target hu h16
  have e34 := hu.2 [3, 4] (by simp [PositiveRow]) (by norm_num [RowLeafCount])
  have e43 := hu.2 [4, 3] (by simp [PositiveRow]) (by norm_num [RowLeafCount])
  exact (lt_asymm (pair34_forces_other_before layout e34) (pair43_forces_big_before layout e43))

theorem height_two_seven_minimum_conditional
    (concat : EmbeddingAppendDuty) (median : MedianSplitDuty)
    (layout : HeightTwoSevenLayoutDuty) : ExactHeightTwoMinimum 7 17 := by
  constructor
  · refine ⟨USevenTwo, ?_, upper_two_leaf_count⟩
    exact ⟨by simp [PositiveRow, USevenTwo], fun s hs hb =>
      published_row_seven_universal concat median s hs.2 hb⟩
  · exact height_two_seven_lower layout

theorem height_two_three_minimum_conditional
    (concat : EmbeddingAppendDuty) (median : MedianSplitDuty)
    (uniform : HeightTwoUniformExtractionDuty) (sumBridge : RowDegreeSumBridgeDuty) :
    ExactHeightTwoMinimum 3 5 := by
  constructor
  · refine ⟨UThreeTwo, ?_, ?_⟩
    · exact ⟨by simp [PositiveRow, UThreeTwo], fun s hs hb =>
        published_row_three_universal concat median s hs.2 hb⟩
    · norm_num [RowLeafCount, UThreeTwo]
  · exact height_two_three_lower uniform sumBridge

def HeightTwoSmallMinimaDuty : Prop :=
  ExactHeightTwoMinimum 2 3 ∧ ExactHeightTwoMinimum 3 5 ∧
    ExactHeightTwoMinimum 7 17 ∧
    (∀ r, UniversalTwo 3 r → RowLeafCount r = 5 → r = [1, 3, 1])

end Partials.ParityAlgorithms.Trees
