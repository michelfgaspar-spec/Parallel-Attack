import Partials.ParityAlgorithms.WordEmbeddings

/-! P5-UPPER/U114. Published odd median-leaf construction attributed to
Fijalkow, Section 5.1/Theorem 4 (Jurdzinski--Lazic lineage), as already
supplied in the frozen paper. Universality uses both side forests and one
middle subtree. Literal leaf counts alone supply no universality evidence. -/

namespace Partials.ParityAlgorithms.Trees

def WeakPositiveRow (r : DegreeRow) : Prop := ∀ d ∈ r, 0 < d
def WeakPositiveThree (t : HeightThree) : Prop := ∀ r ∈ t, PositiveRow r

def WeakUniversalTwo (n : Nat) (target : DegreeRow) : Prop :=
  ∀ source, WeakPositiveRow source → RowLeafCount source ≤ n →
    DegreeRowEmbeds source target

def WeakUniversalThree (n : Nat) (target : HeightThree) : Prop :=
  ∀ source, WeakPositiveThree source → NestedLeafCount source ≤ n →
    NestedEmbeds source target

theorem empty_row_embeds (target : DegreeRow) : DegreeRowEmbeds [] target := by
  refine ⟨Fin.elim0, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

theorem empty_nested_embeds (target : HeightThree) : NestedEmbeds [] target := by
  refine ⟨Fin.elim0, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro i; exact Fin.elim0 i

theorem singleton_row_embeds {a b : Nat} (hab : a ≤ b) :
    DegreeRowEmbeds [a] [b] := by
  refine ⟨id, fun _ _ hij => hij, ?_⟩
  intro i
  have hi : i.val = 0 := by have hb : i.val < 1 := i.isLt; omega
  simpa [hi] using hab

theorem singleton_nested_embeds {a b : DegreeRow} (hab : DegreeRowEmbeds a b) :
    NestedEmbeds [a] [b] := by
  refine ⟨id, fun _ _ hij => hij, ?_⟩
  intro i
  have hi : i.val = 0 := by have hb : i.val < 1 := i.isLt; omega
  simpa [hi] using hab

theorem positive_row_sum_zero {r : DegreeRow} (hr : WeakPositiveRow r) :
    r.sum = 0 ↔ r = [] := by
  constructor
  · intro hs
    cases r with
    | nil => rfl
    | cons d tail =>
      have hd := hr d (by simp)
      simp at hs
      omega
  · intro h; subst r; rfl

theorem unit_row_classification {r : DegreeRow} (hr : WeakPositiveRow r)
    (hs : RowLeafCount r ≤ 1) : r = [] ∨ r = [1] := by
  cases r with
  | nil => exact Or.inl rfl
  | cons d tail =>
    have hd := hr d (by simp)
    have htail : WeakPositiveRow tail := by intro a ha; exact hr a (by simp [ha])
    have ht : tail.sum = 0 := by simp [RowLeafCount] at hs; omega
    have htnil := (positive_row_sum_zero htail).mp ht
    subst tail
    simp [RowLeafCount] at hs
    have heq : d = 1 := by omega
    subst d
    exact Or.inr rfl

theorem weak_unit_row_universal : WeakUniversalTwo 1 [1] := by
  intro source hs hb
  rcases unit_row_classification hs hb with rfl | rfl
  · exact empty_row_embeds _
  · exact row_embedding_refl _

theorem positive_nested_zero {t : HeightThree} (ht : WeakPositiveThree t) :
    NestedLeafCount t = 0 ↔ t = [] := by
  constructor
  · intro hz
    cases t with
    | nil => rfl
    | cons r tail =>
      have hr := ht r (by simp)
      have hpos : 0 < r.sum := by
        exact Nat.pos_of_ne_zero (fun hz => hr.1 ((positive_row_sum_zero hr.2).mp hz))
      change r.sum + NestedLeafCount tail = 0 at hz
      omega
  · intro h; subst t; rfl

theorem weak_unit_nested_universal : WeakUniversalThree 1 [[1]] := by
  intro source hs hb
  cases source with
  | nil => exact empty_nested_embeds _
  | cons r tail =>
    have hr := hs r (by simp)
    have htail : WeakPositiveThree tail := by intro a ha; exact hs a (by simp [ha])
    have hpos : 0 < r.sum := by
      exact Nat.pos_of_ne_zero (fun hz => hr.1 ((positive_row_sum_zero hr.2).mp hz))
    have hb' : r.sum + NestedLeafCount tail ≤ 1 := hb
    have htz : NestedLeafCount tail = 0 := by omega
    have htnil := (positive_nested_zero htail).mp htz
    subst tail
    have hrb : RowLeafCount r ≤ 1 := by simpa [NestedLeafCount, RowLeafCount] using hb
    exact singleton_nested_embeds (weak_unit_row_universal r hr.2 hrb)

/-! Primitive generic index-map append transport; independent of any leaf
budget or named upper target. The ordinary proof offsets right-side indices.
R8-TREE-CONCAT-FORMAL retains its library/elaboration bridge. -/
structure EmbeddingAppendDuty where
  row : ∀ a b c d, DegreeRowEmbeds a b → DegreeRowEmbeds c d →
    DegreeRowEmbeds (a ++ c) (b ++ d)
  nested : ∀ a b c d, NestedEmbeds a b → NestedEmbeds c d →
    NestedEmbeds (a ++ c) (b ++ d)

/-! R8-TREE-MEDIAN-SPLIT: purely weighted list decomposition. No target
embedding, construction or universality is a premise. Empty sides are allowed.
For a source below capacity, select the child crossing the median leaf if
present, or the last child; both side sums are at most k. -/
structure MedianSplitDuty where
  row : ∀ k source, source ≠ [] → WeakPositiveRow source →
    RowLeafCount source ≤ 2 * k + 1 →
    ∃ left d right, source = left ++ [d] ++ right ∧
      WeakPositiveRow left ∧ WeakPositiveRow right ∧
      RowLeafCount left ≤ k ∧ RowLeafCount right ≤ k ∧
      0 < d ∧ d ≤ 2 * k + 1
  nested : ∀ k source, source ≠ [] → WeakPositiveThree source →
    NestedLeafCount source ≤ 2 * k + 1 →
    ∃ left middle right, source = left ++ [middle] ++ right ∧
      WeakPositiveThree left ∧ WeakPositiveThree right ∧
      NestedLeafCount left ≤ k ∧ NestedLeafCount right ≤ k ∧
      PositiveRow middle ∧ RowLeafCount middle ≤ 2 * k + 1

/-- A weighted list can be split at one occurrence with independently
bounded sides. The proof permits empty sides and retains repeated entries. -/
theorem weighted_median_split {α : Type*} (weight : α → Nat) (source : List α)
    (hne : source ≠ []) (hp : ∀ d ∈ source, 0 < weight d) (a b : Nat)
    (hb : (source.map weight).sum ≤ a + b + 1) :
    ∃ left d right, source = left ++ [d] ++ right ∧
      (left.map weight).sum ≤ a ∧ (right.map weight).sum ≤ b ∧
      0 < weight d ∧ weight d ≤ a + b + 1 := by
  induction source generalizing a with
  | nil => exact False.elim (hne rfl)
  | cons d tail ih =>
    have hd : 0 < weight d := hp d (by simp)
    have hs : weight d + (tail.map weight).sum ≤ a + b + 1 := hb
    by_cases ht : (tail.map weight).sum ≤ b
    · exact ⟨[], d, tail, rfl, by simp, ht, hd, by omega⟩
    · have hda : weight d ≤ a := by omega
      have htail : tail ≠ [] := by intro he; simp [he] at ht
      have htp : ∀ e ∈ tail, 0 < weight e := by
        intro e he; exact hp e (by simp [he])
      have htb : (tail.map weight).sum ≤ (a - weight d) + b + 1 := by omega
      obtain ⟨left, e, right, heq, hl, hr, he, heb⟩ := ih htail htp (a - weight d) htb
      refine ⟨d :: left, e, right, ?_, ?_, hr, he, ?_⟩
      · simp only [List.cons_append]; rw [heq]
      · change weight d + (left.map weight).sum ≤ a
        omega
      · omega

/-- Instantiation of the weighted split for both degree rows and root
forests. This supplies the original primitive interface without a target
embedding or a universality premise. -/
def medianSplitSource : MedianSplitDuty where
  row k source hne hp hb := by
    obtain ⟨left, d, right, heq, hl, hr, hd, hdb⟩ :=
      weighted_median_split id source hne hp k k (by simpa [RowLeafCount, two_mul] using hb)
    refine ⟨left, d, right, heq, ?_, ?_, ?_, ?_, hd, ?_⟩
    · intro e he; apply hp e; rw [heq]; simp [he]
    · intro e he; apply hp e; rw [heq]; simp [he]
    · simpa [RowLeafCount] using hl
    · simpa [RowLeafCount] using hr
    · simpa [two_mul] using hdb
  nested k source hne hp hb := by
    have hpos : ∀ r ∈ source, 0 < RowLeafCount r := by
      intro r hr
      have hrp := hp r hr
      exact Nat.pos_of_ne_zero (fun hz => hrp.1 ((positive_row_sum_zero hrp.2).mp hz))
    obtain ⟨left, middle, right, heq, hl, hr, _, hmb⟩ :=
      weighted_median_split RowLeafCount source hne hpos k k
        (by change NestedLeafCount source ≤ k + k + 1; omega)
    refine ⟨left, middle, right, heq, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro r hr; apply hp r; rw [heq]; simp [hr]
    · intro r hr; apply hp r; rw [heq]; simp [hr]
    · exact hl
    · exact hr
    · apply hp middle; rw [heq]; simp
    · simpa [two_mul] using hmb

theorem odd_row_upper (concat : EmbeddingAppendDuty) (median : MedianSplitDuty)
    {k : Nat} {side : DegreeRow} (hs : WeakUniversalTwo k side) :
    WeakUniversalTwo (2 * k + 1) (side ++ [2 * k + 1] ++ side) := by
  intro source hp hb
  by_cases hempty : source = []
  · subst source; exact empty_row_embeds _
  · obtain ⟨left, d, right, heq, hlp, hrp, hlb, hrb, _, hdb⟩ :=
      median.row k source hempty hp hb
    subst source
    exact concat.row _ _ _ _
      (concat.row _ _ _ _ (hs left hlp hlb) (singleton_row_embeds hdb))
      (hs right hrp hrb)

theorem odd_nested_upper (concat : EmbeddingAppendDuty) (median : MedianSplitDuty)
    {k : Nat} {side : HeightThree} {middle : DegreeRow}
    (hs : WeakUniversalThree k side)
    (hm : WeakUniversalTwo (2 * k + 1) middle) :
    WeakUniversalThree (2 * k + 1) (side ++ [middle] ++ side) := by
  intro source hp hb
  by_cases hempty : source = []
  · subst source; exact empty_nested_embeds _
  · obtain ⟨left, center, right, heq, hlp, hrp, hlb, hrb, hcp, hcb⟩ :=
      median.nested k source hempty hp hb
    subst source
    exact concat.nested _ _ _ _
      (concat.nested _ _ _ _ (hs left hlp hlb)
        (singleton_nested_embeds (hm center hcp.2 hcb)))
      (hs right hrp hrb)

def UThreeTwo : DegreeRow := [1, 3, 1]
def USevenTwo : DegreeRow := [1, 3, 1, 7, 1, 3, 1]
def UThreeThree : HeightThree := [[1], [1, 3, 1], [1]]
def PublishedWitness31 : HeightThree :=
  [[1], [1, 3, 1], [1], [1, 3, 1, 7, 1, 3, 1], [1], [1, 3, 1], [1]]

theorem published_row_three_universal (concat : EmbeddingAppendDuty)
    (median : MedianSplitDuty) : WeakUniversalTwo 3 UThreeTwo := by
  simpa [UThreeTwo] using odd_row_upper concat median weak_unit_row_universal

theorem published_row_seven_universal (concat : EmbeddingAppendDuty)
    (median : MedianSplitDuty) : WeakUniversalTwo 7 USevenTwo := by
  simpa [USevenTwo, UThreeTwo] using
    odd_row_upper concat median (published_row_three_universal concat median)

theorem published_nested_three_universal (concat : EmbeddingAppendDuty)
    (median : MedianSplitDuty) : WeakUniversalThree 3 UThreeThree := by
  simpa [UThreeThree, UThreeTwo] using odd_nested_upper concat median
    weak_unit_nested_universal (published_row_three_universal concat median)

theorem published_nested_seven_universal (concat : EmbeddingAppendDuty)
    (median : MedianSplitDuty) : UniversalThree 7 PublishedWitness31 := by
  constructor
  · simp [PositiveThree, PositiveRow, PublishedWitness31]
  · intro source hs hb
    have hu := odd_nested_upper concat median
      (published_nested_three_universal concat median)
      (published_row_seven_universal concat median)
    simpa [PublishedWitness31, UThreeThree, USevenTwo] using hu source hs.2 hb

theorem upper_two_leaf_count : RowLeafCount USevenTwo = 17 := by
  norm_num [RowLeafCount, USevenTwo]

theorem upper_three_leaf_count : NestedLeafCount PublishedWitness31 = 31 := by
  norm_num [NestedLeafCount, PublishedWitness31]

def NestedNodeCount (t : HeightThree) : Nat :=
  1 + t.length + (t.map List.length).sum + NestedLeafCount t

theorem witness_node_count : NestedNodeCount PublishedWitness31 = 56 := by
  norm_num [NestedNodeCount, NestedLeafCount, PublishedWitness31]

def UpperConstructionAttribution : String :=
  "Fijalkow 2018, Section 5.1, Theorem 4; Jurdzinski--Lazic lineage, as frozen source states"

end Partials.ParityAlgorithms.Trees
