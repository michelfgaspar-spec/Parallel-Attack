import Partials.Parity.Model

/-! R8/P5-D1. Blind source, uncompiled. Nodes are literal addresses;
an edge appends exactly one child index. No contraction or suppression of
unary nodes is present. Leaf cost is distinct from total node cost. -/

namespace Partials.ParityAlgorithms.Trees

abbrev Address := List Nat

def ImmediateChild (a b : Address) : Prop := ∃ i, b = a ++ [i]

def OrderedSiblings (a b : Address) : Prop :=
  ∃ p i j, a = p ++ [i] ∧ b = p ++ [j] ∧ i < j

structure OrderedTree (height : Nat) where
  nodes : Finset Address
  root_mem : [] ∈ nodes
  bounded_depth : ∀ a ∈ nodes, a.length ≤ height
  parent_closed : ∀ p i, p ++ [i] ∈ nodes → p ∈ nodes
  positive_outdegree : ∀ a ∈ nodes, a.length < height →
    ∃ i, a ++ [i] ∈ nodes

abbrev Node {h : Nat} (t : OrderedTree h) := {a : Address // a ∈ t.nodes}

def IsLeaf {h : Nat} (t : OrderedTree h) (a : Node t) : Prop :=
  a.val.length = h

def TreeLeaves {h : Nat} (t : OrderedTree h) : Finset Address :=
  t.nodes.filter (fun a => a.length = h)

def TreeLeafCount {h : Nat} (t : OrderedTree h) : Nat := (TreeLeaves t).card

def TreeNodeCount {h : Nat} (t : OrderedTree h) : Nat := t.nodes.card

def RootNode {h : Nat} (t : OrderedTree h) : Node t := ⟨[], t.root_mem⟩

structure FullNodeEmbedding {h : Nat} (s t : OrderedTree h) where
  map : Node s → Node t
  injective : Function.Injective map
  root : map (RootNode s) = RootNode t
  immediate_edge : ∀ a b, ImmediateChild a.val b.val →
    ImmediateChild (map a).val (map b).val
  sibling_order : ∀ a b, OrderedSiblings a.val b.val →
    OrderedSiblings (map a).val (map b).val
  leaves : ∀ a, IsLeaf s a → IsLeaf t (map a)

def FullNodeEmbedding.identity {h : Nat} (t : OrderedTree h) :
    FullNodeEmbedding t t where
  map := id
  injective := Function.injective_id
  root := rfl
  immediate_edge := by intro a b hab; exact hab
  sibling_order := by intro a b hab; exact hab
  leaves := by intro a ha; exact ha

def FullNodeEmbedding.compose {h : Nat} {s t u : OrderedTree h}
    (st : FullNodeEmbedding s t) (tu : FullNodeEmbedding t u) :
    FullNodeEmbedding s u where
  map := tu.map ∘ st.map
  injective := tu.injective.comp st.injective
  root := by simp [Function.comp_def, st.root, tu.root]
  immediate_edge := by
    intro a b hab
    exact tu.immediate_edge _ _ (st.immediate_edge _ _ hab)
  sibling_order := by
    intro a b hab
    exact tu.sibling_order _ _ (st.sibling_order _ _ hab)
  leaves := by intro a ha; exact tu.leaves _ (st.leaves _ ha)

def TreeUniversal {h : Nat} (n : Nat) (target : OrderedTree h) : Prop :=
  ∀ source : OrderedTree h, TreeLeafCount source ≤ n →
    Nonempty (FullNodeEmbedding source target)

def ExactLeafUniversal {h : Nat} (n : Nat) (target : OrderedTree h) : Prop :=
  ∀ source : OrderedTree h, TreeLeafCount source = n →
    Nonempty (FullNodeEmbedding source target)

def ExactLeafMinimum (n h m : Nat) : Prop :=
  (∃ t : OrderedTree h, TreeUniversal n t ∧ TreeLeafCount t = m) ∧
    ∀ t : OrderedTree h, TreeUniversal n t → m ≤ TreeLeafCount t

theorem leaf_cannot_have_child {h : Nat} (t : OrderedTree h)
    {a : Address} (ha : a ∈ t.nodes) (hleaf : a.length = h)
    (i : Nat) : a ++ [i] ∉ t.nodes := by
  intro hc
  have hb := t.bounded_depth _ hc
  simp only [List.length_append, List.length_singleton, hleaf] at hb
  omega

theorem internal_has_literal_child {h : Nat} (t : OrderedTree h)
    {a : Address} (ha : a ∈ t.nodes) (hi : a.length < h) :
    ∃ b ∈ t.nodes, ImmediateChild a b := by
  obtain ⟨i, hi⟩ := t.positive_outdegree a ha hi
  exact ⟨a ++ [i], hi, i, rfl⟩

/-! R8-TREE-PADDING-ADDRESS: precise outstanding construction. Append
new leaf children at depth h-1; every old address and immediate edge remains.
This primitive is NOT universality or a requested minimum. -/
def AddressPaddingDuty : Prop :=
  ∀ h n (source : OrderedTree h), 1 ≤ h →
    1 ≤ TreeLeafCount source → TreeLeafCount source ≤ n →
    ∃ padded : OrderedTree h, TreeLeafCount padded = n ∧
      Nonempty (FullNodeEmbedding source padded)

theorem at_most_from_exact (padding : AddressPaddingDuty)
    {h n : Nat} (hh : 1 ≤ h) (target : OrderedTree h)
    (exactN : ExactLeafUniversal n target)
    (positive : ∀ source : OrderedTree h, 1 ≤ TreeLeafCount source) :
    TreeUniversal n target := by
  intro source hs
  obtain ⟨padded, hp, ⟨sp⟩⟩ := padding h n source hh (positive source) hs
  obtain ⟨pt⟩ := exactN padded hp
  exact ⟨sp.compose pt⟩

abbrev DegreeRow := List Nat
abbrev HeightThree := List DegreeRow

def PositiveRow (r : DegreeRow) : Prop := r ≠ [] ∧ ∀ d ∈ r, 0 < d
def PositiveThree (t : HeightThree) : Prop :=
  t ≠ [] ∧ ∀ r ∈ t, PositiveRow r
def RowLeafCount (r : DegreeRow) : Nat := r.sum
def NestedLeafCount (t : HeightThree) : Nat := (t.map List.sum).sum

def DegreeRowEmbeds (s t : DegreeRow) : Prop :=
  ∃ f : Fin s.length → Fin t.length,
    StrictMono f ∧ ∀ i, s[i] ≤ t[f i]

def NestedEmbeds (s t : HeightThree) : Prop :=
  ∃ f : Fin s.length → Fin t.length,
    StrictMono f ∧ ∀ i, DegreeRowEmbeds s[i] t[f i]

theorem row_embedding_refl (r : DegreeRow) : DegreeRowEmbeds r r := by
  exact ⟨id, fun _ _ hij => hij, fun _ => le_rfl⟩

theorem row_embedding_trans {a b c : DegreeRow}
    (ab : DegreeRowEmbeds a b) (bc : DegreeRowEmbeds b c) :
    DegreeRowEmbeds a c := by
  obtain ⟨f, hf, hd⟩ := ab
  obtain ⟨g, hg, he⟩ := bc
  exact ⟨g ∘ f, hg.comp hf, fun i => le_trans (hd i) (he (f i))⟩

theorem nested_embedding_refl (t : HeightThree) : NestedEmbeds t t := by
  exact ⟨id, fun _ _ hij => hij, fun i => row_embedding_refl t[i]⟩

theorem nested_embedding_trans {a b c : HeightThree}
    (ab : NestedEmbeds a b) (bc : NestedEmbeds b c) : NestedEmbeds a c := by
  obtain ⟨f, hf, hd⟩ := ab
  obtain ⟨g, hg, he⟩ := bc
  exact ⟨g ∘ f, hg.comp hf,
    fun i => row_embedding_trans (hd i) (he (f i))⟩

theorem row_embeds_append (a b : DegreeRow) : DegreeRowEmbeds a (a ++ b) := by
  refine ⟨fun i => ⟨i.val, by simp; omega⟩, ?_, ?_⟩
  · intro i j hij; exact hij
  · intro i
    change a[i.val] ≤ (a ++ b)[i.val]
    rw [List.getElem_append_left i.isLt]

theorem nested_embeds_append (a b : HeightThree) : NestedEmbeds a (a ++ b) := by
  refine ⟨fun i => ⟨i.val, by simp; omega⟩, ?_, ?_⟩
  · intro i j hij; exact hij
  · intro i
    change DegreeRowEmbeds a[i.val] (a ++ b)[i.val]
    rw [List.getElem_append_left i.isLt]
    exact row_embedding_refl a[i]

def PadRow (source : DegreeRow) (n : Nat) : DegreeRow :=
  if RowLeafCount source < n then source ++ [n - RowLeafCount source] else source

def PadNested (source : HeightThree) (n : Nat) : HeightThree :=
  if NestedLeafCount source < n then source ++ [[n - NestedLeafCount source]]
  else source

theorem row_padding_count {source : DegreeRow} {n : Nat}
    (hs : RowLeafCount source ≤ n) : RowLeafCount (PadRow source n) = n := by
  by_cases hlt : RowLeafCount source < n
  · rw [PadRow, if_pos hlt]
    simp only [RowLeafCount, List.sum_append, List.sum_singleton]
    change RowLeafCount source + (n - RowLeafCount source) = n
    omega
  · simp [PadRow, hlt]
    omega

theorem row_padding_embedding (source : DegreeRow) (n : Nat) :
    DegreeRowEmbeds source (PadRow source n) := by
  by_cases hlt : RowLeafCount source < n
  · simpa [PadRow, hlt] using row_embeds_append source [n - RowLeafCount source]
  · simpa [PadRow, hlt] using row_embedding_refl source

theorem nested_padding_count {source : HeightThree} {n : Nat}
    (hs : NestedLeafCount source ≤ n) : NestedLeafCount (PadNested source n) = n := by
  by_cases hlt : NestedLeafCount source < n
  · rw [PadNested, if_pos hlt]
    simp only [NestedLeafCount, List.map_append, List.sum_append,
      List.map_singleton, List.sum_singleton]
    change NestedLeafCount source + (n - NestedLeafCount source) = n
    omega
  · simp [PadNested, hlt]
    omega

theorem nested_padding_embedding (source : HeightThree) (n : Nat) :
    NestedEmbeds source (PadNested source n) := by
  by_cases hlt : NestedLeafCount source < n
  · simpa [PadNested, hlt] using nested_embeds_append source [[n - NestedLeafCount source]]
  · simpa [PadNested, hlt] using nested_embedding_refl source

theorem positive_row_padding {source : DegreeRow} {n : Nat}
    (hs : PositiveRow source) : PositiveRow (PadRow source n) := by
  by_cases hlt : RowLeafCount source < n
  · refine ⟨?_, ?_⟩
    · simp [PadRow, hlt, hs.1]
    · intro d hd
      simp only [PadRow, if_pos hlt, List.mem_append, List.mem_singleton] at hd
      rcases hd with hd | rfl
      · exact hs.2 d hd
      · omega
  · simpa [PadRow, hlt] using hs

theorem positive_nested_padding {source : HeightThree} {n : Nat}
    (hs : PositiveThree source) : PositiveThree (PadNested source n) := by
  by_cases hlt : NestedLeafCount source < n
  · refine ⟨?_, ?_⟩
    · simp [PadNested, hlt, hs.1]
    · intro r hr
      simp only [PadNested, if_pos hlt, List.mem_append, List.mem_singleton] at hr
      rcases hr with hr | rfl
      · exact hs.2 r hr
      · exact ⟨by simp, by intro d hd; simp only [List.mem_singleton] at hd; subst d; omega⟩
  · simpa [PadNested, hlt] using hs

def UniversalTwo (n : Nat) (target : DegreeRow) : Prop :=
  PositiveRow target ∧ ∀ source, PositiveRow source →
    RowLeafCount source ≤ n → DegreeRowEmbeds source target

def UniversalThree (n : Nat) (target : HeightThree) : Prop :=
  PositiveThree target ∧ ∀ source, PositiveThree source →
    NestedLeafCount source ≤ n → NestedEmbeds source target

/-! R8-TREE-NESTED-BRIDGE: all-node address encodings, literal root/parent
and sibling preservation and converse extraction. Not supplied by leaf counts. -/
structure NestedAddressBridgeDuty where
  encodeTwo : (r : DegreeRow) → PositiveRow r → OrderedTree 2
  encodeThree : (t : HeightThree) → PositiveThree t → OrderedTree 3
  leafTwo : ∀ r hr, TreeLeafCount (encodeTwo r hr) = RowLeafCount r
  leafThree : ∀ t ht, TreeLeafCount (encodeThree t ht) = NestedLeafCount t
  ontoTwo : ∀ t : OrderedTree 2, ∃ r hr,
    Nonempty (FullNodeEmbedding t (encodeTwo r hr)) ∧
    Nonempty (FullNodeEmbedding (encodeTwo r hr) t)
  ontoThree : ∀ t : OrderedTree 3, ∃ r hr,
    TreeLeafCount t = NestedLeafCount r ∧
    Nonempty (FullNodeEmbedding t (encodeThree r hr)) ∧
    Nonempty (FullNodeEmbedding (encodeThree r hr) t)
  embeddingTwo : ∀ r s hr hs,
    DegreeRowEmbeds r s ↔ Nonempty (FullNodeEmbedding (encodeTwo r hr) (encodeTwo s hs))
  embeddingThree : ∀ r s hr hs,
    NestedEmbeds r s ↔ Nonempty (FullNodeEmbedding (encodeThree r hr) (encodeThree s hs))

end Partials.ParityAlgorithms.Trees
