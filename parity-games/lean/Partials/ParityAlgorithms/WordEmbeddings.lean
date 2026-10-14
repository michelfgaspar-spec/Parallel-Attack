import Partials.ParityAlgorithms.OrderedTrees
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

/-! P5-WORD. The exact gap condition is equality with a BLOCK MINIMUM.
Coordinatewise degree domination describes height-two child sequences;
it is not a substitute for equality of LCA depths in leaf-gap words.
Metadata U116's word 'dominates' is retained in the inventory and corrected
only in the R8 correspondence note. No finite enumeration was executed. -/

namespace Partials.ParityAlgorithms.Trees

abbrev AncestorWord := List Nat

def WordAlphabet (height : Nat) (word : AncestorWord) : Prop :=
  ∀ d ∈ word, d < height

def GapBlock (word : AncestorWord) (lo hi : Nat) : List Nat :=
  (word.drop lo).take (hi - lo)

def ExactBlockMinimum (word : AncestorWord) (lo hi d : Nat) : Prop :=
  lo < hi ∧ hi ≤ word.length ∧ (GapBlock word lo hi).min? = some d

def WordEmbeds (source target : AncestorWord) : Prop :=
  ∃ f : Fin (source.length + 1) → Fin (target.length + 1),
    StrictMono f ∧ ∀ i : Fin source.length,
      ExactBlockMinimum target
        (f ⟨i.val, by omega⟩).val
        (f ⟨i.val + 1, by omega⟩).val source[i]

theorem singleton_block_minimum (d : Nat) :
    ExactBlockMinimum [d] 0 1 d := by
  simp [ExactBlockMinimum, GapBlock]

theorem singleton_word_embeds_self (d : Nat) : WordEmbeds [d] [d] := by
  refine ⟨id, fun _ _ hij => hij, ?_⟩
  intro i
  have hi : i.val = 0 := by have hb : i.val < 1 := i.isLt; omega
  simp [ExactBlockMinimum, GapBlock, hi]

theorem one_leaf_empty_word_embeds (target : AncestorWord) : WordEmbeds [] target := by
  refine ⟨fun _ => ⟨0, by omega⟩, ?_, ?_⟩
  · intro i j hij
    have hi : i.val < 1 := i.isLt
    have hj : j.val < 1 := j.isLt
    change i.val < j.val at hij
    omega
  · intro i
    have hi := i.isLt
    simp at hi

/-- The smallest counterexample to replacing equality by domination.
Both words belong to the height-two alphabet, yet their two leaves have
different LCA depths. Immediate-edge embeddings cannot change that depth. -/
theorem inequality_does_not_give_exact_gap :
    0 ≤ 1 ∧ ¬ ExactBlockMinimum [1] 0 1 0 := by
  simp [ExactBlockMinimum, GapBlock]

/-- Maximal leaf intervals at every depth are kept separately. Equal
intervals at consecutive depths yield different nodes and a unary edge. -/
def DepthInterval (word : AncestorWord) (depth lo hi : Nat) : Prop :=
  lo ≤ hi ∧ hi < word.length + 1 ∧
  (∀ k, lo ≤ k → k < hi → ∀ hk : k < word.length, depth ≤ word[k]) ∧
  (lo = 0 ∨ ∃ hk : lo - 1 < word.length, word[lo - 1] < depth) ∧
  (hi = word.length ∨ ∃ hk : hi < word.length, word[hi] < depth)

structure IntervalNode where
  depth : Nat
  firstLeaf : Nat
  lastLeaf : Nat
deriving DecidableEq

def WordIntervalNode (height : Nat) (word : AncestorWord)
    (node : IntervalNode) : Prop :=
  node.depth ≤ height ∧ DepthInterval word node.depth node.firstLeaf node.lastLeaf

def IntervalParent (parent child : IntervalNode) : Prop :=
  child.depth = parent.depth + 1 ∧
  parent.firstLeaf ≤ child.firstLeaf ∧ child.lastLeaf ≤ parent.lastLeaf

theorem equal_intervals_consecutive_depths_are_distinct
    (d lo hi : Nat) :
    (⟨d, lo, hi⟩ : IntervalNode) ≠ ⟨d + 1, lo, hi⟩ := by
  intro heq
  have hd := congrArg IntervalNode.depth heq
  simp at hd

/-! R8-TREE-WORD-BRIDGE: construct finite interval trees, prove LCA
interval/block-min identities, and implement the all-node ancestor map.
No desired universality or minimum appears in this primitive interface. -/
structure WordTreeBridgeDuty where
  encode : ∀ height word, WordAlphabet height word → OrderedTree height
  leaf_count : ∀ h a ha, TreeLeafCount (encode h a ha) = a.length + 1
  representation : ∀ h (t : OrderedTree h), ∃ word hw,
    TreeLeafCount t = word.length + 1 ∧
    Nonempty (FullNodeEmbedding t (encode h word hw)) ∧
    Nonempty (FullNodeEmbedding (encode h word hw) t)
  exact_embedding : ∀ h a b ha hb,
    WordEmbeds a b ↔
      Nonempty (FullNodeEmbedding (encode h a ha) (encode h b hb))

def ExactlySevenThreeWordCountTarget : Prop :=
  Fintype.card (Fin 6 → Fin 3) = 729

theorem exactly_seven_three_word_count : ExactlySevenThreeWordCountTarget := by
  norm_num [ExactlySevenThreeWordCountTarget, Fintype.card_fun]

/-- A representation count, with no assertion that these sources were
enumerated, tested against a target or used as a lower-bound certificate. -/
def WordCountInterpretation : String :=
  "3^6=729 describes exactly-seven-leaf height-three source words; no run performed"

end Partials.ParityAlgorithms.Trees
