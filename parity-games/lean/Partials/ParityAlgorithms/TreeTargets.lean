import Partials.ParityAlgorithms.TreeLower

/-! R8 source assembly. Every conditional proof names its remaining
primitive adapters. No primitive assumes UniversalThree 7 PublishedWitness31,
the desired lower bound, or ExactLeafMinimum 7 3 31. Source is uncompiled. -/

namespace Partials.ParityAlgorithms.Trees

def NestedMinimumSevenThreeTarget : Prop :=
  UniversalThree 7 PublishedWitness31 ∧
    ∀ target, UniversalThree 7 target → 31 ≤ NestedLeafCount target

theorem nested_minimum_seven_three_conditional
    (concat : EmbeddingAppendDuty) (median : MedianSplitDuty)
    (thresholds : UniversalThresholdPrimitives) (order : CountOrderExtractionDuty) :
    NestedMinimumSevenThreeTarget := by
  exact ⟨published_nested_seven_universal concat median,
    all_targets_at_least_thirty_one thresholds order⟩

theorem nested_to_full_universality (bridge : NestedAddressBridgeDuty)
    {target : HeightThree} (ht : PositiveThree target)
    (hu : UniversalThree 7 target) : TreeUniversal 7 (bridge.encodeThree target ht) := by
  intro source hs
  obtain ⟨r, hr, hcount, ⟨sr⟩, _⟩ := bridge.ontoThree source
  have hrb : NestedLeafCount r ≤ 7 := by omega
  have hrow := hu.2 r hr hrb
  obtain ⟨rt⟩ := (bridge.embeddingThree r target hr ht).mp hrow
  exact ⟨sr.compose rt⟩

theorem full_to_nested_universality (bridge : NestedAddressBridgeDuty)
    (target : OrderedTree 3) (hu : TreeUniversal 7 target)
    {r : HeightThree} (hr : PositiveThree r)
    (tr : FullNodeEmbedding target (bridge.encodeThree r hr)) : UniversalThree 7 r := by
  constructor
  · exact hr
  · intro source hs hb
    have hcount : TreeLeafCount (bridge.encodeThree source hs) ≤ 7 := by
      rw [bridge.leafThree]
      exact hb
    obtain ⟨st⟩ := hu _ hcount
    exact (bridge.embeddingThree source r hs hr).mpr ⟨st.compose tr⟩

theorem full_node_minimum_seven_three_conditional
    (bridge : NestedAddressBridgeDuty)
    (concat : EmbeddingAppendDuty) (median : MedianSplitDuty)
    (thresholds : UniversalThresholdPrimitives) (order : CountOrderExtractionDuty) :
    ExactLeafMinimum 7 3 31 := by
  have hUpper := published_nested_seven_universal concat median
  constructor
  · refine ⟨bridge.encodeThree PublishedWitness31 hUpper.1,
      nested_to_full_universality bridge hUpper.1 hUpper, ?_⟩
    rw [bridge.leafThree]
    exact upper_three_leaf_count
  · intro target hu
    obtain ⟨r, hr, hcount, ⟨tr⟩, _⟩ := bridge.ontoThree target
    have hur := full_to_nested_universality bridge target hu hr tr
    have hl := all_targets_at_least_thirty_one thresholds order r hur
    omega

/-! The following primitive interfaces remain target declarations. Their
presence is never an admission or an instance supplying a requested theorem. -/
def TreeSourceAdmissionBundle : Prop :=
  Nonempty NestedAddressBridgeDuty ∧
    Nonempty EmbeddingAppendDuty ∧ Nonempty MedianSplitDuty ∧
    Nonempty UniversalThresholdPrimitives ∧ Nonempty CountOrderExtractionDuty ∧
    ThresholdLayerCakeDuty ∧ ThresholdUniversalityDuty ∧ HeightTwoSmallMinimaDuty

def OriginalTreeHeadlineTarget : Prop := ExactLeafMinimum 7 3 31

def FiniteTreeEvaluationAuthorized : Prop := False

def TreeScopeNote : String :=
  "Full-node immediate-edge fixed-height ordered trees, unary nodes allowed; leaf cost; no finite evaluation or priority/novelty claim"

def GeneralMinimumResearchStatus : String :=
  "No claim about current openness or priority follows from the supplied undated discussion"

def NoPathBoundInference : String :=
  "The fixed ordered-tree leaf minimum supplies no strategy-iteration pivot or evaluation bound"

end Partials.ParityAlgorithms.Trees
