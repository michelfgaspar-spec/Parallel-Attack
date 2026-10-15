import Partials.Graceful.Executable

/-! Numerical anchor correspondence and the increasing-smaller-label transfer rule. -/
namespace Partials.Graceful.Executable
open Symbolic NumericConstruction ManuscriptPresentation

/-- All four literal labels on the independent named manuscript vertices. -/
def HasAnchors {u v : ℕ} (f : Vertex u v → Fin (q u v + 1)) (a : Anchor) : Prop :=
  (f (encode (anchorA u v))).val = a.A ∧
  (f (encode (anchorB u v))).val = a.B ∧
  (f (encode (anchorC u v))).val = a.C ∧
  (f (encode (anchorZ u v))).val = a.Z

theorem profile0_anchors (u v t : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hq : q u v = q0 t) (hc : 0 < t ∨ 2 ≤ u) :
    HasAnchors (profile0 u v t hu hv hq hc).labeling (anchor0 t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change internalNat0 t (oneCode 2) = (anchor0 t).A
    simp [oneCode, internalNat0, pick3, q0, anchor0] <;> omega
  · change internalNat0 t (twoCode ⟨2, ⟨1, by decide⟩⟩) = (anchor0 t).B
    simp [twoCode, internalNat0, q0, anchor0] <;> omega
  · change internalNat0 t (twoCode splitDepth) = (anchor0 t).C
    rfl
  · have hm := (profile0 u v t hu hv hq hc).leafMap_mem splitDepth ⟨0, by simp [splitDepth, pendantCount]⟩
    have hn := (liftFiber_mem _ _ _).mp hm
    change ((profile0 u v t hu hv hq hc).labeling (encode (anchorZ u v))).val ∈
      naturalFiber (q u v) (fullFinalParent0 t v) (anchor0 t).C at hn
    simp only [hq] at hn
    unfold fullFinalParent0 at hn
    rw [naturalFiber_fullParent] at hn
    have hs : fibre (q0 t) (finalParent0 t v) (anchor0 t).C = {(anchor0 t).Z} := by
      apply splitParent_C_fibre
      · dsimp [anchor0]; omega
      · dsimp [anchor0]; omega
      · simp only [leafLabels, Finset.mem_Icc, q0, anchor0]; omega
      · intro x _
        exact afterPairs0_avoids_C t v x
    rw [hs] at hn
    exact Finset.mem_singleton.mp hn

theorem profile1_anchors (u v t : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hq : q u v = q1 t) :
    HasAnchors (profile1 u v t hu hv hq).labeling (anchor1 t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change internalNat1 t (oneCode 2) = (anchor1 t).A
    simp [oneCode, internalNat1, pick3, q1, anchor1] <;> omega
  · change internalNat1 t (twoCode ⟨2, ⟨1, by decide⟩⟩) = (anchor1 t).B
    simp [twoCode, internalNat1, q1, anchor1] <;> omega
  · change internalNat1 t (twoCode splitDepth) = (anchor1 t).C
    rfl
  · have hm := (profile1 u v t hu hv hq).leafMap_mem splitDepth ⟨0, by simp [splitDepth, pendantCount]⟩
    have hn := (liftFiber_mem _ _ _).mp hm
    change ((profile1 u v t hu hv hq).labeling (encode (anchorZ u v))).val ∈
      naturalFiber (q u v) (fullFinalParent1 t u) (anchor1 t).C at hn
    simp only [hq] at hn
    unfold fullFinalParent1 at hn
    rw [naturalFiber_fullParent] at hn
    have hs : fibre (q1 t) (finalParent1 t u) (anchor1 t).C = {(anchor1 t).Z} := by
      apply splitParent_C_fibre
      · dsimp [anchor1]; omega
      · dsimp [anchor1]; omega
      · simp only [leafLabels, Finset.mem_Icc, q1, anchor1]; omega
      · intro x _
        exact afterPairs1_avoids_C t u x
    rw [hs] at hn
    exact Finset.mem_singleton.mp hn

theorem profile2_anchors (u v t : ℕ) (hu : 2 ≤ u) (hv : 0 < v)
    (hq : q u v = q2 t) :
    HasAnchors (profile2 u v t hu hv hq).labeling (anchor2 t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change internalNat2 t (oneCode 2) = (anchor2 t).A
    simp [oneCode, internalNat2, pick3, q2, anchor2] <;> omega
  · change internalNat2 t (twoCode ⟨2, ⟨1, by decide⟩⟩) = (anchor2 t).B
    simp [twoCode, internalNat2, q2, anchor2] <;> omega
  · change internalNat2 t (twoCode splitDepth) = (anchor2 t).C
    rfl
  · have hm := (profile2 u v t hu hv hq).leafMap_mem splitDepth ⟨0, by simp [splitDepth, pendantCount]⟩
    have hn := (liftFiber_mem _ _ _).mp hm
    change ((profile2 u v t hu hv hq).labeling (encode (anchorZ u v))).val ∈
      naturalFiber (q u v) (fullFinalParent2 t v) (anchor2 t).C at hn
    simp only [hq] at hn
    unfold fullFinalParent2 at hn
    rw [naturalFiber_fullParent] at hn
    have hs : fibre (q2 t) (finalParent2 t v) (anchor2 t).C = {(anchor2 t).Z} := by
      apply splitParent_C_fibre
      · dsimp [anchor2]; omega
      · dsimp [anchor2]; omega
      · simp only [leafLabels, Finset.mem_Icc, q2, anchor2]; omega
      · intro x _
        exact afterPairs2_avoids_C t v x
    rw [hs] at hn
    exact Finset.mem_singleton.mp hn

theorem alternateProfile_anchors (v t : ℕ) (hv : 0 < v) (hq : q 1 v = q2 t) :
    HasAnchors (alternateProfile v t hv hq).labeling (alternateAnchor t) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change alternateInternalNat t (oneCode 2) = (alternateAnchor t).A
    simp [oneCode, alternateInternalNat, pick3, q2, alternateAnchor]
  · change alternateInternalNat t (twoCode ⟨2, ⟨1, by decide⟩⟩) = (alternateAnchor t).B
    simp [twoCode, alternateInternalNat, q2, alternateAnchor] <;> omega
  · change alternateInternalNat t (twoCode splitDepth) = (alternateAnchor t).C
    rfl
  · have hm := (alternateProfile v t hv hq).leafMap_mem splitDepth ⟨0, by simp [splitDepth, pendantCount]⟩
    have hn := (liftFiber_mem _ _ _).mp hm
    change ((alternateProfile v t hv hq).labeling (encode (anchorZ 1 v))).val ∈
      naturalFiber (q 1 v) (fullAlternateFinalParent t) (alternateAnchor t).C at hn
    simp only [hq] at hn
    unfold fullAlternateFinalParent at hn
    rw [naturalFiber_fullParent] at hn
    have hs : fibre (q2 t) (alternateFinalParent t) (alternateAnchor t).C = {(alternateAnchor t).Z} := by
      apply splitParent_C_fibre
      · dsimp [alternateAnchor]; omega
      · dsimp [alternateAnchor]; omega
      · simp only [leafLabels, Finset.mem_Icc, q2, alternateAnchor]; omega
      · intro x _
        exact alternateAfterFirst_avoids_C t x
    rw [hs] at hn
    exact Finset.mem_singleton.mp hn

theorem small23_anchors : HasAnchors small23Label ⟨23, 2, 9, 16⟩ := by unfold HasAnchors; decide

theorem small27_anchors : HasAnchors small27Label ⟨26, 5, 12, 19⟩ := by unfold HasAnchors; decide

/-- The two literal table rows and the four affine anchor records. -/
def anchorOfRoute {u v : ℕ} : Route u v → Anchor
  | .small23 _ _ => ⟨23, 2, 9, 16⟩
  | .small27 _ _ => ⟨26, 5, 12, 19⟩
  | .residue0 t _ _ => anchor0 t
  | .residue1 t _ => anchor1 t
  | .residue2 t _ _ => anchor2 t
  | .alternate t _ _ => alternateAnchor t

theorem labelOfRoute_anchors {u v : ℕ} (hu : 0 < u) (hv : 0 < v) (r : Route u v) :
    HasAnchors (labelOfRoute hu hv r) (anchorOfRoute r) := by
  cases r with
  | small23 hu1 hv1 => subst u; subst v; exact small23_anchors
  | small27 hu1 hv3 => subst u; subst v; exact small27_anchors
  | residue0 t hq hc => exact profile0_anchors u v t hu hv hq hc
  | residue1 t hq => exact profile1_anchors u v t hu hv hq
  | residue2 t hq hu2 => exact profile2_anchors u v t hu2 hv hq
  | alternate t hq hu1 => subst u; exact alternateProfile_anchors v t hv hq

theorem label_anchors (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    HasAnchors (label u v hu hv) (anchorOfRoute (dispatch u v hu hv)) :=
  labelOfRoute_anchors hu hv _

/-- The sorted list, before forgetting order, used by every standard transfer. -/
def pairStartsInOrder (Q S donor : ℕ) (p : ℕ → ℕ) (a : Anchor) (k : ℕ) : List ℕ :=
  ((eligiblePairStarts Q S donor p a).sort).take k

theorem pairStartsInOrder_strict (Q S donor : ℕ) (p : ℕ → ℕ) (a : Anchor) (k : ℕ) :
    (pairStartsInOrder Q S donor p a k).Pairwise (· < ·) :=
  (Finset.sortedLT_sort _).pairwise.take

theorem pairStartsInOrder_valid (Q S donor : ℕ) (p : ℕ → ℕ) (a : Anchor) (k x : ℕ)
    (hx : x ∈ pairStartsInOrder Q S donor p a k) :
    x < S - x ∧ x ∈ leafLabels Q ∧ S - x ∈ leafLabels Q ∧
    p x = donor ∧ p (S - x) = donor ∧
    x ≠ a.C ∧ x ≠ a.Z ∧ S - x ≠ a.C ∧ S - x ≠ a.Z := by
  have he : x ∈ eligiblePairStarts Q S donor p a := by
    exact (Finset.mem_sort _).mp (List.mem_of_mem_take hx)
  rcases Finset.mem_filter.mp he with ⟨hI, hlt, hrest⟩
  exact ⟨hlt, hI, hrest⟩

theorem selected0_inOrder (t v : ℕ) : selected0 t v =
    (pairStartsInOrder (q0 t) (q0 t + 1) 5 (afterFirst0 t) (anchor0 t) (v-1)).toFinset := rfl

theorem selected1_inOrder (t u : ℕ) : selected1 t u =
    (pairStartsInOrder (q1 t) (q1 t + 1) 4 (afterFirst1 t) (anchor1 t) (u-1)).toFinset := rfl

theorem selected2_inOrder (t v : ℕ) : selected2 t v =
    (pairStartsInOrder (q2 t) (q2 t - 1) 2 (afterFirst2 t) (anchor2 t) (v-1)).toFinset := rfl

/-- Membership means that the smaller label has rank below k in the eligible list. -/
theorem pairStartsInOrder_rank (Q S donor : ℕ) (p : ℕ → ℕ) (a : Anchor) (k x : ℕ)
    (hx : x ∈ eligiblePairStarts Q S donor p a) :
    x ∈ pairStartsInOrder Q S donor p a k ↔
      ((eligiblePairStarts Q S donor p a).sort).idxOf x < k := by
  apply List.mem_take_iff_idxOf_lt
  exact (Finset.mem_sort _).mpr hx

end Partials.Graceful.Executable
