import Partials.Graceful.ExecutableTransport

/-! Exact correspondence of the six numerical constructions before the local
split with the independently defined merged parent graph.  The standard maps
are the actual maps after redistribution; the small maps are the literal
manuscript table rows. -/
namespace Partials.Graceful.Executable
open Symbolic NumericConstruction ManuscriptPresentation

/-- Recover the merged incidence from the proved final incidence. The numerical
map p is an independent input, and its two reserved parent values are required. -/
theorem merged_parent_of_split {u v : ℕ} (f : Vertex u v → Fin (q u v + 1))
    (a : Anchor) (p : ℕ → ℕ) (hi : Function.Injective f) (ha : HasAnchors f a)
    (hC : p a.C = a.B) (hZ : p a.Z = a.B)
    (hfinal : ∀ x : NamedVertex u v,
      Symbolic.splitParent p a (f (encode x)).val = (f (encode (namedParent x))).val)
    (x : NamedVertex u v) :
    p (f (encode x)).val = (f (encode (mergedParent x))).val := by
  by_cases hxC : x = anchorC u v
  · subst x
    change p (f (encode (anchorC u v))).val = (f (encode (anchorB u v))).val
    simpa only [ha.2.2.1, ha.2.1] using hC
  by_cases hxZ : x = anchorZ u v
  · subst x
    change p (f (encode (anchorZ u v))).val = (f (encode (anchorB u v))).val
    simpa only [ha.2.2.2, ha.2.1] using hZ
  have hnC : (f (encode x)).val ≠ a.C := by
    intro h
    apply hxC
    apply (namedEquiv u v).injective
    exact hi (Fin.ext (h.trans ha.2.2.1.symm))
  have hnZ : (f (encode x)).val ≠ a.Z := by
    intro h
    apply hxZ
    apply (namedEquiv u v).injective
    exact hi (Fin.ext (h.trans ha.2.2.2.symm))
  have hp : mergedParent x = namedParent x := by
    simpa only [ManuscriptPresentation.splitParent, if_neg hxC, if_neg hxZ]
      using split_merged_parent x
  simpa only [Symbolic.splitParent, if_neg hnC, if_neg hnZ, hp] using hfinal x

/-- The literal pre-split leaf assignment in the q=23 table. -/
def small23LeafParent (x : ℕ) : ℕ :=
  if x = 9 ∨ x = 13 ∨ x = 16 ∨ x = 18 then 2
  else if x = 7 then 3
  else if x = 10 ∨ x = 12 ∨ x = 17 then 4
  else if x = 15 then 5
  else if x = 14 then 19
  else if x = 8 ∨ x = 11 then 20
  else if x = 6 then 21 else 0

/-- The literal pre-split leaf assignment in the q=27 exceptional table. -/
def small27LeafParent (x : ℕ) : ℕ :=
  if x = 22 then 2
  else if x = 18 then 3
  else if x = 21 then 4
  else if x = 9 ∨ x = 12 ∨ x = 16 ∨ x = 19 then 5
  else if x = 10 ∨ x = 11 ∨ x = 13 ∨ x = 14 ∨ x = 15 ∨ x = 17 then 23
  else if x = 8 then 24
  else if x = 6 ∨ x = 7 ∨ x = 20 then 25 else 0

def small23MergedParent : ℕ → ℕ := fullParent 23 (skeletonParent2 23) small23LeafParent
def small27MergedParent : ℕ → ℕ := fullParent 27 (skeletonParent0 27) small27LeafParent

theorem small23_merged_parent (x : NamedVertex 1 1) :
    small23MergedParent (small23Label (encode x)).val =
      (small23Label (encode (mergedParent x))).val := by
  have h : ∀ x : NamedVertex 1 1,
      small23MergedParent (small23Label (encode x)).val =
        (small23Label (encode (mergedParent x))).val := by decide
  exact h x

theorem small27_merged_parent (x : NamedVertex 1 3) :
    small27MergedParent (small27Label (encode x)).val =
      (small27Label (encode (mergedParent x))).val := by
  have h : ∀ x : NamedVertex 1 3,
      small27MergedParent (small27Label (encode x)).val =
        (small27Label (encode (mergedParent x))).val := by decide
  exact h x

theorem profile0_merged_parent (u v t : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hq : q u v = q0 t) (hc : 0 < t ∨ 2 ≤ u) (x : NamedVertex u v) :
    fullAfterPairs0 t v ((profile0 u v t hu hv hq hc).labeling (encode x)).val =
      ((profile0 u v t hu hv hq hc).labeling (encode (mergedParent x))).val := by
  let F := profile0 u v t hu hv hq hc
  have hC : (anchor0 t).C ∈ leafLabels (q0 t) := by
    simp only [leafLabels, Finset.mem_Icc, anchor0, q0]; omega
  have hZ : (anchor0 t).Z ∈ leafLabels (q0 t) := by
    simp only [leafLabels, Finset.mem_Icc, anchor0, q0]; omega
  apply merged_parent_of_split F.labeling (anchor0 t) (fullAfterPairs0 t v)
      F.realization.injective (profile0_anchors u v t hu hv hq hc)
  · simpa [fullAfterPairs0, fullParent, hC] using (NumericConstruction.afterPairs0_anchor t v).1
  · simpa [fullAfterPairs0, fullParent, hZ] using (NumericConstruction.afterPairs0_anchor t v).2
  · intro y
    have h := congrArg Fin.val (F.realization_parent (encode y))
    rw [← encode_parent] at h
    change fullFinalParent0 t v (F.labeling (encode y)).val =
      (F.labeling (encode (namedParent y))).val at h
    simpa only [fullFinalParent0, finalParent0,
      fullParent_splitParent _ _ _ _ hC hZ, fullAfterPairs0] using h

theorem profile1_merged_parent (u v t : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hq : q u v = q1 t) (x : NamedVertex u v) :
    fullAfterPairs1 t u ((profile1 u v t hu hv hq).labeling (encode x)).val =
      ((profile1 u v t hu hv hq).labeling (encode (mergedParent x))).val := by
  let F := profile1 u v t hu hv hq
  have hC : (anchor1 t).C ∈ leafLabels (q1 t) := by
    simp only [leafLabels, Finset.mem_Icc, anchor1, q1]; omega
  have hZ : (anchor1 t).Z ∈ leafLabels (q1 t) := by
    simp only [leafLabels, Finset.mem_Icc, anchor1, q1]; omega
  apply merged_parent_of_split F.labeling (anchor1 t) (fullAfterPairs1 t u)
      F.realization.injective (profile1_anchors u v t hu hv hq)
  · simpa [fullAfterPairs1, fullParent, hC] using (NumericConstruction.afterPairs1_anchor t u).1
  · simpa [fullAfterPairs1, fullParent, hZ] using (NumericConstruction.afterPairs1_anchor t u).2
  · intro y
    have h := congrArg Fin.val (F.realization_parent (encode y))
    rw [← encode_parent] at h
    change fullFinalParent1 t u (F.labeling (encode y)).val =
      (F.labeling (encode (namedParent y))).val at h
    simpa only [fullFinalParent1, finalParent1,
      fullParent_splitParent _ _ _ _ hC hZ, fullAfterPairs1] using h

theorem profile2_merged_parent (u v t : ℕ) (hu : 2 ≤ u) (hv : 0 < v)
    (hq : q u v = q2 t) (x : NamedVertex u v) :
    fullAfterPairs2 t v ((profile2 u v t hu hv hq).labeling (encode x)).val =
      ((profile2 u v t hu hv hq).labeling (encode (mergedParent x))).val := by
  let F := profile2 u v t hu hv hq
  have hC : (anchor2 t).C ∈ leafLabels (q2 t) := by
    simp only [leafLabels, Finset.mem_Icc, anchor2, q2]; omega
  have hZ : (anchor2 t).Z ∈ leafLabels (q2 t) := by
    simp only [leafLabels, Finset.mem_Icc, anchor2, q2]; omega
  apply merged_parent_of_split F.labeling (anchor2 t) (fullAfterPairs2 t v)
      F.realization.injective (profile2_anchors u v t hu hv hq)
  · simpa [fullAfterPairs2, fullParent, hC] using (NumericConstruction.afterPairs2_anchor t v).1
  · simpa [fullAfterPairs2, fullParent, hZ] using (NumericConstruction.afterPairs2_anchor t v).2
  · intro y
    have h := congrArg Fin.val (F.realization_parent (encode y))
    rw [← encode_parent] at h
    change fullFinalParent2 t v (F.labeling (encode y)).val =
      (F.labeling (encode (namedParent y))).val at h
    simpa only [fullFinalParent2, finalParent2,
      fullParent_splitParent _ _ _ _ hC hZ, fullAfterPairs2] using h

theorem alternateProfile_merged_parent (v t : ℕ) (hv : 0 < v)
    (hq : q 1 v = q2 t) (x : NamedVertex 1 v) :
    fullAlternateAfterFirst t ((alternateProfile v t hv hq).labeling (encode x)).val =
      ((alternateProfile v t hv hq).labeling (encode (mergedParent x))).val := by
  let F := alternateProfile v t hv hq
  have hC : (alternateAnchor t).C ∈ leafLabels (q2 t) := by
    simp only [leafLabels, Finset.mem_Icc, alternateAnchor, q2]; omega
  have hZ : (alternateAnchor t).Z ∈ leafLabels (q2 t) := by
    simp only [leafLabels, Finset.mem_Icc, alternateAnchor, q2]; omega
  apply merged_parent_of_split F.labeling (alternateAnchor t) (fullAlternateAfterFirst t)
      F.realization.injective (alternateProfile_anchors v t hv hq)
  · simpa [fullAlternateAfterFirst, fullParent, hC] using
      (NumericConstruction.alternateAfterFirst_anchor t).1
  · simpa [fullAlternateAfterFirst, fullParent, hZ] using
      (NumericConstruction.alternateAfterFirst_anchor t).2
  · intro y
    have h := congrArg Fin.val (F.realization_parent (encode y))
    rw [← encode_parent] at h
    change fullAlternateFinalParent t (F.labeling (encode y)).val =
      (F.labeling (encode (namedParent y))).val at h
    simpa only [fullAlternateFinalParent, alternateFinalParent,
      fullParent_splitParent _ _ _ _ hC hZ, fullAlternateAfterFirst] using h

/-- Six existing literal numerical constructions before the final split. -/
def preSplitParentOfRoute {u v : ℕ} : Route u v → ℕ → ℕ
  | .small23 _ _ => small23MergedParent
  | .small27 _ _ => small27MergedParent
  | .residue0 t _ _ => fullAfterPairs0 t v
  | .residue1 t _ => fullAfterPairs1 t u
  | .residue2 t _ _ => fullAfterPairs2 t v
  | .alternate t _ _ => fullAlternateAfterFirst t

theorem labelOfRoute_merged_parent {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (r : Route u v) (x : NamedVertex u v) :
    preSplitParentOfRoute r (labelOfRoute hu hv r (encode x)).val =
      (labelOfRoute hu hv r (encode (mergedParent x))).val := by
  cases r with
  | small23 hu1 hv1 => subst u; subst v; exact small23_merged_parent x
  | small27 hu1 hv3 => subst u; subst v; exact small27_merged_parent x
  | residue0 t hq hc => exact profile0_merged_parent u v t hu hv hq hc x
  | residue1 t hq => exact profile1_merged_parent u v t hu hv hq x
  | residue2 t hq hu2 => exact profile2_merged_parent u v t hu2 hv hq x
  | alternate t hq hu1 => subst u; exact alternateProfile_merged_parent v t hv hq x

/-- All positive parameters, with the same computable labels as the final tree. -/
theorem namedLabel_merged_parent (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (x : NamedVertex u v) :
    preSplitParentOfRoute (dispatch u v hu hv) (namedLabel u v hu hv x).val =
      (namedLabel u v hu hv (mergedParent x)).val :=
  labelOfRoute_merged_parent hu hv _ x

/-- Both directions of the exact oriented-edge correspondence. -/
theorem mergedEdge_iff_numeric {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (r : Route u v) (a b : NamedVertex u v) :
    mergedEdge a b ↔
      (labelOfRoute hu hv r (encode b)).val ≠ 0 ∧
      preSplitParentOfRoute r (labelOfRoute hu hv r (encode b)).val =
        (labelOfRoute hu hv r (encode a)).val := by
  have hi := (labelOfRoute_graceful hu hv r).1.1
  have hr := (labelOfRoute_graceful hu hv r).2.1
  have hn : (labelOfRoute hu hv r (encode b)).val = 0 ↔ b = .root := by
    constructor
    · intro h
      apply (namedEquiv u v).injective
      exact hi ((Fin.ext h).trans hr.symm)
    · rintro rfl
      exact congrArg Fin.val hr
  have he : preSplitParentOfRoute r (labelOfRoute hu hv r (encode b)).val =
      (labelOfRoute hu hv r (encode a)).val ↔ mergedParent b = a := by
    rw [labelOfRoute_merged_parent]
    constructor
    · intro h
      exact (namedEquiv u v).injective (hi (Fin.ext h))
    · rintro h
      rw [h]
  exact and_congr (not_congr hn).symm he.symm

end Partials.Graceful.Executable
