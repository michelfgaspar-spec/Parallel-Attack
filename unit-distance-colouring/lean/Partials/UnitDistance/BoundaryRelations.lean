import Partials.UnitDistance.EqualityGadget

/-! Blind source for main.tex lemma join and supplement interfaces.
Not compiled. Complete boundaries carry physical coordinate variables.
Selected edges and missing induced unit pairs are separate factors. -/
namespace Partials.UnitDistance

def BoundaryRelation (G : PhysicalGraph) (B : Set ℂ)
    (assignment : ℂ → Colour4) : Prop :=
  ∃ c : ℂ → Colour4, ProperPhysical G c ∧
    ∀ v ∈ B, c v = assignment v

def ExtraEdgesProper (extra : Set (ℂ × ℂ)) (c : ℂ → Colour4) : Prop :=
  ∀ e ∈ extra, c e.1 ≠ c e.2

structure CompletePhysicalInterfaces {I : Type*}
    (pieces : I → PhysicalGraph) (G : PhysicalGraph)
    (B : Set ℂ) (boundaries : I → Set ℂ)
    (extra : Set (ℂ × ℂ)) : Prop where
  vertex_cover : ∀ v, v ∈ G.vertices ↔ ∃ i, v ∈ (pieces i).vertices
  edge_union : ∀ e, e ∈ G.edges ↔ (∃ i, e ∈ (pieces i).edges) ∨ e ∈ extra
  output_inside : ∀ v ∈ B, v ∈ G.vertices
  local_boundary_inside : ∀ i v, v ∈ boundaries i → v ∈ (pieces i).vertices
  output_boundary : ∀ i v, v ∈ (pieces i).vertices → v ∈ B → v ∈ boundaries i
  overlap_boundary : ∀ i j v, i ≠ j → v ∈ (pieces i).vertices →
    v ∈ (pieces j).vertices → v ∈ boundaries i
  extra_boundary : ∀ i e, e ∈ extra → ∀ v, v ∈ (pieces i).vertices →
    (v = e.1 ∨ v = e.2) → v ∈ boundaries i

def JoinedBoundaryRelation {I : Type*} (pieces : I → PhysicalGraph)
    (boundaries : I → Set ℂ) (extra : Set (ℂ × ℂ)) (B : Set ℂ)
    (assignment : ℂ → Colour4) : Prop :=
  ∃ q : ℂ → Colour4,
    (∀ i, BoundaryRelation (pieces i) (boundaries i) q) ∧
    ExtraEdgesProper extra q ∧ ∀ v ∈ B, q v = assignment v

/-- Classical gluing uses agreement only on physical overlaps. No disjointness
of gadget interiors is needed; there is one actual coordinate variable. -/
theorem glue_physical_functions {I : Type*} (pieces : I → PhysicalGraph)
    (localColour : I → ℂ → Colour4)
    (compatible : ∀ i j v, v ∈ (pieces i).vertices →
      v ∈ (pieces j).vertices → localColour i v = localColour j v) :
    ∃ c : ℂ → Colour4, ∀ i v, v ∈ (pieces i).vertices → c v = localColour i v := by
  classical
  let c : ℂ → Colour4 := fun v ↦
    if h : ∃ i, v ∈ (pieces i).vertices then localColour (Classical.choose h) v else 0
  refine ⟨c, ?_⟩
  intro i v hv
  change (if h : ∃ j, v ∈ (pieces j).vertices then
    localColour (Classical.choose h) v else 0) = localColour i v
  rw [dif_pos (show ∃ j, v ∈ (pieces j).vertices from ⟨i, hv⟩)]
  exact compatible _ i v
    (Classical.choose_spec (show ∃ j, v ∈ (pieces j).vertices from ⟨i, hv⟩)) hv

theorem complete_boundary_join {I : Type*} (pieces : I → PhysicalGraph)
    (G : PhysicalGraph) (B : Set ℂ) (boundaries : I → Set ℂ)
    (extra : Set (ℂ × ℂ))
    (h : CompletePhysicalInterfaces pieces G B boundaries extra)
    (assignment : ℂ → Colour4) :
    BoundaryRelation G B assignment ↔
      JoinedBoundaryRelation pieces boundaries extra B assignment := by
  classical
  constructor
  · rintro ⟨c, hc, hB⟩
    refine ⟨c, ?_, ?_, hB⟩
    · intro i
      refine ⟨c, ?_, ?_⟩
      · intro e he
        exact hc e ((h.edge_union e).mpr (Or.inl ⟨i, he⟩))
      · intro v hv
        rfl
    · intro e he
      exact hc e ((h.edge_union e).mpr (Or.inr he))
  · rintro ⟨q, hlocal, hextra, houtput⟩
    let localColour : I → ℂ → Colour4 := fun i ↦ Classical.choose (hlocal i)
    have hproper : ∀ i, ProperPhysical (pieces i) (localColour i) := by
      intro i
      exact (Classical.choose_spec (hlocal i)).1
    have hboundary : ∀ i v, v ∈ boundaries i → localColour i v = q v := by
      intro i
      exact (Classical.choose_spec (hlocal i)).2
    have hcompatible : ∀ i j v, v ∈ (pieces i).vertices →
        v ∈ (pieces j).vertices → localColour i v = localColour j v := by
      intro i j v hi hj
      by_cases hij : i = j
      · subst j
        rfl
      · exact (hboundary i v (h.overlap_boundary i j v hij hi hj)).trans
          (hboundary j v (h.overlap_boundary j i v (Ne.symm hij) hj hi)).symm
    obtain ⟨c, hglue⟩ := glue_physical_functions pieces localColour hcompatible
    have hExtraValue : ∀ e ∈ extra, ∀ v, (v = e.1 ∨ v = e.2) → c v = q v := by
      intro e he v hv
      have heG : e ∈ G.edges := (h.edge_union e).mpr (Or.inr he)
      have hvG : v ∈ G.vertices := by
        rcases hv with hv | hv
        · simpa only [hv] using (G.endpoints e heG).1
        · simpa only [hv] using (G.endpoints e heG).2
      obtain ⟨i, hi⟩ := (h.vertex_cover v).mp hvG
      exact (hglue i v hi).trans
        (hboundary i v (h.extra_boundary i e he v hi hv))
    refine ⟨c, ?_, ?_⟩
    · intro e he
      rcases (h.edge_union e).mp he with ⟨i, hei⟩ | heextra
      · rw [hglue i e.1 ((pieces i).endpoints e hei).1,
          hglue i e.2 ((pieces i).endpoints e hei).2]
        exact hproper i e hei
      · rw [hExtraValue e heextra e.1 (Or.inl rfl),
          hExtraValue e heextra e.2 (Or.inr rfl)]
        exact hextra e heextra
    · intro v hv
      obtain ⟨i, hi⟩ := (h.vertex_cover v).mp (h.output_inside v hv)
      exact (hglue i v hi).trans
        ((hboundary i v (h.output_boundary i v hi hv)).trans (houtput v hv))

/-- For an induced graph every absent unit pair, including internal pairs,
must be an extra factor. A strict-cross-edge list alone is insufficient. -/
def MissingInducedPairs (G : PhysicalGraph) : Set (ℂ × ℂ) :=
  {e | InducedUnitPair G e.1 e.2 ∧ e ∉ G.edges ∧ e.swap ∉ G.edges}

def BoundaryPalettePartition (B : Set ℂ) (q : ℂ → Colour4) : Setoid B where
  r := fun v w ↦ q v.val = q w.val
  iseqv := ⟨fun _ ↦ rfl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

def BoundaryInclusion {A B : Set ℂ} (hAB : A ⊆ B) (v : A) : B :=
  ⟨v.val, hAB v.property⟩

/-- Restrict the single global partition through the physical boundary
inclusion. Local blocks come from this restriction rather than independently
renamed literal palette labels. -/
theorem global_partition_restricts (q : ℂ → Colour4) (A B : Set ℂ)
    (hAB : A ⊆ B) (v w : A) :
    (BoundaryPalettePartition A q).r v w ↔
      (BoundaryPalettePartition B q).r (BoundaryInclusion hAB v)
        (BoundaryInclusion hAB w) := Iff.rfl

theorem boundary_palette_image_at_most_four (q : ℂ → Colour4) (B : Finset ℂ) :
    (B.image q).card ≤ 4 := by
  classical
  simpa only [Fintype.card_fin] using (Finset.card_le_univ (B.image q))

/- Independently canonicalized local palette names do not satisfy the literal
compatibility premise of glue_physical_functions. The theorem instead uses
restrictions of the same global assignment q. No actual relation tables,
partition table, 8180-variable encoding or SAT clauses were evaluated. -/
end Partials.UnitDistance
