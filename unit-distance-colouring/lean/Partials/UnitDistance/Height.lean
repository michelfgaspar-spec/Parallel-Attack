import Partials.UnitDistance.Model

/-! BLIND coefficient source. Coefficient bounds do not certify M2 membership;
seed transports and all126 units have separate exact algebra/data duties. -/
namespace Partials.UnitDistance.Height

theorem height_add {a b : IntegerCode} {A B : ℕ}
    (ha : Height49AtMost a A) (hb : Height49AtMost b B) :
    Height49AtMost (a + b) (A + B) := by
  intro i
  calc
    |(a + b) i| = |a i + b i| := rfl
    _ ≤ |a i| + |b i| := abs_add_le _ _
    _ ≤ (A : ℤ) + (B : ℤ) := add_le_add (ha i) (hb i)
    _ = ((A + B : ℕ) : ℤ) := by simp

theorem point49_add (a b : IntegerCode) : point49 (a + b) = point49 a + point49 b := by
  simp [point49, evalInteger, add_mul, Finset.sum_add_distrib, add_div]

theorem local_offset_bound {unit seed : IntegerCode}
    (hu : Height49AtMost unit 63) (hs : Height49AtMost seed 154) :
    Height49AtMost (unit + seed) 217 := by
  simpa using height_add hu hs

theorem final_point_bound {anchor offset : IntegerCode}
    (ha : Height49AtMost anchor 3087) (ho : Height49AtMost offset 217) :
    Height49AtMost (anchor + offset) 3304 := by
  simpa using height_add ha ho

/-- Every visited cursor is either the representative or an already-created
endpoint; omitted old-coordinate steps still have bounded anchors. -/
def VisitedAnchorCoverage (visited representatives endpoints : Finset IntegerCode) : Prop :=
  visited ⊆ representatives ∪ endpoints

theorem visited_anchor_height (visited representatives endpoints : Finset IntegerCode)
    (hcover : VisitedAnchorCoverage visited representatives endpoints)
    (hr : ∀ c ∈ representatives, Height49AtMost c 49)
    (he : ∀ c ∈ endpoints, Height49AtMost c 3087) :
    ∀ c ∈ visited, Height49AtMost c 3087 := by
  intro c hc
  rcases Finset.mem_union.mp (hcover hc) with h | h
  · intro i
    have hi := hr c h i
    omega
  · exact he c h

theorem graph_height_from_offsets (G : PhysicalGraph)
    (coverage : ∀ z ∈ G.vertices, ∃ anchor offset : IntegerCode,
      Height49AtMost anchor 3087 ∧ Height49AtMost offset 217 ∧
      z = point49 (anchor + offset)) :
    ∀ z ∈ G.vertices, ∃ c : IntegerCode, z = point49 c ∧ Height49AtMost c 3304 := by
  intro z hz
  obtain ⟨a, o, ha, ho, hval⟩ := coverage z hz
  exact ⟨a + o, hval, final_point_bound ha ho⟩

end Partials.UnitDistance.Height
