import Partials.UnitDistance.Model

/-! BLIND conditional union-bound arithmetic. Occurrence-disjoint paired
blocks may share physical coordinates. Edge counts refer to selected edges.
Numerals below are authored source targets, never current evaluations. -/
namespace Partials.UnitDistance.Counts

def vertexBudget (T P : ℤ) : ℤ := 4096 + 1065 * T - 86 * P
def selectedEdgeBudget (T P : ℤ) : ℤ := 110592 + 6071 * T - 198 * P

theorem paired_vertex_algebra (T P : ℤ) :
    (4096 + T) + 1064 * (T - 2 * P) + 2042 * P = vertexBudget T P := by
  unfold vertexBudget
  ring

theorem paired_selected_edge_algebra (T P : ℤ) :
    110592 + 6071 * (T - 2 * P) + 11944 * P = selectedEdgeBudget T P := by
  unfold selectedEdgeBudget
  ring

theorem paired_union_bounds (V E : ℕ) (T P : ℤ)
    (hV : (V : ℤ) ≤ (4096 + T) + 1064 * (T - 2 * P) + 2042 * P)
    (hE : (E : ℤ) ≤ 110592 + 6071 * (T - 2 * P) + 11944 * P) :
    (V : ℤ) ≤ vertexBudget T P ∧ (E : ℤ) ≤ selectedEdgeBudget T P := by
  rw [paired_vertex_algebra] at hV
  rw [paired_selected_edge_algebra] at hE
  exact ⟨hV, hE⟩

theorem final_budget_arithmetic :
    vertexBudget 3437445 1460199 = 3535305907 ∧
    selectedEdgeBudget 3437445 1460199 = 20579719785 := by
  norm_num [vertexBudget, selectedEdgeBudget]

theorem unpaired_budget_arithmetic : vertexBudget 3437445 0 = 3660883021 := by
  norm_num [vertexBudget]

theorem adding_pairs_improves_budget {T P Q : ℤ} (h : P ≤ Q) :
    vertexBudget T Q ≤ vertexBudget T P ∧
    selectedEdgeBudget T Q ≤ selectedEdgeBudget T P := by
  unfold vertexBudget selectedEdgeBudget
  constructor <;> linarith

theorem graph_bounds_from_accounting (G : PhysicalGraph)
    (hV : (G.vertices.card : ℤ) ≤
      (4096 + 3437445) + 1064 * (3437445 - 2 * 1460199) + 2042 * 1460199)
    (hE : (G.edges.card : ℤ) ≤
      110592 + 6071 * (3437445 - 2 * 1460199) + 11944 * 1460199) :
    G.vertices.card ≤ 3535305907 ∧ G.edges.card ≤ 20579719785 := by
  obtain ⟨hv, he⟩ := paired_union_bounds G.vertices.card G.edges.card 3437445 1460199 hV hE
  obtain ⟨av, ae⟩ := final_budget_arithmetic
  rw [av] at hv
  rw [ae] at he
  exact ⟨by exact_mod_cast hv, by exact_mod_cast he⟩

/-- Primitive finite-union accounting, with the real physical overlaps
retained. Actual counts must be instantiated from exact identified geometry,
the seen forest and eligible occurrence matching, not a final bound witness. -/
structure BlockAccountingDuty (G : PhysicalGraph) (T P : ℕ) where
  disjoint_occurrences : 2 * P ≤ T
  skeleton : ℕ
  skeleton_upper : skeleton ≤ 4096 + T
  single_blocks : ℕ
  pair_blocks : ℕ
  single_count : single_blocks + 2 * P = T
  pair_count : pair_blocks = P
  vertex_union : (G.vertices.card : ℤ) ≤ (skeleton : ℤ) +
    1064 * (single_blocks : ℤ) + 2042 * (pair_blocks : ℤ)
  selected_edge_union : (G.edges.card : ℤ) ≤ 110592 +
    6071 * (single_blocks : ℤ) + 11944 * (pair_blocks : ℤ)

theorem bounds_from_block_accounting (G : PhysicalGraph) (T P : ℕ)
    (d : BlockAccountingDuty G T P) :
    (G.vertices.card : ℤ) ≤ vertexBudget T P ∧
    (G.edges.card : ℤ) ≤ selectedEdgeBudget T P := by
  have hs : (d.skeleton : ℤ) ≤ 4096 + (T : ℤ) := by exact_mod_cast d.skeleton_upper
  have hsingle : (d.single_blocks : ℤ) + 2 * (P : ℤ) = (T : ℤ) := by
    exact_mod_cast d.single_count
  have hpair : (d.pair_blocks : ℤ) = (P : ℤ) := by exact_mod_cast d.pair_count
  have hv := d.vertex_union
  have he := d.selected_edge_union
  unfold vertexBudget selectedEdgeBudget
  constructor <;> linarith

end Partials.UnitDistance.Counts
