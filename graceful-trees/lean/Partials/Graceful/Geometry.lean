import Partials.Graceful.Model
import Mathlib.Combinatorics.SimpleGraph.Diam

/-! Actual graph distances for the family of manuscript §1.  Adjacency is
exactly the undirected version of the edges used by the graceful labeling.
No distance, diameter, or centre assertion is a premise. -/
namespace Partials.Graceful

/-- Forget only the chosen orientation of the existing parent edges. -/
def simpleGraph (u v : ℕ) : SimpleGraph (Vertex u v) where
  Adj a b := Edge a b ∨ Edge b a
  symm := ⟨by intro a b h; exact h.symm⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h <;>
      have hd := parent_depth x h.1
    all_goals rw [h.2] at hd; exact (Nat.lt_irrefl _) hd⟩

/-- This is an adjacency adapter for the *same* finite edge graph. -/
theorem simpleGraph_adj_iff_ends (u v : ℕ) (a b : Vertex u v) :
    (simpleGraph u v).Adj a b ↔
      ∃ e : EdgeIndex u v, (graph u v).ends e = (a,b) ∨
        (graph u v).ends e = (b,a) := by
  change Edge a b ∨ Edge b a ↔ _
  constructor
  · rintro (⟨hb, hp⟩ | ⟨ha, hp⟩)
    · exact ⟨⟨b, hb⟩, Or.inl (Prod.ext hp rfl)⟩
    · exact ⟨⟨a, ha⟩, Or.inr (Prod.ext hp rfl)⟩
  · rintro ⟨e, h | h⟩
    · left
      have hb : e.val = b := congrArg Prod.snd h
      have ha : parent e.val = a := congrArg Prod.fst h
      exact ⟨hb ▸ e.property, hb ▸ ha⟩
    · right
      have ha : e.val = a := congrArg Prod.snd h
      have hb : parent e.val = b := congrArg Prod.fst h
      exact ⟨ha ▸ e.property, ha ▸ hb⟩

theorem parent_adj {u v : ℕ} (x : Vertex u v) (hx : x ≠ .root) :
    (simpleGraph u v).Adj (parent x) x := Or.inl ⟨hx, rfl⟩

/-- The explicit walk from the root follows the given parent incidences. -/
def rootWalk {u v : ℕ} : (x : Vertex u v) → (simpleGraph u v).Walk .root x
  | .root => .nil
  | .levelOne i => (parent_adj (.levelOne i) (by simp)).toWalk
  | .levelTwo i j =>
      (parent_adj (.levelOne i) (by simp)).toWalk.append
        (parent_adj (.levelTwo i j) (by simp)).toWalk
  | .leaf i j k =>
      ((parent_adj (.levelOne i) (by simp)).toWalk.append
        (parent_adj (.levelTwo i j) (by simp)).toWalk).append
          (parent_adj (.leaf i j k) (by simp)).toWalk

theorem rootWalk_length {u v : ℕ} (x : Vertex u v) :
    (rootWalk x).length = depth x := by
  cases x <;> rfl

theorem simpleGraph_connected (u v : ℕ) : (simpleGraph u v).Connected := by
  let : Nonempty (Vertex u v) := ⟨.root⟩
  exact ⟨fun a b => ⟨(rootWalk a).reverse.append (rootWalk b)⟩⟩

theorem depth_le_three {u v : ℕ} (x : Vertex u v) : depth x ≤ 3 := by
  cases x <;> simp [depth]

theorem depth_eq_zero_iff {u v : ℕ} (x : Vertex u v) : depth x = 0 ↔ x = .root := by
  cases x <;> simp [depth]

/-- A branch identifier; the root's arbitrary identifier will not affect any
distance because its depth is zero. -/
def branchIndex {u v : ℕ} : Vertex u v → Fin 3
  | .root => 0
  | .levelOne i => i
  | .levelTwo i _ => i
  | .leaf i _ _ => i

/-- A potential increasing down one branch and decreasing down all others. -/
def signedDepth {u v : ℕ} (i : Fin 3) : Vertex u v → ℤ
  | .root => 0
  | .levelOne j => if j = i then 1 else -1
  | .levelTwo j _ => if j = i then 2 else -2
  | .leaf j _ _ => if j = i then 3 else -3

theorem signedDepth_parent_bounds {u v : ℕ} (i : Fin 3) (x : Vertex u v) :
    signedDepth i x ≤ signedDepth i (parent x) + 1 ∧
      signedDepth i (parent x) ≤ signedDepth i x + 1 := by
  cases x <;> simp only [signedDepth, parent]
  · omega
  all_goals split <;> omega

theorem signedDepth_adj {u v : ℕ} (i : Fin 3) {a b : Vertex u v}
    (h : (simpleGraph u v).Adj a b) : signedDepth i b ≤ signedDepth i a + 1 := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact (signedDepth_parent_bounds i b).1
  · exact (signedDepth_parent_bounds i a).2

/-- Every actual walk has length at least its signed potential increase. -/
theorem signedDepth_walk {u v : ℕ} (i : Fin 3) {a b : Vertex u v}
    (p : (simpleGraph u v).Walk a b) :
    signedDepth i b ≤ signedDepth i a + (p.length : ℤ) := by
  induction p with
  | nil => simp
  | @cons a c b h p ih =>
    have he := signedDepth_adj i h
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    omega

theorem signedDepth_dist {u v : ℕ} (i : Fin 3) (a b : Vertex u v) :
    signedDepth i b ≤ signedDepth i a + ((simpleGraph u v).dist a b : ℤ) := by
  obtain ⟨p, hp⟩ := (simpleGraph_connected u v).exists_walk_length_eq_dist a b
  simpa only [hp] using signedDepth_walk i p

theorem signedDepth_own {u v : ℕ} (x : Vertex u v) :
    signedDepth (branchIndex x) x = (depth x : ℤ) := by
  cases x <;> simp [signedDepth, branchIndex, depth]

theorem signedDepth_other {u v : ℕ} (i : Fin 3) (x : Vertex u v)
    (h : branchIndex x ≠ i) : signedDepth i x = -(depth x : ℤ) := by
  cases x <;> simp_all [signedDepth, branchIndex, depth]

/-- The encoded depth is proved equal to shortest-path distance. -/
theorem dist_root {u v : ℕ} (x : Vertex u v) :
    (simpleGraph u v).dist .root x = depth x := by
  apply le_antisymm
  · simpa only [rootWalk_length] using (simpleGraph u v).dist_le (rootWalk x)
  · have h := signedDepth_dist (branchIndex x) .root x
    rw [signedDepth_own] at h
    simp only [signedDepth, zero_add] at h
    exact_mod_cast h

theorem dist_le_depth_add {u v : ℕ} (a b : Vertex u v) :
    (simpleGraph u v).dist a b ≤ depth a + depth b := by
  simpa only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
    rootWalk_length] using
      (simpleGraph u v).dist_le ((rootWalk a).reverse.append (rootWalk b))

/-- Distinct branches force every shortest walk through the root. -/
theorem dist_of_different_branches {u v : ℕ} (a b : Vertex u v)
    (h : branchIndex a ≠ branchIndex b) :
    (simpleGraph u v).dist a b = depth a + depth b := by
  apply le_antisymm (dist_le_depth_add a b)
  have hp := signedDepth_dist (branchIndex b) a b
  rw [signedDepth_own, signedDepth_other _ _ h] at hp
  omega

/-- In every branch the first depth-two child has one pendant child,
independently of the parameters. -/
def branchLeaf (u v : ℕ) (i : Fin 3) : Vertex u v :=
  .leaf i ⟨0, by unfold depthTwoCount; split <;> omega⟩
    ⟨0, by simp [pendantCount]⟩

@[simp] theorem branchLeaf_depth (u v : ℕ) (i : Fin 3) :
    depth (branchLeaf u v i) = 3 := rfl

@[simp] theorem branchLeaf_branch (u v : ℕ) (i : Fin 3) :
    branchIndex (branchLeaf u v i) = i := rfl

/-- A specified leaf in a branch different from the vertex's branch. -/
def oppositeLeaf {u v : ℕ} (x : Vertex u v) : Vertex u v :=
  branchLeaf u v (if branchIndex x = 0 then 1 else 0)

theorem oppositeLeaf_different {u v : ℕ} (x : Vertex u v) :
    branchIndex x ≠ branchIndex (oppositeLeaf x) := by
  simp only [oppositeLeaf, branchLeaf_branch]
  split <;> simp_all

@[simp] theorem oppositeLeaf_depth {u v : ℕ} (x : Vertex u v) :
    depth (oppositeLeaf x) = 3 := rfl

/-- The opposite-branch witness attains the full eccentricity. -/
theorem dist_oppositeLeaf {u v : ℕ} (x : Vertex u v) :
    (simpleGraph u v).dist x (oppositeLeaf x) = depth x + 3 := by
  simpa only [oppositeLeaf_depth] using
    dist_of_different_branches x (oppositeLeaf x) (oppositeLeaf_different x)

theorem diameter_witness (u v : ℕ) :
    (simpleGraph u v).dist (branchLeaf u v 0) (branchLeaf u v 1) = 6 := by
  simpa using dist_of_different_branches (branchLeaf u v 0) (branchLeaf u v 1)
    (by simp)

/-- Every distance is at most six, using the explicit root walks. -/
theorem dist_le_six {u v : ℕ} (a b : Vertex u v) :
    (simpleGraph u v).dist a b ≤ 6 := by
  have h := dist_le_depth_add a b
  have ha := depth_le_three a
  have hb := depth_le_three b
  omega

/-- Eccentricity is the library supremum of actual shortest-path distances. -/
theorem eccent_eq_depth_add_three {u v : ℕ} (x : Vertex u v) :
    (simpleGraph u v).eccent x = ((depth x + 3 : ℕ) : ℕ∞) := by
  apply le_antisymm
  · apply ((simpleGraph u v).eccent_le_iff _ _).2
    intro y
    rw [← ((simpleGraph_connected u v) x y).coe_dist_eq_edist]
    have h := dist_le_depth_add x y
    have hy := depth_le_three y
    exact_mod_cast (show (simpleGraph u v).dist x y ≤ depth x + 3 by omega)
  · have h := (simpleGraph u v).edist_le_eccent (u := x) (v := oppositeLeaf x)
    rw [← ((simpleGraph_connected u v) x (oppositeLeaf x)).coe_dist_eq_edist,
      dist_oppositeLeaf] at h
    exact h

theorem ediam_eq_six (u v : ℕ) : (simpleGraph u v).ediam = 6 := by
  apply le_antisymm
  · apply SimpleGraph.ediam_le_of_edist_le
    intro a b
    rw [← ((simpleGraph_connected u v) a b).coe_dist_eq_edist]
    exact_mod_cast dist_le_six a b
  · have h := (simpleGraph u v).edist_le_ediam
      (u := branchLeaf u v 0) (v := branchLeaf u v 1)
    rw [← ((simpleGraph_connected u v) _ _).coe_dist_eq_edist,
      diameter_witness] at h
    exact h

/-- Diameter six for the actual undirected edge graph. -/
theorem diameter_six (u v : ℕ) : (simpleGraph u v).diam = 6 := by
  simp [SimpleGraph.diam, ediam_eq_six]

theorem radius_three (u v : ℕ) : (simpleGraph u v).radius = 3 := by
  apply le_antisymm
  · have h := (simpleGraph u v).radius_le_eccent (u := Vertex.root)
    simpa [eccent_eq_depth_add_three, depth] using h
  · rw [SimpleGraph.radius]
    apply le_iInf
    intro x
    rw [eccent_eq_depth_add_three]
    exact_mod_cast (show 3 ≤ depth x + 3 by omega)

/-- The centre is the singleton root, using the library's minimum-eccentricity
definition. -/
theorem center_eq_root (u v : ℕ) :
    (simpleGraph u v).center = {Vertex.root} := by
  ext x
  rw [SimpleGraph.mem_center_iff, radius_three, eccent_eq_depth_add_three]
  change ((depth x + 3 : ℕ) : ℕ∞) = 3 ↔ x = .root
  constructor
  · intro h
    have hd : depth x + 3 = 3 := by exact_mod_cast h
    exact (depth_eq_zero_iff x).1 (by omega)
  · rintro rfl
    rfl

/-- The exact positive-parameter manuscript claim.  Geometry in fact holds
for every natural parameter pair because the fixed pendant witnesses remain. -/
theorem positive_diameter_and_unique_center (u v : ℕ) (_hu : 0 < u) (_hv : 0 < v) :
    (simpleGraph u v).diam = 6 ∧
      (simpleGraph u v).center = {Vertex.root} :=
  ⟨diameter_six u v, center_eq_root u v⟩

end Partials.Graceful
