import Partials.Parity.PlayTransport

/-! Frozen path-iteration.tex P4-D1--D4. These are tree-label ranks, not
Parity.Outcome priorities. No path calculation or tactic has been executed.
The actual height-one tree/name interface is separate from ranked work. -/
namespace Partials.ParityAlgorithms.Path

inductive Priority where
  | one | two
  deriving DecidableEq, Repr

structure Arena (n : Nat) where
  positive : 0 < n
  even : Fin n → Bool
  priority : Fin n → Priority

def Edge {n : Nat} (_A : Arena n) (v w : Fin n) : Prop :=
  v.val + 1 = w.val ∨ w.val + 1 = v.val ∨
    (v = w ∧ (v.val = 0 ∨ v.val + 1 = n))

instance {n : Nat} (A : Arena n) (v w : Fin n) : Decidable (Edge A v w) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _))

theorem edge_symmetric {n : Nat} (A : Arena n) (v w : Fin n) :
    Edge A v w → Edge A w v := by
  rintro (h | h | ⟨h, hb⟩)
  · exact Or.inr (Or.inl h)
  · exact Or.inl h
  · subst w; exact Or.inr (Or.inr ⟨rfl, hb⟩)

theorem edge_self_iff {n : Nat} (A : Arena n) (v : Fin n) :
    Edge A v v ↔ v.val = 0 ∨ v.val + 1 = n := by
  simp [Edge] <;> omega

theorem singleton_has_only_loop (A : Arena 1) (v w : Fin 1) :
    v = w ∧ Edge A v w := by
  have hv : v.val = 0 := by omega
  have hw : w.val = 0 := by omega
  have he : v = w := Fin.ext (hv.trans hw.symm)
  exact ⟨he, Or.inr (Or.inr ⟨he, Or.inl hv⟩)⟩

theorem edge_total {n : Nat} (A : Arena n) (v : Fin n) :
    ∃ w, Edge A v w := by
  by_cases hz : v.val = 0
  · exact ⟨v, Or.inr (Or.inr ⟨rfl, Or.inl hz⟩)⟩
  · let w : Fin n := ⟨v.val - 1, by omega⟩
    exact ⟨w, Or.inr (Or.inl (by dsimp [w]; omega))⟩

/-- Constant-size physical successor constructor: left/right positions and
one endpoint loop, including exactly one loop when n=1. -/
def neighborList {n : Nat} (_A : Arena n) (v : Fin n) : List (Fin n) :=
  (if h : 0 < v.val then [⟨v.val - 1, by omega⟩] else []) ++
  (if h : v.val + 1 < n then [⟨v.val + 1, h⟩] else []) ++
  (if v.val = 0 ∨ v.val + 1 = n then [v] else [])

/-- The physical constant-size list retains exactly the original arcs,
including the endpoint loop and the sole loop of a singleton path. -/
theorem mem_neighborList_iff {n : Nat} (A : Arena n) (v w : Fin n) :
    w ∈ neighborList A v ↔ Edge A v w := by
  have hv := v.isLt
  have hw := w.isLt
  unfold neighborList
  split_ifs <;> simp [Edge, Fin.ext_iff] <;> omega

theorem neighborList_nodup {n : Nat} (A : Arena n) (v : Fin n) :
    (neighborList A v).Nodup := by
  have hv := v.isLt
  unfold neighborList
  split_ifs <;> simp [List.nodup_append, Fin.ext_iff] <;> omega

theorem neighborList_at_most_two {n : Nat} (A : Arena n) (v : Fin n) :
    (neighborList A v).length ≤ 2 := by
  unfold neighborList
  split <;> split <;> split <;> simp_all <;> omega

/-- Exact product over original Odd vertices, including unreachable choices. -/
structure OddPolicy {n : Nat} (A : Arena n) where
  choose : {v : Fin n // A.even v = false} → Fin n
  legal : ∀ v, Edge A v.val (choose v)

def SelectedEdge {n : Nat} {A : Arena n} (τ : OddPolicy A)
    (v w : Fin n) : Prop :=
  Edge A v w ∧ ∀ h : A.even v = false, w = τ.choose ⟨v, h⟩

/-- No phantom Even choices: all original arcs remain at an Even vertex. -/
theorem selected_even_iff {n : Nat} {A : Arena n} (τ : OddPolicy A)
    (v w : Fin n) (he : A.even v = true) :
    SelectedEdge τ v w ↔ Edge A v w := by
  constructor
  · exact And.left
  · intro h; refine ⟨h, ?_⟩; intro ho; simp_all

theorem selected_odd_iff {n : Nat} {A : Arena n} (τ : OddPolicy A)
    (v w : Fin n) (ho : A.even v = false) :
    SelectedEdge τ v w ↔ w = τ.choose ⟨v, ho⟩ := by
  constructor
  · intro h; exact h.2 ho
  · intro h; subst w; exact ⟨τ.legal ⟨v, ho⟩, fun _ => rfl⟩

/-- Full label rank ell is TOP. In priority-two truncation all finite leaves
are the empty tuple; TOP stays strictly above that tuple. -/
def ValidRank (ell r : Nat) : Prop := r ≤ ell
abbrev Vector (n : Nat) := Fin n → Nat
def ValidVector {n : Nat} (ell : Nat) (x : Vector n) : Prop :=
  ∀ v, ValidRank ell (x v)
def VectorLE {n : Nat} (x y : Vector n) : Prop := ∀ v, x v ≤ y v

structure HeightOneInterface (Name : Type*) (n : Nat) where
  ell : Nat
  leaves : Fin ell → Name
  names_injective : Function.Injective leaves
  /- Ranked order is the supplied actual leaf order. Native ordered-tree
  immediate-edge/prefix validation remains an explicit adapter duty. -/
  leaves_at_least_n : n ≤ ell

inductive FullLabel (Name : Type*) where
  | leaf (name : Name)
  | top

def decodeRank {Name : Type*} {n : Nat} (T : HeightOneInterface Name n)
    (r : Fin (T.ell + 1)) : FullLabel Name :=
  if h : r.val < T.ell then .leaf (T.leaves ⟨r.val, h⟩) else .top

def theta {n : Nat} (A : Arena n) (ell : Nat)
    (x : Vector n) (v w : Fin n) : Nat :=
  if v = w then
    match A.priority v with | .one => ell | .two => 0
  else
    match A.priority v with
    | .one => min (x w + 1) ell
    | .two => if x w < ell then 0 else ell

def Satisfied {n : Nat} (A : Arena n) (ell : Nat)
    (x : Vector n) (v w : Fin n) : Prop :=
  match A.priority v with
  | .one => x w < x v ∨ (x v = ell ∧ x w = ell)
  | .two => x w < ell ∨ x v = ell

def Tight {n : Nat} (A : Arena n) (ell : Nat)
    (x : Vector n) (v w : Fin n) : Prop := x v = theta A ell x v w

def Loose {n : Nat} (A : Arena n) (ell : Nat)
    (x : Vector n) (v w : Fin n) : Prop :=
  Satisfied A ell x v w ∧ theta A ell x v w < x v

def liftRank {n : Nat} (A : Arena n) (ell : Nat)
    (x : Vector n) (v w : Fin n) : Nat := max (x v) (theta A ell x v w)

theorem theta_self_one {n : Nat} (A : Arena n) (ell : Nat)
    (x : Vector n) (v : Fin n) (h : A.priority v = .one) :
    theta A ell x v v = ell := by simp [theta, h]

theorem theta_self_two {n : Nat} (A : Arena n) (ell : Nat)
    (x : Vector n) (v : Fin n) (h : A.priority v = .two) :
    theta A ell x v v = 0 := by simp [theta, h]

theorem theta_bounded {n : Nat} (A : Arena n) (ell : Nat)
    (x : Vector n) (v w : Fin n) : theta A ell x v w ≤ ell := by
  by_cases heq : v = w
  · subst w; cases hp : A.priority v <;> simp [theta, hp]
  · cases hp : A.priority v with
    | one => simp [theta, heq, hp]
    | two => by_cases hw : x w < ell <;> simp [theta, heq, hp, hw]

theorem theta_monotone {n : Nat} (A : Arena n) (ell : Nat)
    {x y : Vector n} (hxy : VectorLE x y) (v w : Fin n) :
    theta A ell x v w ≤ theta A ell y v w := by
  unfold theta
  split
  · exact le_refl _
  · cases h : A.priority v with
    | one => exact min_le_min (Nat.add_le_add_right (hxy w) 1) (le_refl ell)
    | two =>
      by_cases hx : x w < ell
      · simp [hx]
      · have hy : ¬ y w < ell := by have := hxy w; omega
        simp [hx, hy]

theorem satisfied_iff_threshold {n : Nat} (A : Arena n) (ell : Nat)
    {x : Vector n} (hx : ValidVector ell x) (v w : Fin n) :
    Satisfied A ell x v w ↔ theta A ell x v w ≤ x v := by
  have hv : x v ≤ ell := hx v
  have hw : x w ≤ ell := hx w
  by_cases heq : v = w
  · subst w; cases hp : A.priority v <;> simp [Satisfied, theta, hp] <;> omega
  · cases hp : A.priority v with
    | one =>
      simp only [Satisfied, hp, theta, if_neg heq]
      by_cases ht : x w + 1 ≤ ell
      · rw [min_eq_left ht]; omega
      · rw [min_eq_right (by omega : ell ≤ x w + 1)]; omega
    | two =>
      simp only [Satisfied, hp, theta, if_neg heq]
      by_cases ht : x w < ell <;> simp [ht] <;> omega

theorem top_satisfies_every_arc {n : Nat} (A : Arena n) (ell : Nat)
    {x : Vector n} (hx : ValidVector ell x) (v w : Fin n)
    (ht : x v = ell) : Satisfied A ell x v w := by
  apply (satisfied_iff_threshold A ell hx v w).mpr
  simpa [ht] using theta_bounded A ell x v w

theorem priority_two_loop_never_eligible {n : Nat} (A : Arena n)
    (ell : Nat) (x : Vector n) (hx : ValidVector ell x)
    (v : Fin n) (hp : A.priority v = .two) :
    Satisfied A ell x v v := by
  have hv : x v ≤ ell := hx v
  simp only [Satisfied, hp]
  omega

def Feasible {n : Nat} {A : Arena n} (ell : Nat) (τ : OddPolicy A)
    (x : Vector n) : Prop :=
  ∀ v, if he : A.even v = true then
    ∃ w, Edge A v w ∧ Satisfied A ell x v w
  else ∀ ho : A.even v = false, Satisfied A ell x v (τ.choose ⟨v, ho⟩)

/-- Independently specified least original feasible answer; no accelerated
evaluator output appears in this definition. Finite-lattice construction of
a witness is R8-D-path-original-fixed-point. -/
def IsEvaluation {n : Nat} {A : Arena n} (ell : Nat) (τ : OddPolicy A)
    (floor answer : Vector n) : Prop :=
  ValidVector ell answer ∧ VectorLE floor answer ∧ Feasible ell τ answer ∧
    ∀ z, ValidVector ell z → VectorLE floor z → Feasible ell τ z →
      VectorLE answer z

theorem evaluation_unique {n : Nat} {A : Arena n} {ell : Nat}
    {τ : OddPolicy A} {f x y : Vector n}
    (hx : IsEvaluation ell τ f x) (hy : IsEvaluation ell τ f y) : x = y := by
  funext v
  exact Nat.le_antisymm (hx.2.2.2 y hy.1 hy.2.1 hy.2.2.1 v)
    (hy.2.2.2 x hx.1 hx.2.1 hx.2.2.1 v)

end Partials.ParityAlgorithms.Path
