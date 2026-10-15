import Partials.Graceful.ManuscriptPresentation

/-! Arbitrary choices of branch and star order for the independently defined
manuscript family. Child multiplicities follow the chosen star, so permutations
do not change u or v or exchange their different branch roles. -/
namespace Partials.Graceful.ManuscriptPresentation

/-- The leaf count is the literal profile of the star selected by τ. -/
inductive OrderedVertex (u v : ℕ) (τ : Equiv.Perm Star) where
  | root
  | branch (b : Branch)
  | star (s : Star)
  | leaf (s : Star) (k : Fin (leaves u v (τ s)))

def orderedParent {u v : ℕ} (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star) :
    OrderedVertex u v τ → OrderedVertex u v τ
  | .root => .root
  | .branch _ => .root
  | .star s => .branch (σ.symm (starBranch (τ s)))
  | .leaf s _ => .star s

def orderedDepth {u v : ℕ} {τ : Equiv.Perm Star} : OrderedVertex u v τ → ℕ
  | .root => 0
  | .branch _ => 1
  | .star _ => 2
  | .leaf _ _ => 3

def orderEncode {u v : ℕ} (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star) :
    OrderedVertex u v τ → NamedVertex u v
  | .root => .root
  | .branch b => .branch (σ b)
  | .star s => .star (τ s)
  | .leaf s k => .leaf (τ s) k

def orderDecode {u v : ℕ} (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star) :
    NamedVertex u v → OrderedVertex u v τ
  | .root => .root
  | .branch b => .branch (σ.symm b)
  | .star s => .star (τ.symm s)
  | .leaf s k => .leaf (τ.symm s)
      (Fin.cast (congrArg (leaves u v) (τ.apply_symm_apply s)).symm k)

theorem fin_cast_heq {m n : ℕ} (h : m = n) (i : Fin m) : HEq (Fin.cast h i) i := by
  subst n
  rfl

theorem orderDecode_encode {u v : ℕ} (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star)
    (x : OrderedVertex u v τ) : orderDecode σ τ (orderEncode σ τ x) = x := by
  cases x <;> simp [orderDecode, orderEncode]
  exact fin_cast_heq _ _

theorem orderEncode_decode {u v : ℕ} (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star)
    (x : NamedVertex u v) : orderEncode σ τ (orderDecode σ τ x) = x := by
  cases x <;> simp [orderDecode, orderEncode]
  exact fin_cast_heq _ _

def orderEquiv (u v : ℕ) (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star) :
    OrderedVertex u v τ ≃ NamedVertex u v where
  toFun := orderEncode σ τ
  invFun := orderDecode σ τ
  left_inv := orderDecode_encode σ τ
  right_inv := orderEncode_decode σ τ

theorem orderEncode_parent {u v : ℕ} (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star)
    (x : OrderedVertex u v τ) :
    orderEncode σ τ (orderedParent σ τ x) = namedParent (orderEncode σ τ x) := by
  cases x <;> simp [orderEncode, orderedParent, namedParent]

theorem orderEncode_root_iff {u v : ℕ} (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star)
    (x : OrderedVertex u v τ) : orderEncode σ τ x = .root ↔ x = .root := by
  constructor
  · intro h
    exact (orderEquiv u v σ τ).injective h
  · rintro rfl
    rfl

def orderedEdge {u v : ℕ} (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star)
    (a b : OrderedVertex u v τ) : Prop :=
  b ≠ .root ∧ orderedParent σ τ b = a

theorem ordered_parent_depth {u v : ℕ} (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star)
    (x : OrderedVertex u v τ) (hx : x ≠ .root) :
    orderedDepth (orderedParent σ τ x) < orderedDepth x := by
  cases x <;> simp_all [orderedParent, orderedDepth]

def orderedGraph (u v : ℕ) (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star) :
    SimpleGraph (OrderedVertex u v τ) where
  Adj a b := orderedEdge σ τ a b ∨ orderedEdge σ τ b a
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro x h
    rcases h with h | h <;> have hd := ordered_parent_depth σ τ x h.1
    all_goals rw [h.2] at hd; exact Nat.lt_irrefl _ hd⟩

theorem orderedEdge_iff_named {u v : ℕ} (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star)
    (a b : OrderedVertex u v τ) :
    orderedEdge σ τ a b ↔ namedEdge (orderEncode σ τ a) (orderEncode σ τ b) := by
  unfold orderedEdge namedEdge
  rw [← orderEncode_parent]
  exact and_congr (not_congr (orderEncode_root_iff σ τ b)).symm
    (orderEquiv u v σ τ).injective.eq_iff.symm

def orderIso (u v : ℕ) (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star) :
    orderedGraph u v σ τ ≃g namedGraph u v where
  toEquiv := orderEquiv u v σ τ
  map_rel_iff' := by
    intro a b
    exact or_congr (orderedEdge_iff_named σ τ a b).symm
      (orderedEdge_iff_named σ τ b a).symm

/-- Root-preserving graph correspondence for every branch/star ordering. -/
def reorderedIso (u v : ℕ) (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star) :
    orderedGraph u v σ τ ≃g simpleGraph u v :=
  (orderIso u v σ τ).trans (originalIso u v)

theorem reorderedIso_root (u v : ℕ) (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star) :
    reorderedIso u v σ τ .root = .root := rfl

/-- Each reordering preserves the literal oriented endpoint pair. -/
theorem orderedEdge_iff_ends {u v : ℕ} (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star)
    (a b : OrderedVertex u v τ) :
    orderedEdge σ τ a b ↔ ∃ e : EdgeIndex u v,
      (graph u v).ends e = (encode (orderEncode σ τ a), encode (orderEncode σ τ b)) := by
  rw [orderedEdge_iff_named, namedEdge_iff_ends]

/-- Parameterized leaf incidence; no equality of different star multiplicities is assumed. -/
theorem reordered_leaf_endpoint (u v : ℕ) (σ : Equiv.Perm Branch)
    (τ : Equiv.Perm Star) (s : Star) (k : Fin (leaves u v (τ s))) :
    orderedEdge σ τ (.star s) (.leaf s k) := by
  constructor
  · intro h
    cases h
  · rfl

end Partials.Graceful.ManuscriptPresentation
