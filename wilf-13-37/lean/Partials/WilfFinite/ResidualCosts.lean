import Partials.WilfFinite.TraversalCosts

/-! Relaxed residual-domain bounds. Complete coverage and singleton exclusion
are separate obligations. No profile, tuple, monomial, box or table is evaluated. -/
namespace Partials.WilfFinite.Application
open scoped BigOperators

def weightedMass (q : ℕ) (α : Fin (q-1) → ℕ) : ℕ :=
  ∑ i, (i.val+1)*α i
def ProfileCondition (q ν : ℕ) (α : Fin (q-1) → ℕ) : Prop :=
  weightedMass q α=ν

theorem weighted_coordinate_bound (q ν : ℕ) (α : Fin (q-1) → ℕ)
    (h : ProfileCondition q ν α) (i : Fin (q-1)) : (i.val+1)*α i ≤ ν := by
  have hs : (i.val+1)*α i ≤ weightedMass q α := by
    exact Finset.single_le_sum (fun j _ => Nat.zero_le ((j.val+1)*α j))
      (Finset.mem_univ i)
  exact h ▸ hs

theorem zero_surplus_unique (q : ℕ) (α : Fin (q-1) → ℕ)
    (h : ProfileCondition q 0 α) : α=fun _ => 0 := by
  funext i
  have hb := weighted_coordinate_bound q 0 α h i
  have ha : α i ≤ (i.val+1)*α i := by nlinarith
  omega

theorem zero_surplus_profile (q : ℕ) :
    ProfileCondition q 0 (fun _ => 0) := by simp [ProfileCondition,weightedMass]

def boundedProfiles (q ν : ℕ) : Finset (Fin (q-1) → Fin (ν+1)) :=
  Finset.univ.filter (fun α => weightedMass q (fun i => (α i).val)=ν)
def profileProductBound (q ν : ℕ) : ℕ :=
  ∏ w ∈ Finset.Icc 1 (q-1), (ν/w+1)
def profileStarsBound (q ν : ℕ) : ℕ := Nat.choose (ν+q-2) (q-2)
def profileCompositionBound (ν : ℕ) : ℕ := if ν=0 then 1 else 2^(ν-1)

/-- The source assumes 2<=q<n, so ν>0. This extension explicitly gives
the empty partition one profile. The q=2 allocation is also a singleton. -/
def ResidualProfileCountTarget : Prop := ∀ q ν : ℕ, 2 ≤ q →
  (boundedProfiles q ν).card ≤ profileProductBound q ν ∧
  (boundedProfiles q ν).card ≤ profileStarsBound q ν ∧
  (boundedProfiles q ν).card ≤ profileCompositionBound ν

theorem coordinate_choices_pow (a : ℕ) : a+1 ≤ 2^a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.pow_succ]
    have hp : 1 ≤ 2^a := by omega
    omega

theorem rectangle_pow_bound {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (α : ι → ℕ) :
    (∏ i ∈ F, (α i+1)) ≤ 2^(∑ i ∈ F, α i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    simp only [Finset.prod_insert hi,Finset.sum_insert hi,Nat.pow_add]
    exact Nat.mul_le_mul (coordinate_choices_pow (α i)) ih

def allocationCount (q : ℕ) (κ : ℕ → ℕ) : ℕ :=
  ∏ j ∈ Finset.Icc 2 (q-1), Nat.choose (κ j+j-2) (j-2)
def AllocationCountTarget : Prop :=
  (∀ κ : ℕ → ℕ, allocationCount 2 κ=1) ∧
  ∀ q : ℕ, ∀ κ : ℕ → ℕ, 3 ≤ q →
    allocationCount q κ ≤ (q-2)^(∑ j ∈ Finset.Icc 2 (q-1), κ j)

def monomialCount (s d : ℕ) : ℕ := Nat.choose (s+d) d-1-s
def labelPrefixBound (M K q : ℕ) : ℕ :=
  (M+1)*∑ i ∈ Finset.Icc 0 (min K M), Nat.choose M i*(q-1)^i
def scalarTupleBound (E F : ℕ) : ℕ := E*(F+1)*(E+F)
def boxPointCount {s : ℕ} (width : Fin s → ℕ) : ℕ := ∏ i, width i
def boxNodeBound {s : ℕ} (width : Fin s → ℕ) : ℕ :=
  if boxPointCount width=0 then 1 else 2*boxPointCount width-1

/-- The simple range-count inequality is independent of the actual tuple
domain and of its additional compression/cutoff tests. -/
theorem rho_fiber_bound (e δ E F : ℕ) (he : e ≤ E) (hδ : δ ≤ F) :
    e+δ ≤ E+F := by omega

theorem strict_cap_pass_bound (initial final decreases : ℕ)
    (h : decreases+final ≤ initial) : decreases ≤ initial := by omega

theorem binary_tree_nodes (internal leaves nodes : ℕ)
    (hfull : leaves=internal+1) (hparts : nodes=internal+leaves) :
    nodes=2*leaves-1 := by omega

theorem disjoint_leaf_injection {Leaf Point : Type*} [DecidableEq Leaf]
    [DecidableEq Point] (leaves : Finset Leaf) (points : Finset Point)
    (choose : Leaf → Point) (hp : ∀ l ∈ leaves, choose l ∈ points)
    (hi : Set.InjOn choose (↑leaves : Set Leaf)) : leaves.card ≤ points.card := by
  apply Finset.card_le_card_of_injOn choose
  · exact hp
  · exact hi

def propagationPassScale (R s b : ℕ) : ℕ := (R*s^2+s+1)*b^2
def integerMatchingScale (T logT b : ℕ) : ℕ := (T^2+T*logT)*b
def residueMatchingScale (A m edges b : ℕ) : ℕ := A*(A+m+edges)*b
def dictionaryScale (M s logM b : ℕ) : ℕ := M*s^2*logM*b^2
def residualDomainProduct (profiles rectangles allocations tuples labels boxes perBox : ℕ) : ℕ :=
  profiles*rectangles*allocations*tuples*labels*boxes*perBox

theorem residual_product_charging (P R A T L B X : ℕ)
    (work : ℕ) (h : work ≤ P*R*A*T*L*B*X) :
    work ≤ residualDomainProduct P R A T L B X := h

/-- This must be instantiated with actual finite domains and actual operation
counters of the specified one-visit, decreasing-cap, midpoint-split scheme.
It is an upper bound, and permits unresolved singleton leaves. -/
def ResidualCostTarget (work output : ℕ → ℕ) : Prop :=
  ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ ∀ n : ℕ, 2 ≤ n →
    work n ≤ A*2^(B*n^2)+output n

end Partials.WilfFinite.Application
