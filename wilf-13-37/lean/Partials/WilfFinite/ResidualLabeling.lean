import Partials.WilfFinite.ResidualDomains

/-! Selected representations are exponent vectors; repeated factors are not
fresh independent variables. These kernels retain one fixed allocation h,
the same numerical value vector, and joint graphs across all degrees.
No actual semigroup selection or historical matcher execution is asserted. -/
namespace Partials.WilfFinite.Forest
open Partials.WilfStructural.Packing
open scoped BigOperators

noncomputable def degreeMonomials (s d : ℕ) : Finset (Monomial s) := by
  classical
  exact (profileRectangle (fun _ : Fin s => d)).filter (fun u => degree u=d)

theorem mem_degreeMonomials (s d : ℕ) (u : Monomial s) :
    u ∈ degreeMonomials s d ↔ degree u=d := by
  classical
  constructor
  · intro h; exact (Finset.mem_filter.mp h).2
  · intro h
    exact Finset.mem_filter.mpr ⟨(mem_profileRectangle _ _).2
      (quota_coordinate_bound u d h),h⟩

noncomputable def DegreesFamily (s first last : ℕ) : Finset (Monomial s) := by
  classical
  exact (Finset.Icc first last).biUnion (degreeMonomials s)

theorem mem_DegreesFamily (s first last : ℕ) (u : Monomial s) :
    u ∈ DegreesFamily s first last ↔ first ≤ degree u ∧ degree u ≤ last := by
  classical
  simp [DegreesFamily,mem_degreeMonomials]

def ProperDivisor {s : ℕ} (v u : Monomial s) : Prop :=
  (∀ i, v i ≤ u i) ∧ 0 < degree v ∧ degree v < degree u

def Bipartition {s : ℕ} (v w u : Monomial s) : Prop :=
  (∀ i, v i+w i=u i) ∧ 0 < degree v ∧ 0 < degree w

theorem bipartition_degrees {s : ℕ} {v w u : Monomial s}
    (h : Bipartition v w u) : degree v+degree w=degree u := by
  unfold degree
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => h.1 i)

theorem bipartition_strict {s : ℕ} {v w u : Monomial s}
    (h : Bipartition v w u) : degree v < degree u ∧ degree w < degree u := by
  have heq := bipartition_degrees h
  have hv := h.2.1
  have hw := h.2.2
  omega

/-- This witness specifies exactly one selected order ideal and value map. Its
existence from numerical semigroups is SEL-global-ideal, still an R9 duty.
The full monomial evaluation may collide; only the selected family is injective. -/
structure SelectedOrderIdeal (s q : ℕ) where
  family : Finset (Monomial s)
  left : Finset (Monomial s)
  top : Finset (Monomial s)
  labels : LeftLabels s
  allocation : Allocation
  values : Fin s → ℤ
  m : ℤ
  rho : ℤ
  left_sub : left ⊆ family
  top_sub : top ⊆ family
  disjoint : Disjoint left top
  positive_iff : ∀ u ∈ family, 0 < labels u ↔ u ∈ left
  divisors : ∀ u ∈ family, ∀ v, ImmediateDivisor v u →
    2 ≤ degree v → v ∈ left ∧ labels v < labels u + (if u ∈ top then q else 0)
  value_injective : Set.InjOn (value values) (↑family : Set (Monomial s))
  quotas : HasQuotas left labels allocation

/-- A zero choice is mandatory precisely when not all remaining monomials must
be selected left. This proves that the actual nonselected choice passes the
total-quota test, even when that monomial is later selected at the top. -/
theorem actual_zero_choice {M : Type*} [DecidableEq M]
    (remaining selected : Finset M) (u : M)
    (hu : u ∈ remaining) (hnot : u ∉ selected) (hsub : selected ⊆ remaining) :
    selected.card < remaining.card := by
  have herase : selected ⊆ remaining.erase u := by
    intro v hv
    exact Finset.mem_erase.mpr ⟨by intro heq; subst v; exact hnot hv,hsub hv⟩
  have hc := Finset.card_le_card herase
  have he := Finset.card_erase_of_mem hu
  have hpos : 0 < remaining.card := Finset.card_pos.mpr ⟨u,hu⟩
  omega

theorem actual_positive_quota {M : Type*} [DecidableEq M]
    (remaining : Finset M) (label : M → ℕ) (u : M) (j : ℕ)
    (hu : u ∈ remaining) (hj : label u=j) :
    0 < (remaining.filter (fun v => label v=j)).card := by
  apply Finset.card_pos.mpr
  exact ⟨u,Finset.mem_filter.mpr ⟨hu,hj⟩⟩

theorem recorded_eligibility_lookahead {M : Type*} [DecidableEq M]
    (actual eligible : Finset M) (hactual : actual ⊆ eligible) (quota : ℕ)
    (hquota : actual.card=quota) : quota ≤ eligible.card :=
  quota_lookahead actual eligible hactual quota hquota

theorem distinct_immediate_divisor_degree {s : ℕ} {v u : Monomial s}
    (h : ImmediateDivisor v u) : degree v < degree u := by
  have hd := h.2
  omega

theorem all_degree_top_bound (q r t : ℕ) (htwo : 2 ≤ t) (hq : t ≤ q)
    (hr : 1 ≤ r) (hdiv : 3 ≤ t → t-1 ≤ r) : t ≤ min q (r+1) :=
  le_min hq (top_degree_from_left_divisor t r htwo hdiv hr)

def occupiedLevels (q : ℕ) (kappa : ℕ → ℕ) (lo hi : ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun j => lo ≤ j ∧ j ≤ hi ∧ 0 < kappa j)

/-- Rounding to the least occupied level cannot exceed an actual admissible
level. A failed proper piece consequently contradicts actual divisibility.
All bipartitions still have to be traversed in the concrete cap adapter. -/
theorem occupied_minimum_retains (q : ℕ) (kappa : ℕ → ℕ) (lo hi actual : ℕ)
    (ha : actual ∈ occupiedLevels q kappa lo hi) :
    ∃ hne : (occupiedLevels q kappa lo hi).Nonempty,
      (occupiedLevels q kappa lo hi).min' hne ≤ actual := by
  let hne : (occupiedLevels q kappa lo hi).Nonempty := ⟨actual,ha⟩
  exact ⟨hne,Finset.min'_le _ actual ha⟩

theorem ranked_interval_retains {s : ℕ} (B : Box s) (x : Fin s → ℤ)
    (hx : B.Contains x) (u : Monomial s) (m rho j : ℤ)
    (hj : value x u ∈ layer m rho j) :
    (monomialInterval B u ∩ layer m rho j).Nonempty := by
  exact ⟨value x u,Finset.mem_inter.mpr ⟨value_mem_interval B x hx u,hj⟩⟩

def signedCeiling (a positiveDenominator : ℤ) : ℤ := -((-a)/positiveDenominator)

theorem multiplicity_propagation (a b exponent xi other loOther hiOther L U : ℤ)
    (hexp : 0 < exponent) (hxi : L ≤ xi ∧ xi ≤ U)
    (hlo : a ≤ exponent*xi+other) (hhi : exponent*xi+other ≤ b)
    (hother : loOther ≤ other ∧ other ≤ hiOther) :
    max L (signedCeiling (a-hiOther) exponent) ≤ xi ∧
      xi ≤ min U ((b-loOther)/exponent) := by
  exact propagation_preserves a b exponent xi other loOther hiOther L U
    hexp hxi hlo hhi hother

theorem same_level_order_propagation (L U x y : ℤ)
    (hL : L ≤ x) (hU : y ≤ U) (horder : x+1 ≤ y) :
    L+1 ≤ y ∧ x ≤ U-1 := adjacent_propagation L U x y hL hU horder

noncomputable def JointIntegerCapacity {s : ℕ} (candidates : Finset (Monomial s))
    (B : Box s) (m rho q : ℤ) : ℕ :=
  matchingCapacity (intervalGraph candidates (topInterval B m rho q))

theorem actual_joint_integer_cap {s : ℕ} (actual candidates : Finset (Monomial s))
    (B : Box s) (x : Fin s → ℤ) (m rho q : ℤ) (delta K : ℕ)
    (hx : B.Contains x) (hsub : actual ⊆ candidates)
    (hinj : Set.InjOn (value x) (↑actual : Set (Monomial s)))
    (htop : ∀ u ∈ actual, value x u ∈ layer m rho q)
    (hpartition : delta=K+actual.card) :
    delta ≤ K+JointIntegerCapacity candidates B m rho q := by
  exact joint_integer_cap actual candidates (topInterval B m rho q) (value x)
    hsub hinj (fun u hu => value_mem_top B x hx u m rho q (htop u hu)) delta K hpartition

/-- Residue and value graphs have different right domains. Their capacities
must be recomputed on the SAME all-degree candidate set after propagation. -/
theorem actual_joint_residue_cap {L : Type*} [DecidableEq L]
    (actual candidates : Finset L) (interval : L → Finset ℤ) (val : L → ℤ)
    (m : ℤ) (hsub : actual ⊆ candidates)
    (hinj : Set.InjOn (fun u => val u % m) (↑actual : Set L))
    (hinterval : ∀ u ∈ actual, val u ∈ interval u) (s delta : ℕ)
    (hcard : actual.card=1+s+delta) :
    1+s+delta ≤ matchingCapacity (residueGraph candidates interval m) ∧
      delta ≤ matchingCapacity (residueGraph candidates interval m)-1-s :=
  joint_residue_cap actual candidates interval val m hsub hinj hinterval s delta hcard

theorem exact_joint_rejection (delta K T R s : ℕ)
    (hT : delta ≤ K+T) (hR : 1+s+delta ≤ R)
    (hreject : min (K+T) (R-1-s) < delta) : False :=
  joint_cap_rejects delta K T R s hT hR hreject

/-- Source/API duties: full all-bipartition ranked recursion, actual selected
ideal/quota instantiation, and exact greedy/augmenting maximum implementations.
Finite maxima above are mathematical reference definitions, never run reports. -/
def RankedCapAdapter {s : ℕ} (actual formal : Finset (Monomial s)) : Prop :=
  actual ⊆ formal

end Partials.WilfFinite.Forest
