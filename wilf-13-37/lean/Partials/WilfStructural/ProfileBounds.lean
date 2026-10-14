import Partials.WilfStructural.PackingBounds

/-! UNCOMPILED L20--L22 kernels. Domain completeness is distinguished from
elimination of every member of that domain. -/
namespace Partials.WilfStructural.Packing

theorem weighted_coordinate_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight α : ι → ℕ) (ν : ℕ) (hsum : ∑ i, weight i * α i = ν)
    (i : ι) (hpositive : 0 < weight i) : α i ≤ ν / weight i := by
  have hterm : weight i * α i ≤ ∑ j, weight j * α j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (weight j * α j)) (Finset.mem_univ i)
  apply (Nat.le_div_iff_mul_le hpositive).2
  simpa [hsum, mul_comm] using hterm

/- The dependent product gives a genuinely finite coordinate rectangle. -/
def profileRectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bound : ι → ℕ) : Finset (ι → ℕ) :=
  Fintype.piFinset fun i => Finset.range (bound i + 1)

theorem mem_profileRectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (bound α : ι → ℕ) : α ∈ profileRectangle bound ↔ ∀ i, α i ≤ bound i := by
  simp [profileRectangle, Nat.lt_succ_iff]

theorem weighted_profile_in_finite_domain {ι : Type*} [Fintype ι] [DecidableEq ι]
    (weight α : ι → ℕ) (ν : ℕ) (hsum : ∑ i, weight i * α i = ν)
    (hpositive : ∀ i, 0 < weight i) :
    α ∈ (profileRectangle fun i => ν / weight i).filter
      (fun a => ∑ i, weight i * a i = ν) := by
  apply Finset.mem_filter.mpr
  exact ⟨(mem_profileRectangle _ _).2
    (fun i => weighted_coordinate_bound weight α ν hsum i (hpositive i)), hsum⟩

theorem quota_coordinate_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ℕ) (κ : ℕ) (hsum : ∑ i, h i = κ) (i : ι) : h i ≤ κ := by
  have ht : h i ≤ ∑ j, h j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  simpa [hsum] using ht

/- One fixed allocation is supplied; no independent choice at each shadow. -/
theorem quota_allocation_in_rectangle {ι : Type*} [Fintype ι] [DecidableEq ι]
    (h : ι → ℕ) (κ : ℕ) (hsum : ∑ i, h i = κ) :
    h ∈ profileRectangle (fun _ => κ) := by
  exact (mem_profileRectangle _ _).2 (quota_coordinate_bound h κ hsum)

theorem ranked_distance (x : ℕ → ℤ) (a d : ℕ) :
    (∀ k, a ≤ k → k < a+d → x k+1 ≤ x (k+1)) →
    x a + (d : ℤ) ≤ x (a+d) := by
  induction d with
  | zero => intro hstep; simp
  | succ d ih =>
    intro hstep
    have hi := ih (fun k hka hkd => hstep k hka (by omega))
    have hs := hstep (a+d) (by omega) (by omega)
    simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, Nat.add_assoc, add_assoc] using
      (show x a + (d : ℤ) + 1 ≤ x (a+d+1) by omega)

theorem simultaneous_rank_bounds (x : ℕ → ℤ) (β a : ℕ) (L U : ℤ)
    (ha : a < β) (hlo : ∀ k, k < β → L ≤ x k)
    (hhi : ∀ k, k < β → x k ≤ U)
    (hstep : ∀ k, k+1 < β → x k+1 ≤ x (k+1)) :
    L+(a : ℤ) ≤ x a ∧ x a ≤ U-((β-1-a : ℕ) : ℤ) := by
  have hleft := ranked_distance x 0 a (by
    intro k hk hka
    exact hstep k (by omega))
  have hright := ranked_distance x a (β-1-a) (by
    intro k hk hka
    exact hstep k (by omega))
  have hzero := hlo 0 (by omega)
  have hlast := hhi (β-1) (by omega)
  have hind : a+(β-1-a) = β-1 := by omega
  rw [hind] at hright
  simp only [Nat.zero_add] at hleft
  omega

/- Pigeonhole lookahead: chosen values inject into the remaining eligible
monomials. Counting a superset of eligibility stays conservative. -/
theorem quota_lookahead {α : Type*} [DecidableEq α]
    (chosen eligible : Finset α) (hsub : chosen ⊆ eligible) (quota : ℕ)
    (hquota : chosen.card = quota) : quota ≤ eligible.card := by
  rw [← hquota]
  exact Finset.card_le_card hsub

theorem top_degree_from_left_divisor (t r : ℕ)
    (ht : 2 ≤ t) (hdivisor : t ≥ 3 → t-1 ≤ r) (hr : 1 ≤ r) : t ≤ r+1 := by
  by_cases h : 3 ≤ t
  · have := hdivisor h
    omega
  · omega

/- Numerical value representatives inject into formal monomials, although the
full monomial-to-value map can have collisions. -/
theorem selected_values_le_formal {V M : Type*} [DecidableEq V] [DecidableEq M]
    (values : Finset V) (formal : Finset M) (repr : V → M) (eval : M → V)
    (hrep : ∀ v ∈ values, repr v ∈ formal)
    (heval : ∀ v ∈ values, eval (repr v) = v) : values.card ≤ formal.card := by
  apply Finset.card_le_card_of_injOn repr hrep
  intro a ha b hb hab
  calc
    a = eval (repr a) := (heval a ha).symm
    _ = eval (repr b) := congrArg eval hab
    _ = b := heval b hb

end Partials.WilfStructural.Packing
