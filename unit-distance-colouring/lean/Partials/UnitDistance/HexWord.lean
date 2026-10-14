import Partials.UnitDistance.SevenPairKernel

/-! R6 BLIND SOURCE / UNCOMPILED. Main `lem:hex`.
These statements use actual integer displacements and six nonnegative
multiplicities. A coordinate description is kept separate from the complex
cyclotomic applicability duty in SevenPairKernel. -/
namespace Partials.UnitDistance.Words

def hexNorm (a b : ℤ) : ℤ := max (max |a| |b|) |a + b|
def pairNorm (p : ℤ × ℤ) : ℤ := hexNorm p.1 p.2
abbrev LocalCounts := Fin 6 → ℕ
def localValue (c : LocalCounts) : ℤ × ℤ :=
  ∑ h : Fin 6, ((c h : ℤ) * (hexStep h).1, (c h : ℤ) * (hexStep h).2)
def localCost (c : LocalCounts) : ℕ := ∑ h : Fin 6, c h

theorem hexStep_coordinate_bounds (h : Fin 6) :
    |(hexStep h).1| ≤ 1 ∧ |(hexStep h).2| ≤ 1 := by
  fin_cases h <;> norm_num [hexStep]

theorem abs_as_if (z : ℤ) : |z| = if 0 ≤ z then z else -z := by
  split_ifs with h
  · exact abs_of_nonneg h
  · exact abs_of_nonpos (le_of_not_ge h)

theorem hexNorm_nonneg (a b : ℤ) : 0 ≤ hexNorm a b := by
  exact le_trans (abs_nonneg a) (le_trans (le_max_left _ _) (le_max_left _ _))

theorem abs_first_le_hex (a b : ℤ) : |a| ≤ hexNorm a b :=
  le_trans (le_max_left _ _) (le_max_left _ _)
theorem abs_second_le_hex (a b : ℤ) : |b| ≤ hexNorm a b :=
  le_trans (le_max_right _ _) (le_max_left _ _)
theorem abs_sum_le_hex (a b : ℤ) : |a + b| ≤ hexNorm a b := le_max_right _ _

theorem hexNorm_add_le (a b c d : ℤ) :
    hexNorm (a + c) (b + d) ≤ hexNorm a b + hexNorm c d := by
  apply max_le
  · apply max_le
    · exact le_trans (abs_add_le _ _) (add_le_add
        (abs_first_le_hex a b) (abs_first_le_hex c d))
    · exact le_trans (abs_add_le _ _) (add_le_add
        (abs_second_le_hex a b) (abs_second_le_hex c d))
  · have hsum : a + c + (b + d) = (a + b) + (c + d) := by ring
    rw [hsum]
    exact le_trans (abs_add_le _ _) (add_le_add
      (abs_sum_le_hex a b) (abs_sum_le_hex c d))

theorem pairNorm_sum_le {α : Type*} (s : Finset α) (v : α → ℤ × ℤ) :
    pairNorm (∑ i ∈ s, v i) ≤ ∑ i ∈ s, pairNorm (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairNorm, hexNorm]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      exact le_trans (hexNorm_add_le _ _ _ _) (add_le_add_right ih _)

theorem scaled_step_norm (h : Fin 6) (n : ℕ) :
    hexNorm ((n : ℤ) * (hexStep h).1) ((n : ℤ) * (hexStep h).2) = n := by
  have hn : (0 : ℤ) ≤ n := Int.ofNat_nonneg n
  fin_cases h <;>
    simp [hexStep, hexNorm, hn, abs_of_nonneg hn, abs_of_nonpos (neg_nonpos.mpr hn)]

/-- Every letter changes the three integer coordinates by at most one.
Subadditivity proves the lower bound for arbitrary nonnegative counts. -/
theorem local_norm_le_cost (c : LocalCounts) :
    pairNorm (localValue c) ≤ (localCost c : ℤ) := by
  have h := pairNorm_sum_le Finset.univ
    (fun h : Fin 6 => ((c h : ℤ) * (hexStep h).1,
      (c h : ℤ) * (hexStep h).2))
  simpa [localValue, localCost, pairNorm, scaled_step_norm, Nat.cast_sum] using h

/-- Cancel opposite signs first; the remaining displacement is along a signed
basis direction. Counts are indexed in the exact six-root order in main.tex. -/
def canonicalLocalCounts (a b : ℤ) : LocalCounts :=
  if 0 ≤ a then
    if 0 ≤ b then ![a.toNat, b.toNat, 0, 0, 0, 0]
    else
      let m := min a (-b)
      ![(a - m).toNat, 0, 0, 0, (-b - m).toNat, m.toNat]
  else
    if 0 ≤ b then
      let m := min (-a) b
      ![0, (b - m).toNat, m.toNat, (-a - m).toNat, 0, 0]
    else ![0, 0, 0, (-a).toNat, (-b).toNat, 0]

theorem canonical_local_value (a b : ℤ) :
    localValue (canonicalLocalCounts a b) = (a, b) := by
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b
  all_goals
    apply Prod.ext <;>
      simp [localValue, canonicalLocalCounts, ha, hb, hexStep,
        Fin.sum_univ_succ] <;> omega

/-- The half-sum identity is proved by sign cases, not postulated as a norm
formula or obtained from stored word lengths. -/
theorem twice_hexNorm (a b : ℤ) :
    2 * hexNorm a b = |a| + |b| + |a + b| := by
  simp only [hexNorm, abs_as_if]
  split_ifs <;> omega

theorem canonical_local_cost (a b : ℤ) :
    (localCost (canonicalLocalCounts a b) : ℤ) = hexNorm a b := by
  have hhalf := twice_hexNorm a b
  simp only [abs_as_if] at hhalf
  by_cases ha : 0 ≤ a <;> by_cases hb : 0 ≤ b <;>
    by_cases hab : 0 ≤ a + b
  all_goals
    simp [localCost, canonicalLocalCounts, ha, hb, Fin.sum_univ_succ]
    simp only [ha, hb, hab, if_true, if_false] at hhalf
    omega

def IsShortestLocal (a b : ℤ) (c : LocalCounts) : Prop :=
  localValue c = (a, b) ∧
    ∀ d : LocalCounts, localValue d = (a, b) → localCost c ≤ localCost d

theorem canonical_is_shortest (a b : ℤ) :
    IsShortestLocal a b (canonicalLocalCounts a b) := by
  refine ⟨canonical_local_value a b, ?_⟩
  intro d hd
  have hlower := local_norm_le_cost d
  rw [hd] at hlower
  have heq := canonical_local_cost a b
  simp only [pairNorm] at hlower
  omega

theorem shortest_local_cost (a b : ℤ) (c : LocalCounts)
    (hc : IsShortestLocal a b c) : (localCost c : ℤ) = hexNorm a b := by
  have hlower := local_norm_le_cost c
  rw [hc.1] at hlower
  have hupper := hc.2 (canonicalLocalCounts a b) (canonical_local_value a b)
  have hcanonical := canonical_local_cost a b
  simp only [pairNorm] at hlower
  omega

end Partials.UnitDistance.Words
