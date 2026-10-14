import Partials.UnitDistance.Characters

/-! R6 blind source. The finite graph and Hoffman/Fourier bridge is an
explicit primitive duty. It is not inferred from stored eigenvalues and
does not include either non-four-colourability or the line-hit iff. -/
namespace Partials.UnitDistance

variable {V : Type*} [AddCommGroup V] [DecidableEq V]

noncomputable def binaryPaletteEncoding : BinaryPalette ≃ Colour4 :=
  Fintype.equivFinOfCardEq (by norm_num [BinaryPalette, Colour4])

def HasFourCayleyColouring (F : CommonBinaryLineFamily V)
    (S : Finset (Fin 21)) : Prop :=
  ∃ c : V → Colour4, ProperCayley F S c

def NoFourCayleyColouring (F : CommonBinaryLineFamily V)
    (S : Finset (Fin 21)) : Prop := ¬ HasFourCayleyColouring F S

theorem not_line_hit_has_four_colour (F : CommonBinaryLineFamily V)
    (S : Finset (Fin 21)) (hnot : ¬ LineHit F S) : HasFourCayleyColouring F S := by
  classical
  unfold LineHit at hnot
  push_neg at hnot
  obtain ⟨h, h0, hmiss⟩ := hnot
  refine ⟨fun v => binaryPaletteEncoding (twoCharacterColor h (h.comp F.R) v), ?_⟩
  intro a b hab he
  exact paired_colour_proper_when_missed F h S hmiss a b hab
    (binaryPaletteEncoding.injective he)

def IndependentCayley (F : CommonBinaryLineFamily V) (S : Finset (Fin 21))
    (s : Finset V) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, a ≠ b → a + b ∉ lineDirections F S

noncomputable def colourClass [Fintype V] (c : V → Colour4) (k : Colour4) : Finset V :=
  Finset.univ.filter (fun v => c v = k)

theorem proper_colour_class_independent [Fintype V]
    (F : CommonBinaryLineFamily V) (S : Finset (Fin 21))
    (c : V → Colour4) (hc : ProperCayley F S c) (k : Colour4) :
    IndependentCayley F S (colourClass c k) := by
  classical
  intro a ha b hb hab hedge
  have hca := (Finset.mem_filter.mp ha).2
  have hcb := (Finset.mem_filter.mp hb).2
  exact hc a b hedge (hca.trans hcb.symm)

/-- Elementary fibre counting, independently of graph or spectral facts. -/
theorem four_fibre_card_sum (s : Finset V) (c : V → Colour4) :
    (∑ k : Colour4, (s.filter (fun v => c v = k)).card) = s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert v s hv ih =>
      have hcount : ∀ k : Colour4,
          ((insert v s).filter (fun x => c x = k)).card =
            (s.filter (fun x => c x = k)).card + if c v = k then 1 else 0 := by
        intro k
        by_cases hk : c v = k <;> simp [Finset.filter_insert, hk, hv]
      simp_rw [hcount]
      rw [Finset.sum_add_distrib, ih]
      simp [hv, eq_comm]

/-- Exact hypotheses for the use of Hoffman's bound. `least_character`
requires the least eigenvalue to occur at an actual nonzero binary
functional, obtained from a complete Fourier basis; `hoffman` is the finite
simple regular graph ratio theorem for every independent set. Its analytic
proof, graph adapter and hypotheses are deferred, not locally executed. -/
structure SpectralRatioDuty [Fintype V]
    (F : CommonBinaryLineFamily V) (S : Finset (Fin 21)) where
  vertex_count : Fintype.card V = 4096
  zero_not_direction : (0 : V) ∉ lineDirections F S
  direction_count : (lineDirections F S).card = 3 * S.card
  least : ℤ
  least_negative : least < 0
  least_functional : V →+ ZMod 2
  least_nonzero : least_functional ≠ 0
  least_character : least = lineEigenvalue F S least_functional
  least_minimal : ∀ h : V →+ ZMod 2, least ≤ lineEigenvalue F S h
  hoffman : ∀ s : Finset V, IndependentCayley F S s →
    (s.card : ℝ) ≤
      4096 * (-(least : ℝ)) / (3 * (S.card : ℝ) - (least : ℝ))

theorem hoffman_ratio_strict_quarter (m q : ℝ)
    (hm : 0 < m) (hq : 0 < q) (hqm : q < m) :
    4096 * q / (3 * m + q) < 1024 := by
  have hden : 0 < 3 * m + q := by linarith
  apply (div_lt_iff₀ hden).2
  nlinarith

theorem four_small_class_sum (b : Colour4 → ℝ) (hb : ∀ k, b k < 1024) :
    (∑ k : Colour4, b k) < 4096 := by
  calc
    (∑ k : Colour4, b k) < ∑ _k : Colour4, (1024 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro k hk
        exact (hb k).le
      · exact ⟨0, by simp, hb 0⟩
    _ = 4096 := by norm_num [Colour4]

theorem hit_independent_card_lt_quarter [Fintype V]
    (F : CommonBinaryLineFamily V) (S : Finset (Fin 21))
    (hhit : LineHit F S) (D : SpectralRatioDuty F S)
    (s : Finset V) (hind : IndependentCayley F S s) : (s.card : ℝ) < 1024 := by
  have hlow : (4 : ℤ) - S.card ≤ D.least := by
    rw [D.least_character]
    exact hit_eigenvalue_lower F S hhit D.least_functional D.least_nonzero
  have hlowR : (4 : ℝ) - (S.card : ℝ) ≤ (D.least : ℝ) := by
    exact_mod_cast hlow
  have hnegative : (D.least : ℝ) < 0 := by exact_mod_cast D.least_negative
  let q : ℝ := -(D.least : ℝ)
  have hm : 0 < (S.card : ℝ) := by linarith
  have hq : 0 < q := by dsimp [q]; linarith
  have hqm : q < (S.card : ℝ) := by dsimp [q]; linarith
  have hbound : (s.card : ℝ) ≤ 4096 * q / (3 * (S.card : ℝ) + q) := by
    simpa only [q, sub_eq_add_neg] using D.hoffman s hind
  exact hbound.trans_lt (hoffman_ratio_strict_quarter (S.card : ℝ) q hm hq hqm)

theorem line_hit_no_four_colour [Fintype V]
    (F : CommonBinaryLineFamily V) (S : Finset (Fin 21))
    (hhit : LineHit F S) (D : SpectralRatioDuty F S) : NoFourCayleyColouring F S := by
  classical
  rintro ⟨c, hc⟩
  have hsmall : ∀ k : Colour4, ((colourClass c k).card : ℝ) < 1024 := by
    intro k
    exact hit_independent_card_lt_quarter F S hhit D (colourClass c k)
      (proper_colour_class_independent F S c hc k)
  have hsum := four_small_class_sum (fun k => ((colourClass c k).card : ℝ)) hsmall
  have hcards : (∑ k : Colour4, (colourClass c k).card) = Fintype.card V := by
    simpa only [colourClass, Finset.card_univ] using four_fibre_card_sum Finset.univ c
  have hsum_eq : (∑ k : Colour4, ((colourClass c k).card : ℝ)) = 4096 := by
    rw [← Nat.cast_sum, hcards, D.vertex_count]
    norm_num
  rw [hsum_eq] at hsum
  linarith

/-- The hypothesis supplies primitive finite-graph spectral facts only for
hitting selections. The converse needs the SAME common R on all whole lines;
this theorem makes no assertion for arbitrary binary two-spaces. -/
theorem line_hit_iff_no_four_colour [Fintype V]
    (F : CommonBinaryLineFamily V) (S : Finset (Fin 21))
    (hspectral : LineHit F S → SpectralRatioDuty F S) :
    NoFourCayleyColouring F S ↔ LineHit F S := by
  constructor
  · intro hno
    by_contra hnot
    exact hno (not_line_hit_has_four_colour F S hnot)
  · intro hhit
    exact line_hit_no_four_colour F S hhit (hspectral hhit)

/-- Fixed selected-graph arithmetic after the actual least eigenvalue -14 and
degree 54 have been admitted by exact spectral/data correspondence. -/
theorem selected_ratio_arithmetic :
    (4096 : ℚ) * 14 / (54 + 14) = 14336 / 17 ∧ (14336 / 17 : ℚ) < 1024 := by
  norm_num

end Partials.UnitDistance
