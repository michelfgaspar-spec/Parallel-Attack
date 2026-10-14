import Partials.UnitDistance.Minimization
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! R6 BLIND SOURCE / UNCOMPILED. Main `thm:147`, (5.6), bit-cost scope and
supplement Root Words. ROOT_WORDS.json multiplicities are defining inputs;
none of this module certifies a retained record, its tie-break, candidate_count
or generator execution. Word order and nonintegral lifting tails are separate.
The conditional uniform minimum theorem exposes both algebraic duties and the
general plane primitives instead of accepting the desired minimum as input. -/
namespace Partials.UnitDistance.Words

open Partials.UnitDistance

noncomputable def pairEmbeddingHom : (ℤ × ℤ) →+ ℂ where
  toFun := pairEmbedding
  map_zero' := by simp [pairEmbedding]
  map_add' := pairEmbedding_add

noncomputable def sevenPairValueHom : SevenPairs →+ ℂ where
  toFun := sevenPairValue
  map_zero' := by simp [sevenPairValue]
  map_add' := by
    intro p q
    simp only [sevenPairValue, Pi.add_apply, Prod.fst_add, Prod.snd_add, Int.cast_add]
    simp_rw [show ∀ k : Fin 7,
      (((p k).1 : ℂ) + (q k).1 + (((p k).2 : ℂ) + (q k).2) * rho) * zeta ^ k.val =
        ((p k).1 + (p k).2 * rho) * zeta ^ k.val +
          ((q k).1 + (q k).2 * rho) * zeta ^ k.val by intro k; ring]
    exact Finset.sum_add_distrib

def groupedCounts (c : RootLetterCount) (k : Fin 7) : LocalCounts :=
  fun h => c (rootIndex k h)
def groupedPairs (c : RootLetterCount) : SevenPairs :=
  fun k => localValue (groupedCounts c k)
def countsFromLocal (L : Fin 7 → LocalCounts) : RootLetterCount :=
  fun r => L (rootClass r).1 (rootClass r).2

theorem grouped_from_local (L : Fin 7 → LocalCounts) :
    groupedCounts (countsFromLocal L) = L := by
  funext k h
  have he := rootClassEquiv.left_inv (k, h)
  simpa [groupedCounts, countsFromLocal, rootClassEquiv] using congrArg (fun kh => L kh.1 kh.2) he

theorem grouped_cost (c : RootLetterCount) :
    rootWordCost c = ∑ k : Fin 7, localCost (groupedCounts c k) := by
  have he := Equiv.sum_comp rootClassEquiv (fun r : Fin 42 => c r)
  simpa [rootWordCost, groupedCounts, localCost, rootClassEquiv,
    Fintype.sum_prod_type] using he.symm

theorem pairEmbedding_localValue (c : LocalCounts) :
    pairEmbedding (localValue c) =
      ∑ h : Fin 6, (c h : ℂ) * pairEmbedding (hexStep h) := by
  change pairEmbeddingHom (∑ h : Fin 6,
    ((c h : ℤ) * (hexStep h).1, (c h : ℤ) * (hexStep h).2)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro h _
  simp [pairEmbeddingHom, pairEmbedding, Int.cast_mul]
  ring

theorem grouped_value (d : RootClassEvaluationDuty) (c : RootLetterCount) :
    rootWordValue c = sevenPairValue (groupedPairs c) := by
  have he := Equiv.sum_comp rootClassEquiv
    (fun r : Fin 42 => (c r : ℂ) * w ^ r.val)
  calc
    rootWordValue c = ∑ k : Fin 7, ∑ h : Fin 6,
        (c (rootIndex k h) : ℂ) * w ^ (rootIndex k h).val := by
      simpa [rootWordValue, rootClassEquiv, Fintype.sum_prod_type] using he.symm
    _ = ∑ k : Fin 7, pairEmbedding (localValue (groupedCounts c k)) * zeta ^ k.val := by
      apply Finset.sum_congr rfl
      intro k _
      rw [pairEmbedding_localValue, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h _
      rw [d.root_evaluation]
      simp [groupedCounts]
      ring
    _ = sevenPairValue (groupedPairs c) := rfl

def powerContribution (c : IntegerCode) (i : Fin 12) : SevenPairs :=
  let r : Fin 42 := ⟨i.val, by omega⟩
  fun k => if k = (rootClass r).1 then
    (c i * (hexStep (rootClass r).2).1, c i * (hexStep (rootClass r).2).2)
    else (0, 0)
def deterministicSevenPairs (c : IntegerCode) : SevenPairs :=
  ∑ i : Fin 12, powerContribution c i

/-- A fixed source-level conversion from twelve signed power-basis
coefficients. This does not assert a tie-break for historical root counts. -/
theorem deterministic_seven_representation (d : RootClassEvaluationDuty) (c : IntegerCode) :
    sevenPairValue (deterministicSevenPairs c) = evalInteger c := by
  have hterm : ∀ i : Fin 12,
      sevenPairValue (powerContribution c i) = (c i : ℂ) * w ^ i.val := by
    intro i
    let r : Fin 42 := ⟨i.val, by omega⟩
    have hr := root_class_evaluation d r
    have hcontribution : ∀ k : Fin 7,
        (((powerContribution c i k).1 : ℂ) + (powerContribution c i k).2 * rho) *
          zeta ^ k.val =
        if k = (rootClass r).1 then
          (c i : ℂ) * (pairEmbedding (hexStep (rootClass r).2) * zeta ^ k.val)
        else 0 := by
      intro k
      by_cases hk : k = (rootClass r).1
      · simp [powerContribution, r, hk, pairEmbedding, Int.cast_mul]
        ring
      · simp [powerContribution, r, hk]
    rw [sevenPairValue]
    simp_rw [hcontribution]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [← hr]
  change sevenPairValueHom (∑ i : Fin 12, powerContribution c i) = _
  rw [map_sum]
  change (∑ i : Fin 12, sevenPairValue (powerContribution c i)) = evalInteger c
  simp_rw [hterm]
  rfl

theorem integral_point_has_seven_representation (d : RootClassEvaluationDuty)
    (n : ℂ) (hn : n ∈ O) : ∃ p : SevenPairs, sevenPairValue p = n := by
  obtain ⟨c, rfl⟩ := hn
  exact ⟨deterministicSevenPairs c, deterministic_seven_representation d c⟩

def localForShift (p : SevenPairs) (A B : ℤ) : Fin 7 → LocalCounts :=
  fun k => canonicalLocalCounts ((p k).1 + A) ((p k).2 + B)
def canonicalWord (p : SevenPairs) (A B : ℤ) : RootLetterCount :=
  countsFromLocal (localForShift p A B)

theorem canonical_grouped_pairs (p : SevenPairs) (A B : ℤ) :
    groupedPairs (canonicalWord p A B) = shiftSeven p A B := by
  funext k
  simp only [groupedPairs, canonicalWord, grouped_from_local, localForShift]
  exact canonical_local_value _ _

theorem canonical_word_value (basis : SevenBasisDuty) (roots : RootClassEvaluationDuty)
    (p : SevenPairs) (A B : ℤ) :
    rootWordValue (canonicalWord p A B) = sevenPairValue p := by
  rw [grouped_value roots, canonical_grouped_pairs, shift_preserves_value basis]

theorem canonical_word_cost (p : SevenPairs) (A B : ℤ) :
    (rootWordCost (canonicalWord p A B) : ℤ) = shiftObjective p A B := by
  rw [grouped_cost]
  simp [canonicalWord, grouped_from_local, localForShift, shiftObjective,
    Nat.cast_sum, canonical_local_cost]

/-- Every root word yields an actual integral shift and hence a lower bound.
The seven integral local displacements are extracted from the word itself. -/
theorem every_word_has_shift_lower_bound (basis : SevenBasisDuty)
    (roots : RootClassEvaluationDuty) (p : SevenPairs) (c : RootLetterCount)
    (hc : rootWordValue c = sevenPairValue p) :
    ∃ A B : ℤ, shiftObjective p A B ≤ (rootWordCost c : ℤ) := by
  have hvalue : sevenPairValue (groupedPairs c) = sevenPairValue p := by
    rw [← grouped_value roots c]
    exact hc
  obtain ⟨A, B, hshift⟩ := (same_value_iff_common_shift basis p (groupedPairs c)).mp hvalue
  refine ⟨A, B, ?_⟩
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 7))) =>
    local_norm_le_cost (groupedCounts c k))
  have hobj : (∑ k : Fin 7, pairNorm (localValue (groupedCounts c k))) =
      shiftObjective p A B := by
    change (∑ k : Fin 7, pairNorm (groupedPairs c k)) = _
    rw [hshift]
    rfl
  rw [hobj] at hsum
  simpa [grouped_cost, Nat.cast_sum] using hsum

def IsShortestRootWord (n : ℂ) (c : RootLetterCount) : Prop :=
  rootWordValue c = n ∧
    ∀ d : RootLetterCount, rootWordValue d = n → rootWordCost c ≤ rootWordCost d

/-- Main Theorem `thm:147`, with only the actual primitive algebraic and
general plane bridges exposed. No certificate counts or desired minimum
equation is an assumption. At most147 DISTINCT candidates are relevant. -/
theorem shortest_root_word_at_candidate (basis : SevenBasisDuty)
    (roots : RootClassEvaluationDuty) (plane : PrimitivePlaneDuty) (p : SevenPairs) :
    ∃ c ∈ candidatePoints p,
      IsShortestRootWord (sevenPairValue p) (canonicalWord p c.1 c.2) ∧
      (rootWordCost (canonicalWord p c.1 c.2) : ℤ) = shiftObjective p c.1 c.2 ∧
      ∀ A B : ℤ, shiftObjective p c.1 c.2 ≤ shiftObjective p A B := by
  obtain ⟨c, hc, hmin⟩ := integer_minimum_at_candidate plane p
  refine ⟨c, hc, ⟨canonical_word_value basis roots p c.1 c.2, ?_⟩,
    canonical_word_cost p c.1 c.2, hmin⟩
  intro d hd
  obtain ⟨A, B, hbound⟩ := every_word_has_shift_lower_bound basis roots p d hd
  have hcandidate := hmin A B
  have hcost := canonical_word_cost p c.1 c.2
  omega

theorem shortest_root_word_cost (basis : SevenBasisDuty)
    (roots : RootClassEvaluationDuty) (plane : PrimitivePlaneDuty)
    (p : SevenPairs) (d : RootLetterCount)
    (hd : IsShortestRootWord (sevenPairValue p) d) :
    ∃ c ∈ candidatePoints p,
      (rootWordCost d : ℤ) = shiftObjective p c.1 c.2 := by
  obtain ⟨c, hc, hshort, hcost, _⟩ := shortest_root_word_at_candidate basis roots plane p
  have hle := hd.2 _ hshort.1
  have hge := hshort.2 d hd.1
  exact ⟨c, hc, by omega⟩

/-- Receipt boundary for retained ROOT_WORDS records. Even a proof of this
predicate does NOT establish generator lexicographic tie-break, decomposition
rule, candidate_count, shortest order or optimality in all126 unit directions.
The three numerical fields are decoded exact inputs; acceptance is separate. -/
structure RootWordRecord where
  target : IntegerCode
  counts : RootLetterCount
  storedShift : ℤ × ℤ
  recordedCandidateCount : ℕ
def RootWordMeaning (r : RootWordRecord) : Prop :=
  rootWordValue r.counts = evalInteger r.target ∧
    IsShortestRootWord (evalInteger r.target) r.counts

def CoefficientsBounded (c : IntegerCode) (C : ℤ) : Prop :=
  0 ≤ C ∧ ∀ i, |c i| ≤ C
def PairsBounded (p : SevenPairs) (M : ℤ) : Prop :=
  0 ≤ M ∧ ∀ k, |(p k).1| ≤ M ∧ |(p k).2| ≤ M

def firstAtHom (k : Fin 7) : SevenPairs →+ ℤ where
  toFun p := (p k).1
  map_zero' := rfl
  map_add' := by intros; rfl
def secondAtHom (k : Fin 7) : SevenPairs →+ ℤ where
  toFun p := (p k).2
  map_zero' := rfl
  map_add' := by intros; rfl

theorem deterministic_pair_bound (c : IntegerCode) (C : ℤ)
    (hc : CoefficientsBounded c C) : PairsBounded (deterministicSevenPairs c) (12 * C) := by
  refine ⟨by nlinarith [hc.1], ?_⟩
  intro k
  have hterm : ∀ i : Fin 12,
      |(powerContribution c i k).1| ≤ C ∧ |(powerContribution c i k).2| ≤ C := by
    intro i
    let r : Fin 42 := ⟨i.val, by omega⟩
    have hb := hexStep_coordinate_bounds (rootClass r).2
    have hi := hc.2 i
    by_cases hclass : k = (rootClass r).1
    · dsimp only [r] at hclass hb
      simp only [powerContribution, hclass, ↓reduceIte, Prod.fst, Prod.snd]
      rw [abs_mul, abs_mul]
      constructor <;> nlinarith [abs_nonneg (c i),
        abs_nonneg (hexStep (rootClass r).2).1,
        abs_nonneg (hexStep (rootClass r).2).2]
    · simpa [powerContribution, r, hclass] using And.intro hc.1 hc.1
  have hfirst : (deterministicSevenPairs c k).1 =
      ∑ i : Fin 12, (powerContribution c i k).1 := by
    change firstAtHom k (∑ i : Fin 12, powerContribution c i) = _
    rw [map_sum]
    rfl
  have hsecond : (deterministicSevenPairs c k).2 =
      ∑ i : Fin 12, (powerContribution c i k).2 := by
    change secondAtHom k (∑ i : Fin 12, powerContribution c i) = _
    rw [map_sum]
    rfl
  constructor
  · rw [hfirst]
    calc
      |∑ i : Fin 12, (powerContribution c i k).1| ≤
          ∑ i : Fin 12, |(powerContribution c i k).1| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin 12, C := Finset.sum_le_sum (fun i _ => (hterm i).1)
      _ = 12 * C := by simp
  · rw [hsecond]
    calc
      |∑ i : Fin 12, (powerContribution c i k).2| ≤
          ∑ i : Fin 12, |(powerContribution c i k).2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin 12, C := Finset.sum_le_sum (fun i _ => (hterm i).2)
      _ = 12 * C := by simp

/-- A useful exact magnitude bound, separate from an integer bit-cost model.
The selected shift can be three times a pair magnitude; the resulting local
cost and counts are linear in that magnitude. -/
theorem candidate_shift_bound (p : SevenPairs) (M : ℤ) (hp : PairsBounded p M)
    (c : ℤ × ℤ) (hc : c ∈ candidatePoints p) : |c.1| ≤ 3 * M ∧ |c.2| ≤ 3 * M := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hc
  have hi := hp.2 i.2.1
  have hj := hp.2 i.2.2
  have hi1 := (abs_le.mp hi.1)
  have hi2 := (abs_le.mp hi.2)
  have hj1 := (abs_le.mp hj.1)
  have hj2 := (abs_le.mp hj.2)
  rcases i with ⟨kind, i, j⟩
  simp only [Prod.fst, Prod.snd] at hi1 hi2 hj1 hj2
  fin_cases kind <;> simp [candidate, abs_le] <;> omega

theorem hexNorm_le_abs_sum (a b : ℤ) : hexNorm a b ≤ |a| + |b| := by
  apply max_le
  · apply max_le <;> have ha := abs_nonneg a <;> have hb := abs_nonneg b <;> omega
  · exact abs_add_le a b

theorem candidate_local_cost_bound (p : SevenPairs) (M : ℤ) (hp : PairsBounded p M)
    (c : ℤ × ℤ) (hc : c ∈ candidatePoints p) (k : Fin 7) :
    (localCost (localForShift p c.1 c.2 k) : ℤ) ≤ 8 * M := by
  obtain ⟨hA, hB⟩ := candidate_shift_bound p M hp c hc
  obtain ⟨ha, hb⟩ := hp.2 k
  rw [localForShift, canonical_local_cost]
  have hn := hexNorm_le_abs_sum ((p k).1 + c.1) ((p k).2 + c.2)
  have hleft := abs_add_le (p k).1 c.1
  have hright := abs_add_le (p k).2 c.2
  omega

theorem candidate_count_bound (p : SevenPairs) (M : ℤ) (hp : PairsBounded p M)
    (c : ℤ × ℤ) (hc : c ∈ candidatePoints p) (r : Fin 42) :
    (canonicalWord p c.1 c.2 r : ℤ) ≤ 8 * M := by
  let k := (rootClass r).1
  let h := (rootClass r).2
  have hcount : localForShift p c.1 c.2 k h ≤ localCost (localForShift p c.1 c.2 k) :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ h)
  have hbound := candidate_local_cost_bound p M hp c hc k
  change ((localForShift p c.1 c.2 k h : ℕ) : ℤ) ≤ _
  omega

theorem candidate_total_cost_bound (p : SevenPairs) (M : ℤ) (hp : PairsBounded p M)
    (c : ℤ × ℤ) (hc : c ∈ candidatePoints p) :
    (rootWordCost (canonicalWord p c.1 c.2) : ℤ) ≤ 56 * M := by
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin 7))) =>
    candidate_local_cost_bound p M hp c hc k)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  norm_num only [Nat.cast_ofNat] at hsum
  have hcost : (rootWordCost (canonicalWord p c.1 c.2) : ℤ) =
      ∑ k : Fin 7, (localCost (localForShift p c.1 c.2 k) : ℤ) := by
    simp [grouped_cost, canonicalWord, grouped_from_local, Nat.cast_sum]
  rw [hcost]
  nlinarith

/-- Exact linear magnitude bound. With C=2^B, each of the42 multiplicities
has O(B) bits. The remaining cost duty is a formal model of integer additions,
comparisons and the fixed147-candidate program, not a numerical replay. -/
theorem compressed_counts_magnitude (input : IntegerCode) (C : ℤ)
    (hi : CoefficientsBounded input C) (c : ℤ × ℤ)
    (hc : c ∈ candidatePoints (deterministicSevenPairs input)) :
    (∀ r : Fin 42,
      (canonicalWord (deterministicSevenPairs input) c.1 c.2 r : ℤ) ≤ 96 * C) ∧
    (rootWordCost (canonicalWord (deterministicSevenPairs input) c.1 c.2) : ℤ) ≤ 672 * C := by
  have hp := deterministic_pair_bound input C hi
  constructor
  · intro r
    have h := candidate_count_bound (deterministicSevenPairs input) (12 * C) hp c hc r
    nlinarith
  · have h := candidate_total_cost_bound (deterministicSevenPairs input) (12 * C) hp c hc
    nlinarith

def oneWord (n : ℕ) : RootLetterCount := fun r => if r = 0 then n else 0

theorem oneWord_value (n : ℕ) : rootWordValue (oneWord n) = (n : ℂ) := by
  simp [rootWordValue, oneWord]
theorem oneWord_cost (n : ℕ) : rootWordCost (oneWord n) = n := by
  simp [rootWordCost, oneWord]

theorem norm_word_le_cost (rootNorm : ∀ r : Fin 42, ‖w ^ r.val‖ = 1)
    (c : RootLetterCount) : ‖rootWordValue c‖ ≤ (rootWordCost c : ℝ) := by
  calc
    ‖rootWordValue c‖ ≤ ∑ r : Fin 42, ‖(c r : ℂ) * w ^ r.val‖ := norm_sum_le _ _
    _ = ∑ r : Fin 42, (c r : ℝ) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [norm_mul, rootNorm r]
      rw [Complex.norm_natCast, mul_one]
    _ = (rootWordCost c : ℝ) := by
      exact (Nat.cast_sum Finset.univ c).symm

/-- Explicit word output can grow like n even though the multiplicity n is
binary encoded. This scope limit does not depend on tie-break or LP facts. -/
theorem oneWord_is_shortest (rootNorm : ∀ r : Fin 42, ‖w ^ r.val‖ = 1) (n : ℕ) :
    IsShortestRootWord (n : ℂ) (oneWord n) := by
  refine ⟨oneWord_value n, ?_⟩
  intro c hc
  have h := norm_word_le_cost rootNorm c
  rw [hc] at h
  simp only [Complex.norm_natCast] at h
  rw [oneWord_cost]
  exact_mod_cast h

/-- External Beck--Hosten scope, expressed in THEIR integral coordinates.
The square-minor predicate refers to the particular supplied matrix. It
does not transfer merely because a different integral basis is equivalent. -/
def TotallyUnimodularInThisBasis (A : Matrix (Fin 12) (Fin 42) ℤ) : Prop :=
  ∀ m : ℕ, ∀ rows : Fin m ↪ Fin 12, ∀ cols : Fin m ↪ Fin 42,
    (A.submatrix rows cols).det = -1 ∨
      (A.submatrix rows cols).det = 0 ∨ (A.submatrix rows cols).det = 1

structure BeckHostenCoordinateDuty (A : Matrix (Fin 12) (Fin 42) ℤ) where
  embedding : IntegerCode →+ ℂ
  injective : Function.Injective embedding
  range_is_O : Set.range embedding = O
  root_columns : ∀ r : Fin 42, embedding (fun i => A i r) = w ^ r.val
  imported_TUM : TotallyUnimodularInThisBasis A

def RealLPFeasible (A : Matrix (Fin 12) (Fin 42) ℤ) (b : IntegerCode)
    (x : Fin 42 → ℝ) : Prop :=
  (∀ i : Fin 12, (∑ r : Fin 42, (A i r : ℝ) * x r) = (b i : ℝ)) ∧
    ∀ r, 0 ≤ x r
def RealLPCost (x : Fin 42 → ℝ) : ℝ := ∑ r : Fin 42, x r

/-- A basic feasible solution uses an independent supported column set and
an invertible square row minor. Integrality of THIS basic point is a separate
determinant/Cramer duty; arbitrary optimal-face points need not be integral.
This structure contains no optimality or integrality conclusion. -/
structure BasicSupport (A : Matrix (Fin 12) (Fin 42) ℤ) (x : Fin 42 → ℝ) where
  size : ℕ
  rows : Fin size ↪ Fin 12
  cols : Fin size ↪ Fin 42
  zero_off_support : ∀ r, r ∉ Set.range cols → x r = 0
  invertible_minor : (A.submatrix rows cols).det ≠ 0

def LPBasicIntegralityTarget (A : Matrix (Fin 12) (Fin 42) ℤ) : Prop :=
  ∀ b : IntegerCode, ∀ x : Fin 42 → ℝ,
    TotallyUnimodularInThisBasis A → RealLPFeasible A b x →
      Nonempty (BasicSupport A x) → ∀ r, ∃ n : ℤ, x r = (n : ℝ)

def IntegralGeneratorSum (g : Fin 42 → IntegerCode) (c : RootLetterCount) : IntegerCode :=
  ∑ r : Fin 42, c r • g r

/-- Integral basis change preserves precisely the feasible multiplicity
vectors. Their cost depends on c alone. No changed-matrix TUM assertion is
in the theorem, and the147 formula above does not invoke LP selection. -/
theorem integral_basis_change_feasible (e : IntegerCode ≃+ IntegerCode)
    (g : Fin 42 → IntegerCode) (b : IntegerCode) (c : RootLetterCount) :
    IntegralGeneratorSum (fun r => e (g r)) c = e b ↔ IntegralGeneratorSum g c = b := by
  have he : IntegralGeneratorSum (fun r => e (g r)) c = e (IntegralGeneratorSum g c) := by
    unfold IntegralGeneratorSum
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro r _
    exact (map_nsmul e (c r) (g r)).symm
  rw [he]
  exact e.injective.eq_iff

/- The external LP route still needs exact published-matrix identification,
the compact cost-sublevel argument, optimal basic-feasible-point existence,
and LPBasicIntegralityTarget. No solver, real optimum, changed-matrix TUM or
arbitrary-optimal-point integrality has been certified in R6. -/

end Partials.UnitDistance.Words
