import Partials.Arrival.Decoder

/-!
R3 SOURCE / UNCOMPILED. Two local `b0` cut labels become cross transfers;
only the two `a0` and two `c0` coordinates absorb globally. Scalar least
selection is unconditional. Physical interpretation is the explicit final
conditional, pending legal-wave and complete-routing abelian correspondence.
-/

namespace Partials.Arrival

def crossCount (k z N M : ℕ) : ℕ := (namedBatchCounts k z ⟨N, M⟩).b0

theorem nat_monotone_of_step (f : ℕ → ℕ) (hs : ∀ x, f x ≤ f (x + 1)) : Monotone f := by
  intro a b
  induction b with
  | zero =>
    intro hab
    have ha : a = 0 := by omega
    subst a
    exact le_rfl
  | succ b ih =>
    intro hab
    by_cases h : a ≤ b
    · exact le_trans (ih h) (hs b)
    · have ha : a = b + 1 := by omega
      subst a
      exact le_rfl

/-- Algebraic proof through the already proved output cocycle and one-chip
total. No abelian conclusion is supplied as a local proof field. -/
theorem crossCount_adjacent (k : ℕ) (hk : 3 ≤ k) (z : ℕ)
    (hz : z < period k) (N M : ℕ) :
    crossCount k z N M ≤ crossCount k z (N + 1) M ∧
      crossCount k z (N + 1) M ≤ crossCount k z N M + 1 := by
  let v : Batch := ⟨N, M⟩
  let w : Batch := ⟨1, 0⟩
  have h := batch_output_cocycle k hk z hz v w
  have hb := congrArg NamedCounts.b0 h
  have ht := decoder_output_total k (finalCoordinate k z v) w
  have he : crossCount k z N M + (namedBatchCounts k (finalCoordinate k z v) w).b0 =
      crossCount k z (N + 1) M := by
    simpa [crossCount, v, w, NamedCounts.add, Batch.add] using hb
  have hb1 : (namedBatchCounts k (finalCoordinate k z v) w).b0 ≤ 1 := by
    unfold NamedCounts.total at ht
    have hw : w.total = 1 := by simp [w, Batch.total]
    rw [hw] at ht
    omega
  constructor <;> omega

theorem crossCount_mono (k : ℕ) (hk : 3 ≤ k) (z : ℕ)
    (hz : z < period k) (M : ℕ) : Monotone (fun N => crossCount k z N M) := by
  apply nat_monotone_of_step
  intro N
  exact (crossCount_adjacent k hk z hz N M).1

theorem crossCount_increment_zero_or_one (k : ℕ) (hk : 3 ≤ k) (z : ℕ)
    (hz : z < period k) (N M : ℕ) :
    crossCount k z (N + 1) M = crossCount k z N M ∨
      crossCount k z (N + 1) M = crossCount k z N M + 1 := by
  have h := crossCount_adjacent k hk z hz N M
  omega

theorem bPrefix_le_div_add_one (k n : ℕ) : bPrefix k n ≤ n / 4 + 1 := by
  unfold bPrefix
  split_ifs <;> omega

/-- Exact integer form of the strict rational bound `b < (N+M)/3+2`. -/
theorem crossCount_strict_bound (k : ℕ) (hk : 3 ≤ k) (z : ℕ)
    (hz : z < period k) (N M : ℕ) : 3 * crossCount k z N M < N + M + 6 := by
  let v : Batch := ⟨N, M⟩
  let q := batchCoordinate k z v / period k
  have hq := decodeUnbounded_quotient k (batchCoordinate k z v)
  have hb := bPrefix_le_div_add_one k (batchCount k z v)
  have hbq : crossCount k z N M ≤ q + 1 := by
    change batchCount k z v / 4 = q at hq
    rw [hq] at hb
    change bPrefix k (batchCount k z v) - bPrefix k (initialPhase k z) ≤ q + 1
    omega
  have hde := Nat.mod_add_div (batchCoordinate k z v) (period k)
  have hlow : period k * q ≤ batchCoordinate k z v := by dsimp [q]; omega
  have hw := inputWeight_le_total k v
  have hupp : batchCoordinate k z v < k * (N + M) + period k := by
    change inputWeight k N M ≤ k * (N + M) at hw
    change z + inputWeight k N M < k * (N + M) + period k
    omega
  by_contra h
  have hqpos : 1 ≤ q := by omega
  have hs : N + M + 3 ≤ 3 * q := by omega
  have hm := Nat.mul_le_mul_left k hs
  unfold period at *
  nlinarith

def couplingMap (k zA zB MA MB x : ℕ) : ℕ :=
  crossCount k zB (crossCount k zA x MA) MB

def couplingBracket (MA MB : ℕ) : ℕ := MA + MB + 10

theorem coupling_mono (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB : ℕ) :
    Monotone (couplingMap k zA zB MA MB) := by
  intro x y hxy
  exact crossCount_mono k hk zB hB MB (crossCount_mono k hk zA hA MA hxy)

theorem coupling_adjacent (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB x : ℕ) :
    couplingMap k zA zB MA MB x ≤ couplingMap k zA zB MA MB (x + 1) ∧
      couplingMap k zA zB MA MB (x + 1) ≤ couplingMap k zA zB MA MB x + 1 := by
  have ha := crossCount_adjacent k hk zA hA x MA
  have hb := crossCount_adjacent k hk zB hB (crossCount k zA x MA) MB
  unfold couplingMap
  by_cases he : crossCount k zA (x + 1) MA = crossCount k zA x MA
  · rw [he]
    constructor <;> omega
  · have he' : crossCount k zA (x + 1) MA = crossCount k zA x MA + 1 := by omega
    rw [he']
    exact hb

theorem coupling_bracket_strict (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB : ℕ) :
    couplingMap k zA zB MA MB (couplingBracket MA MB) < couplingBracket MA MB := by
  have ha := crossCount_strict_bound k hk zA hA (couplingBracket MA MB) MA
  have hb := crossCount_strict_bound k hk zB hB
    (crossCount k zA (couplingBracket MA MB) MA) MB
  unfold couplingMap couplingBracket at *
  omega

theorem coupling_nonpositive_persistent (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB x y : ℕ)
    (hxy : x ≤ y) (hx : couplingMap k zA zB MA MB x ≤ x) :
    couplingMap k zA zB MA MB y ≤ y := by
  have hs : ∀ n, couplingMap k zA zB MA MB (n + 1) ≤ couplingMap k zA zB MA MB n + 1 := by
    intro n
    exact (coupling_adjacent k hk zA zB hA hB MA MB n).2
  have hall : ∀ d, couplingMap k zA zB MA MB (x + d) ≤ x + d := by
    intro d
    induction d with
    | zero => simpa using hx
    | succ d ih =>
      have h := hs (x + d)
      have he : x + (d + 1) = x + d + 1 := by omega
      rw [he]
      omega
  have he : y = x + (y - x) := by omega
  rw [he]
  exact hall (y - x)

/-- Integer difference is monotone, rather than a truncated natural `F-x`. -/
theorem coupling_difference_antitone (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB : ℕ) :
    Antitone (fun x : ℕ => (couplingMap k zA zB MA MB x : ℤ) - (x : ℤ)) := by
  intro x y hxy
  have hs : ∀ n, couplingMap k zA zB MA MB (n + 1) ≤ couplingMap k zA zB MA MB n + 1 := by
    intro n
    exact (coupling_adjacent k hk zA zB hA hB MA MB n).2
  have hall : ∀ d, couplingMap k zA zB MA MB (x + d) ≤ couplingMap k zA zB MA MB x + d := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have h := hs (x + d)
      have he : x + (d + 1) = x + d + 1 := by omega
      rw [he]
      omega
  have he : y = x + (y - x) := by omega
  have h := hall (y - x)
  rw [← he] at h
  dsimp only
  omega

def firstNonpositive (f : ℕ → ℕ) (hex : ∃ x, f x ≤ x) : ℕ := Nat.find hex

theorem firstNonpositive_spec (f : ℕ → ℕ) (hex : ∃ x, f x ≤ x) :
    f (firstNonpositive f hex) ≤ firstNonpositive f hex := Nat.find_spec hex

theorem firstNonpositive_le (f : ℕ → ℕ) (hex : ∃ x, f x ≤ x)
    (x : ℕ) (hx : f x ≤ x) : firstNonpositive f hex ≤ x := Nat.find_min' hex hx

theorem firstNonpositive_fixed (f : ℕ → ℕ) (hm : Monotone f)
    (hex : ∃ x, f x ≤ x) : f (firstNonpositive f hex) = firstNonpositive f hex := by
  have hu := firstNonpositive_spec f hex
  by_cases hz : firstNonpositive f hex = 0
  · omega
  · have hpos : 0 < firstNonpositive f hex := by omega
    have hprev : ¬ f (firstNonpositive f hex - 1) ≤ firstNonpositive f hex - 1 :=
      Nat.find_min hex (by unfold firstNonpositive at *; omega)
    have hm' := hm (show firstNonpositive f hex - 1 ≤ firstNonpositive f hex by omega)
    omega

theorem scalarIterate_mono (f : ℕ → ℕ) (hm : Monotone f) : Monotone (scalarIterate f) := by
  apply nat_monotone_of_step
  intro q
  induction q with
  | zero => simp [scalarIterate]
  | succ q ih => simpa [scalarIterate] using hm ih

theorem scalarIterate_bounded (f : ℕ → ℕ) (hm : Monotone f) (U : ℕ)
    (hU : f U ≤ U) (q : ℕ) : scalarIterate f q ≤ U := by
  induction q with
  | zero => simp [scalarIterate]
  | succ q ih => exact le_trans (hm ih) hU

/-- Finite monotone stabilization is proved from the bound, not assumed. -/
theorem scalarIterate_stationary (f : ℕ → ℕ) (hm : Monotone f) (U : ℕ)
    (hU : f U ≤ U) : ∃ q ≤ U, f (scalarIterate f q) = scalarIterate f q := by
  by_contra h
  push_neg at h
  have hmono := scalarIterate_mono f hm
  have hlow : ∀ q, q ≤ U + 1 → q ≤ scalarIterate f q := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      intro hq
      have hq' : q ≤ U := by omega
      have hi := ih (by omega)
      have hs := hmono (show q ≤ q + 1 by omega)
      have hneq : scalarIterate f (q + 1) ≠ scalarIterate f q := by
        simpa [scalarIterate] using h q hq'
      omega
  have hl := hlow (U + 1) (le_refl _)
  have hu := scalarIterate_bounded f hm U hU (U + 1)
  omega

theorem scalarIterate_reaches_first (f : ℕ → ℕ) (hm : Monotone f)
    (U : ℕ) (hU : f U ≤ U) :
    ∃ q ≤ U, scalarIterate f q = firstNonpositive f ⟨U, hU⟩ := by
  obtain ⟨q, hq, hs⟩ := scalarIterate_stationary f hm U hU
  have hfirst := firstNonpositive_fixed f hm ⟨U, hU⟩
  have hlo := firstNonpositive_le f ⟨U, hU⟩ (scalarIterate f q) (by omega)
  have hhi := scalarIterate_le_fixed f hm (firstNonpositive f ⟨U, hU⟩) hfirst q
  exact ⟨q, hq, by omega⟩

def couplingExists (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB : ℕ) :
    ∃ x, couplingMap k zA zB MA MB x ≤ x :=
  ⟨couplingBracket MA MB, Nat.le_of_lt (coupling_bracket_strict k hk zA zB hA hB MA MB)⟩

def couplingFirst (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB : ℕ) : ℕ :=
  firstNonpositive (couplingMap k zA zB MA MB) (couplingExists k hk zA zB hA hB MA MB)

theorem coupling_first_bracket (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB : ℕ) :
    couplingFirst k hk zA zB hA hB MA MB ≤ couplingBracket MA MB := by
  exact firstNonpositive_le _ _ _
    (Nat.le_of_lt (coupling_bracket_strict k hk zA zB hA hB MA MB))

theorem coupling_first_fixed (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB : ℕ) :
    couplingMap k zA zB MA MB (couplingFirst k hk zA zB hA hB MA MB) =
      couplingFirst k hk zA zB hA hB MA MB := by
  exact firstNonpositive_fixed _ (coupling_mono k hk zA zB hA hB MA MB) _

theorem coupling_first_is_least (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB x : ℕ)
    (hx : couplingMap k zA zB MA MB x = x) :
    couplingFirst k hk zA zB hA hB MA MB ≤ x := by
  exact firstNonpositive_le _ _ _ (by omega)

theorem coupling_least_iteration (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB : ℕ) :
    ∃ q ≤ couplingBracket MA MB,
      scalarIterate (couplingMap k zA zB MA MB) q = couplingFirst k hk zA zB hA hB MA MB := by
  have hm := coupling_mono k hk zA zB hA hB MA MB
  have hU := Nat.le_of_lt (coupling_bracket_strict k hk zA zB hA hB MA MB)
  obtain ⟨q, hq, hs⟩ := scalarIterate_stationary _ hm _ hU
  have hlo := coupling_first_is_least k hk zA zB hA hB MA MB (scalarIterate _ q) hs
  have hhi := scalarIterate_le_fixed _ hm _ (coupling_first_fixed k hk zA zB hA hB MA MB) q
  exact ⟨q, hq, by omega⟩

structure FourAbsorbingCounts where
  aA : ℕ
  cA : ℕ
  aB : ℕ
  cB : ℕ
  deriving DecidableEq

def FourAbsorbingCounts.total (C : FourAbsorbingCounts) : ℕ := C.aA + C.cA + C.aB + C.cB

def absorbingCountsAt (k zA zB MA MB x : ℕ) : FourAbsorbingCounts :=
  let xAB := crossCount k zA x MA
  let CA := namedBatchCounts k zA ⟨x, MA⟩
  let CB := namedBatchCounts k zB ⟨xAB, MB⟩
  ⟨CA.a0, CA.c0, CB.a0, CB.c0⟩

def couplingAbsorbingCounts (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB : ℕ) : FourAbsorbingCounts :=
  absorbingCountsAt k zA zB MA MB (couplingFirst k hk zA zB hA hB MA MB)

theorem absorbingCountsAt_total {k zA zB MA MB x : ℕ}
    (hx : couplingMap k zA zB MA MB x = x) :
    (absorbingCountsAt k zA zB MA MB x).total = MA + MB := by
  have ha := decoder_output_total k zA ⟨x, MA⟩
  have hb := decoder_output_total k zB ⟨crossCount k zA x MA, MB⟩
  change (namedBatchCounts k zA ⟨x, MA⟩).a0 + crossCount k zA x MA +
    (namedBatchCounts k zA ⟨x, MA⟩).c0 = x + MA at ha
  change (namedBatchCounts k zB ⟨crossCount k zA x MA, MB⟩).a0 +
    couplingMap k zA zB MA MB x +
    (namedBatchCounts k zB ⟨crossCount k zA x MA, MB⟩).c0 = crossCount k zA x MA + MB at hb
  dsimp only [absorbingCountsAt, FourAbsorbingCounts.total]
  omega

theorem coupling_four_absorbing_total (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB : ℕ) :
    (couplingAbsorbingCounts k hk zA zB hA hB MA MB).total = MA + MB :=
  absorbingCountsAt_total (coupling_first_fixed k hk zA zB hA hB MA MB)

/-- Local final states from the same two decodes, without a claim that a
legal coupled graph has already been identified with these scalar data. -/
def couplingFinalStates (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB : ℕ) :
    InterfaceState k × InterfaceState k :=
  let xBA := couplingFirst k hk zA zB hA hB MA MB
  let xAB := crossCount k zA xBA MA
  (decodedInterfaceState k zA ⟨xBA, MA⟩, decodedInterfaceState k zB ⟨xAB, MB⟩)

/-- EXACT CONDITIONAL BRIDGE: operational legal waves must supply their
cumulative BA iteration and stationarity; local cut extraction supplies AB.
Other algebraic fixed points are deliberately not identified as physical. -/
theorem coupling_eq_stationary_legal_waves (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB q physicalBA physicalAB : ℕ)
    (wave_count : physicalBA = scalarIterate (couplingMap k zA zB MA MB) q)
    (completed_wave : couplingMap k zA zB MA MB physicalBA = physicalBA)
    (local_cut_count : physicalAB = crossCount k zA physicalBA MA) :
    physicalBA = couplingFirst k hk zA zB hA hB MA MB ∧
    physicalAB = crossCount k zA (couplingFirst k hk zA zB hA hB MA MB) MA := by
  have hlo := coupling_first_is_least k hk zA zB hA hB MA MB physicalBA completed_wave
  have hhi := scalarIterate_le_fixed _ (coupling_mono k hk zA zB hA hB MA MB)
    _ (coupling_first_fixed k hk zA zB hA hB MA MB) q
  rw [← wave_count] at hhi
  have he : physicalBA = couplingFirst k hk zA zB hA hB MA MB := by omega
  exact ⟨he, by simpa [he] using local_cut_count⟩

/-- The manuscript's phantom algebraic cycle. This is a source proof,
not a finite external diagnostic or an executed routing. -/
theorem phantom_fixed_points :
    couplingMap 3 2 2 0 0 0 = 0 ∧ couplingMap 3 2 2 0 0 1 = 1 := by
  norm_num [couplingMap, crossCount, namedBatchCounts, batchCount, initialPhase,
    decoderTraversals, decoderFeedback, batchCoordinate, Batch.total, inputWeight,
    decodeUnbounded, decodeResidue, period, feedbackPrefix, bPrefix, bThreshold]

end Partials.Arrival
