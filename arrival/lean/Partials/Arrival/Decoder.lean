import Partials.Arrival.Arithmetic

/-!
R3 SOURCE / UNCOMPILED. Scalar decoder and batch identities for the exact
canonical two-entry interface. No operational graph theorem is imported.
The last section is an explicit conditional wave-to-routing bridge.
-/

namespace Partials.Arrival

def initialPhase (k z : ℕ) : ℕ := (decodeUnbounded k z).2
def initialHeight (k z : ℕ) : ℕ := (decodeUnbounded k z).1
def batchCoordinate (k z : ℕ) (v : Batch) : ℕ := z + inputWeight k v.N v.M
def batchHeight (k z : ℕ) (v : Batch) : ℕ :=
  (decodeUnbounded k (batchCoordinate k z v)).1
def batchCount (k z : ℕ) (v : Batch) : ℕ :=
  (decodeUnbounded k (batchCoordinate k z v)).2
def finalCoordinate (k z : ℕ) (v : Batch) : ℕ := batchCoordinate k z v % period k
def decoderTraversals (k z : ℕ) (v : Batch) : ℕ :=
  batchCount k z v - initialPhase k z
def decoderFeedback (k z : ℕ) (v : Batch) : ℕ :=
  feedbackPrefix (batchCount k z v) - feedbackPrefix (initialPhase k z)
def batchLineX (k z : ℕ) (v : Batch) : ℕ :=
  initialHeight k z + inputWeight k v.N v.M

def namedBatchCounts (k z : ℕ) (v : Batch) : NamedCounts :=
  ⟨v.total + decoderFeedback k z v - decoderTraversals k z v,
    bPrefix k (batchCount k z v) - bPrefix k (initialPhase k z),
    cPrefix k (batchCount k z v) - cPrefix k (initialPhase k z)⟩

theorem initial_decode {k z : ℕ} (hz : z < period k) :
    decodeUnbounded k z = decodeResidue k z := by
  simp [decodeUnbounded, Nat.div_eq_of_lt hz, Nat.mod_eq_of_lt hz]

theorem initial_phase_lt {k z : ℕ} (hz : z < period k) : initialPhase k z < 4 := by
  unfold initialPhase
  rw [initial_decode hz]
  exact decodeResidue_phase_lt k z

theorem initial_canonical {k z : ℕ} (hz : z < period k) :
    Canonical k (initialHeight k z) (initialPhase k z) := by
  unfold initialHeight initialPhase
  rw [initial_decode hz]
  exact decodeResidue_canonical k z hz

theorem initial_encoded_pair {k h r : ℕ} (hc : Canonical k h r) :
    decodeUnbounded k (encodeResidue k h r) = (h, r) := by
  rw [initial_decode (encodeResidue_lt_period hc), decode_encodeResidue hc]

theorem batch_count_ge_initial (k z : ℕ) (v : Batch) :
    initialPhase k z ≤ batchCount k z v := by
  exact decodeUnbounded_count_mono k z (batchCoordinate k z v) (by
    unfold batchCoordinate
    omega)

theorem batch_canonical (k z : ℕ) (v : Batch) :
    Canonical k (batchHeight k z v) (batchCount k z v % 4) :=
  decodeUnbounded_canonical k (batchCoordinate k z v)

/-- Canonical closure is proved from the arithmetic table, including the
phase-one restriction, rather than supplied as a field of a model. -/
def decodedInterfaceState (k z : ℕ) (v : Batch) : InterfaceState k :=
  { h := ⟨batchHeight k z v, by have hc := batch_canonical k z v; exact Nat.lt_succ_of_le hc.1⟩
    r := ⟨batchCount k z v % 4, Nat.mod_lt _ (by decide)⟩ }

theorem canonical_closure (k : ℕ) (hk : 3 ≤ k) (z : ℕ)
    (hz : z < period k) (v : Batch) :
    Canonical k (decodedInterfaceState k z v).h.val
      (decodedInterfaceState k z v).r.val := batch_canonical k z v

theorem final_coordinate_lt (k z : ℕ) (v : Batch) : finalCoordinate k z v < period k :=
  Nat.mod_lt _ (period_pos k)

theorem final_coordinate_encode (k z : ℕ) (v : Batch) :
    encodeResidue k (batchHeight k z v) (batchCount k z v % 4) =
      finalCoordinate k z v := by
  unfold batchHeight batchCount finalCoordinate
  rw [decodeUnbounded_phase]
  exact encode_decodeResidue k _ (Nat.mod_lt _ (period_pos k))

theorem decoder_terminal_bound (k z : ℕ) (v : Batch) :
    terminalPrefix (batchCount k z v) - terminalPrefix (initialPhase k z) ≤ v.total := by
  have hn := batch_count_ge_initial k z v
  have ht := terminalPrefix_mono hn
  have hz := decodeUnbounded_coordinate k z
  have hy := decodeUnbounded_coordinate k (batchCoordinate k z v)
  have hc := decodeUnbounded_canonical k z
  have hcf := batch_canonical k z v
  have hw := inputWeight_le_total k v
  change z = k * terminalPrefix (initialPhase k z) + initialPhase k z + initialHeight k z at hz
  change batchCoordinate k z v = k * terminalPrefix (batchCount k z v) +
    batchCount k z v + batchHeight k z v at hy
  by_contra h
  have hs : terminalPrefix (initialPhase k z) + v.total + 1 ≤
      terminalPrefix (batchCount k z v) := by omega
  have hm := Nat.mul_le_mul_left k hs
  have hstrict : initialPhase k z < batchCount k z v := by
    by_contra hh
    have he : initialPhase k z = batchCount k z v := by omega
    rw [he] at hs
    omega
  unfold batchCoordinate at hy
  have hh : initialHeight k z ≤ k := hc.1
  nlinarith [hh]

theorem decoder_no_truncated_a0 (k z : ℕ) (v : Batch) :
    decoderTraversals k z v ≤ v.total + decoderFeedback k z v := by
  have hn := batch_count_ge_initial k z v
  have hf := feedbackPrefix_mono hn
  have ht := decoder_terminal_bound k z v
  have hfn := feedbackPrefix_le (batchCount k z v)
  have hfr := feedbackPrefix_le (initialPhase k z)
  unfold terminalPrefix decoderTraversals decoderFeedback at *
  omega

/-- This records the nontruncation obligations for all three subtractions.
Natural-valued output fields alone would not justify the manuscript formula. -/
theorem decoder_nonnegative_differences (k : ℕ) (hk : 3 ≤ k) (z : ℕ)
    (hz : z < period k) (v : Batch) :
    decoderTraversals k z v ≤ v.total + decoderFeedback k z v ∧
    bPrefix k (initialPhase k z) ≤ bPrefix k (batchCount k z v) ∧
    cPrefix k (initialPhase k z) ≤ cPrefix k (batchCount k z v) := by
  have hn := batch_count_ge_initial k z v
  exact ⟨decoder_no_truncated_a0 k z v, bPrefix_mono k hn, cPrefix_mono k hn⟩

theorem decoder_output_total (k z : ℕ) (v : Batch) :
    (namedBatchCounts k z v).total = v.total := by
  have hn := batch_count_ge_initial k z v
  have hf := feedbackPrefix_mono hn
  have hb := bPrefix_mono k hn
  have hc := cPrefix_mono k hn
  have hp := passive_prefix_partition k (initialPhase k z)
  have hq := passive_prefix_partition k (batchCount k z v)
  have ha := decoder_no_truncated_a0 k z v
  dsimp only [namedBatchCounts, NamedCounts.total, decoderTraversals, decoderFeedback] at *
  omega

theorem decoder_a0_balance (k z : ℕ) (v : Batch) :
    (namedBatchCounts k z v).a0 + decoderTraversals k z v =
      v.total + decoderFeedback k z v := by
  have ha := decoder_no_truncated_a0 k z v
  simp only [namedBatchCounts]
  omega

theorem decoder_line_balance (k z : ℕ) (v : Batch) :
    batchLineX k z v + k * decoderFeedback k z v =
      (k + 1) * decoderTraversals k z v + batchHeight k z v := by
  have hn := batch_count_ge_initial k z v
  have hf := feedbackPrefix_mono hn
  have hz := decodeUnbounded_feedback_coordinate k z
  have hy := decodeUnbounded_feedback_coordinate k (batchCoordinate k z v)
  have hr : initialPhase k z + decoderTraversals k z v = batchCount k z v := by
    unfold decoderTraversals
    omega
  have hfr : feedbackPrefix (initialPhase k z) + decoderFeedback k z v =
      feedbackPrefix (batchCount k z v) := by
    unfold decoderFeedback
    omega
  change z + k * feedbackPrefix (initialPhase k z) =
    (k + 1) * initialPhase k z + initialHeight k z at hz
  change batchCoordinate k z v + k * feedbackPrefix (batchCount k z v) =
    (k + 1) * batchCount k z v + batchHeight k z v at hy
  unfold batchCoordinate at hy
  unfold batchLineX
  nlinarith

/-! Least crossing and least fixed root. Integer potentials retain negative
values of `X-L`; no truncated natural comparison replaces that domain. -/

def passivePotential (k r t : ℕ) : ℤ :=
  ((k + 1 : ℕ) : ℤ) * (t : ℤ) -
    (k : ℤ) * ((feedbackPrefix (r + t) : ℤ) - (feedbackPrefix r : ℤ))

def Crossing (k r X t : ℕ) : Prop :=
  (X : ℤ) - ((k + 1 : ℕ) : ℤ) < passivePotential k r t

def LeastCrossing (k r X t : ℕ) : Prop :=
  Crossing k r X t ∧ ∀ s : ℕ, s < t → ¬ Crossing k r X s

theorem passivePotential_zero (k r : ℕ) : passivePotential k r 0 = 0 := by
  simp [passivePotential]

theorem passivePotential_strict (k r : ℕ) : StrictMono (passivePotential k r) := by
  intro a b hab
  have hf := feedbackPrefix_distance (r + a) (r + b) (by omega)
  have hm := feedbackPrefix_mono (show r + a ≤ r + b by omega)
  have hfi : (feedbackPrefix (r + b) : ℤ) - feedbackPrefix (r + a) ≤
      (b : ℤ) - a := by omega
  have hk : (0 : ℤ) ≤ k := by positivity
  have hx : (0 : ℤ) ≤ (k : ℤ) *
      ((b : ℤ) - a - ((feedbackPrefix (r + b) : ℤ) - feedbackPrefix (r + a))) :=
    mul_nonneg hk (by omega)
  unfold passivePotential
  push_cast
  nlinarith

theorem passivePotential_step (k r t : ℕ) :
    passivePotential k r (t + 1) - passivePotential k r t =
      if (r + t) % 4 = 0 then 1 else ((k + 1 : ℕ) : ℤ) := by
  have hs := feedbackPrefix_step (r + t)
  have he : r + (t + 1) = (r + t) + 1 := by omega
  unfold passivePotential
  rw [he, hs]
  split_ifs <;> push_cast <;> ring

theorem decoder_potential_balance (k z : ℕ) (v : Batch) :
    (batchLineX k z v : ℤ) -
      passivePotential k (initialPhase k z) (decoderTraversals k z v) =
      (batchHeight k z v : ℤ) := by
  have hn := batch_count_ge_initial k z v
  have hf := feedbackPrefix_mono hn
  have hr : initialPhase k z + decoderTraversals k z v = batchCount k z v := by
    unfold decoderTraversals
    omega
  have hf' : (decoderFeedback k z v : ℤ) =
      (feedbackPrefix (batchCount k z v) : ℤ) - feedbackPrefix (initialPhase k z) := by
    unfold decoderFeedback
    omega
  have hb := decoder_line_balance k z v
  have hbi : (batchLineX k z v : ℤ) + (k : ℤ) * decoderFeedback k z v =
      ((k + 1 : ℕ) : ℤ) * decoderTraversals k z v + batchHeight k z v := by
    exact_mod_cast hb
  unfold passivePotential
  rw [hr, ← hf']
  linarith

theorem decoder_least_crossing (k : ℕ) (hk : 3 ≤ k) (z : ℕ)
    (hz : z < period k) (v : Batch) :
    LeastCrossing k (initialPhase k z) (batchLineX k z v) (decoderTraversals k z v) := by
  have hc := batch_canonical k z v
  have hb := decoder_potential_balance k z v
  have hn := batch_count_ge_initial k z v
  have hr : initialPhase k z + decoderTraversals k z v = batchCount k z v := by
    unfold decoderTraversals
    omega
  have hcross : Crossing k (initialPhase k z) (batchLineX k z v)
      (decoderTraversals k z v) := by
    unfold Crossing
    have hh : (batchHeight k z v : ℤ) ≤ k := by exact_mod_cast hc.1
    push_cast
    linarith
  refine ⟨hcross, ?_⟩
  intro s hs
  have hpos : 0 < decoderTraversals k z v := by omega
  have he : decoderTraversals k z v - 1 + 1 = decoderTraversals k z v := by omega
  have hstep := passivePotential_step k (initialPhase k z) (decoderTraversals k z v - 1)
  rw [he] at hstep
  have hprev : ¬ Crossing k (initialPhase k z) (batchLineX k z v)
      (decoderTraversals k z v - 1) := by
    unfold Crossing
    by_cases hf : (initialPhase k z + (decoderTraversals k z v - 1)) % 4 = 0
    · have hm : batchCount k z v % 4 = 1 := by omega
      have hh : batchHeight k z v = k := by
        rcases hc.2 with h₀ | h₁ | h₂ | h₃ <;> omega
      rw [if_pos hf] at hstep
      rw [hh] at hb
      push_cast at *
      linarith
    · rw [if_neg hf] at hstep
      push_cast at *
      linarith
  by_cases heq : s = decoderTraversals k z v - 1
  · simpa [heq] using hprev
  · have hlt : s < decoderTraversals k z v - 1 := by omega
    have hm := passivePotential_strict k (initialPhase k z) hlt
    unfold Crossing at *
    linarith

theorem leastCrossing_unique {k r X s t : ℕ}
    (hs : LeastCrossing k r X s) (ht : LeastCrossing k r X t) : s = t := by
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hgt
  · exact ht.2 s hlt hs.1
  · exact hs.2 t hgt ht.1

def lineWaveMap (k r X t : ℕ) : ℕ :=
  (X + k * (feedbackPrefix (r + t) - feedbackPrefix r)) / (k + 1)

theorem lineWaveMap_mono (k r X : ℕ) : Monotone (lineWaveMap k r X) := by
  intro a b hab
  have hf := feedbackPrefix_mono (show r + a ≤ r + b by omega)
  have hfr := feedbackPrefix_mono (show r ≤ r + a by omega)
  have hm := Nat.mul_le_mul_left k (show feedbackPrefix (r + a) - feedbackPrefix r ≤
    feedbackPrefix (r + b) - feedbackPrefix r by omega)
  apply div_mono_from_blocks (k + 1) _ _ (by omega)
  omega

theorem decoder_fixed_root (k z : ℕ) (v : Batch) :
    lineWaveMap k (initialPhase k z) (batchLineX k z v) (decoderTraversals k z v) =
      decoderTraversals k z v := by
  have hr : initialPhase k z + decoderTraversals k z v = batchCount k z v := by
    have hn := batch_count_ge_initial k z v
    unfold decoderTraversals
    omega
  have hb := decoder_line_balance k z v
  have hc := batch_canonical k z v
  unfold lineWaveMap
  rw [hr]
  change (batchLineX k z v + k * decoderFeedback k z v) / (k + 1) = _
  rw [hb]
  have hh : batchHeight k z v ≤ k := hc.1
  exact (div_mod_block (k + 1) _ _ (by omega) (by omega)).1

theorem fixed_root_crosses {k r X t : ℕ} (ht : lineWaveMap k r X t = t) :
    Crossing k r X t := by
  have hf := feedbackPrefix_mono (show r ≤ r + t by omega)
  have he := Nat.mod_add_div (X + k * (feedbackPrefix (r + t) - feedbackPrefix r)) (k + 1)
  have hm := Nat.mod_lt (X + k * (feedbackPrefix (r + t) - feedbackPrefix r))
    (show 0 < k + 1 by omega)
  unfold lineWaveMap at ht
  rw [ht] at he
  have hsub : ((feedbackPrefix (r + t) - feedbackPrefix r : ℕ) : ℤ) =
      (feedbackPrefix (r + t) : ℤ) - feedbackPrefix r := by omega
  have he' : (X : ℤ) + (k : ℤ) * (feedbackPrefix (r + t) - feedbackPrefix r : ℕ) =
      ((k + 1 : ℕ) : ℤ) * t +
        ((X + k * (feedbackPrefix (r + t) - feedbackPrefix r)) % (k + 1) : ℕ) := by
    exact_mod_cast (show X + k * (feedbackPrefix (r + t) - feedbackPrefix r) =
      (k + 1) * t + (X + k * (feedbackPrefix (r + t) - feedbackPrefix r)) % (k + 1) by omega)
  have hmi : ((X + k * (feedbackPrefix (r + t) - feedbackPrefix r)) % (k + 1) : ℕ) < k + 1 := hm
  have hmic : (((X + k * (feedbackPrefix (r + t) - feedbackPrefix r)) % (k + 1) : ℕ) : ℤ) < (k : ℤ) + 1 := by exact_mod_cast hmi
  unfold Crossing passivePotential
  rw [hsub] at he'
  push_cast only [Nat.cast_add, Nat.cast_mul, Nat.cast_one] at he'
  push_cast only [Nat.cast_add, Nat.cast_one]
  nlinarith

theorem decoder_least_fixed_root (k : ℕ) (hk : 3 ≤ k) (z : ℕ)
    (hz : z < period k) (v : Batch) (t : ℕ)
    (ht : lineWaveMap k (initialPhase k z) (batchLineX k z v) t = t) :
    decoderTraversals k z v ≤ t := by
  have hc := decoder_least_crossing k hk z hz v
  have hcross := fixed_root_crosses ht
  by_contra h
  exact hc.2 t (by omega) hcross

/-- Source-facing form with the manuscript's explicit initial `(h,r)`.
All assertions are derived; no desired decoder assertion is a model field. -/
theorem canonical_two_entry_decoder (k : ℕ) (hk : 3 ≤ k) (h r : ℕ)
    (hc : Canonical k h r) (N M : ℕ) :
    let z := encodeResidue k h r
    let v : Batch := ⟨N, M⟩
    let n := batchCount k z v
    Canonical k (batchHeight k z v) (n % 4) ∧
    LeastCrossing k r (h + inputWeight k N M) (n - r) ∧
    namedBatchCounts k z v =
      ⟨N + M + (feedbackPrefix n - feedbackPrefix r) - (n - r),
       bPrefix k n - bPrefix k r, cPrefix k n - cPrefix k r⟩ ∧
    (namedBatchCounts k z v).total = N + M := by
  dsimp only
  have hz := encodeResidue_lt_period hc
  have hi := initial_encoded_pair hc
  have hl := decoder_least_crossing k hk (encodeResidue k h r) hz ⟨N, M⟩
  have ht := decoder_output_total k (encodeResidue k h r) ⟨N, M⟩
  refine ⟨batch_canonical _ _ _, ?_, ?_, ?_⟩
  · simpa only [batchLineX, initialHeight, initialPhase, decoderTraversals, hi] using hl
  · simp only [namedBatchCounts, decoderFeedback, decoderTraversals, initialPhase, hi, Batch.total]
  · exact ht

/-! Batch cocycle: unordered aggregate input counts. An ordered input word
has separate prefix states and is not reconstructed from a `Batch`. -/

theorem batch_state_cocycle (k z : ℕ) (v w : Batch) :
    finalCoordinate k (finalCoordinate k z v) w = finalCoordinate k z (v.add w) := by
  have hw := inputWeight_add k v w
  unfold finalCoordinate batchCoordinate
  rw [hw]
  calc
    _ = (((z + inputWeight k v.N v.M) % period k) % period k +
      inputWeight k w.N w.M % period k) % period k := Nat.add_mod _ _ _
    _ = ((z + inputWeight k v.N v.M) % period k +
      inputWeight k w.N w.M % period k) % period k := by rw [Nat.mod_mod]
    _ = ((z + inputWeight k v.N v.M) + inputWeight k w.N w.M) % period k :=
      (Nat.add_mod _ _ _).symm
    _ = _ := by rw [Nat.add_assoc]

theorem batch_count_lift (k z : ℕ) (v w : Batch) :
    batchCount k z (v.add w) =
      4 * (batchCoordinate k z v / period k) + batchCount k (finalCoordinate k z v) w := by
  have he := Nat.mod_add_div (batchCoordinate k z v) (period k)
  have hw := inputWeight_add k v w
  have hy : batchCoordinate k z (v.add w) =
      period k * (batchCoordinate k z v / period k) +
        batchCoordinate k (finalCoordinate k z v) w := by
    dsimp only [batchCoordinate, finalCoordinate] at *
    rw [hw]
    omega
  unfold batchCount
  rw [hy, decodeUnbounded_shift]

theorem batch_initial_lift (k z : ℕ) (v : Batch) :
    batchCount k z v = 4 * (batchCoordinate k z v / period k) +
      initialPhase k (finalCoordinate k z v) := by
  have he := Nat.mod_add_div (batchCoordinate k z v) (period k)
  have hy : batchCoordinate k z v = period k * (batchCoordinate k z v / period k) +
      finalCoordinate k z v := by unfold finalCoordinate; omega
  unfold batchCount
  conv_lhs => rw [hy, decodeUnbounded_shift]
  rfl

theorem decoder_internal_cocycle (k z : ℕ) (v w : Batch) :
    decoderTraversals k z (v.add w) = decoderTraversals k z v +
      decoderTraversals k (finalCoordinate k z v) w ∧
    decoderFeedback k z (v.add w) = decoderFeedback k z v +
      decoderFeedback k (finalCoordinate k z v) w := by
  have hn := batch_count_ge_initial k z v
  have hn' := batch_count_ge_initial k (finalCoordinate k z v) w
  have hl := batch_count_lift k z v w
  have hi := batch_initial_lift k z v
  have hf := feedbackPrefix_mono hn
  have hf' := feedbackPrefix_mono hn'
  have hfl : feedbackPrefix (batchCount k z (v.add w)) =
      batchCoordinate k z v / period k + feedbackPrefix (batchCount k (finalCoordinate k z v) w) := by
    rw [hl, feedbackPrefix_block]
  have hfi : feedbackPrefix (batchCount k z v) = batchCoordinate k z v / period k +
      feedbackPrefix (initialPhase k (finalCoordinate k z v)) := by
    rw [hi, feedbackPrefix_block]
  unfold decoderTraversals decoderFeedback
  constructor <;> omega

theorem batch_output_cocycle (k : ℕ) (hk : 3 ≤ k) (z : ℕ)
    (hz : z < period k) (v w : Batch) :
    (namedBatchCounts k z v).add (namedBatchCounts k (finalCoordinate k z v) w) =
      namedBatchCounts k z (v.add w) := by
  have hl := batch_count_lift k z v w
  have hi := batch_initial_lift k z v
  have hn := batch_count_ge_initial k z v
  have hn' := batch_count_ge_initial k (finalCoordinate k z v) w
  have hb := bPrefix_mono k hn
  have hb' := bPrefix_mono k hn'
  have hc := cPrefix_mono k hn
  have hc' := cPrefix_mono k hn'
  have hbl : bPrefix k (batchCount k z (v.add w)) =
      batchCoordinate k z v / period k + bPrefix k (batchCount k (finalCoordinate k z v) w) := by
    rw [hl, bPrefix_block]
  have hbi : bPrefix k (batchCount k z v) = batchCoordinate k z v / period k +
      bPrefix k (initialPhase k (finalCoordinate k z v)) := by
    rw [hi, bPrefix_block]
  have hcl : cPrefix k (batchCount k z (v.add w)) =
      2 * (batchCoordinate k z v / period k) + cPrefix k (batchCount k (finalCoordinate k z v) w) := by
    rw [hl, cPrefix_block]
  have hci : cPrefix k (batchCount k z v) = 2 * (batchCoordinate k z v / period k) +
      cPrefix k (initialPhase k (finalCoordinate k z v)) := by
    rw [hi, cPrefix_block]
  have hr := decoder_internal_cocycle k z v w
  have ha := decoder_a0_balance k z v
  have ha' := decoder_a0_balance k (finalCoordinate k z v) w
  have hat := decoder_a0_balance k z (v.add w)
  have hv : (v.add w).total = v.total + w.total := by
    dsimp [Batch.add, Batch.total]
    omega
  apply NamedCounts.ext <;> simp only [NamedCounts.add, namedBatchCounts] at * <;> omega

/-- An ordered word is exposed separately from its unordered multiplicities. -/
def inputWordWeight (k : ℕ) (word : List InputPort) : ℕ :=
  (word.map (fun p => match p with | .E => k | .F => k - 1)).sum

def inputWordBatch (word : List InputPort) : Batch :=
  ⟨word.count .E, word.count .F⟩

theorem inputWordWeight_eq (k : ℕ) (word : List InputPort) :
    inputWordWeight k word = inputWeight k (inputWordBatch word).N (inputWordBatch word).M := by
  induction word with
  | nil => simp [inputWordWeight, inputWordBatch, inputWeight]
  | cons p word ih =>
    cases p <;> simp [inputWordWeight, inputWordBatch, inputWeight, List.count_cons] at * <;>
      nlinarith

/-! Explicit bridge. A physical result needs an operational author to prove
that its cumulative top counts obey this recurrence and that its completed
routing count is a stationary iterate. These premises concern actual legal
waves, not a decoder conclusion field. -/

def scalarIterate (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | q + 1 => f (scalarIterate f q)

theorem scalarIterate_le_fixed (f : ℕ → ℕ) (hm : Monotone f) (t : ℕ)
    (ht : f t = t) (q : ℕ) : scalarIterate f q ≤ t := by
  induction q with
  | zero => simp [scalarIterate]
  | succ q ih => simpa [scalarIterate, ht] using hm ih

theorem decoder_eq_stationary_wave (k : ℕ) (hk : 3 ≤ k) (z : ℕ)
    (hz : z < period k) (v : Batch) (q physicalR : ℕ)
    (wave_count : physicalR = scalarIterate (lineWaveMap k (initialPhase k z) (batchLineX k z v)) q)
    (completed_wave : lineWaveMap k (initialPhase k z) (batchLineX k z v) physicalR = physicalR) :
    physicalR = decoderTraversals k z v := by
  have hlo := decoder_least_fixed_root k hk z hz v physicalR completed_wave
  have hhi := scalarIterate_le_fixed (lineWaveMap k (initialPhase k z) (batchLineX k z v))
    (lineWaveMap_mono k _ _) (decoderTraversals k z v) (decoder_fixed_root k z v) q
  rw [← wave_count] at hhi
  omega

end Partials.Arrival
