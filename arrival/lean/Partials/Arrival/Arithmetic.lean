import Partials.Arrival.Interface

/-!
WIP / UNCHECKED. Drafted without invoking local Lean or Lake.

This module implements only the arithmetic state table in Rotor_Interface,
equations (10)–(13), plus the four-step cumulative-count arithmetic.
It does not prove the table corresponds to legal rotor routing; that is the
separate content of Lemma 4.1 and Theorem 4.4 in the manuscript.
-/


namespace Partials.Arrival

/-- The number of canonical states, `P = 3k + 4` in Section 4. -/
def period (k : ℕ) : ℕ := 3 * k + 4

/-- The paper's exceptional phase-one condition is included. -/
def Canonical (k h r : ℕ) : Prop :=
  h ≤ k ∧ (r = 0 ∨ (r = 1 ∧ h = k) ∨ r = 2 ∨ r = 3)

/-- Formula (11), restricted in use to canonical states. -/
def encodeResidue (k h r : ℕ) : ℕ :=
  match r with
  | 0 => h
  | 1 => k + 1
  | 2 => k + 2 + h
  | 3 => 2 * k + 3 + h
  | _ => 0

/-- The four rows of the residue table (12). Its intended domain is `t < period k`. -/
def decodeResidue (k t : ℕ) : ℕ × ℕ :=
  if t ≤ k then (t, 0)
  else if t = k + 1 then (k, 1)
  else if t ≤ 2 * k + 2 then (t - (k + 2), 2)
  else (t - (2 * k + 3), 3)

theorem encodeResidue_lt_period {k h r : ℕ}
    (hc : Canonical k h r) : encodeResidue k h r < period k := by
  rcases hc with ⟨hh, hr⟩
  rcases hr with h₀ | h₁ | h₂ | h₃
  · subst r
    simp [encodeResidue, period] <;> omega
  · rcases h₁ with ⟨hr, _⟩
    subst r
    simp [encodeResidue, period] <;> omega
  · subst r
    simp [encodeResidue, period] <;> omega
  · subst r
    simp [encodeResidue, period] <;> omega

theorem decodeResidue_canonical (k t : ℕ) (ht : t < period k) :
    Canonical k (decodeResidue k t).1 (decodeResidue k t).2 := by
  by_cases h₀ : t ≤ k
  · simp [decodeResidue, h₀, Canonical]
  · by_cases h₁ : t = k + 1
    · simp [decodeResidue, h₀, h₁, Canonical]
    · by_cases h₂ : t ≤ 2 * k + 2
      · simp [decodeResidue, h₀, h₁, h₂, Canonical] <;> omega
      · simp [decodeResidue, h₀, h₁, h₂, Canonical, period] at * <;> omega

theorem encode_decodeResidue (k t : ℕ) (ht : t < period k) :
    encodeResidue k (decodeResidue k t).1 (decodeResidue k t).2 = t := by
  by_cases h₀ : t ≤ k
  · simp [decodeResidue, h₀, encodeResidue]
  · by_cases h₁ : t = k + 1
    · simp [decodeResidue, h₀, h₁, encodeResidue]
    · by_cases h₂ : t ≤ 2 * k + 2
      · have hlo : k + 2 ≤ t := by omega
        simp only [decodeResidue, if_neg h₀, if_neg h₁, if_pos h₂, Prod.fst, Prod.snd, encodeResidue]
        omega
      · have hlo : 2 * k + 3 ≤ t := by omega
        simp only [decodeResidue, if_neg h₀, if_neg h₁, if_neg h₂, Prod.fst, Prod.snd, encodeResidue]
        omega

theorem decode_encodeResidue {k h r : ℕ} (hc : Canonical k h r) :
    decodeResidue k (encodeResidue k h r) = (h, r) := by
  rcases hc with ⟨hh, hr⟩
  rcases hr with h₀ | h₁ | h₂ | h₃
  · subst r
    simp [encodeResidue, decodeResidue, hh]
  · rcases h₁ with ⟨hr, heq⟩
    subst r
    have hnot : ¬ k + 1 ≤ k := by omega
    simp [encodeResidue, decodeResidue, hnot, heq]
  · subst r
    have hnot : ¬ k + 2 + h ≤ k := by omega
    have hne : k + 2 + h ≠ k + 1 := by omega
    have hle : k + 2 + h ≤ 2 * k + 2 := by omega
    simp [encodeResidue, decodeResidue, hnot, hne, hle] <;> omega
  · subst r
    have hnot : ¬ 2 * k + 3 + h ≤ k := by omega
    have hne : 2 * k + 3 + h ≠ k + 1 := by omega
    have hnot₂ : ¬ 2 * k + 3 + h ≤ 2 * k + 2 := by omega
    simp [encodeResidue, decodeResidue, hnot, hne, hnot₂] <;> omega

/-- Table (12) applied to an unbounded coordinate `y`. -/
def decodeUnbounded (k y : ℕ) : ℕ × ℕ :=
  let q := y / period k
  let t := y % period k
  let s := decodeResidue k t
  (s.1, 4 * q + s.2)

/-- Weight of an `(N,M)` batch, with `k ≥ 3` in the paper. -/
def inputWeight (k N M : ℕ) : ℕ := k * N + (k - 1) * M

/-- Cumulative passive feedback count `F(n) = ⌈n/4⌉`. -/
def feedbackPrefix (n : ℕ) : ℕ := (n + 3) / 4

/-- The phase of the second `b₀` output in the repeated four-step word. -/
def bThreshold (k : ℕ) : ℕ := if k % 2 = 1 then 2 else 3

/-- Cumulative `b₀` output count in equation (5). -/
def bPrefix (k n : ℕ) : ℕ :=
  n / 4 + (if n % 4 ≥ bThreshold k then 1 else 0)

/-- Cumulative `c₀` output count in equation (5). -/
def cPrefix (k n : ℕ) : ℕ := n - feedbackPrefix n - bPrefix k n

theorem feedbackPrefix_add_four (n : ℕ) :
    feedbackPrefix (n + 4) = feedbackPrefix n + 1 := by
  unfold feedbackPrefix
  omega

theorem bPrefix_add_four (k n : ℕ) :
    bPrefix k (n + 4) = bPrefix k n + 1 := by
  have hmod : (n + 4) % 4 = n % 4 := by omega
  have hdiv : (n + 4) / 4 = n / 4 + 1 := by omega
  simp [bPrefix, hmod, hdiv] <;> omega

/-! The retained draft above is extended below. All added proofs are source
arguments only: R3 has not executed a Lean kernel. -/

theorem period_pos (k : ℕ) : 0 < period k := by
  unfold period
  omega

theorem canonical_phase_lt {k h r : ℕ} (hc : Canonical k h r) : r < 4 := by
  rcases hc with ⟨_, hr⟩
  rcases hr with h₀ | h₁ | h₂ | h₃ <;> omega

theorem canonical_zero (k : ℕ) : Canonical k 0 0 := by
  simp [Canonical]

/-- A Euclidean block identity, with its hypotheses visible. -/
theorem div_mod_block (d q t : ℕ) (hd : 0 < d) (ht : t < d) :
    (d * q + t) / d = q ∧ (d * q + t) % d = t := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_left _ _ hd]
    simp [Nat.div_eq_of_lt ht]
  · simp [Nat.add_mod, Nat.mod_eq_of_lt ht]

theorem decodeResidue_phase_lt (k t : ℕ) : (decodeResidue k t).2 < 4 := by
  unfold decodeResidue
  split_ifs <;> simp

theorem decodeResidue_phase_mono (k t u : ℕ) (htu : t ≤ u) :
    (decodeResidue k t).2 ≤ (decodeResidue k u).2 := by
  unfold decodeResidue
  split_ifs <;> simp_all <;> omega

theorem div_mono_from_blocks (d y v : ℕ) (hd : 0 < d) (hyv : y ≤ v) :
    y / d ≤ v / d := by
  exact Nat.div_le_div_right hyv

/-- Encoding of canonical unbounded states. This is a block encoding, not
an unrestricted natural subtraction of `Ln - k F(n)`. -/
def encodeUnbounded (k h n : ℕ) : ℕ :=
  period k * (n / 4) + encodeResidue k h (n % 4)

theorem decodeUnbounded_phase (k y : ℕ) :
    (decodeUnbounded k y).2 % 4 = (decodeResidue k (y % period k)).2 := by
  have hr := decodeResidue_phase_lt k (y % period k)
  simp only [decodeUnbounded]
  omega

theorem decodeUnbounded_quotient (k y : ℕ) :
    (decodeUnbounded k y).2 / 4 = y / period k := by
  have hr := decodeResidue_phase_lt k (y % period k)
  simp only [decodeUnbounded]
  omega

theorem decodeUnbounded_canonical (k y : ℕ) :
    Canonical k (decodeUnbounded k y).1 ((decodeUnbounded k y).2 % 4) := by
  rw [decodeUnbounded_phase]
  exact decodeResidue_canonical k (y % period k) (Nat.mod_lt _ (period_pos k))

theorem encode_decodeUnbounded (k y : ℕ) :
    encodeUnbounded k (decodeUnbounded k y).1 (decodeUnbounded k y).2 = y := by
  unfold encodeUnbounded
  rw [decodeUnbounded_quotient, decodeUnbounded_phase]
  change period k * (y / period k) +
    encodeResidue k (decodeResidue k (y % period k)).1
      (decodeResidue k (y % period k)).2 = y
  rw [encode_decodeResidue k _ (Nat.mod_lt _ (period_pos k))]
  have he := Nat.mod_add_div y (period k)
  omega

theorem decode_encodeUnbounded {k h n : ℕ}
    (hc : Canonical k h (n % 4)) :
    decodeUnbounded k (encodeUnbounded k h n) = (h, n) := by
  have hb := div_mod_block (period k) (n / 4)
    (encodeResidue k h (n % 4)) (period_pos k) (encodeResidue_lt_period hc)
  have he := Nat.mod_add_div n 4
  simp only [decodeUnbounded, encodeUnbounded]
  rw [hb.1, hb.2, decode_encodeResidue hc]
  congr 1
  omega

/-- Uniqueness uses the exceptional phase-one restriction; dropping it
would invalidate the inverse statement. -/
theorem unbounded_representation_unique {k h n h' n' : ℕ}
    (hc : Canonical k h (n % 4)) (hc' : Canonical k h' (n' % 4))
    (he : encodeUnbounded k h n = encodeUnbounded k h' n') :
    h = h' ∧ n = n' := by
  have hd := congrArg (decodeUnbounded k) he
  rw [decode_encodeUnbounded hc, decode_encodeUnbounded hc'] at hd
  exact Prod.mk.inj hd

theorem decodeUnbounded_count_mono (k y v : ℕ) (hyv : y ≤ v) :
    (decodeUnbounded k y).2 ≤ (decodeUnbounded k v).2 := by
  have hq := div_mono_from_blocks (period k) y v (period_pos k) hyv
  have hry := decodeResidue_phase_lt k (y % period k)
  have hrv := decodeResidue_phase_lt k (v % period k)
  by_cases he : y / period k = v / period k
  · have hye := Nat.mod_add_div y (period k)
    have hve := Nat.mod_add_div v (period k)
    rw [he] at hye
    have hm : y % period k ≤ v % period k := by omega
    have hr := decodeResidue_phase_mono k _ _ hm
    simp only [decodeUnbounded]
    omega
  · simp only [decodeUnbounded]
    omega

theorem feedbackPrefix_le (n : ℕ) : feedbackPrefix n ≤ n := by
  unfold feedbackPrefix
  omega

theorem feedbackPrefix_mono : Monotone feedbackPrefix := by
  intro a b hab
  unfold feedbackPrefix
  omega

theorem feedbackPrefix_distance (a b : ℕ) (hab : a ≤ b) :
    feedbackPrefix b - feedbackPrefix a ≤ b - a := by
  unfold feedbackPrefix
  omega

theorem bPrefix_mono (k : ℕ) : Monotone (bPrefix k) := by
  intro a b hab
  by_cases ho : k % 2 = 1
  · simp only [bPrefix, bThreshold, ho, if_true]
    split_ifs <;> omega
  · simp only [bPrefix, bThreshold, ho, if_false]
    split_ifs <;> omega

theorem passive_prefix_partition (k n : ℕ) :
    feedbackPrefix n + bPrefix k n + cPrefix k n = n := by
  by_cases ho : k % 2 = 1
  · simp only [feedbackPrefix, bPrefix, bThreshold, ho, if_true, cPrefix]
    split_ifs <;> omega
  · simp only [feedbackPrefix, bPrefix, bThreshold, ho, if_false, cPrefix]
    split_ifs <;> omega

theorem cPrefix_mono (k : ℕ) : Monotone (cPrefix k) := by
  intro a b hab
  by_cases ho : k % 2 = 1
  · simp only [cPrefix, feedbackPrefix, bPrefix, bThreshold, ho, if_true]
    split_ifs <;> omega
  · simp only [cPrefix, feedbackPrefix, bPrefix, bThreshold, ho, if_false]
    split_ifs <;> omega

/-- Source correspondence for the cut word. The two `c0` slots remain
separate slots even though their destination agrees. -/
theorem passive_prefix_step (k n : ℕ) :
    let d := passiveWord k ⟨n % 4, Nat.mod_lt _ (by decide)⟩
    feedbackPrefix (n + 1) = feedbackPrefix n + (if d = .feedback then 1 else 0) ∧
    bPrefix k (n + 1) = bPrefix k n + (if d = .b0 then 1 else 0) ∧
    cPrefix k (n + 1) = cPrefix k n + (if d = .c0 then 1 else 0) := by
  by_cases ho : k % 2 = 1
  · simp only [passiveWord, feedbackPrefix, bPrefix, bThreshold, cPrefix,
      ho, if_true]
    split_ifs <;> simp_all <;> omega
  · simp only [passiveWord, feedbackPrefix, bPrefix, bThreshold, cPrefix,
      ho, if_false]
    split_ifs <;> simp_all <;> omega

theorem feedbackPrefix_step (n : ℕ) :
    feedbackPrefix (n + 1) = feedbackPrefix n + (if n % 4 = 0 then 1 else 0) := by
  unfold feedbackPrefix
  split_ifs <;> omega

theorem cPrefix_add_four (k n : ℕ) : cPrefix k (n + 4) = cPrefix k n + 2 := by
  have hp := passive_prefix_partition k n
  have hp' := passive_prefix_partition k (n + 4)
  rw [feedbackPrefix_add_four, bPrefix_add_four] at hp'
  omega

theorem feedbackPrefix_block (q n : ℕ) :
    feedbackPrefix (4 * q + n) = q + feedbackPrefix n := by
  induction q with
  | zero => simp
  | succ q ih =>
    have he : 4 * (q + 1) + n = (4 * q + n) + 4 := by omega
    rw [he, feedbackPrefix_add_four, ih]
    omega

theorem bPrefix_block (k q n : ℕ) : bPrefix k (4 * q + n) = q + bPrefix k n := by
  induction q with
  | zero => simp
  | succ q ih =>
    have he : 4 * (q + 1) + n = (4 * q + n) + 4 := by omega
    rw [he, bPrefix_add_four, ih]
    omega

theorem cPrefix_block (k q n : ℕ) : cPrefix k (4 * q + n) = 2 * q + cPrefix k n := by
  induction q with
  | zero => simp
  | succ q ih =>
    have he : 4 * (q + 1) + n = (4 * q + n) + 4 := by omega
    rw [he, cPrefix_add_four, ih]
    omega

def terminalPrefix (n : ℕ) : ℕ := n - feedbackPrefix n

theorem terminalPrefix_partition (k n : ℕ) :
    terminalPrefix n = bPrefix k n + cPrefix k n := by
  have hp := passive_prefix_partition k n
  unfold terminalPrefix
  omega

theorem terminalPrefix_mono : Monotone terminalPrefix := by
  intro a b hab
  have hp := terminalPrefix_partition 0 a
  have hq := terminalPrefix_partition 0 b
  have hb := bPrefix_mono 0 hab
  have hc := cPrefix_mono 0 hab
  omega

theorem terminalPrefix_block (q n : ℕ) :
    terminalPrefix (4 * q + n) = 3 * q + terminalPrefix n := by
  have hf := feedbackPrefix_block q n
  have hle := feedbackPrefix_le n
  unfold terminalPrefix at *
  omega

theorem encodeResidue_coordinate {k h r : ℕ} (hc : Canonical k h r) :
    encodeResidue k h r = k * terminalPrefix r + r + h := by
  rcases hc with ⟨hh, hr⟩
  rcases hr with h₀ | h₁ | h₂ | h₃
  · subst r
    simp [encodeResidue, terminalPrefix, feedbackPrefix]
  · rcases h₁ with ⟨he, hh'⟩
    subst r
    subst h
    simp [encodeResidue, terminalPrefix, feedbackPrefix] <;> omega
  · subst r
    simp [encodeResidue, terminalPrefix, feedbackPrefix] <;> omega
  · subst r
    simp [encodeResidue, terminalPrefix, feedbackPrefix] <;> omega

/-- Natural form of `y = (k+1)n - k ceil(n/4) + h`. -/
theorem encodeUnbounded_coordinate {k h n : ℕ}
    (hc : Canonical k h (n % 4)) :
    encodeUnbounded k h n = k * terminalPrefix n + n + h := by
  have he := Nat.mod_add_div n 4
  have ht : terminalPrefix n = 3 * (n / 4) + terminalPrefix (n % 4) := by
    calc
      terminalPrefix n = terminalPrefix (4 * (n / 4) + n % 4) := by congr 1; omega
      _ = _ := terminalPrefix_block _ _
  unfold encodeUnbounded
  rw [encodeResidue_coordinate hc, ht]
  unfold period
  nlinarith

theorem decodeUnbounded_coordinate (k y : ℕ) :
    y = k * terminalPrefix (decodeUnbounded k y).2 +
      (decodeUnbounded k y).2 + (decodeUnbounded k y).1 := by
  calc
    y = encodeUnbounded k (decodeUnbounded k y).1 (decodeUnbounded k y).2 :=
      (encode_decodeUnbounded k y).symm
    _ = _ := encodeUnbounded_coordinate (decodeUnbounded_canonical k y)

theorem decodeUnbounded_feedback_coordinate (k y : ℕ) :
    y + k * feedbackPrefix (decodeUnbounded k y).2 =
      (k + 1) * (decodeUnbounded k y).2 + (decodeUnbounded k y).1 := by
  have he := decodeUnbounded_coordinate k y
  have hf := feedbackPrefix_le (decodeUnbounded k y).2
  have ht : terminalPrefix (decodeUnbounded k y).2 +
      feedbackPrefix (decodeUnbounded k y).2 = (decodeUnbounded k y).2 := by
    unfold terminalPrefix
    omega
  nlinarith

theorem unbounded_coordinate_representation_unique {k h n h' n' : ℕ}
    (hc : Canonical k h (n % 4)) (hc' : Canonical k h' (n' % 4))
    (he : k * terminalPrefix n + n + h = k * terminalPrefix n' + n' + h') :
    h = h' ∧ n = n' := by
  apply unbounded_representation_unique hc hc'
  rw [encodeUnbounded_coordinate hc, encodeUnbounded_coordinate hc']
  exact he

theorem decodeUnbounded_shift (k q y : ℕ) :
    decodeUnbounded k (period k * q + y) =
      ((decodeUnbounded k y).1, 4 * q + (decodeUnbounded k y).2) := by
  have hc := decodeUnbounded_canonical k y
  have hc' : Canonical k (decodeUnbounded k y).1
      ((4 * q + (decodeUnbounded k y).2) % 4) := by
    have hm : (4 * q + (decodeUnbounded k y).2) % 4 =
        (decodeUnbounded k y).2 % 4 := by omega
    rwa [hm]
  have he : encodeUnbounded k (decodeUnbounded k y).1
      (4 * q + (decodeUnbounded k y).2) = period k * q + y := by
    unfold encodeUnbounded
    have hm : (4 * q + (decodeUnbounded k y).2) % 4 =
        (decodeUnbounded k y).2 % 4 := by omega
    have hd : (4 * q + (decodeUnbounded k y).2) / 4 =
        q + (decodeUnbounded k y).2 / 4 := by omega
    rw [hm, hd]
    have hy := encode_decodeUnbounded k y
    unfold encodeUnbounded at hy
    nlinarith
  rw [← he]
  exact decode_encodeUnbounded hc'

theorem inputWeight_add (k : ℕ) (v w : Batch) :
    inputWeight k (v.add w).N (v.add w).M =
      inputWeight k v.N v.M + inputWeight k w.N w.M := by
  simp only [inputWeight, Batch.add]
  ring

theorem inputWeight_le_total (k : ℕ) (v : Batch) :
    inputWeight k v.N v.M ≤ k * v.total := by
  have hm := Nat.mul_le_mul_right v.M (Nat.sub_le k 1)
  unfold inputWeight Batch.total
  nlinarith

end Partials.Arrival
