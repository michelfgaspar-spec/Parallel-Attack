import Partials.Arrival.Interface

/-! Source-only cost vocabulary. The polynomial charging lemma below is an
arithmetic result about a stated elementary-work model. It does not certify a
running decoder, its intermediate bit lengths, or a binary-search program.
Those correspondence obligations are recorded in COST_PROOF.md. -/
namespace Partials.Arrival.Cost

/-- The integer ceiling of log₂ for positive arguments, with value zero at 0.
The decoder only supplies positive arguments. -/
def ceilLogTwo (n : ℕ) : ℕ :=
  if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

def batchBits (v : Batch) : ℕ := 1 + ceilLogTwo (v.N + v.M + 1)

def decoderBits (k : ℕ) (v : Batch) : ℕ :=
  batchBits v + ceilLogTwo (k + 1) + 1

def scalarStateBits (k : ℕ) : ℕ := ceilLogTwo (3 * k + 4)

def coupledBits (k MA MB : ℕ) : ℕ :=
  1 + ceilLogTwo (MA + MB + 11) + ceilLogTwo (k + 1)

def couplingUpper (MA MB : ℕ) : ℕ := MA + MB + 10

/-- Number of elementary quadratic arithmetic calls, linear arithmetic calls,
and output bit writes. Constants are independent of graph size and batches. -/
structure ElementaryWork where
  quadraticCalls : ℕ
  linearCalls : ℕ
  outputWrites : ℕ
  deriving DecidableEq

def ElementaryWork.charge (w : ElementaryWork) (A : ℕ) : ℕ :=
  w.quadraticCalls * (A * A) + w.linearCalls * A + w.outputWrites

def ElementaryWork.Bounded (w : ElementaryWork) (k c : ℕ) : Prop :=
  w.quadraticCalls ≤ c ∧ w.linearCalls ≤ c * k ∧ w.outputWrites ≤ c * k

theorem decoderBits_positive (k : ℕ) (v : Batch) : 1 ≤ decoderBits k v := by
  unfold decoderBits batchBits
  omega

/-- Uniform pointwise polynomial estimate; the model-to-program bridge is
explicitly separate from this theorem. -/
theorem elementary_charge_bound (w : ElementaryWork) (k c A : ℕ)
    (hA : 1 ≤ A) (hw : w.Bounded k c) :
    w.charge A ≤ 2 * c * (A * A + k * A) := by
  rcases hw with ⟨hq, hl, ho⟩
  have hq' := Nat.mul_le_mul_right (A * A) hq
  have hl' := Nat.mul_le_mul_right A hl
  have ho' : w.outputWrites ≤ (c * k) * A := by
    calc
      w.outputWrites ≤ c * k := ho
      _ ≤ (c * k) * A := by nlinarith
  unfold ElementaryWork.charge
  calc
    w.quadraticCalls * (A * A) + w.linearCalls * A + w.outputWrites
        ≤ c * (A * A) + (c * k) * A + (c * k) * A := by omega
    _ ≤ 2 * c * (A * A + k * A) := by nlinarith

theorem decoder_charge_bound (w : ElementaryWork) (k c : ℕ) (v : Batch)
    (hw : w.Bounded k c) :
    w.charge (decoderBits k v) ≤
      2 * c * (decoderBits k v * decoderBits k v + k * decoderBits k v) :=
  elementary_charge_bound w k c (decoderBits k v) (decoderBits_positive k v) hw

/-- A prospective search evaluation budget; no search implementation or
evaluation-count theorem is hidden in this definition. -/
def searchEvaluations (U : ℕ) : ℕ := ceilLogTwo (U + 1) + 1

def coupledCharge (k MA MB c : ℕ) : ℕ :=
  (2 * searchEvaluations (couplingUpper MA MB) + 2) *
    (2 * c * (coupledBits k MA MB * coupledBits k MA MB +
      k * coupledBits k MA MB))

inductive RequestedOutput where
  | scalarState
  | namedCountsAndFeedback
  | fullRotorVector
  | orderedTerminalWord
  deriving DecidableEq

/-- The manuscript bit bound includes the full vector and binary batch sizes.
An ordered word requires its own output-length charge. -/
def decoderBoundScope : RequestedOutput → Prop
  | .orderedTerminalWord => False
  | _ => True

theorem fullRotorVector_in_scope : decoderBoundScope .fullRotorVector := by
  trivial

theorem orderedTerminalWord_requires_separate_charge :
    ¬ decoderBoundScope .orderedTerminalWord := by
  simp [decoderBoundScope]

end Partials.Arrival.Cost
