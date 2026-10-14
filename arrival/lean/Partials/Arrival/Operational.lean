import Partials.Arrival.Interface

/-! R3/q0002. Uncompiled source contribution, not a kernel receipt.
Source: arrival/main.tex, §2 (eq:upper) and §3.1 (lem:line).
All rotors store the NEXT slot. Named boundaries and external inputs retain
different types. Explicit `...Obligation` propositions below are unproved
bridges, never global instances or custom axioms. -/
namespace Partials.Arrival

inductive UpperVertex (k : ℕ) where
  | boundary : NamedOutput → UpperVertex k
  | a : Fin k → UpperVertex k
  | b : Fin (k - 1) → UpperVertex k
  | c : Fin (k - 2) → UpperVertex k
  deriving DecidableEq, Fintype

def upperIsBoundary {k : ℕ} : UpperVertex k → Prop
  | .boundary _ => True
  | _ => False

def nextBinarySlot (r : Fin 2) : Fin 2 :=
  ⟨(r.val + 1) % 2, Nat.mod_lt _ (by decide)⟩

/-- Fin indices are zero based: `.a i` means a_(i.val+1), etc. -/
def upperSuccessor {k : ℕ} (hk : 3 ≤ k) : UpperVertex k → Fin 2 → UpperVertex k
  | .boundary o, _ => .boundary o
  | .a i, slot =>
    if slot.val = 0 then
      if hi : i.val = 0 then .boundary .a0
      else .a ⟨i.val - 1, by omega⟩
    else if hi : i.val + 1 < k then .a ⟨i.val + 1, hi⟩
    else .b ⟨k - 2, by omega⟩
  | .b i, slot =>
    if hi : i.val = 0 then
      if slot.val = 0 then .a ⟨k - 1, by omega⟩ else .boundary .c0
    else if slot.val = 0 then .b ⟨i.val - 1, by omega⟩
    else .c ⟨i.val - 1, by omega⟩
  | .c i, slot =>
    if hi : i.val = 0 then
      if slot.val = 0 then .boundary .b0 else .boundary .c0
    else if slot.val = 0 then .b ⟨i.val - 1, by omega⟩
    else .c ⟨i.val - 1, by omega⟩

def upperNetwork {k : ℕ} (hk : 3 ≤ k) :
    Partials.Interface.OrderedRotorNetwork (UpperVertex k) where
  slotCount := fun _ => 2
  slots_positive := fun _ => by decide
  successor := upperSuccessor hk
  sink := upperIsBoundary
  sink_fixed := by
    intro v hv slot
    cases v <;> simp_all [upperIsBoundary, upperSuccessor]

theorem upperNetwork_binary {k : ℕ} (hk : 3 ≤ k) :
    Partials.Interface.IsBinaryRotorNetwork (upperNetwork hk) := by
  intro v
  rfl

abbrev UpperRotors (k : ℕ) := UpperVertex k → Fin 2

structure UpperRunningState (k : ℕ) where
  position : UpperVertex k
  rotors : UpperRotors k

/-- The successor reads the old slot; the update subsequently advances it. -/
def upperDeparture {k : ℕ} (hk : 3 ≤ k) (s : UpperRunningState k) :
    UpperRunningState k :=
  ⟨upperSuccessor hk s.position (s.rotors s.position),
    Function.update s.rotors s.position (nextBinarySlot (s.rotors s.position))⟩

def UpperStep {k : ℕ} (hk : 3 ≤ k) (s t : UpperRunningState k) : Prop :=
  ¬ upperIsBoundary s.position ∧ t = upperDeparture hk s

theorem upperDeparture_uses_next {k : ℕ} (hk : 3 ≤ k) (s : UpperRunningState k) :
    (upperDeparture hk s).position =
      upperSuccessor hk s.position (s.rotors s.position) := rfl

theorem upperDeparture_advances {k : ℕ} (hk : 3 ≤ k) (s : UpperRunningState k) :
    (upperDeparture hk s).rotors s.position = nextBinarySlot (s.rotors s.position) := by
  simp [upperDeparture]

theorem upperDeparture_untouched {k : ℕ} (hk : 3 ≤ k)
    (s : UpperRunningState k) (v : UpperVertex k) (hv : v ≠ s.position) :
    (upperDeparture hk s).rotors v = s.rotors v := by
  simp [upperDeparture, Function.update, hv]

inductive UpperTrace {k : ℕ} (hk : 3 ≤ k) :
    UpperRunningState k → UpperRunningState k → ℕ → Prop where
  | nil (s) : UpperTrace hk s s 0
  | cons {s t u n} : UpperStep hk s t → UpperTrace hk t u n →
      UpperTrace hk s u (n + 1)

def upperInputVertex {k : ℕ} (hk : 3 ≤ k) : InputPort → UpperVertex k
  | .E => .a ⟨k - 1, by omega⟩
  | .F => .a ⟨k - 2, by omega⟩

/-- A trace cannot depart from a boundary. Thus its terminal is the first hit.
Internal b1→ak departures occur inside this trace and do not add InputPorts. -/
def CompleteUpperExcursion {k : ℕ} (hk : 3 ≤ k)
    (R R' : UpperRotors k) (input : InputPort) (o : NamedOutput) : Prop :=
  ∃ cost, UpperTrace hk ⟨upperInputVertex hk input, R⟩ ⟨.boundary o, R'⟩ cost

inductive SequentialUpperRouting {k : ℕ} (hk : 3 ≤ k) :
    UpperRotors k → List InputPort → UpperRotors k → List NamedOutput → Prop where
  | nil (R) : SequentialUpperRouting hk R [] R []
  | cons {R R₁ R₂ input inputs o outputs} :
      CompleteUpperExcursion hk R R₁ input o →
      SequentialUpperRouting hk R₁ inputs R₂ outputs →
      SequentialUpperRouting hk R (input :: inputs) R₂ (o :: outputs)

def inputMultiplicities (inputs : List InputPort) : Batch :=
  ⟨inputs.count .E, inputs.count .F⟩

def outputMultiplicities (outputs : List NamedOutput) : NamedCounts :=
  ⟨outputs.count .a0, outputs.count .b0, outputs.count .c0⟩

theorem sequentialUpperRouting_length {k : ℕ} (hk : 3 ≤ k)
    {R R' inputs outputs} (routing : SequentialUpperRouting hk R inputs R' outputs) :
    inputs.length = outputs.length := by
  induction routing with
  | nil => rfl
  | cons _ _ ih => simpa using congrArg Nat.succ ih

/-- OPEN OP-TERM. Exact domain: every binary rotor phase, k≥3, one E/F
external entry; no compressed-orbit or acyclicity assumption. The finite
sink-accessibility proof in §2 has not been translated to Lean here. -/
def UpperTerminationObligation (k : ℕ) (hk : 3 ≤ k) : Prop :=
  ∀ (R : UpperRotors k) (input : InputPort),
    ∃ R' o, CompleteUpperExcursion hk R R' input o

theorem sequentialUpperRouting_exists_of_termination {k : ℕ} (hk : 3 ≤ k)
    (termination : UpperTerminationObligation k hk)
    (inputs : List InputPort) (R : UpperRotors k) :
    ∃ R' outputs, SequentialUpperRouting hk R inputs R' outputs := by
  induction inputs generalizing R with
  | nil => exact ⟨R, [], .nil R⟩
  | cons input inputs ih =>
    obtain ⟨R₁, o, excursion⟩ := termination R input
    obtain ⟨R₂, outputs, rest⟩ := ih R₁
    exact ⟨R₂, o :: outputs, .cons excursion rest⟩

/-! A finite-stack least-action proof. Nonsinks V and exits Exit are separate.
No termination is inferred from this theorem: a complete legal schedule must
exist before uniqueness can be applied. An exit word is not an observable of
the firing vector; its aggregate counts are. -/

def prefixHits {α : Type*} [DecidableEq α] (word : ℕ → α) (target : α) : ℕ → ℕ
  | 0 => 0
  | n + 1 => prefixHits word target n + if word n = target then 1 else 0

theorem prefixHits_mono {α : Type*} [DecidableEq α] (word : ℕ → α) (target : α) :
    Monotone (prefixHits word target) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [prefixHits]
  omega

def stackIncoming {V Exit : Type*} [Fintype V] [DecidableEq V] [DecidableEq Exit]
    (stack : V → ℕ → Sum V Exit) (f : V → ℕ) (v : V) : ℕ :=
  ∑ u, prefixHits (stack u) (.inl v) (f u)

def stackExitCounts {V Exit : Type*} [Fintype V] [DecidableEq V] [DecidableEq Exit]
    (stack : V → ℕ → Sum V Exit) (f : V → ℕ) (o : Exit) : ℕ :=
  ∑ u, prefixHits (stack u) (.inr o) (f u)

theorem stackIncoming_mono {V Exit : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq Exit] (stack : V → ℕ → Sum V Exit)
    {f g : V → ℕ} (hfg : ∀ u, f u ≤ g u) (v : V) :
    stackIncoming stack f v ≤ stackIncoming stack g v := by
  apply Finset.sum_le_sum
  intro u hu
  exact prefixHits_mono (stack u) (.inl v) (hfg u)

inductive LegalStackPrefix {V Exit : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq Exit]
    (initial : V → ℕ) (stack : V → ℕ → Sum V Exit) : (V → ℕ) → Prop where
  | zero : LegalStackPrefix initial stack (fun _ => 0)
  | fire {f} (v : V) : LegalStackPrefix initial stack f →
      f v < initial v + stackIncoming stack f v →
      LegalStackPrefix initial stack (Function.update f v (f v + 1))

def StackComplete {V Exit : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq Exit]
    (initial : V → ℕ) (stack : V → ℕ → Sum V Exit) (f : V → ℕ) : Prop :=
  ∀ v, f v = initial v + stackIncoming stack f v

theorem legalStackPrefix_le_complete {V Exit : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq Exit]
    (initial : V → ℕ) (stack : V → ℕ → Sum V Exit)
    {f b : V → ℕ} (legal : LegalStackPrefix initial stack f)
    (complete : StackComplete initial stack b) : ∀ v, f v ≤ b v := by
  induction legal with
  | zero => intro v; exact Nat.zero_le _
  | @fire f v previous enabled ih =>
    intro w
    by_cases hw : w = v
    · subst w
      simp only [Function.update_self]
      have incoming_le := stackIncoming_mono stack ih v
      have final_balance := complete v
      omega
    · simpa [Function.update, hw] using ih w

theorem completeLegalStack_counts_unique {V Exit : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq Exit]
    (initial : V → ℕ) (stack : V → ℕ → Sum V Exit)
    {f g : V → ℕ} (lf : LegalStackPrefix initial stack f)
    (lg : LegalStackPrefix initial stack g)
    (cf : StackComplete initial stack f) (cg : StackComplete initial stack g) :
    f = g := by
  funext v
  exact Nat.le_antisymm
    (legalStackPrefix_le_complete initial stack lf cg v)
    (legalStackPrefix_le_complete initial stack lg cf v)

theorem completeLegalStack_exits_unique {V Exit : Type*} [Fintype V]
    [DecidableEq V] [DecidableEq Exit]
    (initial : V → ℕ) (stack : V → ℕ → Sum V Exit)
    {f g : V → ℕ} (lf : LegalStackPrefix initial stack f)
    (lg : LegalStackPrefix initial stack g)
    (cf : StackComplete initial stack f) (cg : StackComplete initial stack g) :
    stackExitCounts stack f = stackExitCounts stack g := by
  rw [completeLegalStack_counts_unique initial stack lf lg cf cg]

/-- A stack read at departure n uses initial-next-slot+n, with slot multiplicity
retained. Complete firing counts determine final next-slot residues. -/
def orderedStack {V Exit : Type*} (slots : V → ℕ)
    (positive : ∀ v, 0 < slots v)
    (successor : (v : V) → Fin (slots v) → Sum V Exit)
    (R : (v : V) → Fin (slots v)) (v : V) (n : ℕ) : Sum V Exit :=
  successor v ⟨((R v).val + n) % slots v, Nat.mod_lt _ (positive v)⟩

def finalOrderedRotors {V : Type*} (slots : V → ℕ)
    (positive : ∀ v, 0 < slots v) (R : (v : V) → Fin (slots v))
    (f : V → ℕ) : (v : V) → Fin (slots v) :=
  fun v => ⟨((R v).val + f v) % slots v, Nat.mod_lt _ (positive v)⟩

theorem equalFirings_finalRotors {V : Type*} (slots : V → ℕ)
    (positive : ∀ v, 0 < slots v) (R : (v : V) → Fin (slots v))
    {f g : V → ℕ} (hfg : f = g) :
    finalOrderedRotors slots positive R f = finalOrderedRotors slots positive R g := by
  rw [hfg]

inductive UpperInternal (k : ℕ) where
  | a : Fin k → UpperInternal k
  | b : Fin (k - 1) → UpperInternal k
  | c : Fin (k - 2) → UpperInternal k
  deriving DecidableEq, Fintype

def UpperInternal.vertex {k : ℕ} : UpperInternal k → UpperVertex k
  | .a i => .a i
  | .b i => .b i
  | .c i => .c i

def upperInternalSuccessor {k : ℕ} (hk : 3 ≤ k)
    (v : UpperInternal k) (slot : Fin 2) : Sum (UpperInternal k) NamedOutput :=
  match upperSuccessor hk v.vertex slot with
  | .boundary o => .inr o
  | .a i => .inl (.a i)
  | .b i => .inl (.b i)
  | .c i => .inl (.c i)

def upperOrderedStack {k : ℕ} (hk : 3 ≤ k) (R : UpperRotors k) :
    UpperInternal k → ℕ → Sum (UpperInternal k) NamedOutput :=
  orderedStack (fun _ => 2) (fun _ => by decide) (upperInternalSuccessor hk)
    (fun v => R v.vertex)

/-- External chips only. An internal feedback arrival is counted by
stackIncoming, and must not be inserted again in this initial configuration. -/
def upperExternalChips {k : ℕ} (hk : 3 ≤ k) (inputs : List InputPort)
    (v : UpperInternal k) : ℕ :=
  (if v = .a ⟨k - 1, by omega⟩ then inputs.count .E else 0) +
  (if v = .a ⟨k - 2, by omega⟩ then inputs.count .F else 0)

def upperFinalInternalRotors {k : ℕ} (R : UpperRotors k) (f : UpperInternal k → ℕ) :
    UpperInternal k → Fin 2 :=
  finalOrderedRotors (fun _ => 2) (fun _ => by decide) (fun v => R v.vertex) f

def upperStackNamedCounts {k : ℕ} (hk : 3 ≤ k) (R : UpperRotors k)
    (f : UpperInternal k → ℕ) : NamedCounts :=
  ⟨stackExitCounts (upperOrderedStack hk R) f .a0,
    stackExitCounts (upperOrderedStack hk R) f .b0,
    stackExitCounts (upperOrderedStack hk R) f .c0⟩

/-- OPEN OP-UPPER-STACK-EXTRACTION. The concrete sequential traces must
provide a common legal complete firing vector for the aggregate external
chip configuration. Sequential injection is legal against the aggregate
configuration because all not-yet-injected chips may wait at their ports.
The remaining clauses are primitive trace accounting: local slot advance,
no boundary firing, and named incoming boundary-arc counts. No abelian
conclusion, decoder, compression, or ordered-output invariance is a field. -/
def UpperSequentialStackExtractionObligation (k : ℕ) (hk : 3 ≤ k) : Prop :=
  ∀ (R R' : UpperRotors k) (inputs : List InputPort) (outputs : List NamedOutput),
    SequentialUpperRouting hk R inputs R' outputs →
    ∃ f : UpperInternal k → ℕ,
      LegalStackPrefix (upperExternalChips hk inputs) (upperOrderedStack hk R) f ∧
      StackComplete (upperExternalChips hk inputs) (upperOrderedStack hk R) f ∧
      (∀ v, R' v.vertex = upperFinalInternalRotors R f v) ∧
      (∀ o, R' (.boundary o) = R (.boundary o)) ∧
      outputMultiplicities outputs = upperStackNamedCounts hk R f

theorem upperExternalChips_of_equal_multiplicities {k : ℕ} (hk : 3 ≤ k)
    {inputs inputs' : List InputPort}
    (same : inputMultiplicities inputs = inputMultiplicities inputs') :
    upperExternalChips hk inputs = upperExternalChips hk inputs' := by
  have sameE := congrArg Batch.N same
  have sameF := congrArg Batch.M same
  simp only [inputMultiplicities] at sameE sameF
  funext v
  simp [upperExternalChips, sameE, sameF]

/-- Conditional concrete abelian consequence of the independently proved
finite-stack least action and the explicitly unfinished trace extraction.
The ordered terminal lists may differ; only their multiplicities are equated. -/
theorem upperBatchAbelian_of_stackExtraction {k : ℕ} (hk : 3 ≤ k)
    (extraction : UpperSequentialStackExtractionObligation k hk)
    {R R₁ R₂ : UpperRotors k} {inputs₁ inputs₂ : List InputPort}
    {outputs₁ outputs₂ : List NamedOutput}
    (routing₁ : SequentialUpperRouting hk R inputs₁ R₁ outputs₁)
    (routing₂ : SequentialUpperRouting hk R inputs₂ R₂ outputs₂)
    (sameInputs : inputMultiplicities inputs₁ = inputMultiplicities inputs₂) :
    R₁ = R₂ ∧ outputMultiplicities outputs₁ = outputMultiplicities outputs₂ := by
  obtain ⟨f, lf, cf, rf, bf, of⟩ := extraction R R₁ inputs₁ outputs₁ routing₁
  obtain ⟨g, lg, cg, rg, bg, og⟩ := extraction R R₂ inputs₂ outputs₂ routing₂
  have initial := upperExternalChips_of_equal_multiplicities hk sameInputs
  rw [← initial] at lg cg
  have sameFirings := completeLegalStack_counts_unique
    (upperExternalChips hk inputs₁) (upperOrderedStack hk R) lf lg cf cg
  subst g
  constructor
  · funext v
    cases v with
    | boundary o => exact (bf o).trans (bg o).symm
    | a i => exact (rf (.a i)).trans (rg (.a i)).symm
    | b i => exact (rf (.b i)).trans (rg (.b i)).symm
    | c i => exact (rf (.c i)).trans (rg (.c i)).symm
  · exact of.trans og.symm

/-! Active-line finite-segment potential. Endpoint coordinates are 0 and k+1;
True means next-right. Balance is proved for actual atomic moves and finite
traces, before threshold preservation is used. -/
abbrev LineRotors (k : ℕ) := Fin k → Bool

structure LineRunningState (k : ℕ) where
  position : Fin (k + 2)
  rotors : LineRotors k

def lineRightCount {k : ℕ} (R : LineRotors k) : ℤ :=
  ∑ i, if R i then (1 : ℤ) else 0

def linePotential {k : ℕ} (s : LineRunningState k) : ℤ :=
  (s.position.val : ℤ) + lineRightCount s.rotors

def lineDeparture {k : ℕ} (s : LineRunningState k) (i : Fin k) : LineRunningState k :=
  ⟨if s.rotors i then ⟨i.val + 2, by omega⟩ else ⟨i.val, by omega⟩,
    Function.update s.rotors i (! s.rotors i)⟩

def LineStep {k : ℕ} (s t : LineRunningState k) : Prop :=
  ∃ i : Fin k, s.position.val = i.val + 1 ∧ t = lineDeparture s i

theorem lineRightCount_toggle {k : ℕ} (R : LineRotors k) (i : Fin k) :
    lineRightCount (Function.update R i (! R i)) =
      lineRightCount R + if R i then (-1 : ℤ) else 1 := by
  have pointwise : ∀ j : Fin k,
      (if (Function.update R i (! R i)) j then (1 : ℤ) else 0) =
      (if R j then (1 : ℤ) else 0) +
        (if j = i then (if R i then (-1 : ℤ) else 1) else 0) := by
    intro j
    by_cases hji : j = i
    · subst j; cases hRi : R i <;> simp [hRi]
    · simp [Function.update, hji]
  unfold lineRightCount
  simp_rw [pointwise]
  rw [Finset.sum_add_distrib]
  simp

theorem lineStep_potential {k : ℕ} {s t : LineRunningState k}
    (step : LineStep s t) : linePotential t = linePotential s := by
  obtain ⟨i, position, rfl⟩ := step
  have change := lineRightCount_toggle s.rotors i
  cases hRi : s.rotors i <;>
    simp_all [linePotential, lineDeparture] <;> omega

inductive LineTrace {k : ℕ} : LineRunningState k → LineRunningState k → ℕ → Prop where
  | nil (s) : LineTrace s s 0
  | cons {s t u n} : LineStep s t → LineTrace t u n → LineTrace s u (n + 1)

theorem lineTrace_potential {k : ℕ} {s t : LineRunningState k} {cost : ℕ}
    (trace : LineTrace s t cost) : linePotential t = linePotential s := by
  induction trace with
  | nil => rfl
  | cons step rest ih => exact ih.trans (lineStep_potential step)

def thresholdRotors {k : ℕ} (h : Fin (k + 1)) : LineRotors k :=
  fun i => decide (i.val < h.val)

theorem thresholdRotors_rightCount {k : ℕ} (h : Fin (k + 1)) :
    lineRightCount (thresholdRotors h) = (h.val : ℤ) := by
  induction k with
  | zero => simp [lineRightCount, thresholdRotors] <;> omega
  | succ k ih =>
    by_cases hh : h.val = 0
    · simp [lineRightCount, thresholdRotors, hh]
    · have hb := h.isLt
      let h₀ : Fin (k + 1) := ⟨h.val - 1, by omega⟩
      have tail : ∀ i : Fin k,
          thresholdRotors h i.succ = thresholdRotors h₀ i := by
        intro i
        simp only [thresholdRotors, Fin.val_succ]
        simp only [decide_eq_decide]
        dsimp [h₀]
        omega
      have head : thresholdRotors h 0 = true := by
        simp only [thresholdRotors, Fin.val_zero]
        exact decide_eq_true (Nat.pos_of_ne_zero hh)
      have split := Fin.sum_univ_succ
        (fun i : Fin (k + 1) => if thresholdRotors h i then (1 : ℤ) else 0)
      unfold lineRightCount
      rw [split, head]
      simp_rw [tail]
      change 1 + lineRightCount (thresholdRotors h₀) = (h.val : ℤ)
      rw [ih h₀]
      dsimp [h₀]
      omega

/-- e is a one-particle exit indicator, not a batch or feedback count. -/
def CompleteLineSegment {k : ℕ} (R R' : LineRotors k)
    (j : Fin k) (e : Bool) : Prop :=
  ∃ cost, LineTrace ⟨⟨j.val + 1, by omega⟩, R⟩
    ⟨if e then ⟨k + 1, by omega⟩ else ⟨0, by omega⟩, R'⟩ cost

theorem completeLineSegment_balance {k : ℕ} {R R' : LineRotors k}
    {j : Fin k} {e : Bool} (segment : CompleteLineSegment R R' j e) :
    (j.val + 1 : ℤ) + lineRightCount R =
      lineRightCount R' + (k + 1 : ℤ) * (if e then 1 else 0) := by
  obtain ⟨cost, trace⟩ := segment
  have invariant := lineTrace_potential trace
  cases e <;> simp_all [linePotential] <;> omega

theorem thresholdLineSegment_balance {k : ℕ} {h h' : Fin (k + 1)}
    {j : Fin k} {e : Bool}
    (segment : CompleteLineSegment (thresholdRotors h) (thresholdRotors h') j e) :
    h.val + (j.val + 1) = h'.val + (k + 1) * (if e then 1 else 0) := by
  have balance := completeLineSegment_balance segment
  rw [thresholdRotors_rightCount, thresholdRotors_rightCount] at balance
  cases e <;> simp_all <;> omega

theorem thresholdLineSegment_transfer {k : ℕ} {h h' : Fin (k + 1)}
    {j : Fin k} {e : Bool}
    (segment : CompleteLineSegment (thresholdRotors h) (thresholdRotors h') j e) :
    h'.val = (h.val + (j.val + 1)) % (k + 1) ∧
      (if e then 1 else 0) = (h.val + (j.val + 1)) / (k + 1) := by
  have balance := thresholdLineSegment_balance segment
  have hh' := h'.isLt
  have positive : 0 < k + 1 := by omega
  cases e
  · simp only [Bool.false_eq_true, if_false, Nat.mul_zero, Nat.add_zero] at balance ⊢
    constructor
    · simp [balance, Nat.mod_eq_of_lt hh']
    · simp [balance, Nat.div_eq_of_lt hh']
  · simp only [if_true, Nat.mul_one] at balance ⊢
    constructor
    · simp [balance, Nat.add_mod, Nat.mod_eq_of_lt hh']
    · simp [balance, Nat.add_div, Nat.div_eq_of_lt hh',
        Nat.mod_eq_of_lt hh', Nat.ne_of_gt positive]

/-- OPEN OP-THRESHOLD. Classical chip-addition preservation of acyclic
LAST-edge states must be adapted to NEXT-edge threshold vectors. It supplies
only threshold preservation/existence, not the already proved balance. -/
def ClassicalLineThresholdPreservationObligation (k : ℕ) : Prop :=
  ∀ (h : Fin (k + 1)) (j : Fin k),
    (∃ R' e, CompleteLineSegment (thresholdRotors h) R' j e) ∧
    ∀ R' e, CompleteLineSegment (thresholdRotors h) R' j e →
      ∃ h' : Fin (k + 1), R' = thresholdRotors h'

theorem lineTransfer_of_thresholdPreservation {k : ℕ}
    (preservation : ClassicalLineThresholdPreservationObligation k)
    (h : Fin (k + 1)) (j : Fin k) :
    ∃ h' e, CompleteLineSegment (thresholdRotors h) (thresholdRotors h') j e ∧
      h'.val = (h.val + (j.val + 1)) % (k + 1) ∧
      (if e then 1 else 0) = (h.val + (j.val + 1)) / (k + 1) := by
  obtain ⟨R', e, segment⟩ := (preservation h j).1
  obtain ⟨h', rfl⟩ := (preservation h j).2 R' e segment
  exact ⟨h', e, segment, thresholdLineSegment_transfer segment⟩

/-- Telescope over any list of complete threshold segments. Each entry is
an active-line coordinate, including internal feedback re-entry at coordinate
k when present; this list is not the external E/F word. -/
inductive CompleteLineCollection {k : ℕ} :
    Fin (k + 1) → List (Fin k × Bool) → Fin (k + 1) → Prop where
  | nil (h) : CompleteLineCollection h [] h
  | cons {h h₁ h₂ j e entries} :
      CompleteLineSegment (thresholdRotors h) (thresholdRotors h₁) j e →
      CompleteLineCollection h₁ entries h₂ →
      CompleteLineCollection h ((j, e) :: entries) h₂

def lineEntrySum {k : ℕ} (entries : List (Fin k × Bool)) : ℕ :=
  (entries.map (fun entry => entry.1.val + 1)).sum

def lineRightExits {k : ℕ} (entries : List (Fin k × Bool)) : ℕ :=
  (entries.map (fun entry => if entry.2 then 1 else 0)).sum

theorem completeLineCollection_balance {k : ℕ}
    {h h' : Fin (k + 1)} {entries : List (Fin k × Bool)}
    (collection : CompleteLineCollection h entries h') :
    h.val + lineEntrySum entries = h'.val + (k + 1) * lineRightExits entries := by
  induction collection with
  | nil => simp [lineEntrySum, lineRightExits]
  | cons segment rest ih =>
    have one := thresholdLineSegment_balance segment
    simp only [lineEntrySum, lineRightExits, List.map_cons, List.sum_cons] at *
    rw [Nat.mul_add]
    omega

end Partials.Arrival
