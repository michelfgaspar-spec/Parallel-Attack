import Partials.Arrival.Passive

/-! R3/q0002, uncompiled. Source: arrival/main.tex prop:compression.
The graph has distinct named boundaries and four ORDERED slots at p, even
when destinations repeat. Correspondence is on the stated complete-traversal
orbit. Macro traces do not claim to preserve intermediate passive positions,
atomic step cost, or physical wrapper shortest-distance levels. -/
namespace Partials.Arrival

inductive CompressedVertex (k : ℕ) where
  | boundary : NamedOutput → CompressedVertex k
  | a : Fin k → CompressedVertex k
  | p : CompressedVertex k
  deriving DecidableEq, Fintype

def compressedSlotCount {k : ℕ} : CompressedVertex k → ℕ
  | .p => 4
  | _ => 2

def compressedIsBoundary {k : ℕ} : CompressedVertex k → Prop
  | .boundary _ => True
  | _ => False

def compressedPassiveDestination {k : ℕ} (hk : 3 ≤ k) :
    PassiveDestination → CompressedVertex k
  | .feedback => .a ⟨k - 1, by omega⟩
  | .b0 => .boundary .b0
  | .c0 => .boundary .c0

def compressedSuccessor {k : ℕ} (hk : 3 ≤ k) :
    (v : CompressedVertex k) → Fin (compressedSlotCount v) → CompressedVertex k
  | .boundary o, _ => .boundary o
  | .p, slot => compressedPassiveDestination hk (passiveWord k slot)
  | .a i, slot =>
    if slot.val = 0 then
      if hi : i.val = 0 then .boundary .a0
      else .a ⟨i.val - 1, by omega⟩
    else if hi : i.val + 1 < k then .a ⟨i.val + 1, hi⟩
    else .p

def compressedNetwork {k : ℕ} (hk : 3 ≤ k) :
    Partials.Interface.OrderedRotorNetwork (CompressedVertex k) where
  slotCount := compressedSlotCount
  slots_positive := by intro v; cases v <;> simp [compressedSlotCount]
  successor := compressedSuccessor hk
  sink := compressedIsBoundary
  sink_fixed := by
    intro v hv slot
    cases v <;> simp_all [compressedIsBoundary, compressedSuccessor]

theorem compressedNetwork_fourSlots {k : ℕ} (hk : 3 ≤ k) :
    Partials.Interface.IsFourSlotRotorAt (compressedNetwork hk) .p := rfl

theorem compressedRepeatedSlots_odd {k : ℕ} (hk : 3 ≤ k) (odd : k % 2 = 1) :
    compressedSuccessor hk .p ⟨2, by norm_num [compressedSlotCount]⟩ = .boundary .c0 ∧
    compressedSuccessor hk .p ⟨3, by norm_num [compressedSlotCount]⟩ = .boundary .c0 ∧
    (⟨2, by norm_num [compressedSlotCount]⟩ : Fin 4) ≠ ⟨3, by norm_num [compressedSlotCount]⟩ := by
  simp [compressedSuccessor, compressedPassiveDestination, passiveWord, odd]

theorem compressedRepeatedSlots_even {k : ℕ} (hk : 3 ≤ k) (even : k % 2 ≠ 1) :
    compressedSuccessor hk .p ⟨1, by norm_num [compressedSlotCount]⟩ = .boundary .c0 ∧
    compressedSuccessor hk .p ⟨3, by norm_num [compressedSlotCount]⟩ = .boundary .c0 ∧
    (⟨1, by norm_num [compressedSlotCount]⟩ : Fin 4) ≠ ⟨3, by norm_num [compressedSlotCount]⟩ := by
  simp [compressedSuccessor, compressedPassiveDestination, passiveWord, even]

/-- These are macro_trace positions; `.passive` stands for a complete traversal
starting at b_(k-1), not an intermediate passive vertex. -/
inductive OrbitMacroPosition (k : ℕ) where
  | boundary : NamedOutput → OrbitMacroPosition k
  | a : Fin k → OrbitMacroPosition k
  | passive : OrbitMacroPosition k
  deriving DecidableEq, Fintype

@[ext] structure OrbitMacroState (k : ℕ) where
  position : OrbitMacroPosition k
  active : Fin k → Fin 2
  phase : Fin 4

def macroPassiveDestination {k : ℕ} (hk : 3 ≤ k) :
    PassiveDestination → OrbitMacroPosition k
  | .feedback => .a ⟨k - 1, by omega⟩
  | .b0 => .boundary .b0
  | .c0 => .boundary .c0

def activeMacroDeparture {k : ℕ} (hk : 3 ≤ k)
    (s : OrbitMacroState k) (i : Fin k) : OrbitMacroState k :=
  ⟨if (s.active i).val = 0 then
      if hi : i.val = 0 then .boundary .a0 else .a ⟨i.val - 1, by omega⟩
    else if hi : i.val + 1 < k then .a ⟨i.val + 1, hi⟩ else .passive,
    Function.update s.active i (nextBinarySlot (s.active i)), s.phase⟩

def compressedMacroDeparture {k : ℕ} (hk : 3 ≤ k)
    (s : OrbitMacroState k) : OrbitMacroState k :=
  match s.position with
  | .boundary _ => s
  | .a i => activeMacroDeparture hk s i
  | .passive =>
    ⟨macroPassiveDestination hk (passiveWord k s.phase), s.active, nextFourSlot s.phase⟩

/-- The original macro_trace rule uses the physical cut-passive traversal relation,
not the symbolic output word. Endpoint vectors lie on the four-phase orbit. -/
def OriginalOrbitMacroStep {k : ℕ} (hk : 3 ≤ k)
    (s t : OrbitMacroState k) : Prop :=
  match s.position with
  | .boundary _ => False
  | .a i => t = activeMacroDeparture hk s i
  | .passive => t.active = s.active ∧
    ∃ destination, CompletePassiveTraversal hk (passiveOrbitState k s.phase)
      (passiveOrbitState k t.phase) destination ∧
      t.position = macroPassiveDestination hk destination

def CompressedOrbitMacroStep {k : ℕ} (hk : 3 ≤ k)
    (s t : OrbitMacroState k) : Prop :=
  (match s.position with | .boundary _ => False | _ => True) ∧
    t = compressedMacroDeparture hk s

theorem orbitMacroStep_iff_of_realization {k : ℕ} (hk : 3 ≤ k)
    (realization : PassiveOrbitRealizationObligation k hk)
    (s t : OrbitMacroState k) :
    OriginalOrbitMacroStep hk s t ↔ CompressedOrbitMacroStep hk s t := by
  cases position : s.position with
  | boundary o => simp [OriginalOrbitMacroStep, CompressedOrbitMacroStep, position]
  | a i => simp [OriginalOrbitMacroStep, CompressedOrbitMacroStep,
      compressedMacroDeparture, position]
  | passive =>
    simp only [OriginalOrbitMacroStep, CompressedOrbitMacroStep,
      compressedMacroDeparture, position, true_and]
    constructor
    · rintro ⟨active, destination, traversal, terminal⟩
      obtain ⟨vector, output⟩ := (realization s.phase _ destination).mp traversal
      have phase := passiveOrbitState_injective hk vector
      apply OrbitMacroState.ext
      · simpa [output] using terminal
      · exact active
      · exact phase
    · intro same
      subst t
      exact ⟨rfl, passiveWord k s.phase,
        passiveTraversal_of_orbitRealization hk realization s.phase, rfl⟩

def compressedMacroPosition {k : ℕ} : OrbitMacroPosition k → CompressedVertex k
  | .boundary o => .boundary o
  | .a i => .a i
  | .passive => .p

def compressedMacroRotor {k : ℕ} (s : OrbitMacroState k) :
    (v : CompressedVertex k) → Fin (compressedSlotCount v)
  | .boundary _ => ⟨0, by norm_num [compressedSlotCount]⟩
  | .a i => s.active i
  | .p => s.phase

theorem compressedMacroDeparture_position {k : ℕ} (hk : 3 ≤ k)
    (s : OrbitMacroState k) :
    compressedMacroPosition (compressedMacroDeparture hk s).position =
      compressedSuccessor hk (compressedMacroPosition s.position)
        (compressedMacroRotor s (compressedMacroPosition s.position)) := by
  cases position : s.position with
  | boundary o => simp [compressedMacroPosition, compressedMacroDeparture,
      compressedSuccessor, compressedMacroRotor, position]
  | a i =>
    by_cases slot : (s.active i).val = 0
    · by_cases first : i.val = 0 <;>
        simp [compressedMacroPosition, compressedMacroDeparture, activeMacroDeparture,
          compressedSuccessor, compressedMacroRotor, position, slot, first]
    · by_cases right : i.val + 1 < k <;>
        simp [compressedMacroPosition, compressedMacroDeparture, activeMacroDeparture,
          compressedSuccessor, compressedMacroRotor, position, slot, right]
  | passive =>
    cases destination : passiveWord k s.phase <;>
      simp [compressedMacroPosition, compressedMacroDeparture, compressedSuccessor,
        compressedMacroRotor, position, macroPassiveDestination,
        compressedPassiveDestination, destination]

inductive OrbitMacroTrace {k : ℕ} (step : OrbitMacroState k → OrbitMacroState k → Prop) :
    OrbitMacroState k → OrbitMacroState k → ℕ → Prop where
  | nil (s) : OrbitMacroTrace step s s 0
  | cons {s t u n} : step s t → OrbitMacroTrace step t u n →
      OrbitMacroTrace step s u (n + 1)

theorem orbitMacroTrace_iff_of_realization {k : ℕ} (hk : 3 ≤ k)
    (realization : PassiveOrbitRealizationObligation k hk)
    (s t : OrbitMacroState k) (cost : ℕ) :
    OrbitMacroTrace (OriginalOrbitMacroStep hk) s t cost ↔
      OrbitMacroTrace (CompressedOrbitMacroStep hk) s t cost := by
  constructor
  · intro trace
    induction trace with
    | nil => exact .nil _
    | cons step rest ih =>
      exact .cons ((orbitMacroStep_iff_of_realization hk realization _ _).mp step) ih
  · intro trace
    induction trace with
    | nil => exact .nil _
    | cons step rest ih =>
      exact .cons ((orbitMacroStep_iff_of_realization hk realization _ _).mpr step) ih

def macroInject {k : ℕ} (hk : 3 ≤ k) (s : OrbitMacroState k)
    (input : InputPort) : OrbitMacroState k :=
  { s with position := match input with
    | .E => .a ⟨k - 1, by omega⟩
    | .F => .a ⟨k - 2, by omega⟩ }

def macroTerminal {k : ℕ} (s : OrbitMacroState k)
    (o : NamedOutput) : OrbitMacroState k := { s with position := .boundary o }

def CompleteOrbitMacroExcursion {k : ℕ} (hk : 3 ≤ k)
    (step : OrbitMacroState k → OrbitMacroState k → Prop)
    (s t : OrbitMacroState k) (input : InputPort) (o : NamedOutput) : Prop :=
  ∃ cost, OrbitMacroTrace step (macroInject hk s input) (macroTerminal t o) cost

theorem orbitExcursion_iff_of_realization {k : ℕ} (hk : 3 ≤ k)
    (realization : PassiveOrbitRealizationObligation k hk)
    (s t : OrbitMacroState k) (input : InputPort) (o : NamedOutput) :
    CompleteOrbitMacroExcursion hk (OriginalOrbitMacroStep hk) s t input o ↔
      CompleteOrbitMacroExcursion hk (CompressedOrbitMacroStep hk) s t input o := by
  simp only [CompleteOrbitMacroExcursion]
  exact exists_congr fun cost => orbitMacroTrace_iff_of_realization hk realization _ _ cost

inductive SequentialOrbitMacroRouting {k : ℕ} (hk : 3 ≤ k)
    (step : OrbitMacroState k → OrbitMacroState k → Prop) :
    OrbitMacroState k → List InputPort → OrbitMacroState k → List NamedOutput → Prop where
  | nil (s) : SequentialOrbitMacroRouting hk step s [] s []
  | cons {s s₁ s₂ input inputs o outputs} :
      CompleteOrbitMacroExcursion hk step s s₁ input o →
      SequentialOrbitMacroRouting hk step s₁ inputs s₂ outputs →
      SequentialOrbitMacroRouting hk step s (input :: inputs) s₂ (o :: outputs)

theorem sequentialOrbitCompression_of_realization {k : ℕ} (hk : 3 ≤ k)
    (realization : PassiveOrbitRealizationObligation k hk)
    (s t : OrbitMacroState k) (inputs : List InputPort) (outputs : List NamedOutput) :
    SequentialOrbitMacroRouting hk (OriginalOrbitMacroStep hk) s inputs t outputs ↔
      SequentialOrbitMacroRouting hk (CompressedOrbitMacroStep hk) s inputs t outputs := by
  constructor
  · intro routing
    induction routing with
    | nil => exact .nil _
    | cons excursion rest ih =>
      exact .cons ((orbitExcursion_iff_of_realization hk realization _ _ _ _).mp excursion) ih
  · intro routing
    induction routing with
    | nil => exact .nil _
    | cons excursion rest ih =>
      exact .cons ((orbitExcursion_iff_of_realization hk realization _ _ _ _).mpr excursion) ih

def upperOrbitRotors {k : ℕ} (s : OrbitMacroState k) : UpperRotors k
  | .boundary _ => ⟨0, by norm_num [compressedSlotCount]⟩
  | .a i => s.active i
  | .b i => passiveOrbitState k s.phase (.b i)
  | .c i => passiveOrbitState k s.phase (.c i)

/-- OPEN COMPRESSION-MICRO-LIFT. Upper atomic excursions must be factored
at successive complete passive traversals, and each cut traversal re-glued
at its destination (feedback goes to ak, internally). This duty includes
closure of the COMPLETE passive vector, not arbitrary passive-state coding.
It states trace extraction/expansion, not compressed-decoder correctness. -/
def OrbitUpperExcursionExpansionObligation (k : ℕ) (hk : 3 ≤ k) : Prop :=
  ∀ (s : OrbitMacroState k) (input : InputPort),
    (∀ R' o, CompleteUpperExcursion hk (upperOrbitRotors s) R' input o →
      ∃ t : OrbitMacroState k, R' = upperOrbitRotors t ∧
        CompleteOrbitMacroExcursion hk (OriginalOrbitMacroStep hk) s t input o) ∧
    (∀ (t : OrbitMacroState k) o,
      CompleteOrbitMacroExcursion hk (OriginalOrbitMacroStep hk) s t input o →
        CompleteUpperExcursion hk (upperOrbitRotors s) (upperOrbitRotors t) input o)

theorem concreteUpperCompression_of_bridges {k : ℕ} (hk : 3 ≤ k)
    (realization : PassiveOrbitRealizationObligation k hk)
    (expansion : OrbitUpperExcursionExpansionObligation k hk)
    (s : OrbitMacroState k) (R' : UpperRotors k) (input : InputPort) (o : NamedOutput) :
    CompleteUpperExcursion hk (upperOrbitRotors s) R' input o ↔
      ∃ t : OrbitMacroState k, R' = upperOrbitRotors t ∧
        CompleteOrbitMacroExcursion hk (CompressedOrbitMacroStep hk) s t input o := by
  constructor
  · intro excursion
    obtain ⟨t, rotors, macro_trace⟩ := (expansion s input).1 R' o excursion
    exact ⟨t, rotors, (orbitExcursion_iff_of_realization hk realization _ _ _ _).mp macro_trace⟩
  · rintro ⟨t, rfl, macro_trace⟩
    exact (expansion s input).2 t o
      ((orbitExcursion_iff_of_realization hk realization _ _ _ _).mpr macro_trace)

end Partials.Arrival
