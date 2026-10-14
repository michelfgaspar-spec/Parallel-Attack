import Partials.Arrival.Passive
import Partials.Arrival.Coupling

/-! Concrete cyclic two-copy network and the exact unfinished decoder duty.
This graph is independent of the two-sink lower wrapper. Ordered slots and
multi-particle legal steps are explicit; no desired decoder equality is a field
of the execution relation. Source only, uncompiled. -/
namespace Partials.Arrival.Cyclic

inductive Copy where
  | A | B
  deriving DecidableEq

instance : Fintype Copy where
  elems := {.A, .B}
  complete := by intro c; cases c <;> simp

def Copy.other : Copy → Copy
  | .A => .B
  | .B => .A

theorem Copy.other_other (c : Copy) : c.other.other = c := by cases c <;> rfl

inductive GlobalTerminal where
  | a0 | c0
  deriving DecidableEq

instance : Fintype GlobalTerminal where
  elems := {.a0, .c0}
  complete := by intro o; cases o <;> simp

instance upperBoundaryDecidable (k : ℕ) : DecidablePred (@upperIsBoundary k) := by
  intro v
  cases v <;> dsimp [upperIsBoundary] <;> infer_instance

abbrev Internal (k : ℕ) := {v : UpperVertex k // ¬ upperIsBoundary v}

inductive Vertex (k : ℕ) where
  | internal (copy : Copy) (v : Internal k)
  | absorbing (copy : Copy) (o : GlobalTerminal)
  deriving DecidableEq, Fintype

def IsAbsorbing : Vertex k → Prop
  | .absorbing _ _ => True
  | .internal _ _ => False

def top (hk : 3 ≤ k) (copy : Copy) : Vertex k :=
  .internal copy ⟨.a ⟨k - 1, by omega⟩, by simp [upperIsBoundary]⟩

def externalF (hk : 3 ≤ k) (copy : Copy) : Vertex k :=
  .internal copy ⟨.a ⟨k - 2, by omega⟩, by simp [upperIsBoundary]⟩

/-- A local b0 is a cross transfer to the other copy's ak. -/
def liftUpper (hk : 3 ≤ k) (copy : Copy) : UpperVertex k → Vertex k
  | .a i => .internal copy ⟨.a i, by simp [upperIsBoundary]⟩
  | .b i => .internal copy ⟨.b i, by simp [upperIsBoundary]⟩
  | .c i => .internal copy ⟨.c i, by simp [upperIsBoundary]⟩
  | .boundary .a0 => .absorbing copy .a0
  | .boundary .b0 => top hk copy.other
  | .boundary .c0 => .absorbing copy .c0

def successor (hk : 3 ≤ k) : Vertex k → Fin 2 → Vertex k
  | .internal copy v, slot => liftUpper hk copy (upperSuccessor hk v.val slot)
  | .absorbing copy o, _ => .absorbing copy o

def network (hk : 3 ≤ k) : Partials.Interface.OrderedRotorNetwork (Vertex k) where
  slotCount := fun _ => 2
  slots_positive := fun _ => by decide
  successor := successor hk
  sink := IsAbsorbing
  sink_fixed := by
    intro v hv slot
    cases v <;> simp_all [IsAbsorbing, successor]

theorem local_b0_is_cross_transfer (hk : 3 ≤ k) (copy : Copy) :
    liftUpper hk copy (.boundary .b0) = top hk copy.other := rfl

theorem four_global_absorbers : Fintype.card (Copy × GlobalTerminal) = 4 := by
  decide

def rotorsFromStates (states : Copy → InterfaceState k) : Vertex k → Fin 2
  | .absorbing _ _ => ⟨0, by decide⟩
  | .internal copy v => match v with
    | ⟨.a i, _⟩ => if i.val < (states copy).h.val then ⟨1, by decide⟩ else ⟨0, by decide⟩
    | ⟨.b i, _⟩ => passiveOrbitState k (states copy).r (.b i)
    | ⟨.c i, _⟩ => passiveOrbitState k (states copy).r (.c i)
    | ⟨.boundary _, h⟩ => False.elim (h trivial)

def initialStates (k zA zB : ℕ) : Copy → InterfaceState k
  | .A => decodedInterfaceState k zA ⟨0, 0⟩
  | .B => decodedInterfaceState k zB ⟨0, 0⟩

structure Configuration (k : ℕ) where
  chips : Vertex k → ℕ
  rotors : Vertex k → Fin 2

structure Event (k : ℕ) where
  «from» : Vertex k
  «to» : Vertex k
  slot : Fin 2

def initialChips (hk : 3 ≤ k) (MA MB : ℕ) (v : Vertex k) : ℕ :=
  (if v = externalF hk .A then MA else 0) +
    (if v = externalF hk .B then MB else 0)

def initialConfiguration (hk : 3 ≤ k) (zA zB MA MB : ℕ) : Configuration k :=
  ⟨initialChips hk MA MB, rotorsFromStates (initialStates k zA zB)⟩

def fire (hk : 3 ≤ k) (C : Configuration k) (v : Vertex k) : Configuration k :=
  let w := successor hk v (C.rotors v)
  let removed := Function.update C.chips v (C.chips v - 1)
  ⟨Function.update removed w (removed w + 1),
    Function.update C.rotors v (nextBinarySlot (C.rotors v))⟩

def departure (hk : 3 ≤ k) (C : Configuration k) (v : Vertex k) : Event k :=
  ⟨v, successor hk v (C.rotors v), C.rotors v⟩

inductive Trace (hk : 3 ≤ k) :
    Configuration k → Configuration k → List (Event k) → Prop where
  | nil (C) : Trace hk C C []
  | cons {C D events} (v : Vertex k) : ¬ IsAbsorbing v → 0 < C.chips v →
      Trace hk (fire hk C v) D events →
      Trace hk C D (departure hk C v :: events)

def Complete (hk : 3 ≤ k) (zA zB MA MB : ℕ)
    (D : Configuration k) (events : List (Event k)) : Prop :=
  Trace hk (initialConfiguration hk zA zB MA MB) D events ∧
    ∀ v, ¬ IsAbsorbing v → D.chips v = 0

def absorbingCounts (D : Configuration k) : FourAbsorbingCounts :=
  ⟨D.chips (.absorbing .A .a0), D.chips (.absorbing .A .c0),
    D.chips (.absorbing .B .a0), D.chips (.absorbing .B .c0)⟩

def fromCopy : Vertex k → Option Copy
  | .internal c _ => some c
  | .absorbing _ _ => none

/-- The same-copy b1→ak feedback is not a cross transfer. -/
def crossEvents (hk : 3 ≤ k) (copy : Copy) (events : List (Event k)) : ℕ :=
  (events.filter (fun e => decide
    (fromCopy e.from = some copy ∧ e.to = top hk copy.other))).length

def finalStates (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB : ℕ) :
    Copy → InterfaceState k :=
  let states := couplingFinalStates k hk zA zB hA hB MA MB
  fun c => match c with | .A => states.1 | .B => states.2

/-- OPEN: legal alternating waves, local cut extraction and concrete
stabilization/abelian correspondence must prove this exact graph-level target.
The proposition is not an axiom, a witness field, or an exported proof. -/
def DecoderDuty (k : ℕ) (hk : 3 ≤ k) (zA zB : ℕ)
    (hA : zA < period k) (hB : zB < period k) (MA MB : ℕ) : Prop :=
  (∃ D events, Complete hk zA zB MA MB D events) ∧
  ∀ D events, Complete hk zA zB MA MB D events →
    crossEvents hk .B events = couplingFirst k hk zA zB hA hB MA MB ∧
    crossEvents hk .A events =
      crossCount k zA (couplingFirst k hk zA zB hA hB MA MB) MA ∧
    absorbingCounts D = couplingAbsorbingCounts k hk zA zB hA hB MA MB ∧
    D.rotors = rotorsFromStates (finalStates k hk zA zB hA hB MA MB)

/-! P1 checked auxiliary scope: the zero-chip physical run has no legal firing.
This discharges the physical selection in the phantom-root example without
assuming the universal decoder duty or replaying a diagnostic program. -/

theorem zeroBatch_trace_trivial {k : ℕ} {hk : 3 ≤ k} {zA zB : ℕ}
    {D : Configuration k} {events : List (Event k)}
    (trace : Trace hk (initialConfiguration hk zA zB 0 0) D events) :
    D = initialConfiguration hk zA zB 0 0 ∧ events = [] := by
  cases trace with
  | nil => exact ⟨rfl, rfl⟩
  | cons v nonabsorbing positive rest =>
    simp [initialConfiguration, initialChips] at positive

theorem zeroBatch_complete_exists (hk : 3 ≤ k) (zA zB : ℕ) :
    Complete hk zA zB 0 0 (initialConfiguration hk zA zB 0 0) [] := by
  refine ⟨Trace.nil _, ?_⟩
  intro v nonabsorbing
  simp [initialConfiguration, initialChips]

theorem zeroBatch_complete_counts {k : ℕ} {hk : 3 ≤ k} {zA zB : ℕ}
    {D : Configuration k} {events : List (Event k)}
    (run : Complete hk zA zB 0 0 D events) :
    crossEvents hk .B events = 0 ∧ crossEvents hk .A events = 0 ∧
    absorbingCounts D = ⟨0, 0, 0, 0⟩ ∧
    D.rotors = (initialConfiguration hk zA zB 0 0).rotors := by
  obtain ⟨rfl, rfl⟩ := zeroBatch_trace_trivial run.1
  simp [crossEvents, absorbingCounts, initialConfiguration, initialChips]

theorem phantom_physical_zero_crossings :
    (∃ D events, Complete (by decide : 3 ≤ 3) 2 2 0 0 D events) ∧
    ∀ D events, Complete (by decide : 3 ≤ 3) 2 2 0 0 D events →
      crossEvents (by decide : 3 ≤ 3) .B events = 0 ∧
      crossEvents (by decide : 3 ≤ 3) .A events = 0 := by
  constructor
  · exact ⟨_, [], zeroBatch_complete_exists (by decide) 2 2⟩
  · intro D events run
    have counts := zeroBatch_complete_counts run
    exact ⟨counts.1, counts.2.1⟩

end Partials.Arrival.Cyclic
