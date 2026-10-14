import Partials.Parity.Compiler
import Partials.Parity.TaggedProfiles
import Partials.Parity.ResourceTargets
import Partials.Parity.TieAssembly
import Partials.Parity.Nonfactorization
import Partials.Parity.HistorySemantics

/-! R7 targets and decoder/admission guards. They are open goals, not
supplied witnesses. All full-function policy domains must respect original
Even agreement; dummy Odd choices are not hidden source-policy inputs. -/
namespace Partials.Parity.Targets

def AdmissionRespectsOriginalPolicy {V Exit : Type*} (A : Arena V Exit)
    (admitted : Set (EvenPolicy A)) : Prop :=
  ∀ σ τ, PolicyAgreement A σ τ → (σ ∈ admitted ↔ τ ∈ admitted)

/-- Decoder guard for an explicit integer zone: each finite outcome priority
comes from its declared level/epsilon, no other outcome or hidden coordinate.
Shape/order/zero/odd-bound predicates are separately required by tag legality. -/
def ExactZoneDecoderDuty {Start Exit : Type*}
    (Z : CompilerSource.TaggedIntegerZone Start Exit (Fin 5))
    (slot : Start → ℕ → Fin 5) : Prop :=
  ∀ x i,
    Z.decode x i = match Z.tag i with
    | .bottom => {Outcome.bottom}
    | .top => {Outcome.top}
    | .finite entries => {out | ∃ k < entries.length, ∃ o e,
        entries[k]? = some (o,e) ∧ 0 ≤ x (slot i k) ∧
        out = Outcome.halt o (4 * (x (slot i k)).toNat + if e then 1 else 0)}

def ExactZoneFormatDuty {Start Exit : Type*}
    (cap : ℕ) (exitOrder : Exit → ℕ)
    (Z : CompilerSource.TaggedIntegerZone Start Exit (Fin 5))
    (slot : Start → ℕ → Fin 5) : Prop :=
  (∀ i entries, Z.tag i = .finite entries →
    entries.Pairwise (fun a b => exitOrder a.1 < exitOrder b.1)) ∧
  (∀ x, x Z.zero = 0 → CompilerSource.DBMSatisfied Z.bounds x →
    ∀ i entries, Z.tag i = .finite entries → ∀ k < entries.length, ∀ o e,
      entries[k]? = some (o,e) → slot i k ≠ Z.zero ∧
        0 ≤ x (slot i k) ∧ x (slot i k) ≤ (cap : ℤ) ∧
        (e = true → 1 ≤ x (slot i k)))

def ExactJointZoneGoal {V Exit Start : Type*} (cap : ℕ) (exitOrder : Exit → ℕ) (A : Arena V Exit)
    (starts : Start → V) (admitted : Set (EvenPolicy A)) : Prop :=
  AdmissionRespectsOriginalPolicy A admitted ∧
  ∃ zones : List (CompilerSource.TaggedIntegerZone Start Exit (Fin 5)),
    (∀ Z ∈ zones, ∃ slot, ExactZoneDecoderDuty Z slot ∧ ExactZoneFormatDuty cap exitOrder Z slot) ∧
    CompilerSource.UnionOf (zones.map CompilerSource.representedByZone) =
      JointAttainable A starts admitted ∧
    ∃ recover : Profile Start Exit → EvenPolicy A,
      CompilerSource.CompilerRecoveryTarget A starts admitted
        (CompilerSource.UnionOf (zones.map CompilerSource.representedByZone)) recover

def JointZoneSemanticDuty {V Exit Start : Type*} (cap : ℕ) (exitOrder : Exit → ℕ) (A : Arena V Exit)
    (starts : Start → V) (admitted : Set (EvenPolicy A)) : Prop :=
  ExactJointZoneGoal cap exitOrder A starts admitted

/-- The fixed marked targets still owe the exact table; physical relation
comparison is across the original47/48 and restricted44/45 arenas. -/
def MarkedPolicyNonfactorizationGoal : Prop :=
  ¬ ∃ f : Fixture.FixtureProfile → Fixture.FixtureProfile,
    ∀ q : Bool, f (Fixture.BooleanForward q) = Fixture.BooleanFeedback q

def PhysicalRelationNonfactorizationGoal : Prop :=
  ¬ ∃ f : Set Fixture.FixtureProfile → Set Fixture.FixtureProfile,
    ∀ restricted : Bool,
      f (Fixture.MarkedForwardClass restricted) = Fixture.MarkedFeedbackClass restricted

def ExactMarkedCollisionDuty : Prop := Fixture.collisionTableTarget ∧
  MarkedPolicyNonfactorizationGoal ∧ PhysicalRelationNonfactorizationGoal

def ExactLiteralTieDuty : Prop := Tie.ExactTieConclusion

/- Uniform algorithm/actual decoder-slot legality, capacity/branch procedures,
resource machine and witness templates remain finer duties in the register.
JointZoneSemanticDuty is a semantic output target, not evidence that a
uniform computable algorithm exists. No target is used as an accepted premise. -/
end Partials.Parity.Targets
