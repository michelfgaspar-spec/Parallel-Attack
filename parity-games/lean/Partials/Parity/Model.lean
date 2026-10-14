import Partials.Shared.Arenas
import Partials.Shared.FiniteCertificates
import Mathlib.Data.Finset.Lattice.Fold

/-! R7 blind Model adapted from retained ParityCoreDraft, SHA
d731533cb032c782f8decfea2da8a9ad770ed9693488079e87364124120ab30f.
No historical source theorem is promoted. Finite physical original policies
are compared on Even choices; dummy values at Odd vertices are ignored. -/

universe u v w

namespace Partials.Parity

/-- The stopped outcomes of `preliminaries.tex`, distinct from tree-label TOP. -/
inductive Outcome (Exit : Type v) where
  | bottom
  | top
  | halt (exit : Exit) (priority : Nat)
  deriving DecidableEq

/-- The paper's subpriority order: odds reversed, then evens increasing. -/
def PriorityLE (a b : Nat) : Prop :=
  (a % 2 = 1 ∧ b % 2 = 1 ∧ b ≤ a) ∨
  (a % 2 = 1 ∧ b % 2 = 0) ∨
  (a % 2 = 0 ∧ b % 2 = 0 ∧ a ≤ b)

/-- Different typed exits are incomparable. -/
def OutcomeLE {Exit : Type v} : Outcome Exit → Outcome Exit → Prop
  | .bottom, _ => True
  | _, .top => True
  | .top, _ => False
  | _, .bottom => False
  | .halt o p, .halt o' q => o = o' ∧ PriorityLE p q

/-- The minimal antichain, defined without assuming raw-set finiteness. -/
def MinRow {Exit : Type v} (raw : Set (Outcome Exit)) : Set (Outcome Exit) :=
  {x | x ∈ raw ∧ ∀ y ∈ raw, OutcomeLE y x → OutcomeLE x y}

/-- The upper/result lift. The source requires rows to be nonempty antichains. -/
def RowLE {Exit : Type v} (r s : Set (Outcome Exit)) : Prop :=
  ∀ x ∈ s, ∃ y ∈ r, OutcomeLE y x

abbrev Profile (Start : Type w) (Exit : Type v) :=
  Start → Set (Outcome Exit)

def ProfileLE {Start : Type w} {Exit : Type v}
    (p q : Profile Start Exit) : Prop :=
  ∀ i, RowLE (p i) (q i)

def StrictProfile {Start : Type w} {Exit : Type v}
    (p q : Profile Start Exit) : Prop :=
  ProfileLE p q ∧ ¬ ProfileLE q p

/-- Original finite arena data. Finiteness is imposed by `[Fintype V]` at the
specific parity-game theorems; keeping the structure independent simplifies
the path and policy definitions. Exits are zero-priority, as in the collision
instance. -/
structure Arena (V : Type u) (Exit : Type v) where
  edge : V → V → Prop
  even : V → Bool
  priority : V → Nat
  exitVertex : Exit → V
  exit_injective : Function.Injective exitVertex
  total : ∀ v, ∃ w, edge v w
  exit_zero : ∀ o, priority (exitVertex o) = 0
  exit_sink : ∀ o w, edge (exitVertex o) w ↔ w = exitVertex o

/-- A complete positional Even policy, including unreachable original
vertices. The function's value at an Odd vertex is ignored. -/
structure EvenPolicy {V : Type u} {Exit : Type v} (A : Arena V Exit) where
  move : V → V
  legal_even : ∀ v, A.even v = true → A.edge v (move v)

/-- Literal product over original Even vertices, including unreachable ones.
The full-function EvenPolicy wrapper has irrelevant values at Odd vertices;
this product is the exact source policy domain. -/
structure OriginalEvenPolicy {V : Type u} {Exit : Type v} (A : Arena V Exit) where
  choose : {v : V // A.even v = true} → V
  legal : ∀ v, A.edge v.val (choose v)

def PolicyAgreement {V : Type u} {Exit : Type v} (A : Arena V Exit)
    (σ τ : EvenPolicy A) : Prop := ∀ v, A.even v = true → σ.move v = τ.move v

def selectedEdge {V : Type u} {Exit : Type v} (A : Arena V Exit)
    (σ : EvenPolicy A) (v w : V) : Prop :=
  A.edge v w ∧ (A.even v = true → w = σ.move v)

/-- A path of the selected graph. Odd retains every original alternative. -/
def Compatible {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A) (ρ : Nat → V) : Prop :=
  ∀ n, A.edge (ρ n) (ρ (n + 1)) ∧
    (A.even (ρ n) = true → ρ (n + 1) = σ.move (ρ n))

/-- First arrival at a global exit; `p` is the ordinary numerical maximum,
including the zero-priority exit. -/
def FirstExit {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (ρ : Nat → V) (n : Nat) (o : Exit) (p : Nat) : Prop :=
  ρ n = A.exitVertex o ∧
  (∀ k < n, ∀ o', ρ k ≠ A.exitVertex o') ∧
  p = (Finset.range (n + 1)).sup (fun k => A.priority (ρ k))

/-- Recurrence is stated over all arbitrarily late visits. This avoids
confusing a transient high priority with the parity of an infinite play. -/
def Recurs {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (ρ : Nat → V) (p : Nat) : Prop :=
  ∀ N, ∃ n, N ≤ n ∧ A.priority (ρ n) = p

def LargestRecurring {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (ρ : Nat → V) (p : Nat) : Prop :=
  Recurs A ρ p ∧ ∀ q, Recurs A ρ q → q ≤ p

def FiniteOutcome {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (ρ : Nat → V) (out : Outcome Exit) : Prop :=
  ∃ n o p, FirstExit A ρ n o p ∧ out = .halt o p

def InfiniteOutcome {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (ρ : Nat → V) (out : Outcome Exit) : Prop :=
  (∀ n o, ρ n ≠ A.exitVertex o) ∧
  ∃ p, LargestRecurring A ρ p ∧
    ((p % 2 = 0 ∧ out = .top) ∨ (p % 2 = 1 ∧ out = .bottom))

/-- All Odd histories are represented by all compatible infinite paths.
Showing equivalence with history strategies is a separate paper-to-code
obligation, especially for finite first-exit traces. -/
def RawOutcomes {V : Type u} {Exit : Type v}
    (A : Arena V Exit) (σ : EvenPolicy A) (start : V) :
    Set (Outcome Exit) :=
  {out | ∃ ρ : Nat → V, ρ 0 = start ∧ Compatible A σ ρ ∧
    (FiniteOutcome A ρ out ∨ InfiniteOutcome A ρ out)}

def PolicyProfile {V : Type u} {Exit : Type v} {Start : Type w}
    (A : Arena V Exit) (σ : EvenPolicy A) (startVertex : Start → V) :
    Profile Start Exit :=
  fun i => MinRow (RawOutcomes A σ (startVertex i))

/-- The exact quantifier order: one original policy realizes all starts. -/
def JointAttainable {V : Type u} {Exit : Type v} {Start : Type w}
    (A : Arena V Exit) (startVertex : Start → V)
    (admitted : Set (EvenPolicy A)) : Set (Profile Start Exit) :=
  {p | ∃ σ ∈ admitted, PolicyProfile A σ startVertex = p}

/-- If two complete policies have the same forward profile and distinct
feedback profiles, no function of the forward profile alone can compute the
feedback profile. This is the logical corollary of P2-FB-COLLISION, not its
finite-instance proof. -/
theorem noPolicyProfileTransfer
    {Policy : Type u} {Start : Type w} {Exit : Type v}
    (forward feedback : Policy → Profile Start Exit)
    (σ₂ σ₃ : Policy)
    (hForward : forward σ₂ = forward σ₃)
    (hFeedback : feedback σ₂ ≠ feedback σ₃) :
    ¬ ∃ transfer : Profile Start Exit → Profile Start Exit,
      ∀ σ, transfer (forward σ) = feedback σ := by
  intro h
  obtain ⟨transfer, htransfer⟩ := h
  apply hFeedback
  calc
    feedback σ₂ = transfer (forward σ₂) := (htransfer σ₂).symm
    _ = transfer (forward σ₃) := congrArg transfer hForward
    _ = feedback σ₃ := htransfer σ₃

def ProfileRelation {Policy : Type u} {Start : Type w} {Exit : Type v}
    (profiles : Policy → Profile Start Exit) (admitted : Set Policy) :
    Set (Profile Start Exit) :=
  {p | ∃ σ ∈ admitted, profiles σ = p}

/-- The relation-level obstruction requires two marked arenas/classes with
the same forward attainable relation and different feedback relations. -/
theorem noRelationOnlyTransfer
    {Policy : Type u} {Start : Type w} {Exit : Type v}
    (forward feedback : Policy → Profile Start Exit)
    (admitted₁ admitted₂ : Set Policy)
    (hForward : ProfileRelation forward admitted₁ =
      ProfileRelation forward admitted₂)
    (hFeedback : ProfileRelation feedback admitted₁ ≠
      ProfileRelation feedback admitted₂) :
    ¬ ∃ transfer : Set (Profile Start Exit) → Set (Profile Start Exit),
      ∀ admitted, transfer (ProfileRelation forward admitted) =
        ProfileRelation feedback admitted := by
  intro h
  obtain ⟨transfer, htransfer⟩ := h
  apply hFeedback
  calc
    ProfileRelation feedback admitted₁ =
        transfer (ProfileRelation forward admitted₁) :=
          (htransfer admitted₁).symm
    _ = transfer (ProfileRelation forward admitted₂) :=
          congrArg transfer hForward
    _ = ProfileRelation feedback admitted₂ := htransfer admitted₂

/-- Exact result-table target of `feedback.tex:518`, before the concrete
47/48-vertex arena and policies are defined in Lean. `Fin 2` indexes
`(i₀,i₁)` and `(s₀,s₁)`. The paper asserts an instance of this proposition,
not an arbitrary theorem over these parameters. -/
def MarkedFeedbackTable
    (f₂ f₃ b₂ b₃ : Profile (Fin 2) (Fin 2)) : Prop :=
  f₂ 0 = ({Outcome.halt (0 : Fin 2) 17} : Set (Outcome (Fin 2))) ∧
  f₂ 1 = ({Outcome.halt (1 : Fin 2) 0} : Set (Outcome (Fin 2))) ∧
  f₃ = f₂ ∧
  b₂ = f₂ ∧
  b₃ 0 = ({Outcome.bottom} : Set (Outcome (Fin 2))) ∧
  b₃ 1 = f₂ 1

end Partials.Parity
