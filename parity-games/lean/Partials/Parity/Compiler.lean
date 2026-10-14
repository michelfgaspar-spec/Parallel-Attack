import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Partials.Parity.ChainEndpoints
import Partials.Parity.ChainReduction
import Partials.Parity.IntegerZones
import Partials.Parity.CapacityTransport

/-! Exact-domain compiler source, compilation.tex P1-D01, D06--D08,
P1-L09--L12, P1-T01 and M1-C01. This module supplies syntax, exact logical
operations and OPEN compiler targets. It does not assert a compiler exists.
Neither a final representation nor cell constancy is silently assumed. -/

namespace Partials.Parity.CompilerSource

inductive PhysicalPort where | inLeft | inRight | outLeft | outRight
  deriving DecidableEq

instance physicalPortFintype : Fintype PhysicalPort where
  elems := {.inLeft, .inRight, .outLeft, .outRight}
  complete := by intro x; cases x <;> simp


/-- Exactly the ten possible named interface occurrences in one layer. -/
inductive LayerInterface where
  | router (identity : Fin 2)
  | port (track : Fin 2) (identity : PhysicalPort)
  deriving DecidableEq, Fintype

/-- A literal local destination, one declared forward target or final exit.
There is deliberately no arbitrary layer index or internal hub destination. -/
inductive DeclaredDestination where
  | local (target : LayerInterface)
  | next (target : LayerInterface)
  | exit (identity : Fin 2)
  deriving DecidableEq, Fintype

/-- Syntactic core of P1-D01. Gadget internal menus/arms are generated from
their indexed original intervals. An additional physical decoder must check
active ports, final-layer destinations and total forced continuations. -/
structure ForwardSpecification where
  layerCount : Nat
  layers_positive : 0 < layerCount
  cap : Nat
  chain : Fin layerCount → Fin 2 → Option IntervalChain
  chain_cap : ∀ layer track C, chain layer track = some C →
    ∀ i, i ≤ C.last → C.upper i ≤ (cap : Int)
  routerEven : Fin layerCount → Fin 2 → Bool
  routerTargets : Fin layerCount → Fin 2 → Finset DeclaredDestination
  router_nonempty : ∀ layer router, (routerTargets layer router).Nonempty
  router_atmosttwo : ∀ layer router, (routerTargets layer router).card ≤ 2
  exitContinuation : Fin layerCount → Fin 2 → ChainExit → DeclaredDestination
  startCount : Nat
  starts_atmosttwo : startCount ≤ 2
  startTarget : Fin startCount → LayerInterface
  exitCount : Nat
  exits_atmosttwo : exitCount ≤ 2

/-- Every common suffix point retains the entire twenty-coordinate tuple.
The four local endpoint variables are shared once per physical chain. -/
inductive BranchVariable where
  | anchor
  | suffix (coordinate : Fin 20)
  | localEndpoint (coordinate : Fin 4)
  | output (coordinate : Fin 20)
  deriving DecidableEq, Fintype

def maximumBranchDimension : Nat := 1 + 20 + 4 + 20

theorem maximumBranchDimension_eq : maximumBranchDimension = 45 := by
  norm_num [maximumBranchDimension]

def maximumInterfaceStarts : Nat := 2 + 2 * 4
def maximumSuffixCoordinates : Nat := 2 * maximumInterfaceStarts
def maximumGlobalCoordinates : Nat := 2 * 2

theorem grammar_dimensions :
    maximumInterfaceStarts = 10 ∧ maximumSuffixCoordinates = 20 ∧
      maximumGlobalCoordinates = 4 := by
  norm_num [maximumInterfaceStarts, maximumSuffixCoordinates,
    maximumGlobalCoordinates]

inductive TagRow (Exit : Type*) where
  | bottom
  | top
  | finite (entries : List (Exit × Bool))

def TagRowLegal {Exit : Type*} (row : TagRow Exit) : Prop :=
  match row with
  | .bottom => True
  | .top => True
  | .finite entries =>
      entries ≠ [] ∧ entries.length ≤ 2 ∧ (entries.map Prod.fst).Nodup

structure TaggedIntegerZone (Start Exit : Type*) (Coordinate : Type*) where
  tag : Start → TagRow Exit
  tag_legal : ∀ i, TagRowLegal (tag i)
  zero : Coordinate
  bounds : DBM Coordinate
  decode : (Coordinate → Int) → Profile Start Exit

def representedByZone {Start Exit Coordinate : Type*}
    (Z : TaggedIntegerZone Start Exit Coordinate) : Set (Profile Start Exit) :=
  {p | ∃ x : Coordinate → Int,
    x Z.zero = 0 ∧ DBMSatisfied Z.bounds x ∧ Z.decode x = p}

def UnionOf {X : Type*} (pieces : List (Set X)) : Set X :=
  {x | ∃ piece ∈ pieces, x ∈ piece}

def ProjectRelation {X Y : Type*} (relation : Set (X × Y)) : Set X :=
  {x | ∃ y, (x, y) ∈ relation}

theorem projected_union_exact {X Y : Type*} (pieces : List (Set (X × Y))) :
    ProjectRelation (UnionOf pieces) = UnionOf (pieces.map ProjectRelation) := by
  ext x
  constructor
  · rintro ⟨y, piece, hpiece, hxy⟩
    exact ⟨ProjectRelation piece, List.mem_map.mpr ⟨piece, hpiece, rfl⟩,
      y, hxy⟩
  · rintro ⟨projected, hprojected, hx⟩
    obtain ⟨piece, hpiece, rfl⟩ := List.mem_map.mp hprojected
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, piece, hpiece, hy⟩

/-- Input-only cells are accepted using an actual integer intersection with
an explicitly constructed branch. The intersection point is a representative,
not evidence that every other cell point lies in that same branch. -/
def AcceptedCellUnion {X : Type*} (cells branches : List (Set X)) : Set X :=
  {x | ∃ cell ∈ cells, x ∈ cell ∧
    ∃ representative, representative ∈ cell ∧ representative ∈ UnionOf branches}

theorem branches_covered_by_acceptance {X : Type*}
    (cells branches : List (Set X))
    (hcover : ∀ x ∈ UnionOf branches, ∃ cell ∈ cells, x ∈ cell) :
    UnionOf branches ⊆ AcceptedCellUnion cells branches := by
  intro x hx
  obtain ⟨cell, hcell, hxc⟩ := hcover x hx
  exact ⟨cell, hcell, hxc, x, hxc, hx⟩

theorem acceptance_has_branch_representative {X : Type*}
    (cells branches : List (Set X)) (x : X)
    (hx : x ∈ AcceptedCellUnion cells branches) :
    ∃ cell ∈ cells, x ∈ cell ∧
      ∃ representative ∈ cell, representative ∈ UnionOf branches := by
  exact hx

/-- The unresolved normalization direction must be derived from the
individual rank-map and selected-history constructions. It is NOT a theorem
obtained by assuming desired cell constancy as a compiler premise. -/
def CapacityNormalizationTarget {X : Type*}
    (cells branches : List (Set X)) : Prop :=
  AcceptedCellUnion cells branches = UnionOf branches

/-- A preprojection branch carries ONE whole suffix tuple and one router
vector, not one suffix policy or router vector per current entrance. -/
structure BranchRecord where
  suffixCellIdentity : Nat
  originalRouterVector : Fin 2 → Nat
  conjunction : DBM BranchVariable
  eliminatedInOrder : List BranchVariable
  outputTag : Fin 10 → TagRow (Fin 2)

/-- A stored representative alone never authorizes reuse of its branch
pointer for arbitrary points. The template stores one original full policy,
all hub classes, fixed routers and hidden ranks; concrete query recovery is
a rank transport and must prove exact all-history semantics separately. -/
structure CommonPolicyTemplate (Hub Router : Type*) where
  representative : RankPolicy Hub Router
  fixedConstants : Finset Int
  selectedClasses : Finset Int
  classOfHub : Hub → Int
  class_correct : ∀ h, classOfHub h = representative.hubChoice h
  hiddenRank : Int → Option Nat
  gapLeft : Int → Option Int

/-- Semantic headline target. This definition is open and contains no
claim that a union, construction algorithm or recovery function exists. -/
def CompilerTarget {V Exit Start : Type*} (A : Arena V Exit)
    (starts : Start → V) (admitted : Set (EvenPolicy A))
    (represented : Set (Profile Start Exit)) : Prop :=
  represented = JointAttainable A starts admitted

def CompilerRecoveryTarget {V Exit Start : Type*} (A : Arena V Exit)
    (starts : Start → V) (admitted : Set (EvenPolicy A))
    (represented : Set (Profile Start Exit))
    (recover : Profile Start Exit → EvenPolicy A) : Prop :=
  ∀ p ∈ represented,
    recover p ∈ admitted ∧ PolicyProfile A (recover p) starts = p

def ImprovingPolicyExists {V Exit Start : Type*}
    (A : Arena V Exit) (starts : Start → V) (admitted : Set (EvenPolicy A))
    (baseline : Profile Start Exit) : Prop :=
  ∃ σ ∈ admitted, StrictProfile baseline (PolicyProfile A σ starts)

theorem strict_query_exact_quantifiers {V Exit Start : Type*}
    (A : Arena V Exit) (starts : Start → V) (admitted : Set (EvenPolicy A))
    (baseline : Profile Start Exit) :
    ImprovingPolicyExists A starts admitted baseline ↔
      ∃ p ∈ JointAttainable A starts admitted, StrictProfile baseline p := by
  constructor
  · rintro ⟨σ, hσ, hstrict⟩
    exact ⟨PolicyProfile A σ starts, ⟨σ, hσ, rfl⟩, hstrict⟩
  · rintro ⟨p, ⟨σ, hσ, hprofile⟩, hstrict⟩
    exact ⟨σ, hσ, hprofile.symm ▸ hstrict⟩

theorem strict_integer_complements (u a : Int) :
    (¬ u ≤ a ↔ 0 - u ≤ -a - 1) ∧
      (¬ a ≤ u ↔ u - 0 ≤ a - 1) := by omega

/-- Exact binary targets; numerical cap enumeration is excluded from the
preprocessing algorithm. These constants do not constitute a cost proof. -/
structure CompilerExponents where
  preprocessing : Nat
  scratch : Nat
  zones : Nat
  zoneBits : Nat
  templateBits : Nat

def claimedCompilerExponents : CompilerExponents := ⟨125, 64, 12, 13, 14⟩

def PolynomialCostBound (observed : Nat → Nat) (exponent : Nat) : Prop :=
  ∃ coefficient : Nat, ∀ N, observed N ≤ coefficient * (N + 1) ^ exponent

def BinaryResourceTarget
    (preprocessing scratch zoneCount zoneBits templateBits : Nat → Nat) : Prop :=
  PolynomialCostBound preprocessing 125 ∧ PolynomialCostBound scratch 64 ∧
  PolynomialCostBound zoneCount 12 ∧ PolynomialCostBound zoneBits 13 ∧
  PolynomialCostBound templateBits 14

def ForcedOutputTarget (actualOutputLength actualOutputWork : Nat → Nat) : Prop :=
  ∃ coefficient : Nat, ∀ query,
    actualOutputWork query ≤ coefficient * actualOutputLength query

/-- Remaining algorithm obligation is concrete: decode this fixed grammar,
construct input-only capacity DBMs, enumerate constant router/weak-order/
marked-walk/cycle families, recover eliminated integers, combine one full
suffix policy per stage, construct rank templates, and prove the five binary
costs from the actual operations/encoding. The numerical cap is never a loop
bound except when enumerating requested flat output of actual length Q. -/
def UniformConstructionDuty (EncodedInput EncodedOutput : Type*)
    (valid : EncodedInput → Prop) (compute : EncodedInput → EncodedOutput)
    (specification : EncodedInput → EncodedOutput → Prop) : Prop :=
  ∀ input, valid input → specification input (compute input)

end Partials.Parity.CompilerSource
