import Partials.ParityAlgorithms.SpectralForget

/-! Literal eight-vertex, ten-edge P6 fixture and entire nice decomposition.
Finite `decide` proofs below are Lean source only, never evaluated here.
Displayed tables are targets until all-history completeness is supplied. -/
namespace Partials.ParityAlgorithms.ForgetExample
open Partials.Parity
open Partials.ParityAlgorithms
open Partials.ParityAlgorithms.Spectra

inductive Vertex where
  | a | z | c | y | x | p3 | p4 | p1
  deriving DecidableEq
instance instFintypeVertex : Fintype Vertex where
  elems := {.a, .z, .c, .y, .x, .p3, .p4, .p1}
  complete := by intro v; cases v <;> simp
inductive Edge where
  | az | zy | cc | yp3 | yx | xp4 | xp1 | p3z | p4z | p1z
  deriving DecidableEq
instance instFintypeEdge : Fintype Edge where
  elems := {.az, .zy, .cc, .yp3, .yx, .xp4, .xp1, .p3z, .p4z, .p1z}
  complete := by intro e; cases e <;> simp

def edgeSource : Edge → Vertex
  | .az => .a | .zy => .z | .cc => .c
  | .yp3 | .yx => .y | .xp4 | .xp1 => .x
  | .p3z => .p3 | .p4z => .p4 | .p1z => .p1

def edgeTarget : Edge → Vertex
  | .az | .p3z | .p4z | .p1z => .z
  | .zy => .y | .cc => .c | .yp3 => .p3 | .yx => .x
  | .xp4 => .p4 | .xp1 => .p1

def vertexPriority : Vertex → Priority5
  | .c => 2 | .p3 => 3 | .p4 => 4 | .p1 => 1 | _ => 0

def evenOwned : Vertex → Bool
  | .a | .z | .c | .x => true | _ => false

def graph : VertexArena Vertex Edge where
  source := edgeSource
  target := edgeTarget
  priority := vertexPriority
  even := evenOwned
  total v := by
    cases v
    · exact ⟨.az,rfl⟩
    · exact ⟨.zy,rfl⟩
    · exact ⟨.cc,rfl⟩
    · exact ⟨.yp3,rfl⟩
    · exact ⟨.xp4,rfl⟩
    · exact ⟨.p3z,rfl⟩
    · exact ⟨.p4z,rfl⟩
    · exact ⟨.p1z,rfl⟩

def selectedOriginal (four : Bool) : {v : Vertex // graph.even v = true} → Edge
  | ⟨.a,_⟩ => .az | ⟨.z,_⟩ => .zy | ⟨.c,_⟩ => .cc
  | ⟨.x,_⟩ => if four then .xp4 else .xp1
  | ⟨.y,h⟩ | ⟨.p3,h⟩ | ⟨.p4,h⟩ | ⟨.p1,h⟩ => False.elim (by simpa [graph,evenOwned] using h)

def policy (four : Bool) : OriginalPolicy graph where
  choose := selectedOriginal four
  legal v := by
    rcases v with ⟨v,h⟩
    change evenOwned v = true at h
    cases v with
    | a => rfl
    | z => rfl
    | c => rfl
    | x => cases four <;> rfl
    | y => simp [evenOwned] at h
    | p3 => simp [evenOwned] at h
    | p4 => simp [evenOwned] at h
    | p1 => simp [evenOwned] at h

theorem vertex_count : Fintype.card Vertex = 8 := by decide
theorem edge_count : Fintype.card Edge = 10 := by decide
theorem edge_pair_injective : Function.Injective (fun e => (edgeSource e,edgeTarget e)) := by decide

/-- Original unused arm and its forced return edge stay present under both
policies; only the selected outgoing edge at x differs. -/
theorem original_unselected_vertices_retained :
    graph.source Edge.p4z = Vertex.p4 ∧ graph.source Edge.p1z = Vertex.p1 := by decide

theorem all_original_policies (σ : OriginalPolicy graph) :
    σ = policy true ∨ σ = policy false := by
  have hx := σ.legal ⟨Vertex.x,rfl⟩
  have casesx : σ.choose ⟨Vertex.x,rfl⟩ = Edge.xp4 ∨ σ.choose ⟨Vertex.x,rfl⟩ = Edge.xp1 := by
    cases e : σ.choose ⟨Vertex.x,rfl⟩ <;> simp_all [graph,edgeSource]
  have extpolicy : ∀ four : Bool, σ.choose ⟨Vertex.x,rfl⟩ = selectedOriginal four ⟨Vertex.x,rfl⟩ → σ = policy four := by
    intro four hfour
    cases σ with
    | mk choose legal =>
      congr 1
      funext v
      rcases v with ⟨v,hv⟩
      change evenOwned v = true at hv
      cases v with
      | a =>
        have he := legal ⟨Vertex.a,rfl⟩
        cases e : choose ⟨Vertex.a,rfl⟩ <;> simp_all [graph,edgeSource,selectedOriginal]
      | z =>
        have he := legal ⟨Vertex.z,rfl⟩
        cases e : choose ⟨Vertex.z,rfl⟩ <;> simp_all [graph,edgeSource,selectedOriginal]
      | c =>
        have he := legal ⟨Vertex.c,rfl⟩
        cases e : choose ⟨Vertex.c,rfl⟩ <;> simp_all [graph,edgeSource,selectedOriginal]
      | x => simpa [selectedOriginal] using hfour
      | y => simp [evenOwned] at hv
      | p3 => simp [evenOwned] at hv
      | p4 => simp [evenOwned] at hv
      | p1 => simp [evenOwned] at hv
  rcases casesx with h | h
  · exact Or.inl (extpolicy true h)
  · exact Or.inr (extpolicy false h)

/-- Matrix indexes a,z,c, and a,c preserve their order before/after forget. -/
def oldBoundary : Finset Vertex := {.a,.z,.c}
def newBoundary : Finset Vertex := {.a,.c}

theorem exact_forget : oldBoundary.erase Vertex.z = newBoundary := by decide

def oldStart : Fin 3 → Vertex | 0 => .a | 1 => .z | _ => .c
def newStart : Fin 2 → Vertex | 0 => .a | _ => .c

/-- Full 23-node parent-to-child nice decomposition supplied in the paper. -/
def bag : Fin 23 → Finset Vertex
  | 0 => {.a,.c} | 1 => {.a,.z,.c} | 2 => {.z,.c} | 3 => {.z}
  | 4 => {.z,.y} | 5 => {.z,.y} | 6 => {.z,.y,.p3} | 7 => {.z,.p3}
  | 8 => {.p3} | 9 => ∅ | 10 => {.z,.y} | 11 => {.z,.y,.x}
  | 12 => {.z,.x} | 13 => {.z,.x} | 14 => {.z,.x,.p4} | 15 => {.z,.p4}
  | 16 => {.p4} | 17 => ∅ | 18 => {.z,.x} | 19 => {.z,.x,.p1}
  | 20 => {.z,.p1} | 21 => {.p1} | _ => ∅

def parent : Fin 23 → Option (Fin 23)
  | 0 => none | 1 => some 0 | 2 => some 1 | 3 => some 2 | 4 => some 3
  | 5 => some 4 | 6 => some 5 | 7 => some 6 | 8 => some 7 | 9 => some 8
  | 10 => some 4 | 11 => some 10 | 12 => some 11 | 13 => some 12
  | 14 => some 13 | 15 => some 14 | 16 => some 15 | 17 => some 16
  | 18 => some 12 | 19 => some 18 | 20 => some 19 | 21 => some 20 | _ => some 21

def children : Fin 23 → List (Fin 23)
  | 0 => [1] | 1 => [2] | 2 => [3] | 3 => [4] | 4 => [5,10]
  | 5 => [6] | 6 => [7] | 7 => [8] | 8 => [9] | 9 => []
  | 10 => [11] | 11 => [12] | 12 => [13,18] | 13 => [14]
  | 14 => [15] | 15 => [16] | 16 => [17] | 17 => []
  | 18 => [19] | 19 => [20] | 20 => [21] | 21 => [22] | _ => []

theorem bags_width_two : ∀ b, (bag b).card ≤ 3 := by decide
theorem decomposition_edges_covered : ∀ e : Edge, ∃ b : Fin 23,
    edgeSource e ∈ bag b ∧ edgeTarget e ∈ bag b := by decide
theorem decomposition_child_exact : ∀ b c, c ∈ children b ↔ parent c = some b := by decide
theorem nice_steps : ∀ b, (children b).length ≤ 2 ∧
    ((children b).length = 2 → ∀ c ∈ children b, bag c = bag b) ∧
    ((children b).length = 1 → ∀ c ∈ children b,
      (bag b \ bag c).card + (bag c \ bag b).card = 1) := by decide

/-- Original depths and highest bags containing each original vertex.
They give bounded certificates for the unbounded decomposition fields. -/
def bagDepth : Fin 23 → Nat
  | 0 => 0 | 1 => 1 | 2 => 2 | 3 => 3 | 4 => 4
  | 5 => 5 | 6 => 6 | 7 => 7 | 8 => 8 | 9 => 9
  | 10 => 5 | 11 => 6 | 12 => 7 | 13 => 8 | 14 => 9
  | 15 => 10 | 16 => 11 | 17 => 12 | 18 => 8 | 19 => 9
  | 20 => 10 | 21 => 11 | _ => 12

def vertexAnchor : Vertex → Fin 23
  | .a | .c => 0 | .z => 1 | .y => 4 | .x => 11
  | .p3 => 6 | .p4 => 14 | .p1 => 19

def ancestor (k : Nat) (b : Fin 23) : Option (Fin 23) :=
  ((fun z : Option (Fin 23) => z.bind parent)^[k]) (some b)

theorem ancestor_root : ∀ b, ancestor (bagDepth b) b = some 0 := by decide

theorem anchor_path_certificate : ∀ (v : Vertex) (b : Fin 23), v ∈ bag b →
    ancestor (bagDepth b - bagDepth (vertexAnchor v)) b = some (vertexAnchor v) ∧
    ∀ s : Fin 13, s.val ≤ bagDepth b - bagDepth (vertexAnchor v) →
      ∃ a : Fin 23, ancestor s.val b = some a ∧ v ∈ bag a := by decide

theorem anchor_path_length : ∀ (v : Vertex) (b : Fin 23),
    bagDepth b - bagDepth (vertexAnchor v) < 13 := by decide

/-- Complete supplied decomposition, including connected occurrence paths
and root reachability; no validity flag substitutes for these fields. -/
def niceDecomposition : NiceDecomposition Vertex where
  Node := Fin 23
  parent := parent
  finite_nodes := inferInstance
  root := 0
  bag := bag
  root_no_parent := rfl
  reaches_root b := ⟨bagDepth b, ancestor_root b⟩
  children := children
  child_exact := decomposition_child_exact
  nice := nice_steps
  bags_cap := bags_width_two
  running_intersection v x y hx hy := by
    refine ⟨vertexAnchor v, bagDepth x - bagDepth (vertexAnchor v),
      bagDepth y - bagDepth (vertexAnchor v),
      (anchor_path_certificate v x hx).1, (anchor_path_certificate v y hy).1, ?_, ?_⟩
    · intro s hs
      exact (anchor_path_certificate v x hx).2
        ⟨s, lt_of_le_of_lt hs (anchor_path_length v x)⟩ hs
    · intro s hs
      exact (anchor_path_certificate v y hy).2
        ⟨s, lt_of_le_of_lt hs (anchor_path_length v y)⟩ hs

theorem root_ancestor_only (k : Nat) (v : Fin 23)
    (h : ancestor k 0 = some v) : v = 0 := by
  cases k with
  | zero => simpa [ancestor] using h.symm
  | succ k =>
    have iter_none : ∀ n : Nat,
        ((fun z : Option (Fin 23) => z.bind parent)^[n]) none = none := by
      intro n
      induction n with
      | zero => rfl
      | succ n ih => simpa [Function.iterate_succ_apply] using ih
    have hn : ancestor (k+1) 0 = none := by
      simpa [ancestor, Function.iterate_succ_apply, parent] using iter_none k
    rw [hn] at h
    contradiction

/-- The exact root forget on the unchanged eight-vertex, ten-edge graph. -/
def legalForget : LegalForget graph where
  n_cap := by decide
  decomposition := niceDecomposition
  edge_covered := decomposition_edges_covered
  oldNode := (1 : Fin 23)
  newNode := (0 : Fin 23)
  selected_step := rfl
  old := oldBoundary
  forgotten := .z
  old_exact := rfl
  new_exact := exact_forget.symm
  forgotten_mem := by decide
  old_low := by decide
  old_high := by decide
  no_exterior k v h := by
    have he : v = (0 : Fin 23) := root_ancestor_only k v h
    subst v
    decide

/-- Positive original first-return witness tables; endpoint priorities zero
are included. No-return/negative table claims are not established by them. -/
def episodeThree : List Vertex := [.z,.y,.p3,.z]
def episodeSelected (four : Bool) : List Vertex :=
  [.z,.y,.x,if four then .p4 else .p1,.z]
def prefixAZ : List Vertex := [.a,.z]
def loopC : List Vertex := [.c,.c]

def episodeWeight (four : Bool) : Priority5 := if four then 4 else 1

def oldSpectrum (four : Bool) (u v : Vertex) : Set Priority5 :=
  if u = .a ∧ v = .z then {0}
  else if u = .z ∧ v = .z then {3,episodeWeight four}
  else if u = .c ∧ v = .c then {2} else ∅

def oldRepeated (four : Bool) (u v : Vertex) : Set Priority5 :=
  if u = .a ∧ v = .z then {0,3,episodeWeight four}
  else if u = .z ∧ v = .z then {3,episodeWeight four}
  else if u = .c ∧ v = .c then {2} else ∅

def newSpectrum (u v : Vertex) : Set Priority5 := if u = .c ∧ v = .c then {2} else ∅
def oldClosed (four : Bool) (u : Vertex) (e : Fin 2) : Prop :=
  if u = .c then e = 0 else (u = .a ∨ u = .z) ∧ (e = 1 ∨ four = true)
def newNoReturn (four : Bool) (u : Vertex) (e : Fin 2) : Prop :=
  u = .a ∧ (e = 1 ∨ four = true)

noncomputable def oldDisplayedRecord (four : Bool) : Record Vertex Edge where
  boundary := oldBoundary
  beta := boundaryEdge (policy four) oldBoundary
  spectrum := oldSpectrum four
  noReturn _ _ := False

noncomputable def displayedOldKey (four : Bool) : MinimumKey Vertex Edge where
  beta := boundaryEdge (policy four) oldBoundary
  first u v := minimumWeight (oldSpectrum four u v)
  repeated u v := minimumWeight (oldRepeated four u v)
  noReturn _ _ := False
  closedLoses u := u = .a ∨ u = .z

noncomputable def displayedNewKey (four : Bool) : MinimumKey Vertex Edge where
  beta := boundaryEdge (policy four) newBoundary
  first u v := minimumWeight (newSpectrum u v)
  repeated u v := minimumWeight (newSpectrum u v)
  noReturn := newNoReturn four
  closedLoses u := u = .a

/-- Honest target: all true and false bits, all five key fields, arbitrary
full-history Odd episodes and the exact same complete original σ. -/
def ExactFixtureTableTarget : Prop :=
  (∀ four, attainedRecord (policy four) oldBoundary = oldDisplayedRecord four) ∧
  (∀ four u v p, RepeatedReturn (policy four) oldBoundary u v p ↔ p ∈ oldRepeated four u v) ∧
  (∀ four u e, u ∈ oldBoundary → (ClosedParity (policy four) u e ↔ oldClosed four u e)) ∧
  (∀ four, trueKey (policy four) oldBoundary = displayedOldKey four) ∧
  (∀ four, trueKey (policy four) newBoundary = displayedNewKey four)

/-- Compare displayed finite source minima separately from its semantic
attainment target. Three is least in both {3,4} and {3,1}; {0,3,j} also
has minimum three. The old first a→z entry remains exactly zero. -/
theorem displayed_old_key_equal : displayedOldKey true = displayedOldKey false := by
  unfold displayedOldKey
  congr 1
  · funext v
    cases v <;> simp [boundaryEdge,oldBoundary,policy,selectedOriginal,graph,evenOwned]
  · funext u v
    cases u <;> cases v <;> simp [oldSpectrum,episodeWeight,minimumWeight]
  · funext u v
    cases u <;> cases v <;> simp [oldRepeated,episodeWeight,minimumWeight]

theorem displayed_new_key_diff : displayedNewKey true ≠ displayedNewKey false := by
  intro h
  have he := congrArg (fun k : MinimumKey Vertex Edge => k.noReturn Vertex.a 0) h
  simpa [displayedNewKey,newNoReturn] using he

theorem displayed_spectral_distinction : oldDisplayedRecord true ≠ oldDisplayedRecord false := by
  intro h
  have he := congrArg (fun k : Record Vertex Edge => (4 : Priority5) ∈ k.spectrum Vertex.z Vertex.z) h
  simpa [oldDisplayedRecord,oldSpectrum,episodeWeight] using he

theorem exact_fixture_noncongruence (h : ExactFixtureTableTarget) :
    trueKey (policy true) oldBoundary = trueKey (policy false) oldBoundary ∧
    trueKey (policy true) newBoundary ≠ trueKey (policy false) newBoundary := by
  have hold := h.2.2.2.1
  have hnew := h.2.2.2.2
  exact ⟨by rw [hold true,hold false]; exact displayed_old_key_equal,
    by rw [hnew true,hnew false]; exact displayed_new_key_diff⟩

theorem no_minimum_key_transfer (h : ExactFixtureTableTarget) :
    ¬ ∃ transfer : MinimumKey Vertex Edge → MinimumKey Vertex Edge,
      ∀ σ : OriginalPolicy graph, transfer (trueKey σ oldBoundary) = trueKey σ newBoundary := by
  obtain ⟨hold,hnew⟩ := exact_fixture_noncongruence h
  rintro ⟨transfer,correct⟩
  apply hnew
  calc
    trueKey (policy true) newBoundary = transfer (trueKey (policy true) oldBoundary) := (correct _).symm
    _ = transfer (trueKey (policy false) oldBoundary) := congrArg transfer hold
    _ = trueKey (policy false) newBoundary := correct _

/-- Canonical-witness collapse loses one of the attained new records.
Complete interior selectors/raw closed parity distinguish the two σ already;
this has no winner-selection impossibility implication. -/
def CanonicalWitnessLossTarget : Prop :=
  ∀ chosen : Bool, ∃ other : Bool,
    displayedOldKey chosen = displayedOldKey other ∧
    displayedNewKey chosen ≠ displayedNewKey other

/-- A concrete statement about the displayed keys; attainment remains the
separate ExactFixtureTableTarget and is not added as an implicit premise. -/
theorem displayed_canonical_witness_loss : CanonicalWitnessLossTarget := by
  intro chosen
  cases chosen
  · exact ⟨true, displayed_old_key_equal.symm, Ne.symm displayed_new_key_diff⟩
  · exact ⟨false, displayed_old_key_equal, displayed_new_key_diff⟩

end Partials.ParityAlgorithms.ForgetExample
