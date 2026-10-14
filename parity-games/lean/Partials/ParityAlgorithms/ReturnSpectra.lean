import Partials.ParityAlgorithms.OrderedSyntax

/-! P6-D01/D02, separate fixed-policy vertex-priority model. Positive finite
walk weights include both endpoints. No observed return is an empty walk.
The retained historical SpectralRecord target is credited but replaced by
this attained original-graph/complete-edge-policy semantics. -/
namespace Partials.ParityAlgorithms.Spectra
open Partials.Parity
open Partials.ParityAlgorithms

structure VertexArena (V EdgeId : Type*) where
  source : EdgeId → V
  target : EdgeId → V
  priority : V → Priority5
  even : V → Bool
  total : ∀ v, ∃ e, source e = v

structure OriginalPolicy {V EdgeId : Type*} (G : VertexArena V EdgeId) where
  choose : {v : V // G.even v = true} → EdgeId
  legal : ∀ v, G.source (choose v) = v.val

def VertexArena.parityArena {V EdgeId : Type*} (G : VertexArena V EdgeId) : Arena V Empty where
  edge v w := ∃ e, G.source e = v ∧ G.target e = w
  even := G.even
  priority v := (G.priority v).val
  exitVertex := Empty.elim
  exit_injective := by intro a; cases a
  total v := by obtain ⟨e, he⟩ := G.total v; exact ⟨G.target e, e, he, rfl⟩
  exit_zero := by intro a; cases a
  exit_sink := by intro a; cases a

def OriginalPolicy.parityPolicy {V EdgeId : Type*} {G : VertexArena V EdgeId}
    (σ : OriginalPolicy G) : EvenPolicy G.parityArena where
  move v := if h : G.even v = true then G.target (σ.choose ⟨v,h⟩) else v
  legal_even v h := by
    change G.even v = true at h
    change ∃ e, G.source e = v ∧ G.target e =
      (if h : G.even v = true then G.target (σ.choose ⟨v,h⟩) else v)
    rw [dif_pos h]
    exact ⟨σ.choose ⟨v,h⟩, σ.legal ⟨v,h⟩, rfl⟩

def Selected {V EdgeId : Type*} {G : VertexArena V EdgeId}
    (σ : OriginalPolicy G) (v w : V) : Prop :=
  ∃ e, G.source e = v ∧ G.target e = w ∧
    ∀ h : G.even v = true, e = σ.choose ⟨v,h⟩

theorem selected_iff_paritySelected {V EdgeId : Type*} {G : VertexArena V EdgeId}
    (σ : OriginalPolicy G) (v w : V) :
    Selected σ v w ↔ selectedEdge G.parityArena σ.parityPolicy v w := by
  constructor
  · rintro ⟨e, hs, ht, he⟩
    refine ⟨⟨e, hs, ht⟩, ?_⟩
    intro hv
    change G.even v = true at hv
    change w = if h : G.even v = true then G.target (σ.choose ⟨v,h⟩) else v
    simpa [hv, he hv] using ht.symm
  · rintro ⟨⟨e, hs, ht⟩, he⟩
    by_cases hv : G.even v = true
    · refine ⟨σ.choose ⟨v,hv⟩, σ.legal ⟨v,hv⟩, ?_, ?_⟩
      · simpa [OriginalPolicy.parityPolicy, hv] using (he hv).symm
      · intro h
        rfl
    · exact ⟨e, hs, ht, fun h => False.elim (hv h)⟩

structure Walk {V EdgeId : Type*} {G : VertexArena V EdgeId} (σ : OriginalPolicy G) where
  length : Nat
  vertex : Nat → V
  legal : ∀ k < length, Selected σ (vertex k) (vertex (k+1))

def Walk.weight {V EdgeId : Type*} {G : VertexArena V EdgeId}
    {σ : OriginalPolicy G} (w : Walk σ) : Nat :=
  (Finset.range (w.length+1)).sup fun k => (G.priority (w.vertex k)).val

def Walk.Positive {V EdgeId : Type*} {G : VertexArena V EdgeId}
    {σ : OriginalPolicy G} (w : Walk σ) : Prop := 0 < w.length

theorem walk_weight_bound {V EdgeId : Type*} {G : VertexArena V EdgeId}
    {σ : OriginalPolicy G} (w : Walk σ) : w.weight ≤ 4 := by
  apply Finset.sup_le
  intro k hk
  have h := (G.priority (w.vertex k)).isLt
  omega

theorem walk_weight_endpoint {V EdgeId : Type*} {G : VertexArena V EdgeId}
    {σ : OriginalPolicy G} (w : Walk σ) (k : Nat) (hk : k ≤ w.length) :
    (G.priority (w.vertex k)).val ≤ w.weight := by
  unfold Walk.weight
  exact Finset.le_sup (f := fun j => (G.priority (w.vertex j)).val)
    (Finset.mem_range.mpr (by omega))

/-- Concatenation uses the same original policy and identifies the shared
endpoint. Histories may revisit every interior vertex. -/
def Walk.append {V EdgeId : Type*} {G : VertexArena V EdgeId}
    {σ : OriginalPolicy G} (a b : Walk σ) (join : a.vertex a.length = b.vertex 0) : Walk σ where
  length := a.length + b.length
  vertex k := if k ≤ a.length then a.vertex k else b.vertex (k-a.length)
  legal k hk := by
    by_cases hka : k < a.length
    · have h0 : k ≤ a.length := by omega
      have h1 : k+1 ≤ a.length := by omega
      simp only [if_pos h0,if_pos h1]
      exact a.legal k hka
    · by_cases heq : k = a.length
      · subst k
        have h1 : ¬ a.length+1 ≤ a.length := by omega
        simp only [le_refl,if_true,if_neg h1,Nat.add_sub_cancel_left]
        rw [join]
        exact b.legal 0 (by omega)
      · have h0 : ¬ k ≤ a.length := by omega
        have h1 : ¬ k+1 ≤ a.length := by omega
        have hsub : k+1-a.length = (k-a.length)+1 := by omega
        simp only [if_neg h0,if_neg h1,hsub]
        exact b.legal (k-a.length) (by omega)

theorem appended_walk_positive {V EdgeId : Type*} {G : VertexArena V EdgeId}
    {σ : OriginalPolicy G} (a b : Walk σ) (join : a.vertex a.length = b.vertex 0)
    (positive : a.Positive ∨ b.Positive) : (a.append b join).Positive := by
  simp only [Walk.Positive,Walk.append] at *
  omega

theorem appended_walk_weight {V EdgeId : Type*} {G : VertexArena V EdgeId}
    {σ : OriginalPolicy G} (a b : Walk σ) (join : a.vertex a.length = b.vertex 0) :
    (a.append b join).weight = max a.weight b.weight := by
  apply Nat.le_antisymm
  · apply Finset.sup_le
    intro k hk
    have hlen : k ≤ a.length+b.length := by
      simp only [Finset.mem_range, Walk.append] at hk
      omega
    by_cases hka : k ≤ a.length
    · simpa [Walk.append,hka] using le_trans (walk_weight_endpoint a k hka) (le_max_left a.weight b.weight)
    · have hsub : k-a.length ≤ b.length := by omega
      simpa [Walk.append,hka] using le_trans (walk_weight_endpoint b (k-a.length) hsub) (le_max_right a.weight b.weight)
  · apply max_le
    · apply Finset.sup_le
      intro k hk
      have hka : k ≤ a.length := by
        simp only [Finset.mem_range] at hk
        omega
      simpa [Walk.append,hka] using walk_weight_endpoint (a.append b join) k (by simp [Walk.append]; omega)
    · apply Finset.sup_le
      intro k hk
      have hkb : k ≤ b.length := by
        simp only [Finset.mem_range] at hk
        omega
      by_cases hk0 : k = 0
      · subst k
        simpa [Walk.append,join] using walk_weight_endpoint (a.append b join) a.length (by simp [Walk.append])
      · have hgt : ¬ a.length+k ≤ a.length := by omega
        have hsub : a.length+k-a.length = k := by omega
        simpa [Walk.append,hgt,hsub] using walk_weight_endpoint (a.append b join) (a.length+k) (by simp [Walk.append]; omega)

def FirstReturn {V EdgeId : Type*} [DecidableEq V] {G : VertexArena V EdgeId}
    (σ : OriginalPolicy G) (c : Finset V) (u v : V) (p : Priority5) : Prop :=
  u ∈ c ∧ v ∈ c ∧ ∃ w : Walk σ, w.Positive ∧ w.vertex 0 = u ∧
    w.vertex w.length = v ∧ w.weight = p.val ∧
    ∀ k, 0 < k → k < w.length → w.vertex k ∉ c

def RepeatedReturn {V EdgeId : Type*} [DecidableEq V] {G : VertexArena V EdgeId}
    (σ : OriginalPolicy G) (c : Finset V) (u v : V) (p : Priority5) : Prop :=
  u ∈ c ∧ v ∈ c ∧ ∃ w : Walk σ, w.Positive ∧ w.vertex 0 = u ∧
    w.vertex w.length = v ∧ w.weight = p.val

def NoReturn {V EdgeId : Type*} [DecidableEq V] {G : VertexArena V EdgeId}
    (σ : OriginalPolicy G) (c : Finset V) (u : V) (e : Fin 2) : Prop :=
  u ∈ c ∧ ∃ ρ : Nat → V, ρ 0 = u ∧
    (∀ k, Selected σ (ρ k) (ρ (k+1))) ∧
    (∀ k, 0 < k → ρ k ∉ c) ∧
    ∃ p : Priority5, LargestRecurring G.parityArena ρ p.val ∧ p.val % 2 = e.val

/-- Closed histories observe no stopped boundary: C is only a measurement. -/
def ClosedParity {V EdgeId : Type*} {G : VertexArena V EdgeId}
    (σ : OriginalPolicy G) (u : V) (e : Fin 2) : Prop :=
  ∃ ρ : Nat → V, ρ 0 = u ∧ (∀ k, Selected σ (ρ k) (ρ (k+1))) ∧
    ∃ p : Priority5, LargestRecurring G.parityArena ρ p.val ∧ p.val % 2 = e.val

noncomputable def boundaryEdge {V EdgeId : Type*} [DecidableEq V]
    {G : VertexArena V EdgeId} (σ : OriginalPolicy G) (c : Finset V) (v : V) : Option EdgeId :=
  if h : v ∈ c ∧ G.even v = true then some (σ.choose ⟨v,h.2⟩) else none

structure Record (V EdgeId : Type*) [DecidableEq V] where
  boundary : Finset V
  beta : V → Option EdgeId
  spectrum : V → V → Set Priority5
  noReturn : V → Fin 2 → Prop

noncomputable def attainedRecord {V EdgeId : Type*} [DecidableEq V]
    {G : VertexArena V EdgeId} (σ : OriginalPolicy G) (c : Finset V) : Record V EdgeId where
  boundary := c
  beta := boundaryEdge σ c
  spectrum u v := {p | FirstReturn σ c u v p}
  noReturn := NoReturn σ c

def Attained {V EdgeId : Type*} [DecidableEq V] {G : VertexArena V EdgeId}
    (σ : OriginalPolicy G) (h : Record V EdgeId) : Prop := h = attainedRecord σ h.boundary

noncomputable def minimumWeight (s : Set Priority5) : Option Priority5 := by
  classical
  exact [3,1,0,2,4].find? fun p => decide (p ∈ s)

theorem minimumWeight_empty : minimumWeight ∅ = none := by
  simp [minimumWeight]

/-- All unreachability entries are none; numerical 0 is an attained weight. -/
structure MinimumKey (V EdgeId : Type*) where
  beta : V → Option EdgeId
  first : V → V → Option Priority5
  repeated : V → V → Option Priority5
  noReturn : V → Fin 2 → Prop
  closedLoses : V → Prop

noncomputable def trueKey {V EdgeId : Type*} [DecidableEq V]
    {G : VertexArena V EdgeId} (σ : OriginalPolicy G) (c : Finset V) : MinimumKey V EdgeId where
  beta := boundaryEdge σ c
  first u v := minimumWeight {p | FirstReturn σ c u v p}
  repeated u v := minimumWeight {p | RepeatedReturn σ c u v p}
  noReturn := NoReturn σ c
  closedLoses u := u ∈ c ∧ ClosedParity σ u 1

/-- Only the boundary changes; all of G and σ are arguments, never reduced
or reoptimized. Totality and all history strategies come from the exact R7
adapter to an arena with Empty exits. -/
theorem selected_infinite_history_realized {V EdgeId : Type*} {G : VertexArena V EdgeId}
    (σ : OriginalPolicy G) (ρ : Nat → V)
    (h : ∀ k, Selected σ (ρ k) (ρ (k+1))) :
    ∃ τ : OddHistoryStrategy G.parityArena,
      HistoryRun σ.parityPolicy τ ρ := by
  exact selected_path_realized_by_history σ.parityPolicy ρ
    (fun k => (selected_iff_paritySelected σ _ _).mp (h k))

/-- The prefix extension theorem binds each finite selected walk to an
actual Odd history strategy; it does not force all histories periodic. -/
theorem walk_extends_history {V EdgeId : Type*} {G : VertexArena V EdgeId}
    (σ : OriginalPolicy G) (w : Walk σ) :
    ∃ ρ : Nat → V, Compatible G.parityArena σ.parityPolicy ρ ∧
      ∀ k ≤ w.length, ρ k = w.vertex k := by
  let trace : FiniteSelectedTrace G.parityArena σ.parityPolicy :=
    { length := w.length
      vertex := fun k => w.vertex k.val
      selected := fun k => (selected_iff_paritySelected σ _ _).mp (w.legal k.val k.isLt) }
  refine ⟨extendSelectedTrace trace, extendSelectedTrace_compatible trace, ?_⟩
  intro k hk
  exact extendSelectedTrace_prefix trace k hk

/-- Complete nice decomposition definition, no arbitrary grammarValid flag. -/
structure NiceDecomposition (V : Type*) [DecidableEq V] where
  Node : Type
  parent : Node → Option Node
  finite_nodes : Finite Node
  root : Node
  bag : Node → Finset V
  root_no_parent : parent root = none
  reaches_root : ∀ x, ∃ n, ((fun z : Option Node => z.bind parent)^[n]) (some x) = some root
  children : Node → List Node
  child_exact : ∀ x y, y ∈ children x ↔ parent y = some x
  nice : ∀ x, (children x).length ≤ 2 ∧
    ((children x).length = 2 → ∀ y ∈ children x, bag y = bag x) ∧
    ((children x).length = 1 → ∀ y ∈ children x,
      (bag x \ bag y).card + (bag y \ bag x).card = 1)
  bags_cap : ∀ x, (bag x).card ≤ 3
  running_intersection : ∀ v x y, v ∈ bag x → v ∈ bag y →
    ∃ a nx ny,
      ((fun z : Option Node => z.bind parent)^[nx]) (some x) = some a ∧
      ((fun z : Option Node => z.bind parent)^[ny]) (some y) = some a ∧
      (∀ s ≤ nx, ∃ b, ((fun z : Option Node => z.bind parent)^[s]) (some x) = some b ∧ v ∈ bag b) ∧
      (∀ s ≤ ny, ∃ b, ((fun z : Option Node => z.bind parent)^[s]) (some y) = some b ∧ v ∈ bag b)

structure LegalForget {V EdgeId : Type*} [Fintype V] [Fintype EdgeId] [DecidableEq V]
    (G : VertexArena V EdgeId) where
  n_cap : Fintype.card V ≤ 12
  decomposition : NiceDecomposition V
  edge_covered : ∀ e, ∃ b, G.source e ∈ decomposition.bag b ∧ G.target e ∈ decomposition.bag b
  oldNode : decomposition.Node
  newNode : decomposition.Node
  selected_step : decomposition.parent oldNode = some newNode
  old : Finset V
  forgotten : V
  old_exact : old = decomposition.bag oldNode
  new_exact : decomposition.bag newNode = old.erase forgotten
  forgotten_mem : forgotten ∈ old
  old_low : 2 ≤ old.card
  old_high : old.card ≤ 3
  no_exterior : ∀ k v, ((fun a : Option decomposition.Node => a.bind decomposition.parent)^[k]) (some newNode) = some v →
    forgotten ∉ decomposition.bag v

end Partials.ParityAlgorithms.Spectra
