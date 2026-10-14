import Partials.Parity.Model

/-! Exact complete original policy product and all Odd history strategies.
The off-path legal extension is constructed from totality, rather than
postulated as an all-history/profile equality premise. -/

namespace Partials.Parity

def originalPolicy {V Exit : Type*} {A : Arena V Exit}
    (σ : EvenPolicy A) : OriginalEvenPolicy A where
  choose v := σ.move v.val
  legal v := σ.legal_even v.val v.property

/-- Odd dummy entries are canonicalized to the same vertex. They are not
extra policy options in the paper's product over original Even vertices. -/
def canonicalPolicy {V Exit : Type*} {A : Arena V Exit}
    (σ : OriginalEvenPolicy A) : EvenPolicy A where
  move v := if h : A.even v = true then σ.choose ⟨v, h⟩ else v
  legal_even v h := by
    simp only [dif_pos h]
    exact σ.legal ⟨v, h⟩

def CanonicalOddDummy {V Exit : Type*} {A : Arena V Exit}
    (σ : EvenPolicy A) : Prop :=
  ∀ v, A.even v = false → σ.move v = v

theorem original_canonical {V Exit : Type*} {A : Arena V Exit}
    (σ : OriginalEvenPolicy A) : originalPolicy (canonicalPolicy σ) = σ := by
  cases σ with
  | mk choose legal =>
    simp only [originalPolicy, canonicalPolicy]
    congr
    funext v
    simp only [dif_pos v.property]

theorem canonical_odd_dummy {V Exit : Type*} {A : Arena V Exit}
    (σ : OriginalEvenPolicy A) : CanonicalOddDummy (canonicalPolicy σ) := by
  intro v hv
  simp [canonicalPolicy, hv]

theorem canonical_original_agrees {V Exit : Type*} {A : Arena V Exit}
    (σ : EvenPolicy A) : PolicyAgreement A (canonicalPolicy (originalPolicy σ)) σ := by
  intro v hv
  simp [canonicalPolicy, originalPolicy, hv]

theorem agreement_iff_original {V Exit : Type*} {A : Arena V Exit}
    (σ τ : EvenPolicy A) :
    PolicyAgreement A σ τ ↔ originalPolicy σ = originalPolicy τ := by
  constructor
  · intro h
    cases σ with
    | mk σmove σlegal =>
      cases τ with
      | mk τmove τlegal =>
        simp only [originalPolicy]
        congr
        funext v
        exact h v.val v.property
  · intro h v hv
    exact congrArg (fun p : OriginalEvenPolicy A => p.choose ⟨v, hv⟩) h

theorem canonical_original_exact {V Exit : Type*} {A : Arena V Exit}
    (σ : EvenPolicy A) (hσ : CanonicalOddDummy σ) :
    canonicalPolicy (originalPolicy σ) = σ := by
  cases σ with
  | mk move legal =>
    simp only [canonicalPolicy, originalPolicy]
    congr
    funext v
    by_cases hv : A.even v = true
    · simp [hv]
    · have ho : A.even v = false := by cases h : A.even v <;> simp_all
      simpa [hv] using (hσ v ho).symm

/-- This equivalence is between the exact product and canonical wrappers,
not between the exact product and all functions carrying Odd dummy choices. -/
def originalPolicyEquivCanonical {V Exit : Type*} (A : Arena V Exit) :
    OriginalEvenPolicy A ≃ {σ : EvenPolicy A // CanonicalOddDummy σ} where
  toFun σ := ⟨canonicalPolicy σ, canonical_odd_dummy σ⟩
  invFun σ := originalPolicy σ.val
  left_inv := original_canonical
  right_inv σ := Subtype.ext (canonical_original_exact σ.val σ.property)

theorem selectedEdge_agreement {V Exit : Type*} {A : Arena V Exit}
    {σ τ : EvenPolicy A} (h : PolicyAgreement A σ τ) (v w : V) :
    selectedEdge A σ v w ↔ selectedEdge A τ v w := by
  constructor <;> intro hw
  · exact ⟨hw.1, fun hv => (hw.2 hv).trans (h v hv)⟩
  · exact ⟨hw.1, fun hv => (hw.2 hv).trans (h v hv).symm⟩

theorem compatible_iff_selected {V Exit : Type*} {A : Arena V Exit}
    (σ : EvenPolicy A) (ρ : Nat → V) :
    Compatible A σ ρ ↔ ∀ n, selectedEdge A σ (ρ n) (ρ (n + 1)) := Iff.rfl

theorem compatible_agreement {V Exit : Type*} {A : Arena V Exit}
    {σ τ : EvenPolicy A} (h : PolicyAgreement A σ τ) (ρ : Nat → V) :
    Compatible A σ ρ ↔ Compatible A τ ρ := by
  constructor <;> intro hc n
  · exact (selectedEdge_agreement h (ρ n) (ρ (n + 1))).mp (hc n)
  · exact (selectedEdge_agreement h (ρ n) (ρ (n + 1))).mpr (hc n)

theorem rawOutcomes_agreement {V Exit : Type*} {A : Arena V Exit}
    {σ τ : EvenPolicy A} (h : PolicyAgreement A σ τ) (start : V) :
    RawOutcomes A σ start = RawOutcomes A τ start := by
  ext out
  constructor <;> intro ho
  · obtain ⟨ρ, hstart, hc, hout⟩ := ho
    exact ⟨ρ, hstart, (compatible_agreement h ρ).mp hc, hout⟩
  · obtain ⟨ρ, hstart, hc, hout⟩ := ho
    exact ⟨ρ, hstart, (compatible_agreement h ρ).mpr hc, hout⟩

theorem policyProfile_agreement {V Exit Start : Type*} {A : Arena V Exit}
    {σ τ : EvenPolicy A} (h : PolicyAgreement A σ τ) (starts : Start → V) :
    PolicyProfile A σ starts = PolicyProfile A τ starts := by
  funext i
  rw [PolicyProfile, PolicyProfile, rawOutcomes_agreement h]

def LegalPath {V Exit : Type*} (A : Arena V Exit) (ρ : Nat → V) : Prop :=
  ∀ n, A.edge (ρ n) (ρ (n + 1))

structure LegalHistory {V Exit : Type*} (A : Arena V Exit) where
  length : Nat
  vertex : Fin (length + 1) → V
  legal : ∀ k : Fin length,
    A.edge (vertex ⟨k.val, by omega⟩) (vertex ⟨k.val + 1, by omega⟩)

def LegalHistory.last {V Exit : Type*} {A : Arena V Exit}
    (h : LegalHistory A) : V := h.vertex ⟨h.length, by omega⟩

def pathHistory {V Exit : Type*} {A : Arena V Exit}
    (ρ : Nat → V) (hρ : LegalPath A ρ) (n : Nat) : LegalHistory A where
  length := n
  vertex k := ρ k.val
  legal k := hρ k.val

structure OddHistoryStrategy {V Exit : Type*} (A : Arena V Exit) where
  choose : LegalHistory A → V
  legal : ∀ h, A.even h.last = false → A.edge h.last (choose h)

structure EvenHistoryStrategy {V Exit : Type*} (A : Arena V Exit) where
  choose : LegalHistory A → V
  legal : ∀ h, A.even h.last = true → A.edge h.last (choose h)

noncomputable def totalSuccessor {V Exit : Type*} (A : Arena V Exit) (v : V) : V :=
  Classical.choose (A.total v)

theorem totalSuccessor_legal {V Exit : Type*} (A : Arena V Exit) (v : V) :
    A.edge v (totalSuccessor A v) := Classical.choose_spec (A.total v)

/-- Prescribe the next path move only when the *whole* history is a prefix.
Matching the last vertex alone would incorrectly force revisits to use the
same Odd move. All other legal histories receive a legal totality choice. -/
noncomputable def realizeOddPath {V Exit : Type*} {A : Arena V Exit}
    (ρ : Nat → V) (hρ : LegalPath A ρ) : OddHistoryStrategy A := by
  classical
  refine ⟨fun h => if hm : ∀ k, h.vertex k = ρ k.val then
      ρ (h.length + 1) else totalSuccessor A h.last, ?_⟩
  intro h _
  split_ifs with hm
  · have hlast : h.last = ρ h.length := hm ⟨h.length, by omega⟩
    simpa only [hlast] using hρ h.length
  · exact totalSuccessor_legal A h.last

def FollowsOdd {V Exit : Type*} {A : Arena V Exit}
    (τ : OddHistoryStrategy A) (ρ : Nat → V) (hρ : LegalPath A ρ) : Prop :=
  ∀ n, A.even (ρ n) = false → τ.choose (pathHistory ρ hρ n) = ρ (n + 1)

theorem realizeOddPath_follows {V Exit : Type*} {A : Arena V Exit}
    (ρ : Nat → V) (hρ : LegalPath A ρ) :
    FollowsOdd (realizeOddPath ρ hρ) ρ hρ := by
  classical
  intro n _
  simp [realizeOddPath, pathHistory]

/-- Run conditions are legal history strategies plus the original fixed
Even choices. Compatibility is derived, rather than included as a field. -/
def HistoryRun {V Exit : Type*} {A : Arena V Exit}
    (σ : EvenPolicy A) (τ : OddHistoryStrategy A) (ρ : Nat → V) : Prop :=
  ∃ hρ : LegalPath A ρ,
    (∀ n, A.even (ρ n) = true → ρ (n + 1) = σ.move (ρ n)) ∧
    FollowsOdd τ ρ hρ

theorem selected_path_realized_by_history {V Exit : Type*} {A : Arena V Exit}
    (σ : EvenPolicy A) (ρ : Nat → V) (hc : Compatible A σ ρ) :
    ∃ τ : OddHistoryStrategy A, HistoryRun σ τ ρ := by
  let hρ : LegalPath A ρ := fun n => (hc n).1
  exact ⟨realizeOddPath ρ hρ, hρ, fun n => (hc n).2, realizeOddPath_follows ρ hρ⟩

theorem history_run_selected_path {V Exit : Type*} {A : Arena V Exit}
    {σ : EvenPolicy A} {τ : OddHistoryStrategy A} {ρ : Nat → V}
    (h : HistoryRun σ τ ρ) : Compatible A σ ρ := by
  obtain ⟨hρ, heven, _⟩ := h
  exact fun n => ⟨hρ n, heven n⟩

def StrategyRawOutcomes {V Exit : Type*} (A : Arena V Exit)
    (σ : EvenPolicy A) (start : V) : Set (Outcome Exit) :=
  {out | ∃ τ : OddHistoryStrategy A, ∃ ρ : Nat → V,
    ρ 0 = start ∧ HistoryRun σ τ ρ ∧
      (FiniteOutcome A ρ out ∨ InfiniteOutcome A ρ out)}

theorem rawOutcomes_eq_all_history {V Exit : Type*} (A : Arena V Exit)
    (σ : EvenPolicy A) (start : V) :
    RawOutcomes A σ start = StrategyRawOutcomes A σ start := by
  ext out
  constructor
  · rintro ⟨ρ, hstart, hc, hout⟩
    obtain ⟨τ, hrun⟩ := selected_path_realized_by_history σ ρ hc
    exact ⟨τ, ρ, hstart, hrun, hout⟩
  · rintro ⟨τ, ρ, hstart, hrun, hout⟩
    exact ⟨ρ, hstart, history_run_selected_path hrun, hout⟩

/-- The optimized syntax uses legal Even histories, whereas J uses original
positional policies. These carriers are not silently identified. -/
def BothHistoryRun {V Exit : Type*} {A : Arena V Exit}
    (σ : EvenHistoryStrategy A) (τ : OddHistoryStrategy A) (ρ : Nat → V) : Prop :=
  ∃ hρ : LegalPath A ρ,
    (∀ n, A.even (ρ n) = true →
      ρ (n + 1) = σ.choose (pathHistory ρ hρ n)) ∧ FollowsOdd τ ρ hρ

def HistoryRawOutcomes {V Exit : Type*} (A : Arena V Exit)
    (σ : EvenHistoryStrategy A) (start : V) : Set (Outcome Exit) :=
  {out | ∃ τ : OddHistoryStrategy A, ∃ ρ : Nat → V,
    ρ 0 = start ∧ BothHistoryRun σ τ ρ ∧
      (FiniteOutcome A ρ out ∨ InfiniteOutcome A ρ out)}

def HistoryPolicyProfile {V Exit Start : Type*} (A : Arena V Exit)
    (σ : EvenHistoryStrategy A) (starts : Start → V) : Profile Start Exit :=
  fun i => MinRow (HistoryRawOutcomes A σ (starts i))

/-- Direct R1 carrier adapter. This establishes only the field-level and
compatible-path correspondence, retaining every original vertex. -/
def interfaceArena {V Exit : Type*} [Fintype V] (A : Arena V Exit) :
    Partials.Interface.ParityArenaData V where
  edge := A.edge
  even := A.even
  priority := A.priority
  total := A.total

def interfacePolicy {V Exit : Type*} [Fintype V] {A : Arena V Exit}
    (σ : EvenPolicy A) : Partials.Interface.CompleteEvenPolicy (interfaceArena A) where
  move := σ.move
  legal_even := σ.legal_even

def interfaceExits {V Exit : Type*} [Fintype V] [Fintype Exit]
    (A : Arena V Exit) : Partials.Interface.ParityExitInterface (Exit := Exit) (interfaceArena A) where
  vertex := A.exitVertex
  injective := A.exit_injective
  zero_priority := A.exit_zero
  sink := A.exit_sink

theorem interface_compatible_iff {V Exit : Type*} [Fintype V]
    (A : Arena V Exit) (σ : EvenPolicy A) (ρ : Nat → V) :
    Partials.Interface.PolicyCompatible (interfaceArena A) (interfacePolicy σ) ρ ↔
      Compatible A σ ρ := Iff.rfl

noncomputable def policySuccessor {V Exit : Type*} {A : Arena V Exit}
    (σ : EvenPolicy A) (v : V) : V :=
  if A.even v = true then σ.move v else totalSuccessor A v

theorem policySuccessor_selected {V Exit : Type*} {A : Arena V Exit}
    (σ : EvenPolicy A) (v : V) : selectedEdge A σ v (policySuccessor σ v) := by
  classical
  by_cases hv : A.even v = true
  · simp only [policySuccessor, if_pos hv]
    exact ⟨σ.legal_even v hv, fun _ => rfl⟩
  · simp only [policySuccessor, if_neg hv]
    exact ⟨totalSuccessor_legal A v, fun he => False.elim (hv he)⟩

structure FiniteSelectedTrace {V Exit : Type*} (A : Arena V Exit)
    (σ : EvenPolicy A) where
  length : Nat
  vertex : Fin (length + 1) → V
  selected : ∀ k : Fin length,
    selectedEdge A σ (vertex ⟨k.val, by omega⟩)
      (vertex ⟨k.val + 1, by omega⟩)

/-- Recursively copy the supplied finite prefix, then continue legally.
This also handles a zero-edge history. -/
noncomputable def extendSelectedTrace {V Exit : Type*} {A : Arena V Exit}
    {σ : EvenPolicy A} (h : FiniteSelectedTrace A σ) : Nat → V
  | 0 => h.vertex ⟨0, by omega⟩
  | n + 1 => if hn : n < h.length then h.vertex ⟨n + 1, by omega⟩
      else policySuccessor σ (extendSelectedTrace h n)

theorem extendSelectedTrace_prefix {V Exit : Type*} {A : Arena V Exit}
    {σ : EvenPolicy A} (h : FiniteSelectedTrace A σ) (n : Nat)
    (hn : n ≤ h.length) :
    extendSelectedTrace h n = h.vertex ⟨n, by omega⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hlt : n < h.length := by omega
    simp [extendSelectedTrace, hlt]

theorem extendSelectedTrace_compatible {V Exit : Type*} {A : Arena V Exit}
    {σ : EvenPolicy A} (h : FiniteSelectedTrace A σ) :
    Compatible A σ (extendSelectedTrace h) := by
  intro n
  by_cases hn : n < h.length
  · have h0 := extendSelectedTrace_prefix h n (by omega)
    have h1 := extendSelectedTrace_prefix h (n + 1) (by omega)
    simpa only [h0, h1, selectedEdge] using h.selected ⟨n, hn⟩
  · simpa only [extendSelectedTrace, dif_neg hn, selectedEdge] using
      policySuccessor_selected σ (extendSelectedTrace h n)

theorem finite_selected_trace_history_extension {V Exit : Type*}
    {A : Arena V Exit} {σ : EvenPolicy A} (h : FiniteSelectedTrace A σ) :
    ∃ ρ : Nat → V, ∃ τ : OddHistoryStrategy A,
      (∀ n (hn : n ≤ h.length), ρ n = h.vertex ⟨n, by omega⟩) ∧
      HistoryRun σ τ ρ := by
  obtain ⟨τ, hrun⟩ := selected_path_realized_by_history σ (extendSelectedTrace h)
    (extendSelectedTrace_compatible h)
  exact ⟨extendSelectedTrace h, τ, extendSelectedTrace_prefix h, hrun⟩

end Partials.Parity
