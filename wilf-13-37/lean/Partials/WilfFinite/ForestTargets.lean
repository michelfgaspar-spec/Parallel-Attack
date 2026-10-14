import Partials.WilfFinite.ResidualCover

/-! Conditional full theorem interfaces and independent scope arithmetic.
These targets remain Props without inhabitants where model/producer/codec or
R9 reduction duties persist. Neither VERIFIED instance nor historical CLOSED
run is asserted. Supporting local grammar and finite existence theorems are
in ForestSoundness, not assumptions built into Accepted. UNCOMPILED. -/
namespace Partials.WilfFinite.Forest
open Partials.WilfFinite.Core
open Partials.Interface

theorem canonical_reflection_rank (a : CanonicalState) :
    1 ≤ leftCount a ∧ 2*leftCount a ≤ conductor a := by
  classical
  rcases a with ⟨c,A⟩
  let gaps := (Finset.range c) \ A.left
  have hsub : A.left ⊆ Finset.range c := by
    intro x hx
    exact Finset.mem_range.mpr (A.below x hx)
  have hreflect : ∀ x ∈ A.left, c-1-x ∈ gaps := by
    intro x hx
    have hxc := A.below x hx
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Finset.mem_range.mpr
      omega
    · intro hr
      have hsum : x+(c-1-x)=c-1 := by omega
      have hc1 : c-1 < c := by have := A.c_two; omega
      have hz := A.closed x hx (c-1-x) hr (by omega)
      rw [hsum] at hz
      exact A.gap hz
  have hinj : Set.InjOn (fun x => c-1-x) (↑A.left : Set ℕ) := by
    intro x hx y hy heq
    have hxc := A.below x hx
    have hyc := A.below y hy
    change c-1-x = c-1-y at heq
    omega
  have hcard : A.left.card ≤ gaps.card :=
    Finset.card_le_card_of_injOn (fun x => c-1-x) hreflect hinj
  have hgapcard : gaps.card=c-A.left.card := by
    simpa [gaps] using Finset.card_sdiff_of_subset hsub
  have hpos : 0 < A.left.card := Finset.card_pos.mpr ⟨0,A.zero⟩
  change 1 ≤ A.left.card ∧ 2*A.left.card ≤ c
  omega

theorem canonical_all_rank_scope (C : ℕ) (hC : 2 ≤ C) (a : CanonicalState)
    (hconductor : conductor a ≤ C) :
    1 ≤ leftCount a ∧ leftCount a ≤ C/2 := by
  obtain ⟨hpos,hrank⟩ := canonical_reflection_rank a
  refine ⟨hpos,(Nat.le_div_iff_mul_le (by omega : 0 < 2)).2 ?_⟩
  omega

def narrow200 : Parameters := ⟨200,13,37,by omega,by omega,by omega⟩
def all200 : Parameters := ⟨200,1,100,by omega,by omega,by omega⟩

def ordinaryTwo : CanonicalState := ⟨2,{
  left := {0}
  c_two := by omega
  below := by intro x hx; simp only [Finset.mem_singleton] at hx; omega
  zero := by simp
  gap := by simp
  closed := by intro x hx y hy hxy; simp at hx hy; subst x; subst y; simp }⟩

theorem interval_scope_strict :
    InTarget all200 ordinaryTwo ∧ ¬ InTarget narrow200 ordinaryTwo := by
  simp [InTarget,all200,narrow200,ordinaryTwo,conductor,leftCount,left]

theorem narrow200_scope (a : CanonicalState) (h : InTarget narrow200 a) :
    conductor a ≤ 200 ∧ 13 ≤ leftCount a ∧ leftCount a ≤ 37 := h

theorem narrow200_sub_all200 (a : CanonicalState) (h : InTarget narrow200 a) :
    InTarget all200 a := by
  simp only [InTarget,narrow200,all200] at *
  omega

theorem checked_outputs_iff_primary_records (W0 : CanonicalState → ℤ)
    (adapter : PrimaryModelAdapter W0) (p : Parameters) (h : Header)
    (events : List Event) (outputs : List Output) (ha : Accepted p h events outputs)
    (o : Output) : o ∈ outputs ↔
      ∃ a : CanonicalState, InTarget p a ∧ W0 a < 0 ∧
        o.identity=key a ∧
        ∃ (l : Label) (hc : CanonicalLabel l),
          MultiplicityCorrect l hc ∧ PrimitiveListCorrect l ∧
          o=exactOutput l ∧ key a=(l.c,rebuiltLeft l) := by
  rw [local_grammar_output_exact p h events outputs ha o]
  exact adapter p o

/-- A direct nonnegative comparison is enough at a non-output target. -/
theorem nonoutput_comparison (W W0 : ℤ) (hcmp : W0 ≤ W) (h0 : 0 ≤ W0) :
    0 ≤ W := le_trans h0 hcmp

/-- If a locally reachable label reconstructs a given value, VERIFIED tests it.
The ordered primitive-path theorem supplies the label for every negative-W0
target; it is a separate model proof, not a field of checker acceptance. -/
theorem verified_reachable_value (p : Parameters) (h : Header) (events : List Event)
    (outputs : List Output) (hv : Verified p h events outputs)
    (l : Label) (hl : Reachable p l) (hneed : NeedsOutput p l)
    (W : ℤ) (hW : (reconstruct l).W=W) : 0 ≤ W := by
  have hmem := ground_record_present p events outputs hv.1.2 (exactOutput l)
    ⟨l,hl,hneed,rfl⟩
  have ht := hv.2 _ hmem
  simpa [exactOutput,hW] using ht

def WilfThrough (W : CanonicalState → ℤ) (p : Parameters) : Prop :=
  ∀ a, InTarget p a → 0 ≤ W a

/-- Exact full target: local grammar-to-path and canonical semantic adapters
must prove this. The certificate's output predicate never contains actual W.
No universal coverage conclusion is a certificate/header/state field. -/
def FullForestCheckerTarget (W W0 : CanonicalState → ℤ) : Prop :=
  ∀ p h events outputs, Accepted p h events outputs →
    (outputs.map Output.identity).Nodup ∧
    (∀ a, InTarget p a → W0 a < 0 →
      ∃ o ∈ outputs, o.identity=key a ∧ o.fields.W=W a) ∧
    (∀ o ∈ outputs, ∃ a, InTarget p a ∧ W0 a < 0 ∧
      o.identity=key a ∧ o.fields.W=W a)

theorem verified_bounded_wilf (W W0 : CanonicalState → ℤ)
    (complete : FullForestCheckerTarget W W0) (compare : ∀ a, W0 a ≤ W a)
    (p : Parameters) (h : Header) (events : List Event) (outputs : List Output)
    (hv : Verified p h events outputs) : WilfThrough W p := by
  intro a ha
  by_cases hn : W0 a < 0
  · obtain ⟨o,ho,hkey,hW⟩ := (complete p h events outputs hv.1).2.1 a ha hn
    have hw := hv.2 o ho
    simpa [hW] using hw
  · exact nonoutput_comparison _ _ (compare a) (by omega)

def allRanks (C : ℕ) (hC : 2 ≤ C) : Parameters :=
  ⟨C,1,C/2,hC,by omega,by omega⟩

theorem verified_all_conductors (W W0 : CanonicalState → ℤ)
    (complete : FullForestCheckerTarget W W0) (compare : ∀ a, W0 a ≤ W a)
    (C : ℕ) (hC : 2 ≤ C) (h : Header) (events : List Event) (outputs : List Output)
    (hv : Verified (allRanks C hC) h events outputs) (a : CanonicalState)
    (ha : conductor a ≤ C) : 0 ≤ W a := by
  obtain ⟨hl,hr⟩ := canonical_all_rank_scope C hC a ha
  exact verified_bounded_wilf W W0 complete compare (allRanks C hC) h events outputs hv
    a ⟨ha,hl,hr⟩

/-- Conditional existence form. The antecedent concerns actual mathematical
W at the bounded target; no produced successful certificate is asserted. -/
theorem bounded_wilf_iff_verified_exists (W W0 : CanonicalState → ℤ)
    (complete : FullForestCheckerTarget W W0) (compare : ∀ a, W0 a ≤ W a)
    (p : Parameters) : WilfThrough W p ↔
      ∃ h events outputs, Verified p h events outputs := by
  constructor
  · intro hWilf
    obtain ⟨h,events,outputs,ha⟩ := accepted_forest_exists p
    refine ⟨h,events,outputs,ha,?_⟩
    intro o ho
    obtain ⟨a,hTarget,h0,hkey,hW⟩ := (complete p h events outputs ha).2.2 o ho
    simpa [hW] using hWilf a hTarget
  · rintro ⟨h,events,outputs,hv⟩
    exact verified_bounded_wilf W W0 complete compare p h events outputs hv

def quadraticBound (v : ℕ) : ℕ := (v-3)*(v+1)

/-- R9 bridge duty: its proof uses the quadratic conductor theorem and exact
source-model existence/canonical correspondence. It is not imported here as
an already proved fact. Small v<=4 is a separately retained R9 target. -/
def R9FiniteReductionBridge (W : CanonicalState → ℤ) : Prop :=
  ∀ p : Parameters, 5 ≤ p.v → p.C=quadraticBound p.v →
    (WilfThrough W p ↔ (∀ a, p.u ≤ leftCount a → leftCount a ≤ p.v → 0 ≤ W a))

theorem bounded_rank_certificate_equivalence (W W0 : CanonicalState → ℤ)
    (complete : FullForestCheckerTarget W W0) (compare : ∀ a, W0 a ≤ W a)
    (bridge : R9FiniteReductionBridge W) (p : Parameters)
    (hv : 5 ≤ p.v) (hC : p.C=quadraticBound p.v) :
    (∀ a, p.u ≤ leftCount a → leftCount a ≤ p.v → 0 ≤ W a) ↔
      ∃ h events outputs, Verified p h events outputs := by
  rw [← bridge p hv hC]
  exact bounded_wilf_iff_verified_exists W W0 complete compare p

end Partials.WilfFinite.Forest
