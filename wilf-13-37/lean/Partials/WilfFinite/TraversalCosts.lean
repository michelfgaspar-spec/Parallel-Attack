import Partials.WilfFinite.GeneratorCosts

/-! Bounds count constructed nodes, including rejected children. They do not
derive work from negative-output counts. All bit-machine and exact finite-map
instantiations remain open; the accompanying note proves the combinatorics. -/
namespace Partials.WilfFinite.Application
open Partials.WilfFinite.Core
open Partials.WilfStructural.Foundation
open scoped BigOperators

def traversalDepth (C v : ℕ) : ℕ := min (min v C) (C-2)
def constructedBound (C v : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 (min v (C-2)), Nat.choose (C-1) (j+1)

def constructedLabelUniverse (C v : ℕ) : Finset (ℕ × Finset ℕ) :=
  (Finset.Icc 3 C).biUnion (fun c =>
    ((Finset.Icc 2 (c-1)).powerset.filter
      (fun G => 1 ≤ G.card ∧ G.card ≤ min v (c-2))).image (fun G => (c,G)))

/-- The hypotheses concern the actual producer's labels. Injectivity follows
mathematically from ordered roots and sorted prefix extension; it is not a
trusted producer count. -/
theorem constructed_label_injection {N : Type*} [DecidableEq N]
    (nodes : Finset N) (label : N → ℕ × Finset ℕ) (C v : ℕ)
    (hlabel : ∀ x ∈ nodes, label x ∈ constructedLabelUniverse C v)
    (hinj : Set.InjOn label (↑nodes : Set N)) :
    nodes.card ≤ (constructedLabelUniverse C v).card := by
  classical
  apply Finset.card_le_card_of_injOn label
  · exact hlabel
  · exact hinj

def LabelCountingTarget : Prop := ∀ C v : ℕ, 2 ≤ C → 1 ≤ v →
  (constructedLabelUniverse C v).card=constructedBound C v ∧
  constructedBound C v+C-1 ≤ 2^(C-1)-1

/-- The parent can have v-1 primitives and attempt one more. Omitting that
child gives the wrong bound for all constructed nodes. -/
theorem attempted_length_bound (parent child k v : ℕ)
    (hparent : parent+1 ≤ k) (hk : k ≤ v) (hchild : child=parent+1) :
    child ≤ v := by omega

theorem label_length_depth (j c C v : ℕ) (hc : c ≤ C)
    (hjv : j ≤ v) (hjc : j ≤ c-2) : j ≤ traversalDepth C v := by
  unfold traversalDepth
  apply le_min
  · exact le_min hjv (by omega)
  · omega

theorem arrays_linear (c : ℕ) (hc : 1 ≤ c) :
    c+(2*c-1)+(2*c-1) ≤ 5*c := by omega

def forestTimeScale (I V C bitWidth Z : ℕ) : ℕ := I+V*C^2*bitWidth+C*bitWidth+Z
def forestWorkingScale (I h C bitWidth : ℕ) : ℕ := I+h*C+h^2*bitWidth+bitWidth
def forestCertificateScale (I V C h J vstar bitWidth : ℕ) : ℕ :=
  I+(V+C)*(h+1)*bitWidth+J*(vstar+1)*bitWidth

/-- Counts are lengths, never indices represented in unbounded words.
Serialized enter/exit records each include their complete increasing label. -/
theorem forest_charging (I V C bitWidth Z A read rebuild ordinary serialize : ℕ)
    (hr : read ≤ A*I) (hb : rebuild ≤ A*(V*C^2*bitWidth))
    (ho : ordinary ≤ A*(C*bitWidth)) (hz : serialize ≤ A*Z) :
    read+rebuild+ordinary+serialize ≤ A*forestTimeScale I V C bitWidth Z := by
  unfold forestTimeScale
  nlinarith

theorem stack_charging (I h C bitWidth A header arrays labels scratch : ℕ)
    (hi : header ≤ A*I) (ha : arrays ≤ A*(h*C))
    (hl : labels ≤ A*(h^2*bitWidth)) (hs : scratch ≤ A*bitWidth) :
    header+arrays+labels+scratch ≤ A*forestWorkingScale I h C bitWidth := by
  unfold forestWorkingScale
  nlinarith

theorem full_label_stream_charging (I V C h J vstar bitWidth A header events outputs : ℕ)
    (hi : header ≤ A*I) (he : events ≤ A*((V+C)*(h+1)*bitWidth))
    (ho : outputs ≤ A*(J*(vstar+1)*bitWidth)) :
    header+events+outputs ≤ A*forestCertificateScale I V C h J vstar bitWidth := by
  unfold forestCertificateScale
  nlinarith

def rankCutoff (v : ℕ) : ℕ := (v-3)*(v+1)

theorem rank_polynomial_mono (n v : ℤ) (hn : 5 ≤ n) (hnv : n ≤ v) :
    (n-3)*(n+1) ≤ (v-3)*(v+1) := by
  have hprod := mul_nonneg (show 0 ≤ v-n by omega) (show 0 ≤ v+n-2 by omega)
  nlinarith

/-- This uses the independent structural target at its declared strength.
No headline 13--37 result or historical success enters the cutoff. -/
theorem quadratic_cutoff_conditional (hq : QuadraticTarget) (d : Data)
    (v : ℕ) (hnv : n d ≤ v) (hbad : W d < 0) :
    (d.c : ℤ) ≤ ((v : ℤ)-3)*((v : ℤ)+1) := by
  obtain ⟨hn,_,_,_,_,_,_,hc,hc',hc''⟩ := hq d hbad
  have hmono := rank_polynomial_mono (n d : ℤ) v (by exact_mod_cast hn)
    (by exact_mod_cast hnv)
  omega

/-- A uniform bit-complexity upper-bound interface. Mathematical finite-map,
exact producer/checker and cost-model proofs must inhabit it independently.
It states no lower bound, hardness, polynomial delay or practical feasibility. -/
def RankDecisionCostTarget (decisionWork checkWork encoding space : ℕ → ℕ)
    (binaryLog : ℕ → ℕ) : Prop :=
  ∃ A B : ℕ, 0 < A ∧ 0 < B ∧ ∀ v, 1 ≤ v →
    decisionWork v ≤ A*2^(B*v*binaryLog (v+1)) ∧
    checkWork v ≤ A*2^(B*v*binaryLog (v+1)) ∧
    encoding v ≤ A*2^(B*v*binaryLog (v+1)) ∧
    space v ≤ A*(v^3+v^2*binaryLog (v+1))

def TraversalBitInstantiationTarget
    (time working Z V J bitWidth I : Parameters → ℕ) : Prop :=
  ∃ A : ℕ, 0 < A ∧ ∀ p : Parameters,
    0 < bitWidth p ∧ J p ≤ V p ∧ V p ≤ constructedBound p.C p.v ∧
    time p ≤ A*forestTimeScale (I p) (V p) p.C (bitWidth p) (Z p) ∧
    working p ≤ A*forestWorkingScale (I p) (traversalDepth p.C p.v) p.C (bitWidth p) ∧
    Z p ≤ A*forestCertificateScale (I p) (V p) p.C (traversalDepth p.C p.v)
      (J p) (min p.v p.C) (bitWidth p)

end Partials.WilfFinite.Application
