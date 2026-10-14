import Partials.Shared.Semigroups
import Mathlib.Data.Finset.Interval
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.DivMod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! R9 blind source only. No Lean execution. Uses the inherited exact carrier and
membership predicates. Adapted cutoff/subsum arguments credit the historical
WilfSemigroupModelDraft; no historical unfinished field is imported as a theorem.
All ordinary-semigroup data carry independently checkable least-value certificates.
Existence of such data for every nontrivial semigroup remains FND-model-existence. -/
namespace Partials.WilfStructural.Foundation
open Partials.Interface

structure Data where
  S : NumericalSemigroup
  c : ℕ
  m : ℕ
  conductor : IsConductor S c
  multiplicity : IsMultiplicity S m
  c_pos : 0 < c

def depth (d : Data) : ℕ := (d.c + d.m - 1) / d.m
def rho (d : Data) : ℕ := depth d * d.m - d.c
def level (d : Data) (x : ℕ) : ℕ := (x + rho d) / d.m
noncomputable def L (d : Data) : Finset ℕ := LeftBelow d.S d.c
noncomputable def A (d : Data) : Finset ℕ := by
  classical
  exact (Finset.range (d.c + d.m)).filter (IsAperyAt d.S d.m)
noncomputable def P (d : Data) : Finset ℕ := by
  classical
  exact (Finset.range (d.c + d.m)).filter (IsPrimitive d.S)
noncomputable def D (d : Data) : Finset ℕ := by
  classical
  exact (A d).filter (IsDecomposable d.S)
noncomputable def T (d : Data) : Finset ℕ := by
  classical
  exact (A d).filter (fun x => 0 < x ∧ x < d.c)
noncomputable def R (d : Data) : Finset ℕ := by
  classical
  exact (T d).filter (IsDecomposable d.S)
noncomputable def B (d : Data) : Finset ℕ := by
  classical
  exact (T d).filter (fun x => ¬ IsDecomposable d.S x)
noncomputable def layer (d : Data) (i : ℕ) : Finset ℕ := by
  classical
  exact (A d).filter (fun x => level d x = i)
noncomputable def alpha (d : Data) (i : ℕ) : ℕ := (layer d i).card
noncomputable def kappa (d : Data) (i : ℕ) : ℕ := by
  classical
  exact ((R d).filter (fun x => level d x = i)).card
noncomputable def beta (d : Data) (i : ℕ) : ℕ := alpha d i - kappa d i
noncomputable def n (d : Data) : ℕ := (L d).card
noncomputable def e (d : Data) : ℕ := (P d).card
noncomputable def delta (d : Data) : ℕ := (D d).card
noncomputable def tL (d : Data) : ℕ := (T d).card
noncomputable def s (d : Data) : ℕ := (B d).card
noncomputable def K (d : Data) : ℕ := (R d).card
noncomputable def nu (d : Data) : ℤ := (n d : ℤ) - depth d
noncomputable def leftPrimitives (d : Data) : Finset ℕ := by
  classical
  exact (P d).filter (fun x => x < d.c)
noncomputable def rightPrimitives (d : Data) : Finset ℕ := by
  classical
  exact (P d).filter (fun x => d.c ≤ x)
noncomputable def ellP (d : Data) : ℕ := (leftPrimitives d).card
noncomputable def rP (d : Data) : ℕ := (rightPrimitives d).card
noncomputable def W (d : Data) : ℤ := (n d : ℤ) * e d - d.c
noncomputable def W0 (d : Data) : ℤ := (n d : ℤ) * ellP d + depth d * rP d - d.c

def inclusiveInterval (a b : ℕ) : Finset ℕ := Finset.Icc a b
def halfOpenInterval (a b : ℕ) : Finset ℕ := Finset.Ico a b
/-- Symmetric pairs represented once by the usual order; loops are retained. -/
def unorderedPairs (F : Finset ℕ) : Finset (ℕ × ℕ) :=
  (F ×ˢ F).filter (fun p => p.1 ≤ p.2)

 theorem apery_cutoff (d : Data) {x : ℕ} (hx : IsAperyAt d.S d.m x) :
    x < d.c + d.m := by
  by_contra h
  have hrem : d.c ≤ x - d.m := by omega
  exact hx.2 ⟨x - d.m, d.conductor.1 _ hrem, by omega⟩

 theorem primitive_cutoff (d : Data) {x : ℕ} (hx : IsPrimitive d.S x) :
    x < d.c + d.m := by
  by_contra h
  have hrem : d.c ≤ x - d.m := by omega
  have hcpos := d.c_pos
  exact hx.2.2 ⟨d.m, x - d.m, d.multiplicity.1, by omega,
    d.multiplicity.2.1, d.conductor.1 _ hrem, by omega⟩

 theorem mem_A (d : Data) (x : ℕ) : x ∈ A d ↔ IsAperyAt d.S d.m x := by
  classical
  simp only [A, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨apery_cutoff d h, h⟩⟩

/-- This proves P counts ALL primitives, including those in [c,c+m). -/
 theorem mem_P (d : Data) (x : ℕ) : x ∈ P d ↔ IsPrimitive d.S x := by
  classical
  simp only [P, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨primitive_cutoff d h, h⟩⟩

 theorem mem_L (d : Data) (x : ℕ) : x ∈ L d ↔ x < d.c ∧ x ∈ d.S.carrier := by
  classical
  simp [L, LeftBelow]

 theorem zero_left (d : Data) : 0 ∈ L d :=
  (mem_L d 0).2 ⟨d.c_pos, d.S.carrier.zero_mem⟩

 theorem conductor_predecessor_gap (d : Data) : d.c - 1 ∉ d.S.carrier := by
  intro h
  have hcpos := d.c_pos
  obtain ⟨z, hz, hgap⟩ := d.conductor.2 (d.c - 1) (by omega)
  have hzc : z < d.c := by
    by_contra hn
    exact hgap (d.conductor.1 z (by omega))
  have heq : z = d.c - 1 := by omega
  exact hgap (heq.symm ▸ h)

 theorem multiplicity_primitive (d : Data) : IsPrimitive d.S d.m := by
  refine ⟨d.multiplicity.2.1, d.multiplicity.1, ?_⟩
  rintro ⟨a,b,ha,hb,haS,hbS,heq⟩
  have := d.multiplicity.2.2 a ha haS
  omega

 theorem primitive_other_apery (d : Data) {x : ℕ}
    (hx : IsPrimitive d.S x) (hne : x ≠ d.m) : IsAperyAt d.S d.m x := by
  refine ⟨hx.1, ?_⟩
  rintro ⟨y,hy,heq⟩
  have hxpos := hx.2.1
  have hmpos := d.multiplicity.1
  have hypos : 0 < y := by omega
  exact hx.2.2 ⟨d.m,y,d.multiplicity.1,hypos,d.multiplicity.2.1,hy,heq⟩

 theorem primitive_partition (d : Data) : e d = ellP d + rP d := by
  classical
  unfold e ellP rP leftPrimitives rightPrimitives
  have h := Finset.card_filter_add_card_filter_not (s := P d)
    (p := fun x => x < d.c)
  simpa only [not_lt] using h.symm

 theorem wilf_w0_identity (d : Data) : W d - W0 d = nu d * rP d := by
  have he : (e d : ℤ) = (ellP d : ℤ) + rP d := by
    exact_mod_cast primitive_partition d
  unfold W W0 nu
  rw [he]
  ring

 theorem wilf_ge_w0 (d : Data) (hq : depth d ≤ n d) : W0 d ≤ W d := by
  have hn : 0 ≤ nu d := by
    unfold nu
    exact sub_nonneg.mpr (by exact_mod_cast hq)
  have hr : (0 : ℤ) ≤ rP d := Nat.cast_nonneg _
  have hp := mul_nonneg hn hr
  have he := wilf_w0_identity d
  omega

/-- N is exceptional: its cutoff c+m does not contain the sole primitive 1. -/
def fullNaturals : NumericalSemigroup where
  carrier := ⊤
  finiteGaps := by simpa using (Set.finite_empty : (∅ : Set ℕ).Finite)

 theorem fullNaturals_conductor : IsConductor fullNaturals 0 := by
  constructor
  · intro x hx; trivial
  · intro b hb; omega

 theorem fullNaturals_primitive (x : ℕ) : IsPrimitive fullNaturals x ↔ x = 1 := by
  constructor
  · rintro ⟨hx,hpos,hnd⟩
    by_contra hne
    apply hnd
    exact ⟨1,x-1,by omega,by omega,by trivial,by trivial,by omega⟩
  · rintro rfl
    refine ⟨by trivial, by omega, ?_⟩
    rintro ⟨a,b,ha,hb,_,_,hab⟩
    omega

 theorem exceptional_wilf : (0 : ℤ) * 1 - 0 = 0 := by ring
end Partials.WilfStructural.Foundation
