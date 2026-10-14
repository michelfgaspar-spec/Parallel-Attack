import Partials.WilfStructural.Refinements

/-! R9 blind source assembly. Actual Apéry values, exponent vectors and one
selected finite set; the quotient/Macaulay and profile bridges stay explicit
in integration/shadows-duties.json. This file is not an admitted root. -/
namespace Partials.WilfStructural.Shadow

open Partials.Interface

 theorem apery_lt_conductor_add (S : NumericalSemigroup) (m c a : ℕ)
    (hc : IsConductor S c) (ha : IsAperyAt S m a) : a < c + m := by
  by_contra h
  have hlarge : c + m ≤ a := by omega
  apply ha.2
  refine ⟨a - m, hc.1 (a - m) (by omega), ?_⟩
  omega

 theorem degree_weight_bound {s : ℕ} (b : Fin s → ℕ) (m : ℕ)
    (hb : ∀ i, m ≤ b i) (u : Monomial s) : m * degree u ≤ value b u := by
  simp only [degree, value, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have := Nat.mul_le_mul_left (u i) (hb i)
  simpa [mul_comm] using this

/-- The degree bound is derived from the semigroup domain, not stored as a
selected-set field. All representations of an Apéry value satisfy it. -/
theorem apery_degree_bound {s : ℕ} (S : NumericalSemigroup)
    (b : Fin s → ℕ) (m c q : ℕ) (hm : 0 < m)
    (hc : IsConductor S c) (hdepth : c ≤ q * m)
    (hb : ∀ i, m ≤ b i) (u : Monomial s)
    (ha : IsAperyAt S m (value b u)) : degree u ≤ q := by
  have hval := apery_lt_conductor_add S m c (value b u) hc ha
  have hlo := degree_weight_bound b m hb u
  by_contra h
  have hd : q + 1 ≤ degree u := by omega
  have hmul := Nat.mul_le_mul_left m hd
  nlinarith

noncomputable def selectedFinset {s : ℕ} (S : NumericalSemigroup)
    (b : Fin s → ℕ) (m q : ℕ) : Finset (Monomial s) := by
  classical
  let box : Finset (Monomial s) :=
    (Finset.univ : Finset (Fin s → Fin (q + 1))).image (fun u i => (u i).val)
  exact box.filter (fun u => u ∈ selected (value b) q (IsAperyAt S m))

 theorem mem_selectedFinset {s : ℕ} (S : NumericalSemigroup)
    (b : Fin s → ℕ) (m q : ℕ) (u : Monomial s)
    (hbound : degree u ≤ q) :
    u ∈ selectedFinset S b m q ↔ u ∈ selected (value b) q (IsAperyAt S m) := by
  classical
  have hbox : u ∈ (Finset.univ : Finset (Fin s → Fin (q + 1))).image
      (fun w i => (w i).val) := by
    apply Finset.mem_image.mpr
    refine ⟨(fun i => ⟨u i, ?_⟩), Finset.mem_univ _, rfl⟩
    have := exponent_le_degree u i
    omega
  simp [selectedFinset, hbox]

/-- Full selected order-ideal theorem at the concrete shared semigroup domain.
B may be any finite positive semigroup generator list with b_i≥m. The exact
identification with 1, left primitive variables and D additionally uses the
primitive list and decomposition bridge recorded in SHADOW-APERY-BRIDGE. -/
theorem global_apery_selection {s : ℕ} (S : NumericalSemigroup)
    (b : Fin s → ℕ) (m c q : ℕ) (hm : 0 < m)
    (hc : IsConductor S c) (hdepth : c ≤ q * m)
    (hbmem : ∀ i, b i ∈ S.carrier) (hbmin : ∀ i, m ≤ b i) :
    (∀ w, IsAperyAt S m (value b w) →
      ∃ u ∈ selectedFinset S b m q, value b u = value b w) ∧
    Set.InjOn (value b) (↑(selectedFinset S b m q) : Set (Monomial s)) ∧
    (∀ u ∈ selectedFinset S b m q, ∀ v, Divides v u →
      v ∈ selectedFinset S b m q) := by
  classical
  have hbound : ∀ u, IsAperyAt S m (value b u) → degree u ≤ q :=
    apery_degree_bound S b m c q hm hc hdepth hbmin
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨u, hu, he⟩ := selected_exists (value b) (IsAperyAt S m) w hw
    exact ⟨u, (mem_selectedFinset S b m q u (hbound u hu.1)).2 hu, he⟩
  · intro u hu v hv he
    have hu' : u ∈ selected (value b) q (IsAperyAt S m) :=
      (Finset.mem_filter.mp hu).2
    have hv' : v ∈ selected (value b) q (IsAperyAt S m) :=
      (Finset.mem_filter.mp hv).2
    exact selected_value_injective (value b) (IsAperyAt S m) hbound hu' hv' he
  · intro u hu v hd
    have hu' : u ∈ selected (value b) q (IsAperyAt S m) :=
      (Finset.mem_filter.mp hu).2
    have hv := selected_apery_divisor S b hbmem hu' hd
    exact (mem_selectedFinset S b m q v (hbound v hv.1)).2 hv

/-- Every degree/level fiber in this branch is evaluated on this single U. -/
noncomputable def globalAllocation {s : ℕ} (S : NumericalSemigroup)
    (b : Fin s → ℕ) (m q : ℕ) (level : ℕ → ℕ) (d j : ℕ) : ℕ :=
  allocation (U := {u // u ∈ selectedFinset S b m q})
    (fun u => degree u.val) (fun u => level (value b u.val)) d j

/-- Concrete full zero-tail convention, before the greedy existence and
successor identities are transported to the polynomial Hilbert theorem. -/
def FullBinomialExpansion (j a : ℕ) (digits : Fin j → ℕ) : Prop :=
  (∀ i : Fin j, i.val ≤ digits i) ∧
  StrictMono digits ∧
  a = ∑ i : Fin j, Nat.choose (digits i) (i.val + 1)

def expansionGrowth {j : ℕ} (digits : Fin j → ℕ) : ℕ :=
  ∑ i : Fin j, Nat.choose (digits i + 1) (i.val + 2)

end Partials.WilfStructural.Shadow
