import Partials.Shared.Semigroups
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Int.DivMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Submonoid.BigOperators

/-! R9 blind source. No declarations in this file have been compiled.
Exponent vectors retain multiplicities; divisibility means additive complement.
The recursive positional rank is sum u_i * base^i, including repeated factors. -/
namespace Partials.WilfStructural.Shadow

abbrev Monomial (s : ℕ) := Fin s → ℕ

def degree {s : ℕ} (u : Monomial s) : ℕ := ∑ i, u i

def value {s : ℕ} (b : Fin s → ℕ) (u : Monomial s) : ℕ :=
  ∑ i, u i * b i

def signedValue {s : ℕ} (b : Fin s → ℤ) (u : Monomial s) : ℤ :=
  ∑ i, (u i : ℤ) * b i

def digitRank (base : ℕ) : {s : ℕ} → Monomial s → ℕ
  | 0, _ => 0
  | _ + 1, u => u 0 + base * digitRank base (fun i => u i.succ)

def Divides {s : ℕ} (v u : Monomial s) : Prop := ∃ r, u = v + r

@[simp] theorem degree_add {s : ℕ} (u v : Monomial s) :
    degree (u + v) = degree u + degree v := by
  simp [degree, Finset.sum_add_distrib]

@[simp] theorem value_add {s : ℕ} (b : Fin s → ℕ) (u v : Monomial s) :
    value b (u + v) = value b u + value b v := by
  simp [value, add_mul, Finset.sum_add_distrib]

@[simp] theorem signedValue_add {s : ℕ} (b : Fin s → ℤ) (u v : Monomial s) :
    signedValue b (u + v) = signedValue b u + signedValue b v := by
  simp [signedValue, Nat.cast_add, add_mul, Finset.sum_add_distrib]

@[simp] theorem digitRank_add (base : ℕ) {s : ℕ} (u v : Monomial s) :
    digitRank base (u + v) = digitRank base u + digitRank base v := by
  induction s with
  | zero => simp [digitRank]
  | succ s ih =>
    simp only [digitRank, Pi.add_apply]
    have ht := ih (fun i => u i.succ) (fun i => v i.succ)
    change digitRank base (fun i => u i.succ + v i.succ) =
      digitRank base (fun i => u i.succ) + digitRank base (fun i => v i.succ) at ht
    rw [ht]
    simp only [mul_add]
    omega

 theorem exponent_le_degree {s : ℕ} (u : Monomial s) (i : Fin s) :
    u i ≤ degree u := by
  exact Finset.single_le_sum (fun j _ => Nat.zero_le (u j)) (Finset.mem_univ i)

/-- Positional encoding is injective precisely on the bounded digit box.
No unrestricted injectivity of an additive rank is asserted. -/
theorem digitRank_injective (base : ℕ) (hb : 0 < base) {s : ℕ}
    (u v : Monomial s) (hu : ∀ i, u i < base) (hv : ∀ i, v i < base)
    (h : digitRank base u = digitRank base v) : u = v := by
  induction s with
  | zero => exact Subsingleton.elim _ _
  | succ s ih =>
    have hzero : u 0 = v 0 := by
      have hm := congrArg (fun n => n % base) h
      simpa [digitRank, Nat.add_mod, Nat.mul_mod,
        Nat.mod_eq_of_lt (hu 0), Nat.mod_eq_of_lt (hv 0)] using hm
    have ht : digitRank base (fun i => u i.succ) =
        digitRank base (fun i => v i.succ) := by
      simp only [digitRank, hzero] at h
      have hh : base * digitRank base (fun i => u i.succ) =
          base * digitRank base (fun i => v i.succ) := by omega
      exact Nat.eq_of_mul_eq_mul_left hb hh
    have he := ih (fun i => u i.succ) (fun i => v i.succ)
      (fun i => hu i.succ) (fun i => hv i.succ) ht
    funext i
    refine Fin.cases hzero (fun j => ?_) i
    exact congrFun he j

 theorem bounded_rank_injective {s q : ℕ} (u v : Monomial s)
    (hu : degree u ≤ q) (hv : degree v ≤ q)
    (h : digitRank (q + 1) u = digitRank (q + 1) v) : u = v := by
  apply digitRank_injective (q + 1) (by omega) u v
  · intro i; have := exponent_le_degree u i; omega
  · intro i; have := exponent_le_degree v i; omega
  · exact h

 theorem divides_refl {s : ℕ} (u : Monomial s) : Divides u u := by
  exact ⟨0, by simp⟩

 theorem divides_trans {s : ℕ} {u v w : Monomial s}
    (huv : Divides u v) (hvw : Divides v w) : Divides u w := by
  obtain ⟨a, rfl⟩ := huv
  obtain ⟨b, rfl⟩ := hvw
  exact ⟨a + b, by simp [add_assoc]⟩

 theorem divides_degree_le {s : ℕ} {v u : Monomial s} (h : Divides v u) :
    degree v ≤ degree u := by
  obtain ⟨r, rfl⟩ := h
  simp

 theorem divides_eq_of_degree_eq {s : ℕ} {v u : Monomial s}
    (h : Divides v u) (he : degree v = degree u) : v = u := by
  obtain ⟨r, rfl⟩ := h
  have hr : degree r = 0 := by rw [degree_add] at he; omega
  have hz : r = 0 := by
    funext i
    have := exponent_le_degree r i
    simpa using (show r i = 0 by omega)
  simp [hz]

 theorem value_mem {s : ℕ} (S : Partials.Interface.NumericalSemigroup)
    (b : Fin s → ℕ) (hb : ∀ i, b i ∈ S.carrier) (u : Monomial s) :
    value b u ∈ S.carrier := by
  apply S.carrier.sum_mem
  intro i _
  simpa [nsmul_eq_mul, mul_comm] using S.carrier.nsmul_mem (hb i) (u i)

/-- Direct Apéry closure under monomial divisors, without factor choice. -/
theorem apery_divisor {s m : ℕ} (S : Partials.Interface.NumericalSemigroup)
    (b : Fin s → ℕ) (hb : ∀ i, b i ∈ S.carrier)
    {u v : Monomial s} (ha : Partials.Interface.IsAperyAt S m (value b u))
    (hd : Divides v u) : Partials.Interface.IsAperyAt S m (value b v) := by
  obtain ⟨r, rfl⟩ := hd
  refine ⟨value_mem S b hb v, ?_⟩
  rintro ⟨y, hy, he⟩
  apply ha.2
  refine ⟨y + value b r, S.carrier.add_mem hy (value_mem S b hb r), ?_⟩
  rw [value_add, he]
  omega

end Partials.WilfStructural.Shadow
