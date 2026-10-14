import Partials.WilfStructural.Monomials

/-! R9 blind source: a single selection across all degrees, not one selection
per requested shadow. All proof scripts are authored and unexecuted. -/
namespace Partials.WilfStructural.Shadow

/-- Minimize degree first, and only then the additive positional rank. -/
def IsMinimal {s : ℕ} {α : Type*} (V : Monomial s → α) (base : ℕ)
    (u : Monomial s) : Prop :=
  ∀ v, V v = V u → degree u ≤ degree v ∧
    (degree u = degree v → digitRank base u ≤ digitRank base v)

/-- This is an actual existence construction using two natural minima. -/
theorem minimal_exists {s : ℕ} {α : Type*} (V : Monomial s → α)
    (base : ℕ) (w : Monomial s) :
    ∃ u, V u = V w ∧ IsMinimal V base u := by
  classical
  let hd : ∃ n : ℕ, ∃ u, V u = V w ∧ degree u = n :=
    ⟨degree w, w, rfl, rfl⟩
  let d := Nat.find hd
  obtain ⟨u₀, hu₀, hdu₀⟩ := Nat.find_spec hd
  let hr : ∃ n : ℕ, ∃ u, V u = V w ∧ degree u = d ∧ digitRank base u = n :=
    ⟨digitRank base u₀, u₀, hu₀, hdu₀, rfl⟩
  obtain ⟨u, hu, hdu, hru⟩ := Nat.find_spec hr
  refine ⟨u, hu, ?_⟩
  intro v hv
  have hvw : V v = V w := hv.trans hu
  have hdv : d ≤ degree v := Nat.find_min' hd ⟨v, hvw, rfl⟩
  refine ⟨by omega, ?_⟩
  intro he
  have hrmin : Nat.find hr ≤ digitRank base v :=
    Nat.find_min' hr ⟨v, hvw, by omega, rfl⟩
  omega

/-- Adding the same complement preserves BOTH parts of the lexicographic key. -/
theorem minimal_divisor {s : ℕ} {α : Type*} [AddMonoid α]
    (V : Monomial s → α) (hV : ∀ x y, V (x + y) = V x + V y)
    (base : ℕ) {u v : Monomial s} (hu : IsMinimal V base u)
    (hd : Divides v u) : IsMinimal V base v := by
  obtain ⟨r, rfl⟩ := hd
  intro v' hv'
  have hvwhole : V (v' + r) = V (v + r) := by
    rw [hV, hV, hv']
  obtain ⟨hdeg, hrank⟩ := hu (v' + r) hvwhole
  simp only [degree_add] at hdeg hrank
  refine ⟨by omega, ?_⟩
  intro he
  have hh := hrank (by omega)
  simp only [digitRank_add] at hh
  omega

 theorem minimal_unique {s q : ℕ} {α : Type*} (V : Monomial s → α)
    {u v : Monomial s} (hu : IsMinimal V (q + 1) u)
    (hv : IsMinimal V (q + 1) v) (hvalue : V u = V v)
    (hdu : degree u ≤ q) (hdv : degree v ≤ q) : u = v := by
  have huv := hu v hvalue.symm
  have hvu := hv u hvalue
  have hd : degree u = degree v := Nat.le_antisymm huv.1 hvu.1
  apply bounded_rank_injective u v hdu hdv
  exact Nat.le_antisymm (huv.2 hd) (hvu.2 hd.symm)

/-- The global selected set; Allowed concerns numerical values alone. -/
def selected {s : ℕ} {α : Type*} (V : Monomial s → α) (q : ℕ)
    (Allowed : α → Prop) : Set (Monomial s) :=
  {u | Allowed (V u) ∧ IsMinimal V (q + 1) u}

 theorem selected_exists {s q : ℕ} {α : Type*} (V : Monomial s → α)
    (Allowed : α → Prop) (w : Monomial s) (hw : Allowed (V w)) :
    ∃ u ∈ selected V q Allowed, V u = V w := by
  obtain ⟨u, hu, hm⟩ := minimal_exists V (q + 1) w
  exact ⟨u, ⟨by simpa [hu] using hw, hm⟩, hu⟩

 theorem selected_value_injective {s q : ℕ} {α : Type*}
    (V : Monomial s → α) (Allowed : α → Prop)
    (hbound : ∀ u, Allowed (V u) → degree u ≤ q) :
    Set.InjOn V (selected V q Allowed) := by
  intro u hu v hv he
  exact minimal_unique V hu.2 hv.2 he (hbound u hu.1) (hbound v hv.1)

/-- Apéry instantiation: closure is proved from shared semigroup membership. -/
theorem selected_apery_divisor {s q m : ℕ}
    (S : Partials.Interface.NumericalSemigroup) (b : Fin s → ℕ)
    (hb : ∀ i, b i ∈ S.carrier) {u v : Monomial s}
    (hu : u ∈ selected (value b) q (Partials.Interface.IsAperyAt S m))
    (hd : Divides v u) :
    v ∈ selected (value b) q (Partials.Interface.IsAperyAt S m) := by
  exact ⟨apery_divisor S b hb hu.1 hd,
    minimal_divisor (value b) (value_add b) (q + 1) hu.2 hd⟩

/-- The complement is upward closed under multiplication of monomials.
The polynomial ideal and its quotient basis are a separate explicit duty. -/
theorem complement_multiplicative {s : ℕ} (Z : Set (Monomial s))
    (hZ : ∀ {u v}, u ∈ Z → Divides v u → v ∈ Z)
    {u : Monomial s} (hu : u ∉ Z) (r : Monomial s) : u + r ∉ Z := by
  intro h
  exact hu (hZ h ⟨r, rfl⟩)

/-- An arbitrary equal-degree numerical fiber, used in universal shadows.
Unlike IsMinimal this does not minimize across distinct degrees. -/
def IsDegreeMinimal {s : ℕ} {α : Type*} (V : Monomial s → α)
    (base : ℕ) (u : Monomial s) : Prop :=
  ∀ v, degree v = degree u → V v = V u → digitRank base u ≤ digitRank base v

 theorem degree_minimal_divisor {s : ℕ} {α : Type*} [AddMonoid α]
    (V : Monomial s → α) (hV : ∀ x y, V (x + y) = V x + V y)
    (base : ℕ) {u v : Monomial s} (hu : IsDegreeMinimal V base u)
    (hd : Divides v u) : IsDegreeMinimal V base v := by
  obtain ⟨r, rfl⟩ := hd
  intro v' hdegree hvalue
  have he : V (v' + r) = V (v + r) := by rw [hV, hV, hvalue]
  have hh := hu (v' + r) (by simp [hdegree]) he
  simpa only [digitRank_add, Nat.add_le_add_iff_right] using hh

/-- Fixed-degree selection works even for signed numerical values: minimizing
rank on a nonempty natural-valued fiber requires no positivity assumption. -/
theorem degree_minimal_exists {s : ℕ} {α : Type*} (V : Monomial s → α)
    (base : ℕ) (w : Monomial s) :
    ∃ u, degree u = degree w ∧ V u = V w ∧ IsDegreeMinimal V base u := by
  classical
  let hr : ∃ n : ℕ, ∃ u, degree u = degree w ∧ V u = V w ∧ digitRank base u = n :=
    ⟨digitRank base w, w, rfl, rfl, rfl⟩
  obtain ⟨u, hd, hv, hu⟩ := Nat.find_spec hr
  refine ⟨u, hd, hv, ?_⟩
  intro v hdeg hvalue
  have hmin := Nat.find_min' hr ⟨v, hdeg.trans hd, hvalue.trans hv, rfl⟩
  omega

 theorem degree_minimal_unique {s t : ℕ} {α : Type*} (V : Monomial s → α)
    {u v : Monomial s} (hu : IsDegreeMinimal V (t + 1) u)
    (hv : IsDegreeMinimal V (t + 1) v) (hd : degree u = degree v)
    (hval : V u = V v) (ht : degree u ≤ t) : u = v := by
  apply bounded_rank_injective u v ht (by omega)
  exact Nat.le_antisymm (hu v hd.symm hval.symm) (hv u hd hval)

end Partials.WilfStructural.Shadow
