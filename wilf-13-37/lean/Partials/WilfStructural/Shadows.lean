import Partials.WilfStructural.Selection
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sum

/-! R9 blind source. Counts refer to actual finite sets/types. The one fixed
selected set supplies all fibers. No Hilbert growth inequality is postulated. -/
namespace Partials.WilfStructural.Shadow

 def downwardClosure {s : ℕ} (Y : Set (Monomial s)) : Set (Monomial s) :=
  {v | ∃ u ∈ Y, Divides v u}

 theorem downward_closed {s : ℕ} (Y : Set (Monomial s))
    {u v : Monomial s} (hu : u ∈ downwardClosure Y) (hv : Divides v u) :
    v ∈ downwardClosure Y := by
  obtain ⟨w, hw, huw⟩ := hu
  exact ⟨w, hw, divides_trans hv huw⟩

/-- No spurious degree-t targets arise from closing a pure degree-t set. -/
theorem downward_top_exact {s t : ℕ} (Y : Set (Monomial s))
    (hY : ∀ u ∈ Y, degree u = t) (u : Monomial s) (hu : degree u = t) :
    u ∈ downwardClosure Y ↔ u ∈ Y := by
  constructor
  · rintro ⟨v, hv, hd⟩
    have he : u = v := divides_eq_of_degree_eq hd (hu.trans (hY v hv).symm)
    simpa [he] using hv
  · intro h
    exact ⟨u, h, divides_refl u⟩

 theorem downward_subset_selected {s : ℕ} (Z Y : Set (Monomial s))
    (hZ : ∀ {u v}, u ∈ Z → Divides v u → v ∈ Z) (hY : Y ⊆ Z) :
    downwardClosure Y ⊆ Z := by
  rintro v ⟨u, hu, hd⟩
  exact hZ (hY hu) hd

/-- A precise universal hypothesis; repeated factors are exponent subvectors. -/
def UniversalShadow {s : ℕ} {α : Type*} (V : Monomial s → α)
    (K T : Set α) (d t : ℕ) : Prop :=
  ∀ u, degree u = t → V u ∈ T →
    ∀ v, Divides v u → degree v = d → V v ∈ K

 theorem universal_selected_divisor {s d t : ℕ} {α : Type*} [AddMonoid α]
    (V : Monomial s → α) (hV : ∀ x y, V (x + y) = V x + V y)
    (K T : Set α) (hshadow : UniversalShadow V K T d t)
    {u v : Monomial s} (hu : degree u = t) (hT : V u ∈ T)
    (hmin : IsDegreeMinimal V (t + 1) u)
    (hdiv : Divides v u) (hv : degree v = d) :
    V v ∈ K ∧ IsDegreeMinimal V (t + 1) v := by
  exact ⟨hshadow u hu hT v hdiv hv,
    degree_minimal_divisor V hV (t + 1) hmin hdiv⟩

/-- The SAME U, deg and lev occur on both sides and in every downstream call. -/
noncomputable def allocation {U : Type*} [Fintype U] (deg lev : U → ℕ)
    (d j : ℕ) : ℕ := by
  classical
  exact Fintype.card {u : U // deg u = d ∧ lev u = j}

noncomputable def layerDegreeEquiv {U : Type*} [Fintype U]
    (deg lev : U → ℕ) (j D : ℕ) (hD : ∀ u, lev u = j → deg u < D) :
    {u : U // lev u = j} ≃
      (Σ d : Fin D, {u : U // deg u = d.val ∧ lev u = j}) where
  toFun u := ⟨⟨deg u.val, hD u.val u.property⟩, u.val, rfl, u.property⟩
  invFun p := ⟨p.2.val, p.2.property.2⟩
  left_inv u := by cases u; rfl
  right_inv p := by
    rcases p with ⟨⟨d, hd⟩, u, hu, hj⟩
    cases hu
    rfl

/-- Exact fiber accounting, not a freely feasible matrix h. -/
theorem allocation_budget {U : Type*} [Fintype U] (deg lev : U → ℕ)
    (j D : ℕ) (hD : ∀ u, lev u = j → deg u < D) :
    Fintype.card {u : U // lev u = j} =
      ∑ d : Fin D, allocation deg lev d.val j := by
  classical
  have h := Fintype.card_congr (layerDegreeEquiv deg lev j D hD)
  simpa [allocation, Fintype.card_sigma] using h

 theorem allocation_above_level_zero {U : Type*} [Fintype U]
    (deg lev : U → ℕ) (hbound : ∀ u, deg u ≤ lev u) (d j : ℕ)
    (hjd : j < d) : allocation deg lev d j = 0 := by
  classical
  have he : IsEmpty {u : U // deg u = d ∧ lev u = j} :=
    ⟨fun u => by have hh := hbound u.val; rw [u.property.1, u.property.2] at hh; omega⟩
  letI := he
  simp [allocation]

/-- Prefix and top are an exact disjoint partition, even for noncompressed
subfamilies; using all left values in a cap is a subsequent weakening. -/
noncomputable def leftTopEquiv {U : Type*} (lev : U → ℕ) (q : ℕ)
    (hq : ∀ u, lev u ≤ q) : U ≃
      ({u : U // lev u < q} ⊕ {u : U // lev u = q}) where
  toFun u := if h : lev u < q then Sum.inl ⟨u, h⟩
    else Sum.inr ⟨u, by have := hq u; omega⟩
  invFun u := Sum.elim Subtype.val Subtype.val u
  left_inv u := by by_cases h : lev u < q <;> simp [h]
  right_inv u := by
    rcases u with u | u
    · simp [u.property]
    · have hh : ¬lev u.val < q := by rw [u.property]; omega
      simp [hh]

 theorem exact_left_top_count {U : Type*} [Fintype U] (lev : U → ℕ)
    (q : ℕ) (hq : ∀ u, lev u ≤ q) :
    Fintype.card U = Fintype.card {u : U // lev u < q} +
      Fintype.card {u : U // lev u = q} := by
  classical
  simpa using Fintype.card_congr (leftTopEquiv lev q hq)

/-- A selected pair for a value cannot collide with a representative of a
*different* value. This is the primitive disjointness for forced subtraction. -/
theorem representatives_disjoint {P A B : Type*} (sum : P → ℕ)
    (va : A → ℕ) (vb : B → ℕ) (pa : A → P) (pb : B → P)
    (ha : ∀ a, sum (pa a) = va a) (hb : ∀ b, sum (pb b) = vb b)
    (hd : ∀ a b, va a ≠ vb b) : ∀ a b, pa a ≠ pb b := by
  intro a b he
  apply hd a b
  calc
    va a = sum (pa a) := (ha a).symm
    _ = sum (pb b) := congrArg sum he
    _ = vb b := hb b

 theorem represented_sum_injective {P A : Type*} (sum : P → ℕ)
    (va : A → ℕ) (pa : A → P) (hva : Function.Injective va)
    (hrep : ∀ a, sum (pa a) = va a) : Function.Injective pa := by
  intro a b he
  apply hva
  rw [← hrep a, ← hrep b, he]

/-- All-bipartition induction uses this for EACH split, then takes the maximum.
The ordinary bound includes a one-unit floor defect; noncompression deletes it. -/
theorem ordinary_split_lower (i j a b z : ℤ)
    (hi : i ≤ a) (hj : j ≤ b) (hs : a + b - 1 ≤ z)
    (ha : a + 1 ≤ z) (hb : b + 1 ≤ z) :
    max (i + j - 1) (max (i + 1) (j + 1)) ≤ z := by
  omega

 theorem noncompressed_split_lower (i j a b z : ℤ)
    (hi : i ≤ a) (hj : j ≤ b) (hs : a + b ≤ z)
    (ha : a + 1 ≤ z) (hb : b + 1 ≤ z) :
    max (i + j) (max (i + 1) (j + 1)) ≤ z := by
  omega

 theorem shadow_interval (Q t d ad ac j k : ℤ)
    (hlo : ad ≤ j) (hcomp : ac ≤ k) (hfloor : j + k - 1 ≤ Q)
    (hincrement : j + (t - d) ≤ Q) :
    ad ≤ j ∧ j ≤ min (Q - t + d) (Q - ac + 1) := by omega

 theorem noncompressed_shadow_interval (Q t d ad ac j k : ℤ)
    (hlo : ad ≤ j) (hcomp : ac ≤ k) (hfloor : j + k ≤ Q)
    (hincrement : j + (t - d) ≤ Q) :
    ad ≤ j ∧ j ≤ min (Q - t + d) (Q - ac) := by omega

/-- Iteration itself is elementary; the independent one-step Hilbert theorem
and its concrete binomial convention are recorded as import duties. -/
def iterateGrowth (G : ℕ → ℕ → ℕ) (d : ℕ) : ℕ → ℕ → ℕ
  | 0, a => a
  | n + 1, a => G (d + n) (iterateGrowth G d n a)

 theorem growth_iteration (G : ℕ → ℕ → ℕ) (hG : ∀ j, Monotone (G j))
    (h : ℕ → ℕ) (d n : ℕ) (hstep : ∀ j, d ≤ j → h (j + 1) ≤ G j (h j)) :
    h (d + n) ≤ iterateGrowth G d n (h d) := by
  induction n with
  | zero => simp [iterateGrowth]
  | succ n ih =>
    exact (hstep (d + n) (by omega)).trans (hG (d + n) ih)

/-- A finite disjoint representative injection pays for forced compressed
values once and simultaneously reserves every noncompressed representative. -/
theorem sum_representative_injective {A B P : Type*} (pa : A → P) (pb : B → P)
    (ha : Function.Injective pa) (hb : Function.Injective pb)
    (hd : ∀ a b, pa a ≠ pb b) : Function.Injective (Sum.elim pa pb) := by
  intro x y h
  cases x with
  | inl a =>
    cases y with
    | inl a' => exact congrArg Sum.inl (ha h)
    | inr b => exact False.elim (hd a b h)
  | inr b =>
    cases y with
    | inl a => exact False.elim (hd a b h.symm)
    | inr b' => exact congrArg Sum.inr (hb h)

 theorem disjoint_representative_capacity {A B P : Type*}
    [Fintype A] [Fintype B] [Fintype P]
    (pa : A → P) (pb : B → P) (ha : Function.Injective pa)
    (hb : Function.Injective pb) (hd : ∀ a b, pa a ≠ pb b) :
    Fintype.card A + Fintype.card B ≤ Fintype.card P := by
  have h := Fintype.card_le_of_injective (Sum.elim pa pb)
    (sum_representative_injective pa pb ha hb hd)
  simpa using h

end Partials.WilfStructural.Shadow
