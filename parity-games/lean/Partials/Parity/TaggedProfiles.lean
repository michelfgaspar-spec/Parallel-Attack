import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Partials.Parity.Model

/-! R7 blind explicit tagged decoder. Optional zero/one/two starts and exits
are handled by the grammar adapter, not invented extra coordinates. -/
namespace Partials.Parity.Tags

inductive RowTag (Exit : Type*)
  | bottom
  | top
  | finite (entries : List (Exit × Bool))
  deriving DecidableEq

def epsilon (b : Bool) : ℕ := if b then 1 else 0
def priorityOf (u : ℕ) (odd : Bool) : ℕ := 4 * u + epsilon odd

def FiniteEntryLegal (cap u : ℕ) (odd : Bool) : Prop :=
  u ≤ cap ∧ (odd = true → u ≠ 0)

def TagLegal {Exit : Type*} (exitOrder : Exit → ℕ) : RowTag Exit → Prop
  | .bottom | .top => True
  | .finite entries => entries ≠ [] ∧ entries.length ≤ 2 ∧
      entries.Pairwise (fun a b => exitOrder a.1 < exitOrder b.1)

def decodeRow {Exit : Type*} (tag : RowTag Exit) (levels : List ℕ) : Set (Outcome Exit) :=
  match tag with
  | .bottom => {.bottom}
  | .top => {.top}
  | .finite entries => {out | ∃ k < entries.length,
      ∃ o e, entries[k]? = some (o,e) ∧ levels[k]? = some
        ((levels.getD k 0)) ∧ out = .halt o (priorityOf (levels.getD k 0) e)}

def DecodeShape {Exit : Type*} (tag : RowTag Exit) (levels : List ℕ) : Prop :=
  match tag with
  | .bottom | .top => levels = []
  | .finite entries => levels.length = entries.length

theorem zero_even : priorityOf 0 false = 0 := by rfl
theorem odd_zero_forbidden (cap : ℕ) : ¬ FiniteEntryLegal cap 0 true := by
  simp [FiniteEntryLegal]
theorem numerical_level_separation {u v : ℕ} (h : u < v) (e f : Bool) :
    priorityOf u e < priorityOf v f := by
  cases e <;> cases f <;> simp [priorityOf,epsilon] <;> omega

structure ProfileTag (Start Exit : Type*) where
  row : Start → RowTag Exit
  coordinates : ℕ
  slot : (i : Start) → Fin (match row i with | .finite entries => entries.length | _ => 0) →
    Fin coordinates
  distinct_slots : Function.Injective (fun p :
    (Σ i : Start, Fin (match row i with | .finite entries => entries.length | _ => 0)) =>
      slot p.1 p.2)

def visibleCount {Start Exit : Type*} [Fintype Start] (tag : ProfileTag Start Exit) : ℕ :=
  ∑ i : Start, match tag.row i with | .finite entries => entries.length | _ => 0

theorem at_most_four_visible {Start Exit : Type*} [Fintype Start]
    (tag : ProfileTag Start Exit) (hstarts : Fintype.card Start ≤ 2)
    (hrows : ∀ i, (match tag.row i with | .finite entries => entries.length | _ => 0) ≤ 2) :
    visibleCount tag ≤ 4 := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset Start)) => hrows i)
  simp only [Finset.sum_const,Finset.card_univ,Nat.nsmul_eq_mul] at h
  unfold visibleCount
  omega

/- Exact projected-zone decoder still owes ordered exit identities, shape,
tag/level antichain correspondence, bijective coordinate assignment and
integral zero-anchor bounds. Nothing here is a compiler exactness witness. -/
end Partials.Parity.Tags
