import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Defs

/-! Blind R1 draft, adapted from the historical finite-certificate module.
Paper-specific decoding, exact data acceptance and complete domain coverage
remain explicit obligations. These conditional lemmas close no paper claim. -/
namespace Partials

def ValidOn {α : Type*} (domain : Finset α) (P : α → Prop) : Prop :=
  ∀ x ∈ domain, P x

def checkFinite {α : Type*} [DecidableEq α] (domain : Finset α)
    (P : α → Prop) [DecidablePred P] : Bool := by
  letI : Decidable (ValidOn domain P) :=
    inferInstanceAs (Decidable (∀ x ∈ domain, P x))
  exact decide (ValidOn domain P)

theorem checkFinite_sound {α : Type*} [DecidableEq α] (domain : Finset α)
    (P : α → Prop) [DecidablePred P]
    (h : checkFinite domain P = true) : ValidOn domain P := by
  simpa [checkFinite] using h

def CoversBy {α : Type*} (domain : Finset α) (pieces : List (Finset α)) : Prop :=
  ∀ x ∈ domain, ∃ piece ∈ pieces, x ∈ piece

theorem validOn_of_covered_pieces {α : Type*} (domain : Finset α)
    (pieces : List (Finset α)) (P : α → Prop)
    (hcover : CoversBy domain pieces)
    (hpiece : ∀ piece ∈ pieces, ValidOn piece P) : ValidOn domain P := by
  intro x hx
  obtain ⟨piece, hmember, hinside⟩ := hcover x hx
  exact hpiece piece hmember x hinside

/-- Exact decoding obligations are supplied independently of checker success. -/
structure FiniteEncoding (Code Object : Type*) [Fintype Code] where
  decode : Code → Object
  injective : Function.Injective decode
  surjective : Function.Surjective decode

end Partials
