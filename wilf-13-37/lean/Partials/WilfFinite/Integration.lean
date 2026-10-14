import Partials.WilfFinite.Core
import Partials.WilfFinite.PrefixTransition
import Partials.WilfFinite.ForestSoundness

/-! Root supporting bridge from an actual numerical semigroup to the shared
canonical ground object. Source is blind and uncompiled; primitive/traversal,
forest, residual and data adapters remain separately open. -/
namespace Partials.WilfFinite.Integration
open Partials.Interface
open Partials.WilfStructural.Foundation

theorem conductor_one_impossible (S : NumericalSemigroup)
    (h : IsConductor S 1) : False := by
  obtain ⟨x, hx, hgap⟩ := h.2 0 (by omega)
  apply hgap
  by_cases hz : x = 0
  · subst x
    exact S.carrier.zero_mem
  · exact h.1 x (by omega)

theorem positive_conductor_two (S : NumericalSemigroup) (c : ℕ)
    (h : IsConductor S c) (hc : 0 < c) : 2 ≤ c := by
  by_contra hs
  have he : c = 1 := by omega
  subst c
  exact conductor_one_impossible S h

theorem zero_conductor_membership (S : NumericalSemigroup)
    (h : IsConductor S 0) (x : ℕ) : x ∈ S.carrier :=
  h.1 x (Nat.zero_le x)

theorem zero_conductor_left_count (S : NumericalSemigroup) :
    (LeftBelow S 0).card = 0 := by
  simp [LeftBelow]

noncomputable def canonicalGround (S : NumericalSemigroup) (c : ℕ)
    (h : IsConductor S c) (hc : 2 ≤ c) : CanonicalLeft c := by
  classical
  exact {
    left := LeftBelow S c
    c_two := hc
    below := by
      intro x hx
      exact Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    zero := Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), S.carrier.zero_mem⟩
    gap := by
      intro hx
      have hs : c - 1 ∈ S.carrier := (Finset.mem_filter.mp hx).2
      obtain ⟨x, hlow, hgap⟩ := h.2 (c - 1) (by omega)
      by_cases hxc : x < c
      · have he : x = c - 1 := by omega
        apply hgap
        simpa only [he] using hs
      · exact hgap (h.1 x (by omega))
    closed := by
      intro x hx y hy hxy
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hxy,
        S.carrier.add_mem (Finset.mem_filter.mp hx).2
          (Finset.mem_filter.mp hy).2⟩ }

noncomputable def groundState (S : NumericalSemigroup) (c : ℕ)
    (h : IsConductor S c) (hc : 0 < c) : Core.CanonicalState :=
  ⟨c, canonicalGround S c h (positive_conductor_two S c h hc)⟩

theorem ground_membership (S : NumericalSemigroup) (c : ℕ)
    (h : IsConductor S c) (hc : 0 < c) (x : ℕ) :
    x ∈ (Core.semigroup (groundState S c h hc)).carrier ↔ x ∈ S.carrier := by
  classical
  change (x ∈ LeftBelow S c ∨ c ≤ x) ↔ x ∈ S.carrier
  constructor
  · rintro (hl | ht)
    · exact (Finset.mem_filter.mp hl).2
    · exact h.1 x ht
  · intro hs
    by_cases hx : x < c
    · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hx, hs⟩)
    · exact Or.inr (by omega)

/-- The two independently authored generator semantics agree by induction;
this does not assume forest or PRIMARY completeness. -/
theorem prefix_to_forest_generated {G : List ℕ} {x : ℕ}
    (h : Prefix.Generated G x) : Forest.Generated G x := by
  induction h with
  | zero => exact Forest.Generated.zero
  | generator hg =>
    simpa using Forest.Generated.add Forest.Generated.zero hg
  | add hx hy ihx ihy => exact Forest.generated_add ihx ihy

theorem forest_to_prefix_generated {G : List ℕ} {x : ℕ}
    (h : Forest.Generated G x) : Prefix.Generated G x := by
  induction h with
  | zero => exact Prefix.Generated.zero
  | add hx hg ih => exact Prefix.Generated.add ih (Prefix.Generated.generator hg)

theorem generated_agree (G : List ℕ) (x : ℕ) :
    Prefix.Generated G x ↔ Forest.Generated G x :=
  ⟨prefix_to_forest_generated, forest_to_prefix_generated⟩

def forestLabel (s : Prefix.PrefixState) : Forest.Label :=
  ⟨Prefix.c s, s.m, s.G⟩

theorem independent_closures_agree (s : Prefix.PrefixState) :
    Forest.rebuiltLeft (forestLabel s) = Prefix.closureBelow (Prefix.c s) s.G := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨hxc, hxg⟩ := (Forest.mem_rebuiltLeft (forestLabel s) x).1 hx
    exact (Prefix.mem_closureBelow (Prefix.c s) s.G x).2
      ⟨hxc, forest_to_prefix_generated hxg⟩
  · intro hx
    obtain ⟨hxc, hxg⟩ := (Prefix.mem_closureBelow (Prefix.c s) s.G x).1 hx
    exact (Forest.mem_rebuiltLeft (forestLabel s) x).2
      ⟨hxc, prefix_to_forest_generated hxg⟩

theorem independent_left_agrees (s : Prefix.PrefixState) :
    Forest.rebuiltLeft (forestLabel s) = Core.left s.canonical := by
  rw [independent_closures_agree, s.closure]
  rfl

theorem forestLabel_canonical (s : Prefix.PrefixState) :
    Forest.CanonicalLabel (forestLabel s) := by
  refine ⟨s.canonical.2.c_two, ?_⟩
  rw [independent_left_agrees]
  exact s.canonical.2.gap

theorem reconstructed_state_agrees (s : Prefix.PrefixState) :
    Forest.canonicalState (forestLabel s) (forestLabel_canonical s) = s.canonical := by
  apply Core.key_injective
  rw [Forest.canonicalState_key, independent_left_agrees]
  rfl

theorem forestLabel_multiplicity (s : Prefix.PrefixState) :
    Forest.MultiplicityCorrect (forestLabel s) (forestLabel_canonical s) := by
  change IsMultiplicity
    (Core.semigroup (Forest.canonicalState (forestLabel s) (forestLabel_canonical s))) s.m
  rw [reconstructed_state_agrees]
  exact s.multiplicity

theorem independent_primitives_agree (s : Prefix.PrefixState) :
    Forest.rebuiltPrimitives (forestLabel s) = P (Prefix.data s) := by
  classical
  ext x
  rw [Forest.all_primitive_test (forestLabel s) (forestLabel_canonical s)
    (forestLabel_multiplicity s), mem_P]
  change IsPrimitive
    (Core.semigroup (Forest.canonicalState (forestLabel s) (forestLabel_canonical s))) x ↔
    IsPrimitive (Core.semigroup s.canonical) x
  rw [reconstructed_state_agrees]

theorem independent_full_embedding_agrees (s : Prefix.PrefixState) :
    (Forest.reconstruct (forestLabel s)).e = Prefix.e s := by
  rw [Forest.full_primitive_partition, independent_primitives_agree]
  rfl

end Partials.WilfFinite.Integration
