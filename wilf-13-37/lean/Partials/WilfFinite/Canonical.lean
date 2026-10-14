import Partials.WilfFinite.PrefixModel

/-! Exact actual-conductor reconstruction. Primitive/order/DFS targets in the
later modules remain separate from this unconditional closure construction. -/
namespace Partials.WilfFinite.Prefix
open Partials.Interface

noncomputable def canonicalFromGenerators (c : ℕ) (G : List ℕ)
    (hc : 2≤c) (hgap : c-1 ∉ closureBelow c G) : Core.CanonicalState :=
  ⟨c, {
    left := closureBelow c G
    c_two := hc
    below := by intro x hx; exact ((mem_closureBelow c G x).1 hx).1
    zero := (mem_closureBelow c G 0).2 ⟨by omega,Generated.zero⟩
    gap := hgap
    closed := by
      intro x hx y hy hxy
      exact (mem_closureBelow c G (x+y)).2
        ⟨hxy,Generated.add ((mem_closureBelow c G x).1 hx).2
          ((mem_closureBelow c G y).1 hy).2⟩ }⟩

theorem reconstructed_key (c : ℕ) (G : List ℕ) (hc : 2≤c)
    (hgap : c-1 ∉ closureBelow c G) :
    Core.key (canonicalFromGenerators c G hc hgap) = (c,closureBelow c G) := rfl

theorem reconstructed_membership (c : ℕ) (G : List ℕ) (hc : 2≤c)
    (hgap : c-1 ∉ closureBelow c G) (x : ℕ) :
    x ∈ (Core.semigroup (canonicalFromGenerators c G hc hgap)).carrier ↔ Member c G x := by
  change (x ∈ closureBelow c G ∨ c≤x) ↔ (Generated G x ∨ c≤x)
  constructor
  · rintro (h | h)
    · exact Or.inl ((mem_closureBelow c G x).1 h).2
    · exact Or.inr h
  · rintro (h | h)
    · by_cases hxc : x<c
      · exact Or.inl ((mem_closureBelow c G x).2 ⟨hxc,h⟩)
      · exact Or.inr (by omega)
    · exact Or.inr h

theorem reconstructed_actual_conductor (c : ℕ) (G : List ℕ) (hc : 2≤c)
    (hgap : c-1 ∉ closureBelow c G) :
    IsConductor (Core.semigroup (canonicalFromGenerators c G hc hgap)) c :=
  Core.actual_conductor _

theorem reconstructed_decomposition (c : ℕ) (G : List ℕ) (hc : 2≤c)
    (hgap : c-1 ∉ closureBelow c G) (x : ℕ) :
    IsDecomposable (Core.semigroup (canonicalFromGenerators c G hc hgap)) x ↔
      Decomposable c G x := by
  constructor
  · rintro ⟨u,v,hu,hv,huS,hvS,hx⟩
    exact ⟨u,v,hu,hv,(reconstructed_membership c G hc hgap u).1 huS,
      (reconstructed_membership c G hc hgap v).1 hvS,hx⟩
  · rintro ⟨u,v,hu,hv,huS,hvS,hx⟩
    exact ⟨u,v,hu,hv,(reconstructed_membership c G hc hgap u).2 huS,
      (reconstructed_membership c G hc hgap v).2 hvS,hx⟩

theorem reconstructed_primitive (c : ℕ) (G : List ℕ) (hc : 2≤c)
    (hgap : c-1 ∉ closureBelow c G) (x : ℕ) :
    IsPrimitive (Core.semigroup (canonicalFromGenerators c G hc hgap)) x ↔ Primitive c G x := by
  unfold IsPrimitive Primitive
  rw [reconstructed_membership,reconstructed_decomposition]

theorem failed_gap_permanent {c : ℕ} {G H : List ℕ}
    (hGH : ∀ g ∈ G, g ∈ H) (hbad : c-1 ∈ closureBelow c G) :
    c-1 ∈ closureBelow c H := closure_mono hGH hbad

theorem left_card_mono {c : ℕ} {G H : List ℕ}
    (hGH : ∀ g ∈ G, g ∈ H) :
    (closureBelow c G).card ≤ (closureBelow c H).card :=
  Finset.card_le_card (closure_mono hGH)

/-- The canonical gap condition is sufficient; no primitive list, gcd or
successful enumeration appears among the premises. -/
theorem canonical_characterization (c : ℕ) (L : Finset ℕ) (hc : 2≤c)
    (hbelow : ∀ x ∈ L, x<c) (hzero : 0∈L) (hgap : c-1∉L)
    (hclosed : ∀ x∈L, ∀ y∈L, x+y<c → x+y∈L) :
    ∃ a : Core.CanonicalState, Core.key a=(c,L) := by
  exact ⟨⟨c,⟨L,hc,hbelow,hzero,hgap,hclosed⟩⟩,rfl⟩

theorem canonical_identity_unique {a a' : Core.CanonicalState}
    (h : Core.key a=Core.key a') : a=a' := Core.key_injective h

noncomputable def ordinaryCanonical (c : ℕ) (hc : 2≤c) : Core.CanonicalState :=
  ⟨c, {
    left := {0}
    c_two := hc
    below := by
      intro x hx
      have hx0 : x=0 := by simpa using hx
      subst x
      omega
    zero := by simp
    gap := by
      intro h
      have hzero : c-1=0 := by simpa using h
      omega
    closed := by
      intro x hx y hy _
      have hx0 : x=0 := by simpa using hx
      have hy0 : y=0 := by simpa using hy
      subst x
      subst y
      simp }⟩

theorem ordinary_key (c : ℕ) (hc : 2≤c) :
    Core.key (ordinaryCanonical c hc)=(c,{0}) := rfl

theorem ordinary_membership (c : ℕ) (hc : 2≤c) (x : ℕ) :
    x∈(Core.semigroup (ordinaryCanonical c hc)).carrier ↔ x=0 ∨ c≤x := by
  change (x∈({0} : Finset ℕ) ∨ c≤x) ↔ x=0 ∨ c≤x
  simp

noncomputable def multiplicityCandidates (a : Core.CanonicalState) : Finset ℕ :=
  (Core.left a).erase 0 ∪ {Core.conductor a}

theorem multiplicityCandidates_nonempty (a : Core.CanonicalState) :
    (multiplicityCandidates a).Nonempty := by
  classical
  exact ⟨Core.conductor a,by simp [multiplicityCandidates]⟩

noncomputable def reconstructedMultiplicity (a : Core.CanonicalState) : ℕ :=
  (multiplicityCandidates a).min' (multiplicityCandidates_nonempty a)

/-- This least-value proof uses the complete L and the full tail. P4 checks the
actual pinned Finset.min' API; it assumes no successful traversal. -/
theorem reconstructedMultiplicity_spec (a : Core.CanonicalState) :
    IsMultiplicity (Core.semigroup a) (reconstructedMultiplicity a) := by
  classical
  have hmem : reconstructedMultiplicity a ∈ multiplicityCandidates a :=
    Finset.min'_mem _ _
  have hc : 2≤Core.conductor a := a.2.c_two
  have hpos : 0<reconstructedMultiplicity a := by
    rcases Finset.mem_union.mp hmem with hl | ht
    · have := (Finset.mem_erase.mp hl).1
      omega
    · have heq : reconstructedMultiplicity a=Core.conductor a := by simpa using ht
      omega
  have hS : reconstructedMultiplicity a ∈ (Core.semigroup a).carrier := by
    change reconstructedMultiplicity a ∈ Core.left a ∨ Core.conductor a≤reconstructedMultiplicity a
    rcases Finset.mem_union.mp hmem with hl | ht
    · exact Or.inl (Finset.mem_erase.mp hl).2
    · have heq : reconstructedMultiplicity a=Core.conductor a := by simpa using ht
      exact Or.inr (by omega)
  refine ⟨hpos,hS,?_⟩
  intro n hn hnS
  change n∈Core.left a ∨ Core.conductor a≤n at hnS
  rcases hnS with hl | ht
  · exact Finset.min'_le _ n (Finset.mem_union.mpr (Or.inl
      (Finset.mem_erase.mpr ⟨by omega,hl⟩)))
  · have hmin : reconstructedMultiplicity a≤Core.conductor a :=
      Finset.min'_le _ _ (by simp [multiplicityCandidates])
    omega

end Partials.WilfFinite.Prefix
