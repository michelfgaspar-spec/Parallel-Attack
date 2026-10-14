import Partials.WilfFinite.Primary
import Mathlib.Data.Finset.Sort

/-! Original full interfaces retained as Prop definitions. P4 supplies selected
inhabitants separately below. Full PRIMARY exactness, seed/ordinary counts,
concrete codec/stream and large-tail combinatorial bridges remain open; proof
source and finite relational label semantics do not supply those missing facts. -/
namespace Partials.WilfFinite.Prefix
open Partials.Interface
open Partials.WilfStructural.Foundation

def PrimitiveGenerationTarget : Prop := ∀ (a : Core.CanonicalState) (x : ℕ),
  x∈Core.left a → ∃ xs : List ℕ, xs.sum=x ∧
    ∀ g∈xs, IsPrimitive (Core.semigroup a) g ∧ g<Core.conductor a

def SortedPrimitiveListTarget : Prop := ∀ a : Core.CanonicalState,
  ∃! G : List ℕ, G.Pairwise (fun x y => x<y) ∧
    (∀ x, x∈G ↔ IsPrimitive (Core.semigroup a) x ∧ x<Core.conductor a) ∧
    Core.left a=closureBelow (Core.conductor a) G

def SameConductorPrefixesTarget : Prop := ∀ (s : PrefixState) (i : ℕ),
  1 ≤ i → i ≤ s.G.length →
  c s-1∉closureBelow (c s) (s.G.take i) ∧
  ∃ a : Core.CanonicalState, Core.conductor a=c s ∧
    Core.left a=closureBelow (c s) (s.G.take i) ∧
    IsMultiplicity (Core.semigroup a) s.m

def ExactInvariantCountsTarget : Prop := ∀ s : PrefixState,
  ell s=s.G.length ∧ k s=(closureBelow (c s) s.G).card ∧
  q s=(c s+s.m-1)/s.m ∧ rho s=q s*s.m-c s ∧
  e s=ell s+r s ∧ W0 s=(k s : ℤ)*ell s+(q s : ℤ)*r s-c s ∧
  W s=(k s : ℤ)*e s-c s

def SeedExactTarget : Prop := ∀ s : PrefixState, s.G=[s.m] →
  k s=q s ∧ ell s=1 ∧ r s=s.m-1 ∧ W0 s=(rho s : ℤ) ∧ 0≤W0 s

def OrdinaryExactTarget : Prop := ∀ a : Core.CanonicalState,
  Core.left a={0} →
  let d := sourceData a
  d.m=d.c ∧ n d=1 ∧ depth d=1 ∧ ellP d=0 ∧ rP d=d.c ∧
  Partials.WilfStructural.Foundation.e d=d.c ∧
  Partials.WilfStructural.Foundation.W0 d=0 ∧ Partials.WilfStructural.Foundation.W d=0

def LabelInjectivityTarget : Prop := ∀ s t : PrefixState,
  Core.key s.canonical=Core.key t.canonical → label s=label t

def ChildMeasureTarget : Prop := ∀ (s t : PrefixState) (a : ℕ),
  Child s t a → measure t<measure s

def VisitedFiniteTarget : Prop := ∀ p : Core.Parameters,
  {l : ℕ×List ℕ | ∃ s, Visited p s ∧ label s=l}.Finite

/-- Includes c=2,...,C ordinary accounting and exactly one nonordinary
canonical prefix path. Mathematical W is reported, never used as a filter. -/
def PrimaryExactTarget : Prop := ∀ (p : Core.Parameters) (a : Core.CanonicalState),
  (∃ o∈primaryRecords p, outputKey o=Core.key a) ↔
    Core.InTarget p a ∧ Partials.WilfStructural.Foundation.W0 (sourceData a)<0

def PrimaryNoRepeatTarget : Prop := ∀ (p : Core.Parameters) (s t : PrefixState),
  Emits p s → Emits p t → Core.key s.canonical=Core.key t.canonical → label s=label t

def ReferenceSubsetTarget : Prop := ∀ (p : Core.Parameters),
  {key | ∃ o∈primaryRecords p, outputKey o=key} =
    {key | ∃ a : Core.CanonicalState, Core.InTarget p a ∧
      Partials.WilfStructural.Foundation.W0 (sourceData a)<0 ∧ Core.key a=key}

/-- Required preservation premise for a specified implementation. Equality of
its decoded states with the canonical transition must be supplied separately;
no implementation or machine width is selected here. -/
def ImplementationCorrespondenceDuty (Machine : Type) (decode : Machine → Core.CanonicalState)
    (step : Machine → ℕ → Machine) : Prop :=
  ∀ (s t : PrefixState) (a : ℕ) (machine : Machine),
    decode machine=s.canonical → Child s t a → decode (step machine a)=t.canonical

/-- Set semantics only. Binary-digit and fixed-width implementations need the
separate representation author and an actual preservation proof. -/
def ChildSetSemanticsTarget : Prop := ∀ (c a : ℕ) (G : List ℕ) (x : ℕ),
  x∈closureBelow c (G++[a]) ↔
    x<c ∧ ∃ y∈closureBelow c G, ∃ j : ℕ, x=y+j*a

/-- U49 belongs to the different residual Cover/Pack procedure. There is no
implication from PRIMARY exactness to closure of those profile/box loops. -/
def HistoricalCoverControlFlowDuty : Prop :=
  ∀ (n : ℕ) (branches : Finset ℕ) (closed unresolved : ℕ → Prop),
  14≤n → n≤37 → (∀ b∈branches, closed b ∨ unresolved b) →
  (∀ b∈branches, ¬unresolved b) → ∀ b∈branches, closed b

/-- Strong induction supplies actual expressions in the complete left
primitive set; no traversal, finite-run or factorization premise is used. -/
theorem primitive_generation : PrimitiveGenerationTarget := by
  classical
  intro a x
  induction x using Nat.strong_induction_on with
  | h x ih =>
    intro hx
    by_cases hx0 : x=0
    · subst x
      exact ⟨[], by simp, by simp⟩
    have hxc : x<Core.conductor a := a.2.below x hx
    have hxS : x∈(Core.semigroup a).carrier := by
      change x∈Core.left a ∨ Core.conductor a≤x
      exact Or.inl hx
    by_cases hp : IsPrimitive (Core.semigroup a) x
    · refine ⟨[x], by simp, ?_⟩
      intro g hg
      have heq : g=x := by simpa using hg
      subst g
      exact ⟨hp,hxc⟩
    have hd : IsDecomposable (Core.semigroup a) x := by
      by_contra hnd
      exact hp ⟨hxS, by omega, hnd⟩
    obtain ⟨u,v,hu,hv,huS,hvS,heq⟩ := hd
    have huL : u∈Core.left a := by
      change u∈Core.left a ∨ Core.conductor a≤u at huS
      rcases huS with h | h
      · exact h
      · omega
    have hvL : v∈Core.left a := by
      change v∈Core.left a ∨ Core.conductor a≤v at hvS
      rcases hvS with h | h
      · exact h
      · omega
    obtain ⟨xs,hxs,hpxs⟩ := ih u (by omega) huL
    obtain ⟨ys,hys,hpys⟩ := ih v (by omega) hvL
    refine ⟨xs++ys, by simp [hxs,hys,heq], ?_⟩
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hpxs g hg
    · exact hpys g hg

theorem sorted_primitive_list : SortedPrimitiveListTarget := by
  classical
  intro a
  let G := (leftPrimitives (sourceData a)).sort
  have hsort : G.Pairwise (fun x y => x<y) :=
    (leftPrimitives (sourceData a)).sortedLT_sort.pairwise
  have hexact : ∀ x, x∈G ↔ IsPrimitive (Core.semigroup a) x ∧ x<Core.conductor a := by
    intro x
    simp only [G, Finset.mem_sort, leftPrimitives, Finset.mem_filter, mem_P]
    rfl
  have hclosure : Core.left a=closureBelow (Core.conductor a) G := by
    ext x
    constructor
    · intro hx
      obtain ⟨xs,hxs,hpxs⟩ := primitive_generation a x hx
      refine (mem_closureBelow _ _ _).2 ⟨a.2.below x hx, ?_⟩
      rw [←hxs]
      exact generated_sum G xs (by intro g hg; exact (hexact g).2 (hpxs g hg))
    · intro hx
      obtain ⟨hxc,hG⟩ := (mem_closureBelow _ _ _).1 hx
      have hxS : x∈(Core.semigroup a).carrier := by
        clear hx hxc
        induction hG with
        | zero => exact (Core.semigroup a).carrier.zero_mem
        | generator hg => exact ((hexact _).1 hg).1.1
        | add hu hv ihu ihv => exact (Core.semigroup a).carrier.add_mem ihu ihv
      change x∈Core.left a ∨ Core.conductor a≤x at hxS
      rcases hxS with h | h
      · exact h
      · omega
  refine ⟨G, ⟨hsort,hexact,hclosure⟩, ?_⟩
  intro H hH
  exact hH.1.eq_of_mem_iff hsort (by intro x; exact (hH.2.1 x).trans (hexact x).symm)

theorem exact_invariant_counts : ExactInvariantCountsTarget := by
  intro s
  refine ⟨ell_list_length s, ?_, rfl, rfl, full_embedding_dimension s, rfl, rfl⟩
  unfold k Core.leftCount
  rw [s.closure]
  rfl

theorem label_injectivity : LabelInjectivityTarget := by
  intro s t hkey
  have hcan := Core.key_injective hkey
  have hG : s.G=t.G := s.increasing.eq_of_mem_iff t.increasing (by
    intro x
    rw [s.primitive_exact, t.primitive_exact, hcan])
  simp only [label, c, hcan, hG]

/-- This is the exact relational label target. It establishes equality of
labels for equal canonical keys, without claiming a stream occurrence count. -/
theorem primary_no_repeat_labels : PrimaryNoRepeatTarget := by
  intro p s t hs ht hkey
  exact label_injectivity s t hkey

theorem child_set_semantics : ChildSetSemanticsTarget := by
  intro c a G x
  constructor
  · intro hx
    obtain ⟨hxc,hgen⟩ := (mem_closureBelow c (G++[a]) x).1 hx
    obtain ⟨y,j,hy,heq⟩ := (generated_append_iff G a x).1 hgen
    refine ⟨hxc,y,(mem_closureBelow c G y).2 ⟨by omega,hy⟩,j,heq⟩
  · rintro ⟨hxc,y,hy,j,heq⟩
    exact (mem_closureBelow c (G++[a]) x).2 ⟨hxc,
      (generated_append_iff G a x).2 ⟨y,j,((mem_closureBelow c G y).1 hy).2,heq⟩⟩

theorem foldl_max_below (G : List ℕ) (t a : ℕ) (ht : t<a)
    (hG : ∀ g∈G, g<a) : G.foldl max t<a := by
  induction G generalizing t with
  | nil => exact ht
  | cons g G ih =>
    apply ih (max t g)
    · exact max_lt ht (hG g (by simp))
    · intro x hx
      exact hG x (by simp [hx])

theorem state_max_below (s : PrefixState) : b s<c s := by
  have hc := s.canonical.2.c_two
  change 2≤Core.conductor s.canonical at hc
  exact foldl_max_below s.G 0 (c s) (by change 0<Core.conductor s.canonical; omega)
    s.below

theorem child_measure : ChildMeasureTarget := by
  intro s t a hchild
  obtain ⟨hc,hm,hG,hba,hac,hgap⟩ := hchild
  have hbale : s.G.foldl max 0≤a := Nat.le_of_lt hba
  have hbt : b t=a := by
    simp [b, hG, List.foldl_append, max_eq_right hbale]
  unfold measure
  rw [hc,hbt]
  omega

theorem visited_conductor_bound (p : Core.Parameters) (s : PrefixState)
    (h : Visited p s) : c s≤p.C := by
  induction h with
  | seed hs => exact hs.1
  | child hvisit hk hprod hreach hchild ih => simpa [hchild.1] using ih

/-- Finiteness of the abstract visited label set. This does not introduce an
executable traversal or establish the number of occurrences in an output stream. -/
theorem visited_finite : VisitedFiniteTarget := by
  classical
  intro p
  let labels : Finset (ℕ×List ℕ) :=
    ((Finset.range (p.C+1)) ×ˢ (Finset.range p.C).powerset).image
      (fun z : ℕ×Finset ℕ => (z.1,z.2.sort))
  apply labels.finite_toSet.subset
  rintro l ⟨s,hvisit,rfl⟩
  have hc := visited_conductor_bound p s hvisit
  have hGsub : s.G.toFinset⊆Finset.range p.C := by
    intro g hg
    have hgb := s.below g (List.mem_toFinset.mp hg)
    exact Finset.mem_range.mpr (by change g<c s at hgb; omega)
  have hsorted : s.G.toFinset.sort=s.G :=
    s.G.toFinset.sortedLT_sort.pairwise.eq_of_mem_iff s.increasing (by simp)
  apply Finset.mem_image.mpr
  refine ⟨(c s,s.G.toFinset), ?_, ?_⟩
  · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by omega),
      Finset.mem_powerset.mpr hGsub⟩
  · simpa [label] using congrArg (fun G => (c s,G)) hsorted

theorem residual_closed_only_after_all_branches (n : ℕ) (branches : Finset ℕ)
    (closed unresolved : ℕ → Prop)
    (hall : ∀ b∈branches, closed b ∨ unresolved b)
    (hno : ∀ b∈branches, ¬unresolved b) : ∀ b∈branches, closed b := by
  intro b hb
  rcases hall b hb with hc | hu
  · exact hc
  · exact False.elim (hno b hb hu)

end Partials.WilfFinite.Prefix
