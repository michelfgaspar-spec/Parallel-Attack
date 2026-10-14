import Partials.WilfFinite.Core

/-! R10 authored this source blind; P4 compilation is tracked in the workspace.
The monoid is specified independently of
any traversal verdict. `Generated` permits repeated generators and has no gcd
condition. Its exact finite left closure, not a moving window, is retained. -/
namespace Partials.WilfFinite.Prefix
open Partials.Interface

inductive Generated (G : List ℕ) : ℕ → Prop
  | zero : Generated G 0
  | generator {g : ℕ} : g ∈ G → Generated G g
  | add {x y : ℕ} : Generated G x → Generated G y → Generated G (x+y)

def Member (c : ℕ) (G : List ℕ) (x : ℕ) : Prop := Generated G x ∨ c ≤ x
def Decomposable (c : ℕ) (G : List ℕ) (x : ℕ) : Prop :=
  ∃ u v : ℕ, 0 < u ∧ 0 < v ∧ Member c G u ∧ Member c G v ∧ x=u+v
def Primitive (c : ℕ) (G : List ℕ) (x : ℕ) : Prop :=
  Member c G x ∧ 0 < x ∧ ¬Decomposable c G x

noncomputable def closureBelow (c : ℕ) (G : List ℕ) : Finset ℕ := by
  classical
  exact (Finset.range c).filter (Generated G)

theorem mem_closureBelow (c : ℕ) (G : List ℕ) (x : ℕ) :
    x ∈ closureBelow c G ↔ x<c ∧ Generated G x := by
  classical
  simp [closureBelow]

theorem generated_mono {G H : List ℕ}
    (hGH : ∀ g ∈ G, g ∈ H) {x : ℕ} (hx : Generated G x) : Generated H x := by
  induction hx with
  | zero => exact Generated.zero
  | generator hg => exact Generated.generator (hGH _ hg)
  | add hu hv ihu ihv => exact Generated.add ihu ihv

theorem generated_sum (G xs : List ℕ) (h : ∀ x ∈ xs, x ∈ G) :
    Generated G xs.sum := by
  induction xs with
  | nil => exact Generated.zero
  | cons x xs ih =>
    have hx := Generated.generator (h x (by simp))
    have ht := ih (by intro y hy; exact h y (by simp [hy]))
    simpa using Generated.add hx ht

theorem generated_list_expression {G : List ℕ} {x : ℕ} (hx : Generated G x) :
    ∃ xs : List ℕ, xs.sum=x ∧ ∀ g ∈ xs, g ∈ G := by
  induction hx with
  | zero => exact ⟨[], by simp, by simp⟩
  | @generator g hg =>
    refine ⟨[g], by simp, ?_⟩
    intro y hy
    have heq : y=g := by simpa using hy
    simpa [heq] using hg
  | add hu hv ihu ihv =>
    obtain ⟨xs,hxs,hGxs⟩ := ihu
    obtain ⟨ys,hys,hGys⟩ := ihv
    refine ⟨xs++ys, by simp [hxs,hys], ?_⟩
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hGxs g hg
    · exact hGys g hg

theorem generated_append_old {G : List ℕ} {a x : ℕ}
    (hx : Generated G x) : Generated (G++[a]) x :=
  generated_mono (by intro g hg; simp [hg]) hx

/-- Appending a cannot create any member strictly below a. This is stronger
than primitive persistence and does not assume it. -/
theorem generated_below_append {G : List ℕ} {a x : ℕ}
    (hx : Generated (G++[a]) x) (hxa : x<a) : Generated G x := by
  revert hxa
  induction hx with
  | zero => intro _; exact Generated.zero
  | @generator g hg =>
    intro hxa
    rcases List.mem_append.mp hg with hg | hg
    · exact Generated.generator hg
    · have heq : g = a := by simpa using hg
      omega
  | add hu hv ihu ihv =>
    intro hxa
    exact Generated.add (ihu (by omega)) (ihv (by omega))

/-- Exact monoid decomposition after one append; x is the old-generator part.
Both inclusions are proved, so this is not a child-closure correctness premise. -/
theorem generated_append_iff (G : List ℕ) (a z : ℕ) :
    Generated (G++[a]) z ↔ ∃ x j : ℕ, Generated G x ∧ z=x+j*a := by
  constructor
  · intro hz
    induction hz with
    | zero => exact ⟨0,0,Generated.zero,by simp⟩
    | @generator g hg =>
      rcases List.mem_append.mp hg with hg | hg
      · exact ⟨_,0,Generated.generator hg,by simp⟩
      · have heq : g = a := by simpa using hg
        subst_vars
        exact ⟨0,1,Generated.zero,by simp⟩
    | add hu hv ihu ihv =>
      obtain ⟨x,j,hx,hu⟩ := ihu
      obtain ⟨y,k,hy,hv⟩ := ihv
      exact ⟨x+y,j+k,Generated.add hx hy,by rw [hu,hv]; ring⟩
  · rintro ⟨x,j,hx,rfl⟩
    have hj : Generated (G++[a]) (j*a) := by
      induction j with
      | zero => simpa using (Generated.zero : Generated (G++[a]) 0)
      | succ j ih =>
        simpa [Nat.succ_mul] using
          Generated.add ih (Generated.generator (by simp : a ∈ G++[a]))
    exact Generated.add (generated_append_old hx) hj

theorem closure_mono {c : ℕ} {G H : List ℕ}
    (h : ∀ g ∈ G, g ∈ H) : closureBelow c G ⊆ closureBelow c H := by
  intro x hx
  obtain ⟨hxc,hxG⟩ := (mem_closureBelow c G x).1 hx
  exact (mem_closureBelow c H x).2 ⟨hxc,generated_mono h hxG⟩

/-- A positive generated non-generator has a genuine two-positive-term split.
This uses the construction tree, not assumed primitive classification. -/
theorem generated_positive_cases {G : List ℕ} {x : ℕ}
    (hx : Generated G x) (hpos : 0<x) :
    x ∈ G ∨ ∃ u v : ℕ, 0<u ∧ 0<v ∧ Generated G u ∧ Generated G v ∧ x=u+v := by
  revert hpos
  induction hx with
  | zero => intro hpos; omega
  | generator hg => intro _; exact Or.inl hg
  | @add u v hu hv ihu ihv =>
    intro hpos
    by_cases huz : u=0
    · subst u
      simpa using ihv (by omega)
    · by_cases hvz : v=0
      · subst v
        simpa using ihu (by omega)
      · exact Or.inr ⟨u,v,by omega,by omega,hu,hv,rfl⟩

structure PrefixState where
  canonical : Core.CanonicalState
  G : List ℕ
  m : ℕ
  m_two : 2 ≤ m
  m_left : m < Core.conductor canonical
  multiplicity : IsMultiplicity (Core.semigroup canonical) m
  nonempty : G ≠ []
  increasing : G.Pairwise (fun x y => x<y)
  positive : ∀ g ∈ G, 0<g
  below : ∀ g ∈ G, g<Core.conductor canonical
  closure : Core.left canonical = closureBelow (Core.conductor canonical) G
  primitive_exact : ∀ x : ℕ, x ∈ G ↔
    IsPrimitive (Core.semigroup canonical) x ∧ x<Core.conductor canonical

def c (s : PrefixState) : ℕ := Core.conductor s.canonical
def k (s : PrefixState) : ℕ := Core.leftCount s.canonical
def b (s : PrefixState) : ℕ := s.G.foldl max 0
def label (s : PrefixState) : ℕ × List ℕ := (c s,s.G)

noncomputable def data (s : PrefixState) : Partials.WilfStructural.Foundation.Data where
  S := Core.semigroup s.canonical
  c := c s
  m := s.m
  conductor := Core.actual_conductor s.canonical
  multiplicity := s.multiplicity
  c_pos := by have := s.canonical.2.c_two; change 0<s.canonical.1; omega

noncomputable def q (s : PrefixState) : ℕ := Partials.WilfStructural.Foundation.depth (data s)
noncomputable def rho (s : PrefixState) : ℕ := Partials.WilfStructural.Foundation.rho (data s)
noncomputable def ell (s : PrefixState) : ℕ := Partials.WilfStructural.Foundation.ellP (data s)
noncomputable def r (s : PrefixState) : ℕ := Partials.WilfStructural.Foundation.rP (data s)
noncomputable def e (s : PrefixState) : ℕ := Partials.WilfStructural.Foundation.e (data s)
noncomputable def W0 (s : PrefixState) : ℤ := (k s : ℤ)*ell s+(q s : ℤ)*r s-c s
noncomputable def W (s : PrefixState) : ℤ := (k s : ℤ)*e s-c s
noncomputable def Delta (s : PrefixState) : ℤ := (k s : ℤ)+ell s+1-q s

end Partials.WilfFinite.Prefix
