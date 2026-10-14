import Partials.WilfFinite.Primitives

/-! Transition lemmas are proved from positive generator expressions and the
actual missing member a. A child certificate is not assumed as a headline. -/
namespace Partials.WilfFinite.Prefix
open Partials.Interface

theorem member_below {c : ℕ} {G : List ℕ} {x : ℕ}
    (hx : Member c G x) (hxc : x<c) : Generated G x := by
  rcases hx with hx | hx
  · exact hx
  · omega

theorem state_membership (s : PrefixState) (x : ℕ) :
    x∈(Core.semigroup s.canonical).carrier ↔ Member (c s) s.G x := by
  change (x∈Core.left s.canonical ∨ c s≤x) ↔ (Generated s.G x ∨ c s≤x)
  rw [s.closure]
  constructor
  · rintro (h | h)
    · exact Or.inl ((mem_closureBelow _ _ _).1 h).2
    · exact Or.inr h
  · rintro (h | h)
    · by_cases hx : x<c s
      · exact Or.inl ((mem_closureBelow _ _ _).2 ⟨hx,h⟩)
      · exact Or.inr (by omega)
    · exact Or.inr h

theorem old_primitive_survives {c a g : ℕ} {G : List ℕ}
    (hg : Primitive c G g) (hgc : g<c) (hga : g<a) :
    Primitive c (G++[a]) g := by
  refine ⟨?_,hg.2.1,?_⟩
  · exact Or.inl (generated_append_old (member_below hg.1 hgc))
  · rintro ⟨u,v,hu,hv,huS,hvS,heq⟩
    have huG := generated_below_append (member_below huS (by omega)) (by omega)
    have hvG := generated_below_append (member_below hvS (by omega)) (by omega)
    exact hg.2.2 ⟨u,v,hu,hv,Or.inl huG,Or.inl hvG,heq⟩

theorem new_primitive {c a : ℕ} {G : List ℕ}
    (ha : 0<a) (hac : a<c) (hgap : a∉closureBelow c G) :
    Primitive c (G++[a]) a := by
  refine ⟨Or.inl (Generated.generator (by simp)),ha,?_⟩
  rintro ⟨u,v,hu,hv,huS,hvS,heq⟩
  have huG := generated_below_append (member_below huS (by omega)) (by omega)
  have hvG := generated_below_append (member_below hvS (by omega)) (by omega)
  exact hgap ((mem_closureBelow c G a).2 ⟨hac,by rw [heq]; exact Generated.add huG hvG⟩)

theorem raw_primitive_is_generator {c x : ℕ} {G : List ℕ}
    (hp : Primitive c G x) (hxc : x<c) : x∈G := by
  rcases generated_positive_cases (member_below hp.1 hxc) hp.2.1 with hg | hd
  · exact hg
  · obtain ⟨u,v,hu,hv,huG,hvG,heq⟩ := hd
    exact False.elim (hp.2.2 ⟨u,v,hu,hv,Or.inl huG,Or.inl hvG,heq⟩)

theorem appended_primitive_list_exact {c a : ℕ} {G : List ℕ}
    (hpos : 0<a) (hac : a<c) (hgap : a∉closureBelow c G)
    (hold : ∀ g∈G, Primitive c G g ∧ g<c ∧ g<a) (x : ℕ) :
    (Primitive c (G++[a]) x ∧ x<c) ↔ x∈G++[a] := by
  constructor
  · rintro ⟨hp,hxc⟩
    exact raw_primitive_is_generator hp hxc
  · intro hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨hp,hgc,hga⟩ := hold x hx
      exact ⟨old_primitive_survives hp hgc hga,hgc⟩
    · have heq : x=a := by simpa using hx
      subst x
      exact ⟨new_primitive hpos hac hgap,hac⟩

theorem closure_append_growth {c a : ℕ} {G : List ℕ}
    (hac : a<c) (hgap : a∉closureBelow c G) :
    (closureBelow c G).card+1≤(closureBelow c (G++[a])).card := by
  classical
  have hincl : insert a (closureBelow c G) ⊆ closureBelow c (G++[a]) := by
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · subst x
      exact (mem_closureBelow c (G++[a]) a).2
        ⟨hac,Generated.generator (by simp)⟩
    · exact closure_mono (by intro g hg; simp [hg]) hx
  have hcard := Finset.card_le_card hincl
  simpa [Finset.card_insert_of_notMem hgap] using hcard

theorem generated_membership_recurrence (G : List ℕ) {x : ℕ} (hpos : 0<x) :
    Generated G x ↔ ∃ g∈G, g≤x ∧ Generated G (x-g) := by
  constructor
  · intro hx
    obtain ⟨xs,hxs,hGxs⟩ := generated_list_expression hx
    cases xs with
    | nil => simp at hxs; omega
    | cons g gs =>
      have hg := hGxs g (by simp)
      have hgs : Generated G gs.sum :=
        generated_sum G gs (by intro y hy; exact hGxs y (by simp [hy]))
      have hsum : g+gs.sum=x := by simpa using hxs
      have heq : x-g=gs.sum := by omega
      exact ⟨g,hg,by omega,by rw [heq]; exact hgs⟩
  · rintro ⟨g,hg,hgx,hrem⟩
    have heq : g+(x-g)=x := by omega
    rw [←heq]
    exact Generated.add (Generated.generator hg) hrem

/-- Every actual Child keeps the fixed conductor and appends exactly one gap.
All remaining fields of t are reconstructed through its PrefixState definition.
There is no right-primitive update formula in this relation. -/
def Child (s t : PrefixState) (a : ℕ) : Prop :=
  c t=c s ∧ t.m=s.m ∧ t.G=s.G++[a] ∧ b s<a ∧ a<c s ∧ a∉Core.left s.canonical

theorem child_k_growth (s t : PrefixState) (a : ℕ) (h : Child s t a) :
    k s+1≤k t := by
  obtain ⟨hc,hm,hG,hba,hac,hgap⟩ := h
  have hgapRaw : a∉closureBelow (c s) s.G := by
    change a∉closureBelow (Core.conductor s.canonical) s.G
    rw [←s.closure]
    exact hgap
  unfold k Core.leftCount
  rw [s.closure,t.closure]
  change (closureBelow (c s) s.G).card+1≤(closureBelow (c t) t.G).card
  rw [hc,hG]
  exact closure_append_growth hac hgapRaw

theorem child_depth_fixed (s t : PrefixState) (a : ℕ) (h : Child s t a) : q t=q s := by
  obtain ⟨hc,hm,_,_,_,_⟩ := h
  change (c t+t.m-1)/t.m=(c s+s.m-1)/s.m
  rw [hc,hm]

inductive Descendant : PrefixState → PrefixState → Prop
  | refl (s : PrefixState) : Descendant s s
  | extend {s t z : PrefixState} {a : ℕ} :
      Descendant s t → Child t z a → Descendant s z

theorem descendant_k_mono {s t : PrefixState} (h : Descendant s t) : k s≤k t := by
  induction h with
  | refl => exact le_rfl
  | extend hpath hchild ih =>
    have hk := child_k_growth _ _ _ hchild
    omega

theorem descendant_conductor_fixed {s t : PrefixState} (h : Descendant s t) : c t=c s := by
  induction h with
  | refl => rfl
  | extend hpath hchild ih => exact hchild.1.trans ih

theorem descendant_depth_fixed {s t : PrefixState} (h : Descendant s t) : q t=q s := by
  induction h with
  | refl => rfl
  | extend hpath hchild ih => exact (child_depth_fixed _ _ _ hchild).trans ih

def ProperDescendant (s t : PrefixState) : Prop :=
  ∃ z a, Child s z a ∧ Descendant z t

/-- The substantive finite-list/multiplicity assembly still needs Lean
translation. The generator primitive result and cardinal growth above do not
assume this target. -/
def OrderedExtensionTarget : Prop := ∀ (s : PrefixState) (a : ℕ),
  b s<a → a<c s → a∉Core.left s.canonical →
  c s-1∉closureBelow (c s) (s.G++[a]) → ∃ t : PrefixState, Child s t a

def TransitionCountsTarget : Prop := ∀ (s t : PrefixState) (a : ℕ), Child s t a →
  k s+1≤k t ∧ ell t=ell s+1 ∧ q t=q s

theorem child_ell_growth (s t : PrefixState) (a : ℕ) (h : Child s t a) :
    ell t = ell s+1 := by
  rw [ell_list_length, ell_list_length, h.2.2.1]
  simp

theorem transition_counts : TransitionCountsTarget := by
  intro s t a h
  exact ⟨child_k_growth s t a h, child_ell_growth s t a h,
    child_depth_fixed s t a h⟩

theorem descendant_ell_mono {s t : PrefixState} (h : Descendant s t) : ell s≤ell t := by
  induction h with
  | refl => exact le_rfl
  | extend hpath hchild ih =>
    have he := child_ell_growth _ _ _ hchild
    omega

end Partials.WilfFinite.Prefix
