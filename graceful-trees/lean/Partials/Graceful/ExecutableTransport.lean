import Partials.Graceful.ExecutableAnchors

/-! The executable labeling on the independent named and reordered presentations. -/
namespace Partials.Graceful.Executable
open ManuscriptPresentation

/-- Root-zero gracefulness stated directly with the actual parent endpoints. -/
def ParentGraceful {V : Type*} (Q : ℕ) (p : V → V) (r : V) (f : V → Fin (Q + 1)) : Prop :=
  Function.Bijective f ∧ f r = 0 ∧
  (∀ d : ℕ, (1 ≤ d ∧ d ≤ Q) ↔
    ∃ x : {x : V // x ≠ r}, Nat.dist (f (p x.val)).val (f x.val).val = d) ∧
  Function.Injective (fun x : {x : V // x ≠ r} =>
    Nat.dist (f (p x.val)).val (f x.val).val)

theorem parentGraceful_iff {u v : ℕ} (f : Vertex u v → Fin (q u v + 1)) :
    ParentGraceful (q u v) parent .root f ↔ RootZeroGraceful u v f := Iff.rfl

/-- Parent and root preserving maps transport both coverage and edge uniqueness. -/
theorem parentGraceful_transport {V W : Type*} {Q : ℕ} {p : V → V} {s : W → W}
    {r : V} {t : W} (e : V ≃ W) (hr : e r = t) (hp : ∀ x, e (p x) = s (e x))
    {f : W → Fin (Q + 1)} (hf : ParentGraceful Q s t f) :
    ParentGraceful Q p r (fun x => f (e x)) := by
  have hn : ∀ x, e x ≠ t ↔ x ≠ r := by
    intro x
    rw [← hr, e.injective.ne_iff]
  refine ⟨hf.1.comp e.bijective, by simpa [hr] using hf.2.1, ?_, ?_⟩
  · intro d
    constructor
    · intro hd
      obtain ⟨y, hy⟩ := (hf.2.2.1 d).mp hd
      refine ⟨⟨e.symm y.val, (hn _).mp (by simpa using y.property)⟩, ?_⟩
      simpa only [hp, e.apply_symm_apply] using hy
    · rintro ⟨x, hx⟩
      apply (hf.2.2.1 d).mpr
      refine ⟨⟨e x.val, (hn _).mpr x.property⟩, ?_⟩
      simpa only [hp] using hx
  · intro x y h
    apply Subtype.ext
    apply e.injective
    have he := hf.2.2.2 (a₁ := ⟨e x.val, (hn _).mpr x.property⟩)
      (a₂ := ⟨e y.val, (hn _).mpr y.property⟩) (by simpa only [hp] using h)
    exact congrArg Subtype.val he

def namedLabel (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    NamedVertex u v → Fin (q u v + 1) :=
  fun x => label u v hu hv (encode x)

theorem namedLabel_graceful (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    ParentGraceful (q u v) namedParent .root (namedLabel u v hu hv) :=
  parentGraceful_transport (namedEquiv u v) rfl encode_parent (label_graceful u v hu hv)

def orderedLabel (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star) :
    OrderedVertex u v τ → Fin (q u v + 1) :=
  fun x => namedLabel u v hu hv (orderEncode σ τ x)

theorem orderedLabel_graceful (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star) :
    ParentGraceful (q u v) (orderedParent σ τ) .root (orderedLabel u v hu hv σ τ) :=
  parentGraceful_transport (orderEquiv u v σ τ) rfl (orderEncode_parent σ τ)
    (namedLabel_graceful u v hu hv)

theorem namedLabel_eq_originalIso (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (x : NamedVertex u v) :
    namedLabel u v hu hv x = label u v hu hv (originalIso u v x) := rfl

theorem orderedLabel_eq_originalIso (u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (σ : Equiv.Perm Branch) (τ : Equiv.Perm Star) (x : OrderedVertex u v τ) :
    orderedLabel u v hu hv σ τ x = label u v hu hv (reorderedIso u v σ τ x) := rfl

/-- The returned executable function puts zero at the manuscript's unique centre. -/
theorem label_center_zero (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    (simpleGraph u v).diam = 6 ∧
      ∀ x, x ∈ (simpleGraph u v).center ↔ label u v hu hv x = 0 := by
  have hf := label_graceful u v hu hv
  refine ⟨diameter_six u v, ?_⟩
  intro x
  rw [center_eq_root, Set.mem_singleton_iff]
  constructor
  · rintro rfl
    exact hf.2.1
  · intro hx
    exact hf.1.1 (hx.trans hf.2.1.symm)

end Partials.Graceful.Executable
