import Partials.Graceful.Model
import Mathlib.Data.Finset.Sort

/-! Graph-level pair transfer and star split, included in the project build.

The hypotheses below describe pendant vertices, distinct attachment sites,
old incidences, and the paper's label equations. No operation theorem assumes
that the new graph is a tree or that its differences are a permutation.
-/

namespace Partials.Graceful.Operations

open Partials.Interface

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- One edge for each vertex other than the root. -/
abbrev RootEdge (T : RootedParentTree V) := {v : V // v ≠ T.root}

/-- A pendant vertex has no nonroot child in the parent presentation. -/
def Pendant (T : RootedParentTree V) (x : V) : Prop :=
  x ≠ T.root ∧ ∀ v, v ≠ T.root → T.parent v ≠ x

/-- The parent presentation supplies a simple finite graph on the same vertices. -/
def parentGraph (T : RootedParentTree V) : FiniteEdgeGraph V (RootEdge T) where
  ends e := (T.parent e.val, e.val)
  nonloop := by
    intro e h
    change T.parent e.val = e.val at h
    have hd := T.parent_depth e.val e.property
    rw [h] at hd
    exact (Nat.lt_irrefl _) hd
  unique_edge := by
    intro e f h
    rcases h with h | ⟨h₁, h₂⟩
    · exact Subtype.ext (congrArg Prod.snd h)
    · have he := T.parent_depth e.val e.property
      have hf := T.parent_depth f.val f.property
      change T.parent e.val = f.val at h₁
      change e.val = T.parent f.val at h₂
      rw [h₁] at he
      rw [← h₂] at hf
      omega

theorem parentGraph_compatible (T : RootedParentTree V) :
    ParentCompatible (parentGraph T) T := by
  intro a b
  constructor
  · rintro ⟨e, he⟩
    have hb : e.val = b := congrArg Prod.snd he
    have ha : T.parent e.val = a := congrArg Prod.fst he
    exact ⟨by simpa [hb] using e.property, by simpa [hb] using ha⟩
  · rintro ⟨hb, ha⟩
    exact ⟨⟨b, hb⟩, Prod.ext ha rfl⟩

/-- Strict depth decrease gives a path to the root; this is not a connectivity
assumption smuggled into an operation. -/
theorem parent_reaches_root (T : RootedParentTree V) (v : V) :
    ∃ n : ℕ, (T.parent^[n]) v = T.root := by
  have h : ∀ n : ℕ, ∀ w : V, T.depth w = n →
      ∃ k : ℕ, (T.parent^[k]) w = T.root := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hw
      by_cases hroot : w = T.root
      · exact ⟨0, by simpa [hroot]⟩
      · have hlt : T.depth (T.parent w) < n := by
          simpa [hw] using T.parent_depth w hroot
        obtain ⟨k, hk⟩ := ih (T.depth (T.parent w)) hlt (T.parent w) rfl
        refine ⟨k + 1, ?_⟩
        simpa only [Function.iterate_succ_apply] using hk
  exact h (T.depth v) v rfl

/-- Change precisely two parent incidences. -/
def twoParent (T : RootedParentTree V) (x y a b : V) (v : V) : V :=
  if v = x then a else if v = y then b else T.parent v

/-- Assign new depths to precisely the same two vertices. -/
def twoDepth (T : RootedParentTree V) (x y : V) (dx dy : ℕ) (v : V) : ℕ :=
  if v = x then dx else if v = y then dy else T.depth v

theorem twoParent_unchanged (T : RootedParentTree V) (x y a b v : V)
    (hvx : v ≠ x) (hvy : v ≠ y) :
    twoParent T x y a b v = T.parent v := by
  simp [twoParent, hvx, hvy]

/-- Reattaching two pendant vertices at another vertex gives a parent tree.
The old common parent is unnecessary for this structural result. -/
def pairTransferTree (T : RootedParentTree V) (x y p : V)
    (hx : Pendant T x) (hy : Pendant T y) (hxy : x ≠ y)
    (hpx : p ≠ x) (hpy : p ≠ y) : RootedParentTree V where
  root := T.root
  parent := twoParent T x y p p
  depth := twoDepth T x y (T.depth p + 1) (T.depth p + 1)
  root_parent := by
    simpa [twoParent, Ne.symm hx.1, Ne.symm hy.1] using T.root_parent
  root_depth := by
    simpa [twoDepth, Ne.symm hx.1, Ne.symm hy.1] using T.root_depth
  parent_depth := by
    intro v hv
    by_cases hvx : v = x
    · subst v
      simp [twoParent, twoDepth, hpx, hpy]
    · by_cases hvy : v = y
      · subst v
        simp [twoParent, twoDepth, Ne.symm hxy, hpx, hpy]
      · have hpvx := hx.2 v hv
        have hpvy := hy.2 v hv
        simpa [twoParent, twoDepth, hvx, hvy, hpvx, hpvy]
          using T.parent_depth v hv

theorem pairTransfer_root (T : RootedParentTree V) (x y p : V)
    (hx : Pendant T x) (hy : Pendant T y) (hxy : x ≠ y)
    (hpx : p ≠ x) (hpy : p ≠ y) :
    (pairTransferTree T x y p hx hy hxy hpx hpy).root = T.root := rfl

/-- Other pendant vertices, and the moved leaves themselves, stay pendant
unless they are the new attachment vertex. This supplies the induction
invariant for transfers on disjoint reflection pairs. -/
theorem pairTransfer_preservesPendant (T : RootedParentTree V) (x y p z : V)
    (hx : Pendant T x) (hy : Pendant T y) (hxy : x ≠ y)
    (hpx : p ≠ x) (hpy : p ≠ y) (hz : Pendant T z) (hpz : p ≠ z) :
    Pendant (pairTransferTree T x y p hx hy hxy hpx hpy) z := by
  refine ⟨hz.1, ?_⟩
  intro v hv
  by_cases hvx : v = x
  · simpa [pairTransferTree, twoParent, hvx] using hpz
  · by_cases hvy : v = y
    · simpa [pairTransferTree, twoParent, hvx, hvy] using hpz
    · simpa [pairTransferTree, twoParent, hvx, hvy] using hz.2 v hv

theorem pairTransfer_parent_unchanged (T : RootedParentTree V) (x y p z : V)
    (hx : Pendant T x) (hy : Pendant T y) (hxy : x ≠ y)
    (hpx : p ≠ x) (hpy : p ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) :
    (pairTransferTree T x y p hx hy hxy hpx hpy).parent z = T.parent z := by
  simp [pairTransferTree, twoParent, hzx, hzy]

/-- Replace the two leaves C,Z by the path A,C,Z. -/
def starSplitTree (T : RootedParentTree V) (C Z A : V)
    (hC : Pendant T C) (hZ : Pendant T Z) (hCZ : C ≠ Z)
    (hAC : A ≠ C) (hAZ : A ≠ Z) : RootedParentTree V where
  root := T.root
  parent := twoParent T C Z A C
  depth := twoDepth T C Z (T.depth A + 1) (T.depth A + 2)
  root_parent := by
    simpa [twoParent, Ne.symm hC.1, Ne.symm hZ.1] using T.root_parent
  root_depth := by
    simpa [twoDepth, Ne.symm hC.1, Ne.symm hZ.1] using T.root_depth
  parent_depth := by
    intro v hv
    by_cases hvC : v = C
    · subst v
      simp [twoParent, twoDepth, hAC, hAZ]
    · by_cases hvZ : v = Z
      · subst v
        simp [twoParent, twoDepth, Ne.symm hCZ]
      · have hpvC := hC.2 v hv
        have hpvZ := hZ.2 v hv
        simpa [twoParent, twoDepth, hvC, hvZ, hpvC, hpvZ]
          using T.parent_depth v hv

theorem starSplit_root (T : RootedParentTree V) (C Z A : V)
    (hC : Pendant T C) (hZ : Pendant T Z) (hCZ : C ≠ Z)
    (hAC : A ≠ C) (hAZ : A ≠ Z) :
    (starSplitTree T C Z A hC hZ hCZ hAC hAZ).root = T.root := rfl

/-- The paper's AB edge remains AB after the split. -/
theorem starSplit_keeps_AB (T : RootedParentTree V) (A B C Z : V)
    (hC : Pendant T C) (hZ : Pendant T Z) (hCZ : C ≠ Z)
    (hAC : A ≠ C) (hAZ : A ≠ Z) (hBC : B ≠ C) (hBZ : B ≠ Z)
    (hAB : T.parent B = A) :
    (starSplitTree T C Z A hC hZ hCZ hAC hAZ).parent B = A := by
  simpa [starSplitTree, twoParent, hBC, hBZ] using hAB

theorem starSplit_child_C (T : RootedParentTree V) (C Z A : V)
    (hC : Pendant T C) (hZ : Pendant T Z) (hCZ : C ≠ Z)
    (hAC : A ≠ C) (hAZ : A ≠ Z) :
    (starSplitTree T C Z A hC hZ hCZ hAC hAZ).parent C = A := by
  simp [starSplitTree, twoParent]

/-- The old pendant assumption is what makes Z the sole child of C. -/
theorem starSplit_sole_child (T : RootedParentTree V) (C Z A : V)
    (hC : Pendant T C) (hZ : Pendant T Z) (hCZ : C ≠ Z)
    (hAC : A ≠ C) (hAZ : A ≠ Z) (v : V) (hv : v ≠ T.root) :
    (starSplitTree T C Z A hC hZ hCZ hAC hAZ).parent v = C ↔ v = Z := by
  by_cases hvC : v = C
  · subst v
    simp [starSplitTree, twoParent, hAC, hCZ]
  · by_cases hvZ : v = Z
    · subst v
      simp [starSplitTree, twoParent, Ne.symm hCZ]
    · simp [starSplitTree, twoParent, hvC, hvZ, hC.2 v hv]

/- The swap is constructed, rather than postulated as a proof field. -/
def swapTwo {α : Type*} [DecidableEq α] (x y v : α) : α :=
  if v = x then y else if v = y then x else v

theorem swapTwo_involutive {α : Type*} [DecidableEq α] (x y : α) :
    Function.Involutive (swapTwo x y) := by
  intro v
  by_cases hxy : x = y
  · subst y
    by_cases hv : v = x <;> simp [swapTwo, hv]
  · by_cases hvx : v = x
    · subst v
      simp [swapTwo, hxy, Ne.symm hxy]
    · by_cases hvy : v = y
      · subst v
        simp [swapTwo, hxy, Ne.symm hxy]
      · simp [swapTwo, hvx, hvy]

def swapEquiv {α : Type*} [DecidableEq α] (x y : α) : α ≃ α where
  toFun := swapTwo x y
  invFun := swapTwo x y
  left_inv := swapTwo_involutive x y
  right_inv := swapTwo_involutive x y

/-- Nat-valued form of main.tex lines 154--158. -/
theorem pairTransferDifferencesNat (b p x y : ℕ) (hsum : x + y = b + p) :
    Nat.dist p x = Nat.dist b y ∧ Nat.dist p y = Nat.dist b x := by
  simp only [Nat.dist]
  omega

/-- Nat-valued form of main.tex lines 176--178. The integer d can have either
sign. Distinctness and nonzero d belong to the paper's incidence hypotheses;
the exchange equalities themselves also hold at d = 0. -/
theorem splitStarDifferencesNat (A B C Z : ℕ) (d : ℤ)
    (hA : (A : ℤ) = (C : ℤ) - 2 * d)
    (hB : (B : ℤ) = (C : ℤ) + d)
    (hZ : (Z : ℤ) = (C : ℤ) - d) :
    Nat.dist A C = Nat.dist B Z ∧ Nat.dist C Z = Nat.dist B C := by
  simp only [Nat.dist]
  omega

theorem pairTransfer_edgePermutation (T : RootedParentTree V) (f : V → ℕ)
    (b p x y : V) (hx : Pendant T x) (hy : Pendant T y) (hxy : x ≠ y)
    (hpx : p ≠ x) (hpy : p ≠ y)
    (hbx : T.parent x = b) (hby : T.parent y = b)
    (hsum : f x + f y = f b + f p) (e : RootEdge T) :
    EdgeDifference (parentGraph (pairTransferTree T x y p hx hy hxy hpx hpy)) f e =
      EdgeDifference (parentGraph T) f
        (swapEquiv (⟨x, hx.1⟩ : RootEdge T) ⟨y, hy.1⟩ e) := by
  change Nat.dist (f (twoParent T x y p p e.val)) (f e.val) =
    Nat.dist (f (T.parent (swapTwo (⟨x, hx.1⟩ : RootEdge T) ⟨y, hy.1⟩ e).val))
      (f (swapTwo (⟨x, hx.1⟩ : RootEdge T) ⟨y, hy.1⟩ e).val)
  have hdiff := pairTransferDifferencesNat (f b) (f p) (f x) (f y) hsum
  by_cases hex : e.val = x
  · have he : e = (⟨x, hx.1⟩ : RootEdge T) := Subtype.ext hex
    rw [he]
    simpa [EdgeDifference, parentGraph, pairTransferTree, twoParent,
      swapEquiv, Equiv.coe_fn_mk, swapTwo, hbx, hby] using hdiff.1
  · by_cases hey : e.val = y
    · have he : e = (⟨y, hy.1⟩ : RootEdge T) := Subtype.ext hey
      rw [he]
      simpa [EdgeDifference, parentGraph, pairTransferTree, twoParent,
        swapEquiv, Equiv.coe_fn_mk, swapTwo, hxy, Ne.symm hxy, hbx, hby] using hdiff.2
    · have hsx : e ≠ (⟨x, hx.1⟩ : RootEdge T) := by
        intro h
        exact hex (congrArg Subtype.val h)
      have hsy : e ≠ (⟨y, hy.1⟩ : RootEdge T) := by
        intro h
        exact hey (congrArg Subtype.val h)
      simp [EdgeDifference, parentGraph, pairTransferTree, twoParent,
        swapEquiv, Equiv.coe_fn_mk, swapTwo, hex, hey, hsx, hsy]

theorem starSplit_edgePermutation (T : RootedParentTree V) (f : V → ℕ)
    (A B C Z : V) (d : ℤ)
    (hC : Pendant T C) (hZ : Pendant T Z) (hCZ : C ≠ Z)
    (hAC : A ≠ C) (hAZ : A ≠ Z)
    (hBC : T.parent C = B) (hBZ : T.parent Z = B)
    (hA : (f A : ℤ) = (f C : ℤ) - 2 * d)
    (hB : (f B : ℤ) = (f C : ℤ) + d)
    (hZlabel : (f Z : ℤ) = (f C : ℤ) - d) (e : RootEdge T) :
    EdgeDifference (parentGraph (starSplitTree T C Z A hC hZ hCZ hAC hAZ)) f e =
      EdgeDifference (parentGraph T) f
        (swapEquiv (⟨C, hC.1⟩ : RootEdge T) ⟨Z, hZ.1⟩ e) := by
  change Nat.dist (f (twoParent T C Z A C e.val)) (f e.val) =
    Nat.dist (f (T.parent (swapTwo (⟨C, hC.1⟩ : RootEdge T) ⟨Z, hZ.1⟩ e).val))
      (f (swapTwo (⟨C, hC.1⟩ : RootEdge T) ⟨Z, hZ.1⟩ e).val)
  have hdiff := splitStarDifferencesNat (f A) (f B) (f C) (f Z) d hA hB hZlabel
  by_cases heC : e.val = C
  · have he : e = (⟨C, hC.1⟩ : RootEdge T) := Subtype.ext heC
    rw [he]
    simpa [EdgeDifference, parentGraph, starSplitTree, twoParent,
      swapEquiv, Equiv.coe_fn_mk, swapTwo, hBC, hBZ] using hdiff.1
  · by_cases heZ : e.val = Z
    · have he : e = (⟨Z, hZ.1⟩ : RootEdge T) := Subtype.ext heZ
      rw [he]
      simpa [EdgeDifference, parentGraph, starSplitTree, twoParent,
        swapEquiv, Equiv.coe_fn_mk, swapTwo, hCZ, Ne.symm hCZ, hBC, hBZ] using hdiff.2
    · have hsC : e ≠ (⟨C, hC.1⟩ : RootEdge T) := by
        intro h
        exact heC (congrArg Subtype.val h)
      have hsZ : e ≠ (⟨Z, hZ.1⟩ : RootEdge T) := by
        intro h
        exact heZ (congrArg Subtype.val h)
      simp [EdgeDifference, parentGraph, starSplitTree, twoParent,
        swapEquiv, Equiv.coe_fn_mk, swapTwo, heC, heZ, hsC, hsZ]

/-- The full graceful predicate is invariant under a proved edge permutation.
The label function and the chosen root are literally the same on both sides. -/
theorem graceful_of_edgePermutation {E : Type*} [Fintype E]
    (G G' : FiniteEdgeGraph V E) (root : V) (q : ℕ)
    (f : V → Fin (q + 1)) (σ : E ≃ E)
    (hperm : ∀ e, EdgeDifference G' (fun v ↦ (f v).val) e =
      EdgeDifference G (fun v ↦ (f v).val) (σ e))
    (hg : Partials.Interface.RootZeroGraceful G root q f) : Partials.Interface.RootZeroGraceful G' root q f := by
  rcases hg with ⟨hbij, hzero, hcover, hinj⟩
  refine ⟨hbij, hzero, ?_, ?_⟩
  · intro d
    rw [hcover d]
    constructor
    · rintro ⟨e, he⟩
      refine ⟨σ.symm e, ?_⟩
      rw [hperm, σ.apply_symm_apply]
      exact he
    · rintro ⟨e, he⟩
      exact ⟨σ e, (hperm e).symm.trans he⟩
  · intro e e' he
    apply σ.injective
    apply hinj
    rw [← hperm e, ← hperm e']
    exact he

/-- Paper Lemma `lem:transfer`: structural and graceful preservation. -/
theorem pairTransfer_preservesGraceful (T : RootedParentTree V) (q : ℕ)
    (f : V → Fin (q + 1)) (b p x y : V)
    (hx : Pendant T x) (hy : Pendant T y) (hxy : x ≠ y)
    (hpx : p ≠ x) (hpy : p ≠ y)
    (hbx : T.parent x = b) (hby : T.parent y = b)
    (hsum : (f x).val + (f y).val = (f b).val + (f p).val)
    (hg : Partials.Interface.RootZeroGraceful (parentGraph T) T.root q f) :
    Partials.Interface.RootZeroGraceful
      (parentGraph (pairTransferTree T x y p hx hy hxy hpx hpy)) T.root q f := by
  apply graceful_of_edgePermutation (parentGraph T)
    (parentGraph (pairTransferTree T x y p hx hy hxy hpx hpy)) T.root q f
    (swapEquiv (⟨x, hx.1⟩ : RootEdge T) ⟨y, hy.1⟩)
  · exact pairTransfer_edgePermutation T (fun v ↦ (f v).val)
      b p x y hx hy hxy hpx hpy hbx hby hsum
  · exact hg

/-- Paper Lemma `lem:split`: the nonzero-d anchor preserves gracefulness.
An AB incidence is not needed for the more general preservation result;
`starSplit_keeps_AB` records that incidence when it is supplied. -/
theorem starSplit_preservesGraceful (T : RootedParentTree V) (q : ℕ)
    (f : V → Fin (q + 1)) (A B C Z : V) (d : ℤ)
    (hC : Pendant T C) (hZ : Pendant T Z) (hCZ : C ≠ Z)
    (hAC : A ≠ C) (hAZ : A ≠ Z)
    (hBC : T.parent C = B) (hBZ : T.parent Z = B) (hd : d ≠ 0)
    (hA : ((f A).val : ℤ) = ((f C).val : ℤ) - 2 * d)
    (hB : ((f B).val : ℤ) = ((f C).val : ℤ) + d)
    (hZlabel : ((f Z).val : ℤ) = ((f C).val : ℤ) - d)
    (hg : Partials.Interface.RootZeroGraceful (parentGraph T) T.root q f) :
    Partials.Interface.RootZeroGraceful
      (parentGraph (starSplitTree T C Z A hC hZ hCZ hAC hAZ)) T.root q f := by
  apply graceful_of_edgePermutation (parentGraph T)
    (parentGraph (starSplitTree T C Z A hC hZ hCZ hAC hAZ)) T.root q f
    (swapEquiv (⟨C, hC.1⟩ : RootEdge T) ⟨Z, hZ.1⟩)
  · exact starSplit_edgePermutation T (fun v ↦ (f v).val)
      A B C Z d hC hZ hCZ hAC hAZ hBC hBZ hA hB hZlabel
  · exact hg

/-! Simultaneous transfers on a finite set of paired pendant vertices. -/

theorem pendantSet_root_not_mem (T : RootedParentTree V) (L : Finset V)
    (hpend : ∀ v ∈ L, Pendant T v) : T.root ∉ L := by
  intro hr
  exact (hpend T.root hr).1 rfl

/-- Simultaneously reattach all selected pendant vertices at p. -/
def batchTransferTree (T : RootedParentTree V) (L : Finset V) (p : V)
    (hpend : ∀ v ∈ L, Pendant T v) (hp : p ∉ L) : RootedParentTree V where
  root := T.root
  parent v := if v ∈ L then p else T.parent v
  depth v := if v ∈ L then T.depth p + 1 else T.depth v
  root_parent := by
    simpa [pendantSet_root_not_mem T L hpend] using T.root_parent
  root_depth := by
    simpa [pendantSet_root_not_mem T L hpend] using T.root_depth
  parent_depth := by
    intro v hv
    by_cases hvl : v ∈ L
    · simp [hvl, hp]
    · have hpvl : T.parent v ∉ L := by
        intro hpl
        exact (hpend (T.parent v) hpl).2 v hv rfl
      simpa [hvl, hpvl] using T.parent_depth v hv

theorem batchTransfer_parent_unchanged (T : RootedParentTree V) (L : Finset V) (p z : V)
    (hpend : ∀ v ∈ L, Pendant T v) (hp : p ∉ L) (hz : z ∉ L) :
    (batchTransferTree T L p hpend hp).parent z = T.parent z := by
  simp [batchTransferTree, hz]

/-- In particular, protected anchor leaves remain pendant when the recipient
is distinct from them. The same result holds for selected pendant leaves. -/
theorem batchTransfer_preservesPendant (T : RootedParentTree V) (L : Finset V) (p z : V)
    (hpend : ∀ v ∈ L, Pendant T v) (hp : p ∉ L)
    (hz : Pendant T z) (hpz : p ≠ z) :
    Pendant (batchTransferTree T L p hpend hp) z := by
  refine ⟨hz.1, ?_⟩
  intro v hv
  by_cases hvl : v ∈ L
  · simpa [batchTransferTree, hvl] using hpz
  · simpa [batchTransferTree, hvl] using hz.2 v hv

/-- An involution fixed outside L necessarily carries L into itself. -/
theorem mate_mem (L : Finset V) (mate : V → V)
    (hinv : Function.Involutive mate) (hfix : ∀ v, v ∉ L → mate v = v)
    (v : V) (hv : v ∈ L) : mate v ∈ L := by
  by_contra hmate
  have he : v = mate v := (hinv v).symm.trans (hfix (mate v) hmate)
  exact hmate (by simpa [← he] using hv)

/-- Lift the explicitly supplied mate involution to the nonroot edge indices. -/
def batchEdgeEquiv (T : RootedParentTree V) (L : Finset V) (mate : V → V)
    (hinv : Function.Involutive mate) (hfix : ∀ v, v ∉ L → mate v = v)
    (hpend : ∀ v ∈ L, Pendant T v) : RootEdge T ≃ RootEdge T where
  toFun e := ⟨mate e.val, by
    intro hr
    have he : e.val = T.root := calc
      e.val = mate (mate e.val) := (hinv e.val).symm
      _ = mate T.root := congrArg mate hr
      _ = T.root := hfix T.root (pendantSet_root_not_mem T L hpend)
    exact e.property he⟩
  invFun e := ⟨mate e.val, by
    intro hr
    have he : e.val = T.root := calc
      e.val = mate (mate e.val) := (hinv e.val).symm
      _ = mate T.root := congrArg mate hr
      _ = T.root := hfix T.root (pendantSet_root_not_mem T L hpend)
    exact e.property he⟩
  left_inv e := Subtype.ext (hinv e.val)
  right_inv e := Subtype.ext (hinv e.val)

theorem batchTransfer_edgePermutation (T : RootedParentTree V) (f : V → ℕ)
    (L : Finset V) (b p : V) (hpend : ∀ v ∈ L, Pendant T v) (hp : p ∉ L)
    (hdonor : ∀ v ∈ L, T.parent v = b) (mate : V → V)
    (hinv : Function.Involutive mate) (hfix : ∀ v, v ∉ L → mate v = v)
    (hsum : ∀ v ∈ L, f v + f (mate v) = f b + f p) (e : RootEdge T) :
    EdgeDifference (parentGraph (batchTransferTree T L p hpend hp)) f e =
      EdgeDifference (parentGraph T) f (batchEdgeEquiv T L mate hinv hfix hpend e) := by
  by_cases hel : e.val ∈ L
  · have hmel := mate_mem L mate hinv hfix e.val hel
    have hmparent := hdonor (mate e.val) hmel
    have hd := (pairTransferDifferencesNat (f b) (f p) (f e.val)
      (f (mate e.val)) (hsum e.val hel)).1
    simpa [EdgeDifference, parentGraph, batchTransferTree, batchEdgeEquiv,
      hel, hmparent] using hd
  · simp [EdgeDifference, parentGraph, batchTransferTree, batchEdgeEquiv,
      hel, hfix e.val hel]

theorem batchTransfer_preservesGraceful (T : RootedParentTree V) (q : ℕ)
    (f : V → Fin (q + 1)) (L : Finset V) (b p : V)
    (hpend : ∀ v ∈ L, Pendant T v) (hp : p ∉ L)
    (hdonor : ∀ v ∈ L, T.parent v = b) (mate : V → V)
    (hinv : Function.Involutive mate) (hfix : ∀ v, v ∉ L → mate v = v)
    (hsum : ∀ v ∈ L, (f v).val + (f (mate v)).val = (f b).val + (f p).val)
    (hg : Partials.Interface.RootZeroGraceful (parentGraph T) T.root q f) :
    Partials.Interface.RootZeroGraceful
      (parentGraph (batchTransferTree T L p hpend hp)) T.root q f := by
  apply graceful_of_edgePermutation (parentGraph T)
    (parentGraph (batchTransferTree T L p hpend hp)) T.root q f
    (batchEdgeEquiv T L mate hinv hfix hpend)
  · exact batchTransfer_edgePermutation T (fun v ↦ (f v).val)
      L b p hpend hp hdonor mate hinv hfix hsum
  · exact hg

/-- Encoding a positive edge difference by its predecessor gives precisely
Fin q, i.e. the positive labels 1,...,q rather than Fin (q+1). -/
def positiveDifference {E : Type*} [Fintype E]
    (G : FiniteEdgeGraph V E) (root : V) (q : ℕ) (f : V → Fin (q + 1))
    (hg : Partials.Interface.RootZeroGraceful G root q f) (e : E) : Fin q :=
  ⟨EdgeDifference G (fun v ↦ (f v).val) e - 1, by
    have h := (hg.2.2.1 _).2 ⟨e, rfl⟩
    omega⟩

theorem positiveDifference_spec {E : Type*} [Fintype E]
    (G : FiniteEdgeGraph V E) (root : V) (q : ℕ) (f : V → Fin (q + 1))
    (hg : Partials.Interface.RootZeroGraceful G root q f) (e : E) :
    (positiveDifference G root q f hg e).val + 1 =
      EdgeDifference G (fun v ↦ (f v).val) e := by
  have h := (hg.2.2.1 _).2 ⟨e, rfl⟩
  dsimp [positiveDifference]
  omega

theorem positiveDifference_bijective {E : Type*} [Fintype E]
    (G : FiniteEdgeGraph V E) (root : V) (q : ℕ) (f : V → Fin (q + 1))
    (hg : Partials.Interface.RootZeroGraceful G root q f) :
    Function.Bijective (positiveDifference G root q f hg) := by
  constructor
  · intro a b hab
    apply hg.2.2.2
    have hval := congrArg Fin.val hab
    have ha := positiveDifference_spec G root q f hg a
    have hb := positiveDifference_spec G root q f hg b
    omega
  · intro d
    have hd : 1 ≤ d.val + 1 ∧ d.val + 1 ≤ q := by omega
    obtain ⟨e, he⟩ := (hg.2.2.1 (d.val + 1)).1 hd
    refine ⟨e, Fin.ext ?_⟩
    have hs := positiveDifference_spec G root q f hg e
    omega

/-! Deterministic ordered selection and reflection-pair accounting. -/

/-- Select the first k starts in increasing order. For k larger than the
available cardinality this definition returns all available starts. -/
def firstK (s : Finset ℕ) (k : ℕ) : Finset ℕ :=
  ((s.sort (· ≤ ·)).take k).toFinset

theorem firstK_mem (s : Finset ℕ) (k x : ℕ) :
    x ∈ firstK s k ↔ x ∈ (s.sort (· ≤ ·)).take k := by
  simp [firstK]

theorem firstK_subset (s : Finset ℕ) (k : ℕ) : firstK s k ⊆ s := by
  intro x hx
  have htake : x ∈ (s.sort (· ≤ ·)).take k := (firstK_mem s k x).1 hx
  have hsort : x ∈ s.sort (· ≤ ·) := List.mem_of_mem_take htake
  simpa using hsort

theorem firstK_card (s : Finset ℕ) (k : ℕ) (hk : k ≤ s.card) :
    (firstK s k).card = k := by
  have hn : ((s.sort (· ≤ ·)).take k).Nodup := (s.sort_nodup (· ≤ ·)).take
  rw [firstK, List.toFinset_card_of_nodup hn, List.length_take, Finset.length_sort]
  exact Nat.min_eq_left hk

def reflectionPair (S x : ℕ) : Finset ℕ := {x, S - x}

def reflectionPairs (S : ℕ) (s : Finset ℕ) : Finset ℕ :=
  s.biUnion (reflectionPair S)

theorem reflectionPair_card (S x : ℕ) (hx : 2 * x < S) :
    (reflectionPair S x).card = 2 := by
  have hne : x ≠ S - x := by omega
  simp [reflectionPair, hne]

theorem reflectionPair_disjoint (S x y : ℕ)
    (hx : 2 * x < S) (hy : 2 * y < S) (hxy : x ≠ y) :
    Disjoint (reflectionPair S x) (reflectionPair S y) := by
  apply Finset.disjoint_left.mpr
  intro z hzx hzy
  simp only [reflectionPair, Finset.mem_insert, Finset.mem_singleton] at hzx hzy
  rcases hzx with hzx | hzx <;> rcases hzy with hzy | hzy <;> omega

theorem reflectionPairs_mem (S x : ℕ) (s : Finset ℕ) :
    x ∈ reflectionPairs S s ↔ ∃ a ∈ s, x = a ∨ x = S - a := by
  simp [reflectionPairs, reflectionPair]

theorem reflectionPairs_subset (S : ℕ) (s t : Finset ℕ) (hst : s ⊆ t) :
    reflectionPairs S s ⊆ reflectionPairs S t := by
  intro x hx
  obtain ⟨a, ha, hxa⟩ := (reflectionPairs_mem S x s).1 hx
  exact (reflectionPairs_mem S x t).2 ⟨a, hst ha, hxa⟩

theorem reflectionPairs_union (S : ℕ) (s t : Finset ℕ) :
    reflectionPairs S (s ∪ t) = reflectionPairs S s ∪ reflectionPairs S t := by
  ext x
  simp only [reflectionPairs_mem, Finset.mem_union]
  constructor
  · rintro ⟨a, ha | ha, hxa⟩
    · exact Or.inl ⟨a, ha, hxa⟩
    · exact Or.inr ⟨a, ha, hxa⟩
  · rintro (⟨a, ha, hxa⟩ | ⟨a, ha, hxa⟩)
    · exact ⟨a, Or.inl ha, hxa⟩
    · exact ⟨a, Or.inr ha, hxa⟩

theorem reflectionPairs_reflect (S : ℕ) (s : Finset ℕ)
    (hvalid : ∀ a ∈ s, 2 * a < S) (x : ℕ) (hx : x ∈ reflectionPairs S s) :
    S - x ∈ reflectionPairs S s := by
  obtain ⟨a, ha, hxa | hxa⟩ := (reflectionPairs_mem S x s).1 hx
  · exact (reflectionPairs_mem S (S - x) s).2
      ⟨a, ha, Or.inr (by rw [hxa])⟩
  · have hbound := hvalid a ha
    exact (reflectionPairs_mem S (S - x) s).2
      ⟨a, ha, Or.inl (by omega)⟩

theorem reflectionPairs_reflection_involutive (S : ℕ) (s : Finset ℕ)
    (hvalid : ∀ a ∈ s, 2 * a < S) (x : ℕ) (hx : x ∈ reflectionPairs S s) :
    S - (S - x) = x := by
  obtain ⟨a, ha, hxa | hxa⟩ := (reflectionPairs_mem S x s).1 hx
  · have hbound := hvalid a ha
    omega
  · omega

theorem reflectionPairs_disjoint (S : ℕ) (s t : Finset ℕ)
    (hs : ∀ a ∈ s, 2 * a < S) (ht : ∀ b ∈ t, 2 * b < S)
    (hst : Disjoint s t) : Disjoint (reflectionPairs S s) (reflectionPairs S t) := by
  apply Finset.disjoint_left.mpr
  intro x hxs hxt
  obtain ⟨a, ha, hxa⟩ := (reflectionPairs_mem S x s).1 hxs
  obtain ⟨b, hb, hxb⟩ := (reflectionPairs_mem S x t).1 hxt
  have hab : a ≠ b := by
    intro hab
    exact (Finset.disjoint_left.mp hst) ha (by simpa [hab] using hb)
  have hdis := reflectionPair_disjoint S a b (hs a ha) (ht b hb) hab
  exact (Finset.disjoint_left.mp hdis)
    (by simpa [reflectionPair] using hxa) (by simpa [reflectionPair] using hxb)

/-- This exactly matches the predicate used by Symbolic.moveSelectedPairs.
Positive starts exclude the spurious truncated-subtraction match at 0. -/
theorem reflectionPairs_mem_iff (S : ℕ) (s : Finset ℕ)
    (hvalid : ∀ a ∈ s, 2 * a < S) (hpositive : ∀ a ∈ s, 0 < a) (x : ℕ) :
    x ∈ reflectionPairs S s ↔ x ∈ s ∨ S - x ∈ s := by
  constructor
  · intro hx
    obtain ⟨a, ha, hxa | hxa⟩ := (reflectionPairs_mem S x s).1 hx
    · exact Or.inl (by simpa [hxa] using ha)
    · have hbound := hvalid a ha
      have he : S - x = a := by omega
      exact Or.inr (by simpa [he] using ha)
  · rintro (hx | hx)
    · exact (reflectionPairs_mem S x s).2 ⟨x, hx, Or.inl rfl⟩
    · have hp := hpositive (S - x) hx
      exact (reflectionPairs_mem S x s).2
        ⟨S - x, hx, Or.inr (by omega)⟩

theorem reflectionPairs_positive (S : ℕ) (s : Finset ℕ)
    (hvalid : ∀ a ∈ s, 2 * a < S) (hpositive : ∀ a ∈ s, 0 < a)
    (x : ℕ) (hx : x ∈ reflectionPairs S s) : 0 < x := by
  obtain ⟨a, ha, hxa | hxa⟩ := (reflectionPairs_mem S x s).1 hx
  · simpa [hxa] using hpositive a ha
  · have hb := hvalid a ha
    omega

/-- Construct the reflection mate on the union and fix every other label. -/
def reflectSelected (S : ℕ) (s : Finset ℕ) (x : ℕ) : ℕ :=
  if x ∈ reflectionPairs S s then S - x else x

theorem reflectSelected_involutive (S : ℕ) (s : Finset ℕ)
    (hvalid : ∀ a ∈ s, 2 * a < S) : Function.Involutive (reflectSelected S s) := by
  intro x
  by_cases hx : x ∈ reflectionPairs S s
  · have hr := reflectionPairs_reflect S s hvalid x hx
    have hi := reflectionPairs_reflection_involutive S s hvalid x hx
    simpa [reflectSelected, hx, hr] using hi
  · simp [reflectSelected, hx]

theorem reflectSelected_fixed (S : ℕ) (s : Finset ℕ) (x : ℕ)
    (hx : x ∉ reflectionPairs S s) : reflectSelected S s x = x := by
  simp [reflectSelected, hx]

theorem reflectSelected_sum (S : ℕ) (s : Finset ℕ)
    (hvalid : ∀ a ∈ s, 2 * a < S) (x : ℕ) (hx : x ∈ reflectionPairs S s) :
    x + reflectSelected S s x = S := by
  have hbound : x ≤ S := by
    obtain ⟨a, ha, hxa | hxa⟩ := (reflectionPairs_mem S x s).1 hx
    · have hb := hvalid a ha
      omega
    · omega
  simp only [reflectSelected, if_pos hx]
  omega

/-- The bounded finite-label version of the same explicit involution. -/
def reflectFin (Q S : ℕ) (s : Finset ℕ)
    (hvalid : ∀ a ∈ s, 2 * a < S)
    (hbounded : ∀ x ∈ reflectionPairs S s, x ≤ Q) (x : Fin (Q + 1)) : Fin (Q + 1) :=
  ⟨reflectSelected S s x.val, by
    by_cases hx : x.val ∈ reflectionPairs S s
    · have hb := hbounded (S - x.val) (reflectionPairs_reflect S s hvalid x.val hx)
      simp only [reflectSelected, if_pos hx]
      omega
    · simpa [reflectSelected, hx] using x.isLt⟩

theorem reflectFin_involutive (Q S : ℕ) (s : Finset ℕ)
    (hvalid : ∀ a ∈ s, 2 * a < S)
    (hbounded : ∀ x ∈ reflectionPairs S s, x ≤ Q) :
    Function.Involutive (reflectFin Q S s hvalid hbounded) := by
  intro x
  apply Fin.ext
  exact reflectSelected_involutive S s hvalid x.val

theorem reflectFin_fixed (Q S : ℕ) (s : Finset ℕ)
    (hvalid : ∀ a ∈ s, 2 * a < S)
    (hbounded : ∀ x ∈ reflectionPairs S s, x ≤ Q) (x : Fin (Q + 1))
    (hx : x.val ∉ reflectionPairs S s) : reflectFin Q S s hvalid hbounded x = x := by
  apply Fin.ext
  exact reflectSelected_fixed S s x.val hx

theorem reflectFin_sum (Q S : ℕ) (s : Finset ℕ)
    (hvalid : ∀ a ∈ s, 2 * a < S)
    (hbounded : ∀ x ∈ reflectionPairs S s, x ≤ Q) (x : Fin (Q + 1))
    (hx : x.val ∈ reflectionPairs S s) :
    x.val + (reflectFin Q S s hvalid hbounded x).val = S := by
  exact reflectSelected_sum S s hvalid x.val hx

/-- Numeric parent-map form of the simultaneous operation. -/
def transferSelectedParent (parent : ℕ → ℕ) (S p : ℕ) (s : Finset ℕ) (x : ℕ) : ℕ :=
  if x ∈ reflectionPairs S s then p else parent x

theorem transferSelectedParent_predicate (parent : ℕ → ℕ) (S p : ℕ) (s : Finset ℕ)
    (hvalid : ∀ a ∈ s, 2 * a < S) (hpositive : ∀ a ∈ s, 0 < a) (x : ℕ) :
    transferSelectedParent parent S p s x =
      if x ∈ s ∨ S - x ∈ s then p else parent x := by
  simp only [transferSelectedParent, reflectionPairs_mem_iff S s hvalid hpositive x]

/-- Directly consumable by a symbolic parent map: after transfer, the
difference at x is the old difference at its reflected mate. The tree proof
is separately supplied by batchTransferTree, rather than inferred from this
arithmetic identity. -/
theorem transferSelected_difference (parent : ℕ → ℕ) (S b p : ℕ) (s : Finset ℕ)
    (hvalid : ∀ a ∈ s, 2 * a < S) (hsum : b + p = S)
    (hdonor : ∀ x ∈ reflectionPairs S s, parent x = b) (x : ℕ) :
    Nat.dist x (transferSelectedParent parent S p s x) =
      Nat.dist (reflectSelected S s x) (parent (reflectSelected S s x)) := by
  by_cases hx : x ∈ reflectionPairs S s
  · have hr := reflectionPairs_reflect S s hvalid x hx
    have hm : reflectSelected S s x ∈ reflectionPairs S s := by
      simpa [reflectSelected, hx] using hr
    have hp := hdonor (reflectSelected S s x) hm
    have he := reflectSelected_sum S s hvalid x hx
    have hex : x + reflectSelected S s x = b + p := by omega
    have hd := (pairTransferDifferencesNat b p x (reflectSelected S s x) hex).1
    simpa [transferSelectedParent, hx, hp, Nat.dist_comm] using hd
  · simp [transferSelectedParent, reflectSelected, hx]

/-- Disjoint pairs have exactly twice as many labels as starts. -/
theorem reflectionPairs_card (S : ℕ) (s : Finset ℕ)
    (hvalid : ∀ x ∈ s, 2 * x < S) :
    (reflectionPairs S s).card = 2 * s.card := by
  classical
  revert hvalid
  induction s using Finset.induction_on with
  | empty =>
    intro hvalid
    simp [reflectionPairs]
  | @insert a s ha ih =>
    intro hvalid
    have hsa : 2 * a < S := hvalid a (Finset.mem_insert_self a s)
    have hs : ∀ b ∈ s, 2 * b < S := by
      intro b hb
      exact hvalid b (Finset.mem_insert_of_mem hb)
    have hdisjoint : Disjoint (reflectionPair S a) (reflectionPairs S s) := by
      apply Finset.disjoint_left.mpr
      intro z hza hzs
      obtain ⟨b, hb, hzb⟩ := Finset.mem_biUnion.mp hzs
      have hab : a ≠ b := by
        intro hab
        apply ha
        simpa [hab] using hb
      exact (Finset.disjoint_left.mp (reflectionPair_disjoint S a b hsa (hs b hb) hab))
        hza hzb
    have hrec := ih hs
    change ((insert a s).biUnion (reflectionPair S)).card = 2 * (insert a s).card
    rw [Finset.biUnion_insert]
    change (reflectionPair S a ∪ reflectionPairs S s).card = 2 * (insert a s).card
    rw [Finset.card_union_of_disjoint hdisjoint, reflectionPair_card S a hsa,
      Finset.card_insert_of_notMem ha]
    change 2 + (reflectionPairs S s).card = 2 * (s.card + 1)
    rw [hrec]
    omega

theorem firstK_reflectionPairs_card (S : ℕ) (s : Finset ℕ) (k : ℕ)
    (hk : k ≤ s.card) (hvalid : ∀ x ∈ s, 2 * x < S) :
    (reflectionPairs S (firstK s k)).card = 2 * k := by
  rw [reflectionPairs_card S (firstK s k)]
  · rw [firstK_card s k hk]
  · intro x hx
    exact hvalid x (firstK_subset s k hx)

end Partials.Graceful.Operations
