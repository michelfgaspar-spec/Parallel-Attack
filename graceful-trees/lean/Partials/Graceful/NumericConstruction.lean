import Partials.Graceful.Symbolic
import Partials.Graceful.Realization
import Mathlib.Tactic.FinCases

set_option maxHeartbeats 2000000

/-! R2 numeric/profile integration, native request q0004. Authored blind:
no Lean/Lake/Power execution or kernel-check claim. -/
namespace Partials.Graceful.NumericConstruction

open Symbolic

def oneCode (i : Fin 3) : InternalCode := .inr (.inl i)
def twoCode (c : DepthCode) : InternalCode := .inr (.inr c)
def splitDepth : DepthCode := ⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩
def splitCode : InternalCode := twoCode splitDepth

def internalParentCode : InternalCode → InternalCode
  | .inl _ => .inl ()
  | .inr (.inl _) => .inl ()
  | .inr (.inr c) => oneCode c.1

theorem internalParentCode_ne_two (a : InternalCode) (c : DepthCode) :
    internalParentCode a ≠ twoCode c := by
  rcases a with a | a
  · simp [internalParentCode, twoCode]
  · rcases a with i | d <;> simp [internalParentCode, oneCode, twoCode]

/-- Lift a natural finite set by its exact value-membership predicate. -/
def liftFiber (Q : ℕ) (s : Finset ℕ) : Finset (Fin (Q + 1)) :=
  Finset.univ.filter fun y => y.val ∈ s

theorem liftFiber_mem (Q : ℕ) (s : Finset ℕ) (y : Fin (Q + 1)) :
    y ∈ liftFiber Q s ↔ y.val ∈ s := by simp [liftFiber]

def boundedFiberEquiv (Q : ℕ) (s : Finset ℕ) (hs : ∀ x ∈ s, x ≤ Q) :
    ↥s ≃ ↥(liftFiber Q s) where
  toFun x := ⟨⟨x.val, by have h := hs x.val x.property; omega⟩,
    (liftFiber_mem Q s _).2 x.property⟩
  invFun y := ⟨y.val.val, (liftFiber_mem Q s y.val).1 y.property⟩
  left_inv x := by apply Subtype.ext; rfl
  right_inv y := by apply Subtype.ext; apply Fin.ext; rfl

theorem liftFiber_card (Q : ℕ) (s : Finset ℕ) (hs : ∀ x ∈ s, x ≤ Q) :
    (liftFiber Q s).card = s.card := by
  simpa using (Fintype.card_congr (boundedFiberEquiv Q s hs)).symm

def naturalFiber (Q : ℕ) (p : ℕ → ℕ) (b : ℕ) : Finset ℕ :=
  (leafLabels Q).filter fun x => p x = b

theorem naturalFiber_mem (Q : ℕ) (p : ℕ → ℕ) (b x : ℕ) :
    x ∈ naturalFiber Q p b ↔ x ∈ leafLabels Q ∧ p x = b := by
  simp [naturalFiber]

theorem naturalFiber_bound (Q : ℕ) (p : ℕ → ℕ) (b : ℕ) :
    ∀ x ∈ naturalFiber Q p b, x ≤ Q := by
  intro x hx
  have hx' := ((naturalFiber_mem Q p b x).1 hx).1
  simp only [leafLabels, Finset.mem_Icc] at hx'
  omega

def liftParent (Q : ℕ) (p : ℕ → ℕ) (hp : ∀ x ≤ Q, p x ≤ Q) :
    Fin (Q + 1) → Fin (Q + 1) :=
  fun x => ⟨p x.val, by have h := hp x.val (by omega); omega⟩

def liftInternal (Q : ℕ) (m : InternalCode → ℕ) (hm : ∀ a, m a ≤ Q) :
    InternalCode → Fin (Q + 1) := fun a => ⟨m a, by have h := hm a; omega⟩

theorem liftInternal_injective (Q : ℕ) (m : InternalCode → ℕ)
    (hm : ∀ a, m a ≤ Q) (hi : Function.Injective m) :
    Function.Injective (liftInternal Q m hm) := by
  intro a b hab
  exact hi (congrArg Fin.val hab)

/-- All finite-profile fields are constructed from natural incidences and
exact natural fiber counts. No graceful-labeling premise occurs here. -/
def frameOfNaturalFibers (u v : ℕ) (p : ℕ → ℕ) (m : InternalCode → ℕ)
    (hp : ∀ x ≤ q u v, p x ≤ q u v) (hm : ∀ a, m a ≤ q u v)
    (hi : Function.Injective m) (hroot : m (.inl ()) = 0)
    (hparent : ∀ a, p (m a) = m (internalParentCode a))
    (hcover : ∀ x ≤ q u v, x ∉ leafLabels (q u v) → ∃ a, m a = x)
    (hrange : ∀ x ∈ leafLabels (q u v), x ≠ m splitCode → ∃ c, p x = m (twoCode c))
    (hcard : ∀ c, (naturalFiber (q u v) p (m (twoCode c))).card =
      pendantCount u v c.1 c.2) : ProfileFrame u v where
  numericParent := liftParent (q u v) p hp
  internal := liftInternal (q u v) m hm
  internal_injective := liftInternal_injective (q u v) m hm hi
  root_zero := by apply Fin.ext; exact hroot
  parent_root := by
    apply Fin.ext
    have h := hparent (.inl ())
    simpa [liftParent, internalParentCode, hroot] using h
  parent_one := by
    intro i
    apply Fin.ext
    exact hparent (oneCode i)
  parent_two := by
    intro c
    apply Fin.ext
    exact hparent (twoCode c)
  fibers c := liftFiber (q u v) (naturalFiber (q u v) p (m (twoCode c)))
  fiber_card := by
    intro c
    rw [liftFiber_card _ _ (naturalFiber_bound _ _ _)]
    exact hcard c
  fiber_parent := by
    intro c y hy
    apply Fin.ext
    exact ((naturalFiber_mem _ _ _ _).1 ((liftFiber_mem _ _ _).1 hy)).2
  fiber_avoids_internal := by
    intro c y hy a he
    have hv : y.val = m a := congrArg Fin.val he
    have hp' := ((naturalFiber_mem _ _ _ _).1 ((liftFiber_mem _ _ _).1 hy)).2
    rw [hv, hparent a] at hp'
    exact internalParentCode_ne_two a c (hi hp')
  covers := by
    intro y
    by_cases hinternal : ∃ a, m a = y.val
    · obtain ⟨a, ha⟩ := hinternal
      exact Or.inl ⟨a, Fin.ext ha⟩
    · have hyleaf : y.val ∈ leafLabels (q u v) := by
        by_contra hn
        exact hinternal (hcover y.val (by omega) hn)
      have hC : y.val ≠ m splitCode := by
        intro he
        exact hinternal ⟨splitCode, he.symm⟩
      obtain ⟨c, hc⟩ := hrange y.val hyleaf hC
      exact Or.inr ⟨c, (liftFiber_mem _ _ _).2 ((naturalFiber_mem _ _ _ _).2 ⟨hyleaf, hc⟩)⟩

/-! Full parent maps. The source's Symbolic parents describe the original
leaf interval only; these definitions add every skeleton incidence. -/

def skeletonParent0 (Q x : ℕ) : ℕ :=
  if x = Q ∨ x = 1 ∨ x = Q-1 then 0
  else if x = 2 ∨ x = Q-2 ∨ x = 3 then Q
  else if x = Q-3 ∨ x = 4 ∨ x = Q-4 then 1
  else if x = 5 then Q-1 else 0

def skeletonParent1 (Q x : ℕ) : ℕ :=
  if x = Q ∨ x = 1 ∨ x = Q-1 then 0
  else if x = 2 ∨ x = Q-2 ∨ x = 3 then Q
  else if x = Q-3 then 1
  else if x = 4 ∨ x = Q-4 ∨ x = 5 then Q-1 else 0

def skeletonParent2 (Q x : ℕ) : ℕ :=
  if x = Q ∨ x = 1 ∨ x = Q-1 then 0
  else if x = 2 then Q
  else if x = Q-2 ∨ x = 3 ∨ x = Q-3 then 1
  else if x = 4 ∨ x = Q-4 ∨ x = 5 then Q-1 else 0

def alternateSkeletonParent (Q x : ℕ) : ℕ :=
  if x = Q ∨ x = 2 ∨ x = Q-1 then 0
  else if x = 3 ∨ x = 4 ∨ x = Q-4 then Q
  else if x = Q-3 then 2
  else if x = 1 ∨ x = 5 ∨ x = Q-2 then Q-1 else 0

def fullParent (Q : ℕ) (skeleton leaf : ℕ → ℕ) (x : ℕ) : ℕ :=
  if x ∈ leafLabels Q then leaf x else skeleton x

def fullBaseParent0 (t : ℕ) := fullParent (q0 t) (skeletonParent0 (q0 t)) (baseParent0 t)
def fullBaseParent1 (t : ℕ) := fullParent (q1 t) (skeletonParent1 (q1 t)) (baseParent1 t)
def fullBaseParent2 (t : ℕ) := fullParent (q2 t) (skeletonParent2 (q2 t)) (baseParent2 t)
def fullAlternateBaseParent (t : ℕ) :=
  fullParent (q2 t) (alternateSkeletonParent (q2 t)) (alternateBaseParent t)

def fullFinalParent0 (t v : ℕ) := fullParent (q0 t) (skeletonParent0 (q0 t)) (finalParent0 t v)
def fullFinalParent1 (t u : ℕ) := fullParent (q1 t) (skeletonParent1 (q1 t)) (finalParent1 t u)
def fullFinalParent2 (t v : ℕ) := fullParent (q2 t) (skeletonParent2 (q2 t)) (finalParent2 t v)
def fullAlternateFinalParent (t : ℕ) :=
  fullParent (q2 t) (alternateSkeletonParent (q2 t)) (alternateFinalParent t)

def pick3 (a b c i : ℕ) : ℕ := if i = 0 then a else if i = 1 then b else c

/-- Exact order of the final three branches: (1,1,3), (1,1,2v), (1,2u). -/
def internalNat0 (t : ℕ) : InternalCode → ℕ
  | .inl _ => 0
  | .inr (.inl i) => pick3 (q0 t) 1 (q0 t-1) i.val
  | .inr (.inr ⟨i,j⟩) =>
    if i.val = 0 then pick3 2 3 (q0 t-2) j.val
    else if i.val = 1 then pick3 (q0 t-3) 4 (q0 t-4) j.val
    else if j.val = 0 then (anchor0 t).C else 5

def internalNat1 (t : ℕ) : InternalCode → ℕ
  | .inl _ => 0
  | .inr (.inl i) => pick3 (q1 t) (q1 t-1) 1 i.val
  | .inr (.inr ⟨i,j⟩) =>
    if i.val = 0 then pick3 2 3 (q1 t-2) j.val
    else if i.val = 1 then pick3 (q1 t-4) 5 4 j.val
    else if j.val = 0 then (anchor1 t).C else q1 t-3

def internalNat2 (t : ℕ) : InternalCode → ℕ
  | .inl _ => 0
  | .inr (.inl i) => pick3 (q2 t-1) 1 (q2 t) i.val
  | .inr (.inr ⟨i,j⟩) =>
    if i.val = 0 then pick3 4 5 (q2 t-4) j.val
    else if i.val = 1 then pick3 (q2 t-2) 3 (q2 t-3) j.val
    else if j.val = 0 then (anchor2 t).C else 2

def alternateInternalNat (t : ℕ) : InternalCode → ℕ
  | .inl _ => 0
  | .inr (.inl i) => pick3 (q2 t-1) (q2 t) 2 i.val
  | .inr (.inr ⟨i,j⟩) =>
    if i.val = 0 then pick3 1 5 (q2 t-2) j.val
    else if i.val = 1 then pick3 3 (q2 t-4) 4 j.val
    else if j.val = 0 then (alternateAnchor t).C else q2 t-3

theorem baseParent0_bound (t x : ℕ) : baseParent0 t x ≤ q0 t := by
  simp only [baseParent0, q0]; split_ifs <;> omega
theorem baseParent1_bound (t x : ℕ) : baseParent1 t x ≤ q1 t := by
  simp only [baseParent1, q1]; split_ifs <;> omega
theorem baseParent2_bound (t x : ℕ) : baseParent2 t x ≤ q2 t := by
  simp only [baseParent2, q2]; split_ifs <;> omega
theorem alternateBaseParent_bound (t x : ℕ) : alternateBaseParent t x ≤ q2 t := by
  simp only [alternateBaseParent, q2]; split_ifs <;> omega

theorem moveTwo_bound (Q : ℕ) (p : ℕ → ℕ) (a b r : ℕ)
    (hp : ∀ x, p x ≤ Q) (hr : r ≤ Q) (x : ℕ) : moveTwo p a b r x ≤ Q := by
  unfold moveTwo
  split_ifs
  · exact hr
  · exact hp x

theorem moveSelectedPairs_bound (Q : ℕ) (p : ℕ → ℕ) (S r : ℕ) (s : Finset ℕ)
    (hp : ∀ x, p x ≤ Q) (hr : r ≤ Q) (x : ℕ) : moveSelectedPairs p S r s x ≤ Q := by
  unfold moveSelectedPairs
  split_ifs
  · exact hr
  · exact hp x

theorem splitParent_bound (Q : ℕ) (p : ℕ → ℕ) (a : Anchor)
    (hp : ∀ x, p x ≤ Q) (hA : a.A ≤ Q) (hC : a.C ≤ Q) (x : ℕ) :
    splitParent p a x ≤ Q := by
  unfold splitParent
  split_ifs
  · exact hA
  · exact hC
  · exact hp x

theorem afterFirst0_bound (t x : ℕ) : afterFirst0 t x ≤ q0 t := by
  unfold afterFirst0
  split_ifs
  all_goals apply moveTwo_bound _ _ _ _ _ (baseParent0_bound t); omega
theorem afterFirst1_bound (t x : ℕ) : afterFirst1 t x ≤ q1 t := by
  exact moveTwo_bound _ _ _ _ _ (baseParent1_bound t) (by dsimp [q1]; omega) x
theorem afterFirst2_bound (t x : ℕ) : afterFirst2 t x ≤ q2 t := by
  exact moveTwo_bound _ _ _ _ _ (baseParent2_bound t) (by dsimp [q2]; omega) x
theorem alternateAfterFirst_bound (t x : ℕ) : alternateAfterFirst t x ≤ q2 t := by
  exact moveTwo_bound _ _ _ _ _ (alternateBaseParent_bound t) (by dsimp [q2]; omega) x

theorem finalParent0_bound (t v x : ℕ) : finalParent0 t v x ≤ q0 t := by
  apply splitParent_bound _ _ _
  · intro y
    exact moveSelectedPairs_bound _ _ _ _ _ (afterFirst0_bound t) (by omega) y
  · dsimp [anchor0, q0]; omega
  · dsimp [anchor0, q0]; omega
theorem finalParent1_bound (t u x : ℕ) : finalParent1 t u x ≤ q1 t := by
  apply splitParent_bound _ _ _
  · intro y
    exact moveSelectedPairs_bound _ _ _ _ _ (afterFirst1_bound t) (by omega) y
  · dsimp [anchor1, q1]; omega
  · dsimp [anchor1, q1]; omega
theorem finalParent2_bound (t v x : ℕ) : finalParent2 t v x ≤ q2 t := by
  apply splitParent_bound _ _ _
  · intro y
    exact moveSelectedPairs_bound _ _ _ _ _ (afterFirst2_bound t) (by omega) y
  · dsimp [anchor2, q2]; omega
  · dsimp [anchor2, q2]; omega
theorem alternateFinalParent_bound (t x : ℕ) : alternateFinalParent t x ≤ q2 t := by
  exact splitParent_bound _ _ _ (alternateAfterFirst_bound t)
    (by dsimp [alternateAnchor, q2]; omega) (by dsimp [alternateAnchor, q2]; omega) x

theorem skeletonParent0_bound (Q x : ℕ) (hQ : 1 ≤ Q) : skeletonParent0 Q x ≤ Q := by
  simp only [skeletonParent0]; split_ifs <;> omega
theorem skeletonParent1_bound (Q x : ℕ) (hQ : 1 ≤ Q) : skeletonParent1 Q x ≤ Q := by
  simp only [skeletonParent1]; split_ifs <;> omega
theorem skeletonParent2_bound (Q x : ℕ) (hQ : 1 ≤ Q) : skeletonParent2 Q x ≤ Q := by
  simp only [skeletonParent2]; split_ifs <;> omega
theorem alternateSkeletonParent_bound (Q x : ℕ) (hQ : 2 ≤ Q) :
    alternateSkeletonParent Q x ≤ Q := by
  simp only [alternateSkeletonParent]; split_ifs <;> omega

theorem fullParent_bound (Q : ℕ) (s p : ℕ → ℕ)
    (hs : ∀ x, s x ≤ Q) (hp : ∀ x, p x ≤ Q) (x : ℕ) : fullParent Q s p x ≤ Q := by
  unfold fullParent
  split_ifs
  · exact hp x
  · exact hs x

theorem fullFinalParent0_bound (t v x : ℕ) : fullFinalParent0 t v x ≤ q0 t :=
  fullParent_bound _ _ _ (fun y => skeletonParent0_bound _ y (by dsimp [q0]; omega)) (finalParent0_bound t v) x
theorem fullFinalParent1_bound (t u x : ℕ) : fullFinalParent1 t u x ≤ q1 t :=
  fullParent_bound _ _ _ (fun y => skeletonParent1_bound _ y (by dsimp [q1]; omega)) (finalParent1_bound t u) x
theorem fullFinalParent2_bound (t v x : ℕ) : fullFinalParent2 t v x ≤ q2 t :=
  fullParent_bound _ _ _ (fun y => skeletonParent2_bound _ y (by dsimp [q2]; omega)) (finalParent2_bound t v) x
theorem fullAlternateFinalParent_bound (t x : ℕ) : fullAlternateFinalParent t x ≤ q2 t :=
  fullParent_bound _ _ _ (fun y => alternateSkeletonParent_bound _ y (by dsimp [q2]; omega))
    (alternateFinalParent_bound t) x

def finalNumericParent0 (t v : ℕ) : Fin (q0 t + 1) → Fin (q0 t + 1) :=
  liftParent _ (fullFinalParent0 t v) (fun x _ => fullFinalParent0_bound t v x)
def finalNumericParent1 (t u : ℕ) : Fin (q1 t + 1) → Fin (q1 t + 1) :=
  liftParent _ (fullFinalParent1 t u) (fun x _ => fullFinalParent1_bound t u x)
def finalNumericParent2 (t v : ℕ) : Fin (q2 t + 1) → Fin (q2 t + 1) :=
  liftParent _ (fullFinalParent2 t v) (fun x _ => fullFinalParent2_bound t v x)
def alternateFinalNumericParent (t : ℕ) : Fin (q2 t + 1) → Fin (q2 t + 1) :=
  liftParent _ (fullAlternateFinalParent t) (fun x _ => fullAlternateFinalParent_bound t x)

theorem internalNat0_bound (t : ℕ) (a : InternalCode) : internalNat0 t a ≤ q0 t := by
  fin_cases a <;> simp [internalNat0, pick3, q0, anchor0] <;> omega
theorem internalNat1_bound (t : ℕ) (a : InternalCode) : internalNat1 t a ≤ q1 t := by
  fin_cases a <;> simp [internalNat1, pick3, q1, anchor1] <;> omega
theorem internalNat2_bound (t : ℕ) (a : InternalCode) : internalNat2 t a ≤ q2 t := by
  fin_cases a <;> simp [internalNat2, pick3, q2, anchor2] <;> omega
theorem alternateInternalNat_bound (t : ℕ) (a : InternalCode) : alternateInternalNat t a ≤ q2 t := by
  fin_cases a <;> simp [alternateInternalNat, pick3, q2, alternateAnchor] <;> omega

theorem internalNat0_injective (t : ℕ) : Function.Injective (internalNat0 t) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp [internalNat0, pick3, q0, anchor0] at hab ⊢ <;> omega
theorem internalNat1_injective (t : ℕ) : Function.Injective (internalNat1 t) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp [internalNat1, pick3, q1, anchor1] at hab ⊢ <;> omega
theorem internalNat2_injective (t : ℕ) : Function.Injective (internalNat2 t) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp [internalNat2, pick3, q2, anchor2] at hab ⊢ <;> omega
theorem alternateInternalNat_injective (t : ℕ) : Function.Injective (alternateInternalNat t) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> simp [alternateInternalNat, pick3, q2, alternateAnchor] at hab ⊢ <;> omega

theorem fullFinalParent0_internal (t v : ℕ) (a : InternalCode) :
    fullFinalParent0 t v (internalNat0 t a) = internalNat0 t (internalParentCode a) := by
  fin_cases a <;> simp [fullFinalParent0, fullParent, internalNat0, pick3,
    internalParentCode, oneCode, skeletonParent0, leafLabels, q0, finalParent0,
    splitParent, anchor0] <;> (try split_ifs) <;> omega
theorem fullFinalParent1_internal (t u : ℕ) (a : InternalCode) :
    fullFinalParent1 t u (internalNat1 t a) = internalNat1 t (internalParentCode a) := by
  fin_cases a <;> simp [fullFinalParent1, fullParent, internalNat1, pick3,
    internalParentCode, oneCode, skeletonParent1, leafLabels, q1, finalParent1,
    splitParent, anchor1] <;> (try split_ifs) <;> omega
theorem fullFinalParent2_internal (t v : ℕ) (a : InternalCode) :
    fullFinalParent2 t v (internalNat2 t a) = internalNat2 t (internalParentCode a) := by
  fin_cases a <;> simp [fullFinalParent2, fullParent, internalNat2, pick3,
    internalParentCode, oneCode, skeletonParent2, leafLabels, q2, finalParent2,
    splitParent, anchor2] <;> (try split_ifs) <;> omega
theorem fullAlternateFinalParent_internal (t : ℕ) (a : InternalCode) :
    fullAlternateFinalParent t (alternateInternalNat t a) =
      alternateInternalNat t (internalParentCode a) := by
  fin_cases a <;> simp [fullAlternateFinalParent, fullParent, alternateInternalNat, pick3,
    internalParentCode, oneCode, alternateSkeletonParent, leafLabels, q2,
    alternateFinalParent, splitParent, alternateAnchor] <;> (try split_ifs) <;> omega

theorem naturalFiber_fullParent (Q : ℕ) (s p : ℕ → ℕ) (b : ℕ) :
    naturalFiber Q (fullParent Q s p) b = Symbolic.fibre Q p b := by
  ext x
  simp only [naturalFiber_mem, Symbolic.fibre, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hp⟩
    exact ⟨hx, by simpa [fullParent, hx] using hp⟩
  · rintro ⟨hx, hp⟩
    exact ⟨hx, by simpa [fullParent, hx] using hp⟩

theorem skeleton_label_cases (Q x : ℕ) (hQ : 11 ≤ Q) (hx : x ≤ Q)
    (hn : x ∉ leafLabels Q) :
    x=0 ∨ x=1 ∨ x=2 ∨ x=3 ∨ x=4 ∨ x=5 ∨
    x=Q-4 ∨ x=Q-3 ∨ x=Q-2 ∨ x=Q-1 ∨ x=Q := by
  simp only [leafLabels, Finset.mem_Icc] at hn
  omega

theorem internalNat0_covers (t x : ℕ) (hx : x ≤ q0 t) (hn : x ∉ leafLabels (q0 t)) :
    ∃ a, internalNat0 t a = x := by
  rcases skeleton_label_cases (q0 t) x (by dsimp [q0]; omega) hx hn with
    h|h|h|h|h|h|h|h|h|h|h
  · exact ⟨.inl (), h.symm⟩
  · exact ⟨oneCode 1, by simpa [internalNat0, oneCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, by simpa [internalNat0, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩, by simpa [internalNat0, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩, by simpa [internalNat0, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨2, by decide⟩, ⟨1, by decide⟩⟩, by simpa [internalNat0, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩, by simpa [internalNat0, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, by simpa [internalNat0, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩, by simpa [internalNat0, twoCode, pick3] using h.symm⟩
  · exact ⟨oneCode 2, by simpa [internalNat0, oneCode, pick3] using h.symm⟩
  · exact ⟨oneCode 0, by simpa [internalNat0, oneCode, pick3] using h.symm⟩

theorem internalNat1_covers (t x : ℕ) (hx : x ≤ q1 t) (hn : x ∉ leafLabels (q1 t)) :
    ∃ a, internalNat1 t a = x := by
  rcases skeleton_label_cases (q1 t) x (by dsimp [q1]; omega) hx hn with
    h|h|h|h|h|h|h|h|h|h|h
  · exact ⟨.inl (), h.symm⟩
  · exact ⟨oneCode 2, by simpa [internalNat1, oneCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, by simpa [internalNat1, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩, by simpa [internalNat1, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩, by simpa [internalNat1, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩, by simpa [internalNat1, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, by simpa [internalNat1, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨2, by decide⟩, ⟨1, by decide⟩⟩, by simpa [internalNat1, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩, by simpa [internalNat1, twoCode, pick3] using h.symm⟩
  · exact ⟨oneCode 1, by simpa [internalNat1, oneCode, pick3] using h.symm⟩
  · exact ⟨oneCode 0, by simpa [internalNat1, oneCode, pick3] using h.symm⟩

theorem internalNat2_covers (t x : ℕ) (hx : x ≤ q2 t) (hn : x ∉ leafLabels (q2 t)) :
    ∃ a, internalNat2 t a = x := by
  rcases skeleton_label_cases (q2 t) x (by dsimp [q2]; omega) hx hn with
    h|h|h|h|h|h|h|h|h|h|h
  · exact ⟨.inl (), h.symm⟩
  · exact ⟨oneCode 1, by simpa [internalNat2, oneCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨2, by decide⟩, ⟨1, by decide⟩⟩, by simpa [internalNat2, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩, by simpa [internalNat2, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, by simpa [internalNat2, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩, by simpa [internalNat2, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩, by simpa [internalNat2, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩, by simpa [internalNat2, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, by simpa [internalNat2, twoCode, pick3] using h.symm⟩
  · exact ⟨oneCode 0, by simpa [internalNat2, oneCode, pick3] using h.symm⟩
  · exact ⟨oneCode 2, by simpa [internalNat2, oneCode, pick3] using h.symm⟩

theorem alternateInternalNat_covers (t x : ℕ) (hx : x ≤ q2 t) (hn : x ∉ leafLabels (q2 t)) :
    ∃ a, alternateInternalNat t a = x := by
  rcases skeleton_label_cases (q2 t) x (by dsimp [q2]; omega) hx hn with
    h|h|h|h|h|h|h|h|h|h|h
  · exact ⟨.inl (), h.symm⟩
  · exact ⟨twoCode ⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, by simpa [alternateInternalNat, twoCode, pick3] using h.symm⟩
  · exact ⟨oneCode 2, by simpa [alternateInternalNat, oneCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, by simpa [alternateInternalNat, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩, by simpa [alternateInternalNat, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩, by simpa [alternateInternalNat, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩, by simpa [alternateInternalNat, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨2, by decide⟩, ⟨1, by decide⟩⟩, by simpa [alternateInternalNat, twoCode, pick3] using h.symm⟩
  · exact ⟨twoCode ⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩, by simpa [alternateInternalNat, twoCode, pick3] using h.symm⟩
  · exact ⟨oneCode 0, by simpa [alternateInternalNat, oneCode, pick3] using h.symm⟩
  · exact ⟨oneCode 1, by simpa [alternateInternalNat, oneCode, pick3] using h.symm⟩

theorem fullFinalParent0_range (t v x : ℕ) (hx : x ∈ leafLabels (q0 t))
    (hC : x ≠ internalNat0 t splitCode) : ∃ c, fullFinalParent0 t v x = internalNat0 t (twoCode c) := by
  have hC' : x ≠ (anchor0 t).C := by simpa [internalNat0, splitCode, splitDepth, twoCode] using hC
  unfold fullFinalParent0 fullParent
  rw [if_pos hx]
  unfold finalParent0 splitParent
  rw [if_neg hC']
  unfold afterPairs0 moveSelectedPairs afterFirst0 moveTwo baseParent0
  try simp only [ite_apply]
  split_ifs <;> first
  | contradiction
  | (refine ⟨⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, ?_⟩; simp [internalNat0, twoCode, pick3, q0, anchor0] <;> omega)
  | (refine ⟨⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩, ?_⟩; simp [internalNat0, twoCode, pick3, q0, anchor0] <;> omega)
  | (refine ⟨⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩, ?_⟩; simp [internalNat0, twoCode, pick3, q0, q0, anchor0] <;> omega)
  | (refine ⟨⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ?_⟩; simp [internalNat0, twoCode, pick3, q0, q0, anchor0] <;> omega)
  | (refine ⟨⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩, ?_⟩; simp [internalNat0, twoCode, pick3, q0, anchor0] <;> omega)
  | (refine ⟨⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩, ?_⟩; simp [internalNat0, twoCode, pick3, q0, q0, anchor0] <;> omega)
  | (refine ⟨⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩, ?_⟩; simp [internalNat0, twoCode, pick3, q0, anchor0] <;> omega)
  | (refine ⟨⟨⟨2, by decide⟩, ⟨1, by decide⟩⟩, ?_⟩; simp [internalNat0, twoCode, pick3, q0, anchor0] <;> omega)

theorem fullFinalParent1_range (t u x : ℕ) (hx : x ∈ leafLabels (q1 t))
    (hC : x ≠ internalNat1 t splitCode) : ∃ c, fullFinalParent1 t u x = internalNat1 t (twoCode c) := by
  have hC' : x ≠ (anchor1 t).C := by simpa [internalNat1, splitCode, splitDepth, twoCode] using hC
  unfold fullFinalParent1 fullParent
  rw [if_pos hx]
  unfold finalParent1 splitParent
  rw [if_neg hC']
  unfold afterPairs1 moveSelectedPairs afterFirst1 moveTwo baseParent1
  try simp only [ite_apply]
  split_ifs <;> first
  | contradiction
  | (refine ⟨⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, ?_⟩; simp [internalNat1, twoCode, pick3, q1, anchor1] <;> omega)
  | (refine ⟨⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩, ?_⟩; simp [internalNat1, twoCode, pick3, q1, anchor1] <;> omega)
  | (refine ⟨⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩, ?_⟩; simp [internalNat1, twoCode, pick3, q1, q1, anchor1] <;> omega)
  | (refine ⟨⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ?_⟩; simp [internalNat1, twoCode, pick3, q1, q1, anchor1] <;> omega)
  | (refine ⟨⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩, ?_⟩; simp [internalNat1, twoCode, pick3, q1, anchor1] <;> omega)
  | (refine ⟨⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩, ?_⟩; simp [internalNat1, twoCode, pick3, q1, anchor1] <;> omega)
  | (refine ⟨⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩, ?_⟩; simp [internalNat1, twoCode, pick3, q1, anchor1] <;> omega)
  | (refine ⟨⟨⟨2, by decide⟩, ⟨1, by decide⟩⟩, ?_⟩; simp [internalNat1, twoCode, pick3, q1, q1, anchor1] <;> omega)

theorem fullFinalParent2_range (t v x : ℕ) (hx : x ∈ leafLabels (q2 t))
    (hC : x ≠ internalNat2 t splitCode) : ∃ c, fullFinalParent2 t v x = internalNat2 t (twoCode c) := by
  have hC' : x ≠ (anchor2 t).C := by simpa [internalNat2, splitCode, splitDepth, twoCode] using hC
  unfold fullFinalParent2 fullParent
  rw [if_pos hx]
  unfold finalParent2 splitParent
  rw [if_neg hC']
  unfold afterPairs2 moveSelectedPairs afterFirst2 moveTwo baseParent2
  try simp only [ite_apply]
  split_ifs <;> first
  | contradiction
  | (refine ⟨⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, ?_⟩; simp [internalNat2, twoCode, pick3, q2, anchor2] <;> omega)
  | (refine ⟨⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩, ?_⟩; simp [internalNat2, twoCode, pick3, q2, anchor2] <;> omega)
  | (refine ⟨⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩, ?_⟩; simp [internalNat2, twoCode, pick3, q2, q2, anchor2] <;> omega)
  | (refine ⟨⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ?_⟩; simp [internalNat2, twoCode, pick3, q2, q2, anchor2] <;> omega)
  | (refine ⟨⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩, ?_⟩; simp [internalNat2, twoCode, pick3, q2, anchor2] <;> omega)
  | (refine ⟨⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩, ?_⟩; simp [internalNat2, twoCode, pick3, q2, q2, anchor2] <;> omega)
  | (refine ⟨⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩, ?_⟩; simp [internalNat2, twoCode, pick3, q2, anchor2] <;> omega)
  | (refine ⟨⟨⟨2, by decide⟩, ⟨1, by decide⟩⟩, ?_⟩; simp [internalNat2, twoCode, pick3, q2, anchor2] <;> omega)

theorem fullAlternateFinalParent_range (t x : ℕ) (hx : x ∈ leafLabels (q2 t))
    (hC : x ≠ alternateInternalNat t splitCode) :
    ∃ c, fullAlternateFinalParent t x = alternateInternalNat t (twoCode c) := by
  have hC' : x ≠ (alternateAnchor t).C := by
    simpa [alternateInternalNat, splitCode, splitDepth, twoCode] using hC
  unfold fullAlternateFinalParent fullParent
  rw [if_pos hx]
  unfold alternateFinalParent splitParent
  rw [if_neg hC']
  unfold alternateAfterFirst moveTwo alternateBaseParent
  try simp only [ite_apply]
  split_ifs <;> first
  | contradiction
  | (refine ⟨⟨⟨0, by decide⟩, ⟨0, by decide⟩⟩, ?_⟩; simp [alternateInternalNat, twoCode, pick3, q2, alternateAnchor] <;> omega)
  | (refine ⟨⟨⟨0, by decide⟩, ⟨1, by decide⟩⟩, ?_⟩; simp [alternateInternalNat, twoCode, pick3, q2, alternateAnchor] <;> omega)
  | (refine ⟨⟨⟨0, by decide⟩, ⟨2, by decide⟩⟩, ?_⟩; simp [alternateInternalNat, twoCode, pick3, q2, q2, alternateAnchor] <;> omega)
  | (refine ⟨⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩, ?_⟩; simp [alternateInternalNat, twoCode, pick3, q2, alternateAnchor] <;> omega)
  | (refine ⟨⟨⟨1, by decide⟩, ⟨1, by decide⟩⟩, ?_⟩; simp [alternateInternalNat, twoCode, pick3, q2, q2, alternateAnchor] <;> omega)
  | (refine ⟨⟨⟨1, by decide⟩, ⟨2, by decide⟩⟩, ?_⟩; simp [alternateInternalNat, twoCode, pick3, q2, alternateAnchor] <;> omega)
  | (refine ⟨⟨⟨2, by decide⟩, ⟨0, by decide⟩⟩, ?_⟩; simp [alternateInternalNat, twoCode, pick3, q2, alternateAnchor] <;> omega)
  | (refine ⟨⟨⟨2, by decide⟩, ⟨1, by decide⟩⟩, ?_⟩; simp [alternateInternalNat, twoCode, pick3, q2, q2, alternateAnchor] <;> omega)

def profile0OfCounts (u v t : ℕ) (hq : q u v = q0 t)
    (hc : ∀ c, (Symbolic.fibre (q0 t) (finalParent0 t v) (internalNat0 t (twoCode c))).card =
      pendantCount u v c.1 c.2) : ProfileFrame u v :=
  frameOfNaturalFibers u v (fullFinalParent0 t v) (internalNat0 t)
    (fun x _ => by rw [hq]; exact fullFinalParent0_bound t v x)
    (fun a => by rw [hq]; exact internalNat0_bound t a)
    (internalNat0_injective t) rfl (fullFinalParent0_internal t v)
    (by simpa only [hq] using internalNat0_covers t)
    (by simpa only [hq] using fullFinalParent0_range t v)
    (by intro c; rw [hq]; unfold fullFinalParent0; rw [naturalFiber_fullParent]; exact hc c)

def profile1OfCounts (u v t : ℕ) (hq : q u v = q1 t)
    (hc : ∀ c, (Symbolic.fibre (q1 t) (finalParent1 t u) (internalNat1 t (twoCode c))).card =
      pendantCount u v c.1 c.2) : ProfileFrame u v :=
  frameOfNaturalFibers u v (fullFinalParent1 t u) (internalNat1 t)
    (fun x _ => by rw [hq]; exact fullFinalParent1_bound t u x)
    (fun a => by rw [hq]; exact internalNat1_bound t a)
    (internalNat1_injective t) rfl (fullFinalParent1_internal t u)
    (by simpa only [hq] using internalNat1_covers t)
    (by simpa only [hq] using fullFinalParent1_range t u)
    (by intro c; rw [hq]; unfold fullFinalParent1; rw [naturalFiber_fullParent]; exact hc c)

def profile2OfCounts (u v t : ℕ) (hq : q u v = q2 t)
    (hc : ∀ c, (Symbolic.fibre (q2 t) (finalParent2 t v) (internalNat2 t (twoCode c))).card =
      pendantCount u v c.1 c.2) : ProfileFrame u v :=
  frameOfNaturalFibers u v (fullFinalParent2 t v) (internalNat2 t)
    (fun x _ => by rw [hq]; exact fullFinalParent2_bound t v x)
    (fun a => by rw [hq]; exact internalNat2_bound t a)
    (internalNat2_injective t) rfl (fullFinalParent2_internal t v)
    (by simpa only [hq] using internalNat2_covers t)
    (by simpa only [hq] using fullFinalParent2_range t v)
    (by intro c; rw [hq]; unfold fullFinalParent2; rw [naturalFiber_fullParent]; exact hc c)

def alternateProfileOfCounts (u v t : ℕ) (hq : q u v = q2 t)
    (hc : ∀ c, (Symbolic.fibre (q2 t) (alternateFinalParent t) (alternateInternalNat t (twoCode c))).card =
      pendantCount u v c.1 c.2) : ProfileFrame u v :=
  frameOfNaturalFibers u v (fullAlternateFinalParent t) (alternateInternalNat t)
    (fun x _ => by rw [hq]; exact fullAlternateFinalParent_bound t x)
    (fun a => by rw [hq]; exact alternateInternalNat_bound t a)
    (alternateInternalNat_injective t) rfl (fullAlternateFinalParent_internal t)
    (by simpa only [hq] using alternateInternalNat_covers t)
    (by simpa only [hq] using fullAlternateFinalParent_range t)
    (by intro c; rw [hq]; unfold fullAlternateFinalParent; rw [naturalFiber_fullParent]; exact hc c)

/-! Complete raw difference coverage of the four base parent presentations. -/

def RawCoverage (Q : ℕ) (p : ℕ → ℕ) : Prop :=
  ∀ d : ℕ, (1 ≤ d ∧ d ≤ Q) ↔ ∃ x : ℕ, 1 ≤ x ∧ x ≤ Q ∧ Nat.dist x (p x) = d

def standardSkeletonRange (Q d : ℕ) : Prop :=
  d=1 ∨ d=2 ∨ d=3 ∨ (Q-6 ≤ d ∧ d ≤ Q)
def alternateSkeletonRange (Q d : ℕ) : Prop :=
  d=1 ∨ d=2 ∨ d=4 ∨ (Q-6 ≤ d ∧ d ≤ Q)

def skeletonInverse0 (Q d : ℕ) : ℕ :=
  if d=1 then 1 else if d=2 then Q-2 else if d=3 then 4
  else if d=Q-6 then 5 else if d=Q-5 then Q-4 else if d=Q-4 then Q-3
  else if d=Q-3 then 3 else if d=Q-2 then 2 else if d=Q-1 then Q-1 else Q
def skeletonInverse1 (Q d : ℕ) : ℕ :=
  if d=1 then 1 else if d=2 then Q-2 else if d=3 then Q-4
  else if d=Q-6 then 5 else if d=Q-5 then 4 else if d=Q-4 then Q-3
  else if d=Q-3 then 3 else if d=Q-2 then 2 else if d=Q-1 then Q-1 else Q
def skeletonInverse2 (Q d : ℕ) : ℕ :=
  if d=1 then 1 else if d=2 then 3 else if d=3 then Q-4
  else if d=Q-6 then 5 else if d=Q-5 then 4 else if d=Q-4 then Q-3
  else if d=Q-3 then Q-2 else if d=Q-2 then 2 else if d=Q-1 then Q-1 else Q
def alternateSkeletonInverse (Q d : ℕ) : ℕ :=
  if d=1 then Q-2 else if d=2 then 2 else if d=4 then Q-4
  else if d=Q-6 then 5 else if d=Q-5 then Q-3 else if d=Q-4 then 4
  else if d=Q-3 then 3 else if d=Q-2 then 1 else if d=Q-1 then Q-1 else Q

theorem skeletonParent0_coverage (Q : ℕ) (hQ : 23 ≤ Q) (d : ℕ) :
    (∃ x, 1 ≤ x ∧ x ≤ Q ∧ x ∉ leafLabels Q ∧ Nat.dist x (skeletonParent0 Q x) = d) ↔
      standardSkeletonRange Q d := by
  constructor
  · rintro ⟨x, hx, hxb, hn, hd⟩
    have hc := skeleton_label_cases Q x (by omega) hxb hn
    rcases hc with h|h|h|h|h|h|h|h|h|h|h
    · subst x
      omega
    · subst x
      have hp : skeletonParent0 Q (1) = 0 := by
        unfold skeletonParent0
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      left
      omega
    · subst x
      have hp : skeletonParent0 Q (2) = Q := by
        unfold skeletonParent0
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent0 Q (3) = Q := by
        unfold skeletonParent0
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent0 Q (4) = 1 := by
        unfold skeletonParent0
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; left
      omega
    · subst x
      have hp : skeletonParent0 Q (5) = Q-1 := by
        unfold skeletonParent0
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent0 Q (Q-4) = 1 := by
        unfold skeletonParent0
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent0 Q (Q-3) = 1 := by
        unfold skeletonParent0
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent0 Q (Q-2) = Q := by
        unfold skeletonParent0
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; left
      omega
    · subst x
      have hp : skeletonParent0 Q (Q-1) = 0 := by
        unfold skeletonParent0
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent0 Q (Q) = 0 := by
        unfold skeletonParent0
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
  · intro hd
    simp only [standardSkeletonRange] at hd
    rcases hd with hd | hd | hd | ⟨hlo, hhi⟩
    · subst d
      refine ⟨1, by omega, by omega, ?_, ?_⟩
      · simp only [leafLabels, Finset.mem_Icc]
        omega
      · have hp : skeletonParent0 Q (1) = 0 := by
          unfold skeletonParent0
          split_ifs <;> omega
        rw [hp]
        simp only [Nat.dist] <;> omega
    · subst d
      refine ⟨Q-2, by omega, by omega, ?_, ?_⟩
      · simp only [leafLabels, Finset.mem_Icc]
        omega
      · have hp : skeletonParent0 Q (Q-2) = Q := by
          unfold skeletonParent0
          split_ifs <;> omega
        rw [hp]
        simp only [Nat.dist] <;> omega
    · subst d
      refine ⟨4, by omega, by omega, ?_, ?_⟩
      · simp only [leafLabels, Finset.mem_Icc]
        omega
      · have hp : skeletonParent0 Q (4) = 1 := by
          unfold skeletonParent0
          split_ifs <;> omega
        rw [hp]
        simp only [Nat.dist] <;> omega
    · have hcases : d = Q-6 ∨ d = Q-5 ∨ d = Q-4 ∨ d = Q-3 ∨ d = Q-2 ∨ d = Q-1 ∨ d = Q := by omega
      rcases hcases with hd | hd | hd | hd | hd | hd | hd
      · subst d
        refine ⟨5, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent0 Q (5) = Q-1 := by
            unfold skeletonParent0
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨Q-4, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent0 Q (Q-4) = 1 := by
            unfold skeletonParent0
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨Q-3, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent0 Q (Q-3) = 1 := by
            unfold skeletonParent0
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨3, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent0 Q (3) = Q := by
            unfold skeletonParent0
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨2, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent0 Q (2) = Q := by
            unfold skeletonParent0
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨Q-1, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent0 Q (Q-1) = 0 := by
            unfold skeletonParent0
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨Q, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent0 Q (Q) = 0 := by
            unfold skeletonParent0
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega

theorem skeletonParent1_coverage (Q : ℕ) (hQ : 23 ≤ Q) (d : ℕ) :
    (∃ x, 1 ≤ x ∧ x ≤ Q ∧ x ∉ leafLabels Q ∧ Nat.dist x (skeletonParent1 Q x) = d) ↔
      standardSkeletonRange Q d := by
  constructor
  · rintro ⟨x, hx, hxb, hn, hd⟩
    have hc := skeleton_label_cases Q x (by omega) hxb hn
    rcases hc with h|h|h|h|h|h|h|h|h|h|h
    · subst x
      omega
    · subst x
      have hp : skeletonParent1 Q (1) = 0 := by
        unfold skeletonParent1
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      left
      omega
    · subst x
      have hp : skeletonParent1 Q (2) = Q := by
        unfold skeletonParent1
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent1 Q (3) = Q := by
        unfold skeletonParent1
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent1 Q (4) = Q-1 := by
        unfold skeletonParent1
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent1 Q (5) = Q-1 := by
        unfold skeletonParent1
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent1 Q (Q-4) = Q-1 := by
        unfold skeletonParent1
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; left
      omega
    · subst x
      have hp : skeletonParent1 Q (Q-3) = 1 := by
        unfold skeletonParent1
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent1 Q (Q-2) = Q := by
        unfold skeletonParent1
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; left
      omega
    · subst x
      have hp : skeletonParent1 Q (Q-1) = 0 := by
        unfold skeletonParent1
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent1 Q (Q) = 0 := by
        unfold skeletonParent1
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
  · intro hd
    simp only [standardSkeletonRange] at hd
    rcases hd with hd | hd | hd | ⟨hlo, hhi⟩
    · subst d
      refine ⟨1, by omega, by omega, ?_, ?_⟩
      · simp only [leafLabels, Finset.mem_Icc]
        omega
      · have hp : skeletonParent1 Q (1) = 0 := by
          unfold skeletonParent1
          split_ifs <;> omega
        rw [hp]
        simp only [Nat.dist] <;> omega
    · subst d
      refine ⟨Q-2, by omega, by omega, ?_, ?_⟩
      · simp only [leafLabels, Finset.mem_Icc]
        omega
      · have hp : skeletonParent1 Q (Q-2) = Q := by
          unfold skeletonParent1
          split_ifs <;> omega
        rw [hp]
        simp only [Nat.dist] <;> omega
    · subst d
      refine ⟨Q-4, by omega, by omega, ?_, ?_⟩
      · simp only [leafLabels, Finset.mem_Icc]
        omega
      · have hp : skeletonParent1 Q (Q-4) = Q-1 := by
          unfold skeletonParent1
          split_ifs <;> omega
        rw [hp]
        simp only [Nat.dist] <;> omega
    · have hcases : d = Q-6 ∨ d = Q-5 ∨ d = Q-4 ∨ d = Q-3 ∨ d = Q-2 ∨ d = Q-1 ∨ d = Q := by omega
      rcases hcases with hd | hd | hd | hd | hd | hd | hd
      · subst d
        refine ⟨5, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent1 Q (5) = Q-1 := by
            unfold skeletonParent1
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨4, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent1 Q (4) = Q-1 := by
            unfold skeletonParent1
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨Q-3, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent1 Q (Q-3) = 1 := by
            unfold skeletonParent1
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨3, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent1 Q (3) = Q := by
            unfold skeletonParent1
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨2, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent1 Q (2) = Q := by
            unfold skeletonParent1
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨Q-1, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent1 Q (Q-1) = 0 := by
            unfold skeletonParent1
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨Q, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent1 Q (Q) = 0 := by
            unfold skeletonParent1
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega

theorem skeletonParent2_coverage (Q : ℕ) (hQ : 23 ≤ Q) (d : ℕ) :
    (∃ x, 1 ≤ x ∧ x ≤ Q ∧ x ∉ leafLabels Q ∧ Nat.dist x (skeletonParent2 Q x) = d) ↔
      standardSkeletonRange Q d := by
  constructor
  · rintro ⟨x, hx, hxb, hn, hd⟩
    have hc := skeleton_label_cases Q x (by omega) hxb hn
    rcases hc with h|h|h|h|h|h|h|h|h|h|h
    · subst x
      omega
    · subst x
      have hp : skeletonParent2 Q (1) = 0 := by
        unfold skeletonParent2
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      left
      omega
    · subst x
      have hp : skeletonParent2 Q (2) = Q := by
        unfold skeletonParent2
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent2 Q (3) = 1 := by
        unfold skeletonParent2
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; left
      omega
    · subst x
      have hp : skeletonParent2 Q (4) = Q-1 := by
        unfold skeletonParent2
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent2 Q (5) = Q-1 := by
        unfold skeletonParent2
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent2 Q (Q-4) = Q-1 := by
        unfold skeletonParent2
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; left
      omega
    · subst x
      have hp : skeletonParent2 Q (Q-3) = 1 := by
        unfold skeletonParent2
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent2 Q (Q-2) = 1 := by
        unfold skeletonParent2
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent2 Q (Q-1) = 0 := by
        unfold skeletonParent2
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : skeletonParent2 Q (Q) = 0 := by
        unfold skeletonParent2
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold standardSkeletonRange
      right; right; right
      constructor <;> omega
  · intro hd
    simp only [standardSkeletonRange] at hd
    rcases hd with hd | hd | hd | ⟨hlo, hhi⟩
    · subst d
      refine ⟨1, by omega, by omega, ?_, ?_⟩
      · simp only [leafLabels, Finset.mem_Icc]
        omega
      · have hp : skeletonParent2 Q (1) = 0 := by
          unfold skeletonParent2
          split_ifs <;> omega
        rw [hp]
        simp only [Nat.dist] <;> omega
    · subst d
      refine ⟨3, by omega, by omega, ?_, ?_⟩
      · simp only [leafLabels, Finset.mem_Icc]
        omega
      · have hp : skeletonParent2 Q (3) = 1 := by
          unfold skeletonParent2
          split_ifs <;> omega
        rw [hp]
        simp only [Nat.dist] <;> omega
    · subst d
      refine ⟨Q-4, by omega, by omega, ?_, ?_⟩
      · simp only [leafLabels, Finset.mem_Icc]
        omega
      · have hp : skeletonParent2 Q (Q-4) = Q-1 := by
          unfold skeletonParent2
          split_ifs <;> omega
        rw [hp]
        simp only [Nat.dist] <;> omega
    · have hcases : d = Q-6 ∨ d = Q-5 ∨ d = Q-4 ∨ d = Q-3 ∨ d = Q-2 ∨ d = Q-1 ∨ d = Q := by omega
      rcases hcases with hd | hd | hd | hd | hd | hd | hd
      · subst d
        refine ⟨5, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent2 Q (5) = Q-1 := by
            unfold skeletonParent2
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨4, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent2 Q (4) = Q-1 := by
            unfold skeletonParent2
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨Q-3, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent2 Q (Q-3) = 1 := by
            unfold skeletonParent2
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨Q-2, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent2 Q (Q-2) = 1 := by
            unfold skeletonParent2
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨2, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent2 Q (2) = Q := by
            unfold skeletonParent2
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨Q-1, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent2 Q (Q-1) = 0 := by
            unfold skeletonParent2
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨Q, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : skeletonParent2 Q (Q) = 0 := by
            unfold skeletonParent2
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega

theorem alternateSkeletonParent_coverage (Q : ℕ) (hQ : 23 ≤ Q) (d : ℕ) :
    (∃ x, 1 ≤ x ∧ x ≤ Q ∧ x ∉ leafLabels Q ∧ Nat.dist x (alternateSkeletonParent Q x) = d) ↔
      alternateSkeletonRange Q d := by
  constructor
  · rintro ⟨x, hx, hxb, hn, hd⟩
    have hc := skeleton_label_cases Q x (by omega) hxb hn
    rcases hc with h|h|h|h|h|h|h|h|h|h|h
    · subst x
      omega
    · subst x
      have hp : alternateSkeletonParent Q (1) = Q-1 := by
        unfold alternateSkeletonParent
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold alternateSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : alternateSkeletonParent Q (2) = 0 := by
        unfold alternateSkeletonParent
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold alternateSkeletonRange
      right; left
      omega
    · subst x
      have hp : alternateSkeletonParent Q (3) = Q := by
        unfold alternateSkeletonParent
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold alternateSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : alternateSkeletonParent Q (4) = Q := by
        unfold alternateSkeletonParent
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold alternateSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : alternateSkeletonParent Q (5) = Q-1 := by
        unfold alternateSkeletonParent
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold alternateSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : alternateSkeletonParent Q (Q-4) = Q := by
        unfold alternateSkeletonParent
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold alternateSkeletonRange
      right; right; left
      omega
    · subst x
      have hp : alternateSkeletonParent Q (Q-3) = 2 := by
        unfold alternateSkeletonParent
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold alternateSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : alternateSkeletonParent Q (Q-2) = Q-1 := by
        unfold alternateSkeletonParent
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold alternateSkeletonRange
      left
      omega
    · subst x
      have hp : alternateSkeletonParent Q (Q-1) = 0 := by
        unfold alternateSkeletonParent
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold alternateSkeletonRange
      right; right; right
      constructor <;> omega
    · subst x
      have hp : alternateSkeletonParent Q (Q) = 0 := by
        unfold alternateSkeletonParent
        split_ifs <;> omega
      rw [hp] at hd
      simp only [Nat.dist] at hd
      unfold alternateSkeletonRange
      right; right; right
      constructor <;> omega
  · intro hd
    simp only [alternateSkeletonRange] at hd
    rcases hd with hd | hd | hd | ⟨hlo, hhi⟩
    · subst d
      refine ⟨Q-2, by omega, by omega, ?_, ?_⟩
      · simp only [leafLabels, Finset.mem_Icc]
        omega
      · have hp : alternateSkeletonParent Q (Q-2) = Q-1 := by
          unfold alternateSkeletonParent
          split_ifs <;> omega
        rw [hp]
        simp only [Nat.dist] <;> omega
    · subst d
      refine ⟨2, by omega, by omega, ?_, ?_⟩
      · simp only [leafLabels, Finset.mem_Icc]
        omega
      · have hp : alternateSkeletonParent Q (2) = 0 := by
          unfold alternateSkeletonParent
          split_ifs <;> omega
        rw [hp]
        simp only [Nat.dist] <;> omega
    · subst d
      refine ⟨Q-4, by omega, by omega, ?_, ?_⟩
      · simp only [leafLabels, Finset.mem_Icc]
        omega
      · have hp : alternateSkeletonParent Q (Q-4) = Q := by
          unfold alternateSkeletonParent
          split_ifs <;> omega
        rw [hp]
        simp only [Nat.dist] <;> omega
    · have hcases : d = Q-6 ∨ d = Q-5 ∨ d = Q-4 ∨ d = Q-3 ∨ d = Q-2 ∨ d = Q-1 ∨ d = Q := by omega
      rcases hcases with hd | hd | hd | hd | hd | hd | hd
      · subst d
        refine ⟨5, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : alternateSkeletonParent Q (5) = Q-1 := by
            unfold alternateSkeletonParent
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨Q-3, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : alternateSkeletonParent Q (Q-3) = 2 := by
            unfold alternateSkeletonParent
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨4, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : alternateSkeletonParent Q (4) = Q := by
            unfold alternateSkeletonParent
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨3, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : alternateSkeletonParent Q (3) = Q := by
            unfold alternateSkeletonParent
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨1, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : alternateSkeletonParent Q (1) = Q-1 := by
            unfold alternateSkeletonParent
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨Q-1, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : alternateSkeletonParent Q (Q-1) = 0 := by
            unfold alternateSkeletonParent
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega
      · subst d
        refine ⟨Q, by omega, by omega, ?_, ?_⟩
        · simp only [leafLabels, Finset.mem_Icc]
          omega
        · have hp : alternateSkeletonParent Q (Q) = 0 := by
            unfold alternateSkeletonParent
            split_ifs <;> omega
          rw [hp]
          simp only [Nat.dist] <;> omega

theorem rawCoverage_of_partition (Q : ℕ) (s p : ℕ → ℕ) (A B : ℕ → Prop)
    (hsk : ∀ d, (∃ x, 1 ≤ x ∧ x ≤ Q ∧ x ∉ leafLabels Q ∧ Nat.dist x (s x) = d) ↔ A d)
    (hleaf : ∀ d, (∃ x ∈ leafLabels Q, Nat.dist x (p x) = d) ↔ B d)
    (hparts : ∀ d, A d ∨ B d ↔ 1 ≤ d ∧ d ≤ Q) : RawCoverage Q (fullParent Q s p) := by
  intro d
  constructor
  · intro hd
    rcases (hparts d).2 hd with ha | hb
    · obtain ⟨x, hx, hxb, hn, he⟩ := (hsk d).2 ha
      exact ⟨x, hx, hxb, by simpa [fullParent, hn] using he⟩
    · obtain ⟨x, hx, he⟩ := (hleaf d).2 hb
      have hxb := hx
      simp only [leafLabels, Finset.mem_Icc] at hxb
      exact ⟨x, by omega, by omega, by simpa [fullParent, hx] using he⟩
  · rintro ⟨x, hx, hxb, he⟩
    apply (hparts d).1
    by_cases hl : x ∈ leafLabels Q
    · exact Or.inr ((hleaf d).1 ⟨x, hl, by simpa [fullParent, hl] using he⟩)
    · exact Or.inl ((hsk d).1 ⟨x, hx, hxb, hl, by simpa [fullParent, hl] using he⟩)

theorem fullBaseParent0_coverage (t : ℕ) : RawCoverage (q0 t) (fullBaseParent0 t) := by
  apply rawCoverage_of_partition _ _ _ (standardSkeletonRange _) (fun d => 4≤d ∧ d≤q0 t-7)
  · exact skeletonParent0_coverage _ (by dsimp [q0]; omega)
  · exact baseDifference0 t
  · intro d; dsimp [standardSkeletonRange, q0]; omega
theorem fullBaseParent1_coverage (t : ℕ) : RawCoverage (q1 t) (fullBaseParent1 t) := by
  apply rawCoverage_of_partition _ _ _ (standardSkeletonRange _) (fun d => 4≤d ∧ d≤q1 t-7)
  · exact skeletonParent1_coverage _ (by dsimp [q1]; omega)
  · exact baseDifference1 t
  · intro d; dsimp [standardSkeletonRange, q1]; omega
theorem fullBaseParent2_coverage (t : ℕ) : RawCoverage (q2 t) (fullBaseParent2 t) := by
  apply rawCoverage_of_partition _ _ _ (standardSkeletonRange _) (fun d => 4≤d ∧ d≤q2 t-7)
  · exact skeletonParent2_coverage _ (by dsimp [q2]; omega)
  · exact baseDifference2 t
  · intro d; dsimp [standardSkeletonRange, q2]; omega
theorem fullAlternateBaseParent_coverage (t : ℕ) : RawCoverage (q2 t) (fullAlternateBaseParent t) := by
  apply rawCoverage_of_partition _ _ _ (alternateSkeletonRange _)
    (fun d => d=3 ∨ (5≤d ∧ d≤q2 t-7))
  · exact alternateSkeletonParent_coverage _ (by dsimp [q2]; omega)
  · exact alternateBaseDifference t
  · intro d; dsimp [alternateSkeletonRange, q2]; omega

theorem rawCoverage_of_involution (Q : ℕ) (p p' σ : ℕ → ℕ)
    (hinv : Function.Involutive σ)
    (hmem : ∀ x, 1 ≤ x → x ≤ Q → 1 ≤ σ x ∧ σ x ≤ Q)
    (hperm : ∀ x, Nat.dist x (p' x) = Nat.dist (σ x) (p (σ x)))
    (h : RawCoverage Q p) : RawCoverage Q p' := by
  intro d
  rw [h d]
  constructor
  · rintro ⟨x, hx, hxb, hd⟩
    have hm := hmem x hx hxb
    refine ⟨σ x, hm.1, hm.2, ?_⟩
    rw [hperm, hinv x]
    exact hd
  · rintro ⟨x, hx, hxb, hd⟩
    have hm := hmem x hx hxb
    exact ⟨σ x, hm.1, hm.2, (hperm x).symm.trans hd⟩

theorem swapTwo_interval (Q a b : ℕ) (ha : 1 ≤ a ∧ a ≤ Q) (hb : 1 ≤ b ∧ b ≤ Q)
    (x : ℕ) (hx : 1 ≤ x) (hxb : x ≤ Q) :
    1 ≤ Operations.swapTwo a b x ∧ Operations.swapTwo a b x ≤ Q := by
  simp only [Operations.swapTwo]
  split_ifs
  · exact hb
  · exact ha
  · exact ⟨hx, hxb⟩

theorem moveTwo_difference (p : ℕ → ℕ) (a b donor recipient : ℕ)
    (hab : a ≠ b) (hpa : p a = donor) (hpb : p b = donor)
    (hsum : a + b = donor + recipient) (x : ℕ) :
    Nat.dist x (moveTwo p a b recipient x) =
      Nat.dist (Operations.swapTwo a b x) (p (Operations.swapTwo a b x)) := by
  have hd := Operations.pairTransferDifferencesNat donor recipient a b hsum
  by_cases hxa : x = a
  · subst x
    simpa [moveTwo, Operations.swapTwo, hpa, hpb, Nat.dist_comm] using hd.1
  · by_cases hxb : x = b
    · subst x
      simpa [moveTwo, Operations.swapTwo, hab, Ne.symm hab, hpa, hpb, Nat.dist_comm] using hd.2
    · simp [moveTwo, Operations.swapTwo, hxa, hxb]

theorem rawCoverage_moveTwo (Q : ℕ) (p : ℕ → ℕ) (a b donor recipient : ℕ)
    (ha : 1 ≤ a ∧ a ≤ Q) (hb : 1 ≤ b ∧ b ≤ Q) (hab : a ≠ b)
    (hpa : p a = donor) (hpb : p b = donor) (hsum : a+b=donor+recipient)
    (h : RawCoverage Q p) : RawCoverage Q (moveTwo p a b recipient) :=
  rawCoverage_of_involution Q p _ (Operations.swapTwo a b)
    (Operations.swapTwo_involutive a b) (swapTwo_interval Q a b ha hb)
    (moveTwo_difference p a b donor recipient hab hpa hpb hsum) h

theorem fullParent_moveTwo (Q : ℕ) (s p : ℕ → ℕ) (a b r : ℕ)
    (ha : a ∈ leafLabels Q) (hb : b ∈ leafLabels Q) :
    fullParent Q s (moveTwo p a b r) = moveTwo (fullParent Q s p) a b r := by
  funext x
  by_cases hx : x ∈ leafLabels Q
  · simp [fullParent, moveTwo, hx]
  · have hxa : x ≠ a := by intro he; exact hx (by simpa [he] using ha)
    have hxb : x ≠ b := by intro he; exact hx (by simpa [he] using hb)
    simp [fullParent, moveTwo, hx, hxa, hxb]

def fullAfterFirst0 (t : ℕ) := fullParent (q0 t) (skeletonParent0 (q0 t)) (afterFirst0 t)
def fullAfterFirst1 (t : ℕ) := fullParent (q1 t) (skeletonParent1 (q1 t)) (afterFirst1 t)
def fullAfterFirst2 (t : ℕ) := fullParent (q2 t) (skeletonParent2 (q2 t)) (afterFirst2 t)
def fullAlternateAfterFirst (t : ℕ) :=
  fullParent (q2 t) (alternateSkeletonParent (q2 t)) (alternateAfterFirst t)

theorem leaf_positive_bound (Q x : ℕ) (hx : x ∈ leafLabels Q) : 1 ≤ x ∧ x ≤ Q := by
  simp only [leafLabels, Finset.mem_Icc] at hx
  omega

theorem fullAfterFirst0_coverage (t : ℕ) : RawCoverage (q0 t) (fullAfterFirst0 t) := by
  by_cases ht : t = 0
  · subst t
    have ha : 13 ∈ leafLabels (q0 0) := by simp [leafLabels, q0]
    have hb : 17 ∈ leafLabels (q0 0) := by simp [leafLabels, q0]
    have he := rawCoverage_moveTwo (q0 0) (fullBaseParent0 0) 13 17 5 (q0 0-2)
      (leaf_positive_bound _ _ ha) (leaf_positive_bound _ _ hb) (by decide)
      (by simp [fullBaseParent0, fullParent, ha, baseParent0])
      (by simp [fullBaseParent0, fullParent, hb, baseParent0]) firstPair0_small_sum
      (fullBaseParent0_coverage 0)
    simpa only [fullBaseParent0, ite_true, fullAfterFirst0, afterFirst0, if_pos rfl, fullParent_moveTwo _ _ _ _ _ _ ha hb] using he
  · have ht' : 0 < t := by omega
    have ha : 9+2*t ∈ leafLabels (q0 t) := by simp only [leafLabels, q0, Finset.mem_Icc]; omega
    have hb : 21+4*t ∈ leafLabels (q0 t) := by simp only [leafLabels, q0, Finset.mem_Icc]; omega
    have hpa : fullBaseParent0 t (9+2*t) = 5 := by
      simp only [fullBaseParent0, fullParent, if_pos ha, baseParent0]; split_ifs <;> omega
    have hpb : fullBaseParent0 t (21+4*t) = 5 := by
      simp only [fullBaseParent0, fullParent, if_pos hb, baseParent0]; split_ifs <;> omega
    have he := rawCoverage_moveTwo (q0 t) (fullBaseParent0 t) (9+2*t) (21+4*t) 5 (q0 t-2)
      (leaf_positive_bound _ _ ha) (leaf_positive_bound _ _ hb) (by omega) hpa hpb
      (firstPair0_sum t) (fullBaseParent0_coverage t)
    simpa only [fullBaseParent0, ite_true, fullAfterFirst0, afterFirst0, if_neg ht, fullParent_moveTwo _ _ _ _ _ _ ha hb] using he

theorem fullAfterFirst1_coverage (t : ℕ) : RawCoverage (q1 t) (fullAfterFirst1 t) := by
  have ha : 13+3*t ∈ leafLabels (q1 t) := by simp only [leafLabels, q1, Finset.mem_Icc]; omega
  have hb : 14+3*t ∈ leafLabels (q1 t) := by simp only [leafLabels, q1, Finset.mem_Icc]; omega
  have hpa : fullBaseParent1 t (13+3*t) = 4 := by
    simp only [fullBaseParent1, fullParent, if_pos ha, baseParent1]; split_ifs <;> omega
  have hpb : fullBaseParent1 t (14+3*t) = 4 := by
    simp only [fullBaseParent1, fullParent, if_pos hb, baseParent1]; split_ifs <;> omega
  have he := rawCoverage_moveTwo (q1 t) (fullBaseParent1 t) (13+3*t) (14+3*t) 4 (q1 t-2)
    (leaf_positive_bound _ _ ha) (leaf_positive_bound _ _ hb) (by omega) hpa hpb
    (firstPair1_sum t) (fullBaseParent1_coverage t)
  simpa only [fullBaseParent1, ite_true, fullAfterFirst1, afterFirst1, fullParent_moveTwo _ _ _ _ _ _ ha hb] using he

theorem fullAfterFirst2_coverage (t : ℕ) : RawCoverage (q2 t) (fullAfterFirst2 t) := by
  have ha : 8+2*t ∈ leafLabels (q2 t) := by simp only [leafLabels, q2, Finset.mem_Icc]; omega
  have hb : 19+4*t ∈ leafLabels (q2 t) := by simp only [leafLabels, q2, Finset.mem_Icc]; omega
  have hpa : fullBaseParent2 t (8+2*t) = 2 := by
    simp only [fullBaseParent2, fullParent, if_pos ha, baseParent2]; split_ifs <;> omega
  have hpb : fullBaseParent2 t (19+4*t) = 2 := by
    simp only [fullBaseParent2, fullParent, if_pos hb, baseParent2]; split_ifs <;> omega
  have he := rawCoverage_moveTwo (q2 t) (fullBaseParent2 t) (8+2*t) (19+4*t) 2 (q2 t-4)
    (leaf_positive_bound _ _ ha) (leaf_positive_bound _ _ hb) (by omega) hpa hpb
    (firstPair2_sum t) (fullBaseParent2_coverage t)
  simpa only [fullBaseParent2, ite_true, fullAfterFirst2, afterFirst2, fullParent_moveTwo _ _ _ _ _ _ ha hb] using he

theorem fullAlternateAfterFirst_coverage (t : ℕ) : RawCoverage (q2 t) (fullAlternateAfterFirst t) := by
  have ha : 14+3*t ∈ leafLabels (q2 t) := by simp only [leafLabels, q2, Finset.mem_Icc]; omega
  have hb : 17+3*t ∈ leafLabels (q2 t) := by simp only [leafLabels, q2, Finset.mem_Icc]; omega
  have hpa : fullAlternateBaseParent t (14+3*t) = 4 := by
    simp only [fullAlternateBaseParent, fullParent, if_pos ha, alternateBaseParent]; split_ifs <;> omega
  have hpb : fullAlternateBaseParent t (17+3*t) = 4 := by
    simp only [fullAlternateBaseParent, fullParent, if_pos hb, alternateBaseParent]; split_ifs <;> omega
  have he := rawCoverage_moveTwo (q2 t) (fullAlternateBaseParent t) (14+3*t) (17+3*t) 4 (q2 t-2)
    (leaf_positive_bound _ _ ha) (leaf_positive_bound _ _ hb) (by omega) hpa hpb
    (alternateFirstPair_sum t) (fullAlternateBaseParent_coverage t)
  simpa only [fullAlternateBaseParent, ite_true, fullAlternateAfterFirst, alternateAfterFirst, fullParent_moveTwo _ _ _ _ _ _ ha hb] using he

theorem eligible_midpoint (Q S b : ℕ) (p : ℕ → ℕ) (a : Anchor) (s : Finset ℕ)
    (hs : s ⊆ eligiblePairStarts Q S b p a) : ∀ x ∈ s, 2*x < S := by
  intro x hx
  have he := hs hx
  simp only [eligiblePairStarts, Finset.mem_filter] at he
  omega

theorem eligible_positive (Q S b : ℕ) (p : ℕ → ℕ) (a : Anchor) (s : Finset ℕ)
    (hs : s ⊆ eligiblePairStarts Q S b p a) : ∀ x ∈ s, 0 < x := by
  intro x hx
  have he := hs hx
  simp only [eligiblePairStarts, Finset.mem_filter, leafLabels, Finset.mem_Icc] at he
  omega

theorem eligible_pair_properties (Q S b : ℕ) (p : ℕ → ℕ) (a : Anchor) (s : Finset ℕ)
    (hs : s ⊆ eligiblePairStarts Q S b p a) (x : ℕ) (hx : x ∈ Operations.reflectionPairs S s) :
    x ∈ leafLabels Q ∧ p x = b ∧ x ≠ a.C ∧ x ≠ a.Z := by
  obtain ⟨y, hy, hxy | hxy⟩ := (Operations.reflectionPairs_mem S x s).1 hx
  · have he := hs hy
    simp only [eligiblePairStarts, Finset.mem_filter] at he
    subst x
    exact ⟨he.1, he.2.2.2.1, he.2.2.2.2.2.1, he.2.2.2.2.2.2.1⟩
  · have he := hs hy
    simp only [eligiblePairStarts, Finset.mem_filter] at he
    subst x
    exact ⟨he.2.2.1, he.2.2.2.2.1, he.2.2.2.2.2.2.2.1, he.2.2.2.2.2.2.2.2⟩

theorem fullParent_moveSelectedPairs (Q S r : ℕ) (sk p : ℕ → ℕ) (s : Finset ℕ)
    (hv : ∀ x ∈ s, 2*x<S) (hp : ∀ x ∈ s, 0<x)
    (hleaf : ∀ x ∈ Operations.reflectionPairs S s, x ∈ leafLabels Q) :
    fullParent Q sk (moveSelectedPairs p S r s) =
      Operations.transferSelectedParent (fullParent Q sk p) S r s := by
  funext x
  rw [Operations.transferSelectedParent_predicate _ S r s hv hp]
  by_cases hx : x ∈ leafLabels Q
  · simp [fullParent, moveSelectedPairs, hx]
  · have hsel : ¬(x ∈ s ∨ S-x ∈ s) := by
      intro hsx
      exact hx (hleaf x ((Operations.reflectionPairs_mem_iff S s hv hp x).2 hsx))
    simp [fullParent, moveSelectedPairs, hx, hsel]

theorem rawCoverage_selectedPairs (Q S donor recipient : ℕ) (sk p : ℕ → ℕ)
    (a : Anchor) (s : Finset ℕ) (hs : s ⊆ eligiblePairStarts Q S donor p a)
    (hsum : donor+recipient=S) (h : RawCoverage Q (fullParent Q sk p)) :
    RawCoverage Q (fullParent Q sk (moveSelectedPairs p S recipient s)) := by
  have hv := eligible_midpoint Q S donor p a s hs
  have hp := eligible_positive Q S donor p a s hs
  have hprops := eligible_pair_properties Q S donor p a s hs
  rw [fullParent_moveSelectedPairs Q S recipient sk p s hv hp (fun x hx => (hprops x hx).1)]
  apply rawCoverage_of_involution Q (fullParent Q sk p) _ (Operations.reflectSelected S s)
  · exact Operations.reflectSelected_involutive S s hv
  · intro x hx hxb
    by_cases hsel : x ∈ Operations.reflectionPairs S s
    · have hr := Operations.reflectionPairs_reflect S s hv x hsel
      simpa [Operations.reflectSelected, hsel] using leaf_positive_bound Q (S-x) ((hprops _ hr).1)
    · simpa [Operations.reflectSelected, hsel] using And.intro hx hxb
  · apply Operations.transferSelected_difference (fullParent Q sk p) S donor recipient s hv hsum
    intro x hx
    have hpx := hprops x hx
    simpa [fullParent, hpx.1] using hpx.2.1
  · exact h

def fullAfterPairs0 (t v : ℕ) := fullParent (q0 t) (skeletonParent0 (q0 t)) (afterPairs0 t v)
def fullAfterPairs1 (t u : ℕ) := fullParent (q1 t) (skeletonParent1 (q1 t)) (afterPairs1 t u)
def fullAfterPairs2 (t v : ℕ) := fullParent (q2 t) (skeletonParent2 (q2 t)) (afterPairs2 t v)

theorem fullAfterPairs0_coverage (t v : ℕ) : RawCoverage (q0 t) (fullAfterPairs0 t v) := by
  exact rawCoverage_selectedPairs _ _ 5 _ _ _ _ _ (Operations.firstK_subset _ _)
    (by dsimp [q0]; omega) (fullAfterFirst0_coverage t)
theorem fullAfterPairs1_coverage (t u : ℕ) : RawCoverage (q1 t) (fullAfterPairs1 t u) := by
  exact rawCoverage_selectedPairs _ _ 4 _ _ _ _ _ (Operations.firstK_subset _ _)
    (by dsimp [q1]; omega) (fullAfterFirst1_coverage t)
theorem fullAfterPairs2_coverage (t v : ℕ) : RawCoverage (q2 t) (fullAfterPairs2 t v) := by
  exact rawCoverage_selectedPairs _ _ 2 _ _ _ _ _ (Operations.firstK_subset _ _)
    (by dsimp [q2]; omega) (fullAfterFirst2_coverage t)

theorem selectedPairs_keeps_anchor (Q S b r : ℕ) (p : ℕ → ℕ) (a : Anchor) (s : Finset ℕ)
    (hs : s ⊆ eligiblePairStarts Q S b p a) :
    moveSelectedPairs p S r s a.C = p a.C ∧ moveSelectedPairs p S r s a.Z = p a.Z := by
  have hv := eligible_midpoint Q S b p a s hs
  have hp := eligible_positive Q S b p a s hs
  have hprop := eligible_pair_properties Q S b p a s hs
  have hC : ¬(a.C ∈ s ∨ S-a.C ∈ s) := by
    intro hc
    have hm := (Operations.reflectionPairs_mem_iff S s hv hp a.C).2 hc
    exact (hprop a.C hm).2.2.1 rfl
  have hZ : ¬(a.Z ∈ s ∨ S-a.Z ∈ s) := by
    intro hz
    have hm := (Operations.reflectionPairs_mem_iff S s hv hp a.Z).2 hz
    exact (hprop a.Z hm).2.2.2 rfl
  simp [moveSelectedPairs, hC, hZ]

theorem afterFirst0_anchor (t : ℕ) :
    afterFirst0 t (anchor0 t).C = (anchor0 t).B ∧ afterFirst0 t (anchor0 t).Z = (anchor0 t).B := by
  have h := Symbolic.afterFirst0_anchor t
  exact ⟨h.2.2.1, h.2.2.2.1⟩

theorem afterFirst1_anchor (t : ℕ) :
    afterFirst1 t (anchor1 t).C = (anchor1 t).B ∧ afterFirst1 t (anchor1 t).Z = (anchor1 t).B := by
  have h := Symbolic.afterFirst1_anchor t
  exact ⟨h.2.2.1, h.2.2.2.1⟩

theorem afterFirst2_anchor (t : ℕ) :
    afterFirst2 t (anchor2 t).C = (anchor2 t).B ∧ afterFirst2 t (anchor2 t).Z = (anchor2 t).B := by
  have h := Symbolic.afterFirst2_anchor t
  exact ⟨h.2.2.1, h.2.2.2.1⟩

theorem alternateAfterFirst_anchor (t : ℕ) :
    alternateAfterFirst t (alternateAnchor t).C = (alternateAnchor t).B ∧
      alternateAfterFirst t (alternateAnchor t).Z = (alternateAnchor t).B := by
  have h := Symbolic.alternateAfterFirst_anchor t
  exact ⟨h.2.2.1, h.2.2.2.1⟩

theorem afterPairs0_anchor (t v : ℕ) :
    afterPairs0 t v (anchor0 t).C = (anchor0 t).B ∧ afterPairs0 t v (anchor0 t).Z = (anchor0 t).B := by
  have he := selectedPairs_keeps_anchor (q0 t) (q0 t+1) 5 (q0 t-4)
    (afterFirst0 t) (anchor0 t) (selected0 t v) (Operations.firstK_subset _ _)
  exact ⟨he.1.trans (afterFirst0_anchor t).1, he.2.trans (afterFirst0_anchor t).2⟩
theorem afterPairs1_anchor (t u : ℕ) :
    afterPairs1 t u (anchor1 t).C = (anchor1 t).B ∧ afterPairs1 t u (anchor1 t).Z = (anchor1 t).B := by
  have he := selectedPairs_keeps_anchor (q1 t) (q1 t+1) 4 (q1 t-3)
    (afterFirst1 t) (anchor1 t) (selected1 t u) (Operations.firstK_subset _ _)
  exact ⟨he.1.trans (afterFirst1_anchor t).1, he.2.trans (afterFirst1_anchor t).2⟩
theorem afterPairs2_anchor (t v : ℕ) :
    afterPairs2 t v (anchor2 t).C = (anchor2 t).B ∧ afterPairs2 t v (anchor2 t).Z = (anchor2 t).B := by
  have he := selectedPairs_keeps_anchor (q2 t) (q2 t-1) 2 (q2 t-3)
    (afterFirst2 t) (anchor2 t) (selected2 t v) (Operations.firstK_subset _ _)
  exact ⟨he.1.trans (afterFirst2_anchor t).1, he.2.trans (afterFirst2_anchor t).2⟩

theorem fullParent_splitParent (Q : ℕ) (sk p : ℕ → ℕ) (a : Anchor)
    (hC : a.C ∈ leafLabels Q) (hZ : a.Z ∈ leafLabels Q) :
    fullParent Q sk (splitParent p a) = splitParent (fullParent Q sk p) a := by
  funext x
  by_cases hx : x ∈ leafLabels Q
  · simp [fullParent, splitParent, hx]
  · have hxC : x ≠ a.C := by intro he; exact hx (by simpa [he] using hC)
    have hxZ : x ≠ a.Z := by intro he; exact hx (by simpa [he] using hZ)
    simp [fullParent, splitParent, hx, hxC, hxZ]

theorem splitParent_difference (p : ℕ → ℕ) (a : Anchor) (ha : a.Valid)
    (hCZ : a.C ≠ a.Z) (hC : p a.C = a.B) (hZ : p a.Z = a.B) (x : ℕ) :
    Nat.dist x (splitParent p a x) =
      Nat.dist (Operations.swapTwo a.C a.Z x) (p (Operations.swapTwo a.C a.Z x)) := by
  have hd : Nat.dist a.C a.A = Nat.dist a.Z a.B ∧ Nat.dist a.Z a.C = Nat.dist a.C a.B := by
    rcases ha with ⟨h₁,h₂⟩
    simp only [Nat.dist]
    omega
  by_cases hxC : x = a.C
  · subst x
    simpa [splitParent, Operations.swapTwo, hZ] using hd.1
  · by_cases hxZ : x = a.Z
    · subst x
      simpa [splitParent, Operations.swapTwo, hCZ, Ne.symm hCZ, hC] using hd.2
    · simp [splitParent, Operations.swapTwo, hxC, hxZ]

theorem rawCoverage_splitParent (Q : ℕ) (p : ℕ → ℕ) (a : Anchor) (ha : a.Valid)
    (hCZ : a.C ≠ a.Z) (hCm : 1 ≤ a.C ∧ a.C ≤ Q) (hZm : 1 ≤ a.Z ∧ a.Z ≤ Q)
    (hC : p a.C = a.B) (hZ : p a.Z = a.B) (h : RawCoverage Q p) :
    RawCoverage Q (splitParent p a) :=
  rawCoverage_of_involution Q p _ (Operations.swapTwo a.C a.Z)
    (Operations.swapTwo_involutive a.C a.Z) (swapTwo_interval Q a.C a.Z hCm hZm)
    (splitParent_difference p a ha hCZ hC hZ) h

theorem fullFinalParent0_coverage (t v : ℕ) : RawCoverage (q0 t) (fullFinalParent0 t v) := by
  have hC : (anchor0 t).C ∈ leafLabels (q0 t) := by simp only [anchor0, leafLabels, q0, Finset.mem_Icc]; omega
  have hZ : (anchor0 t).Z ∈ leafLabels (q0 t) := by simp only [anchor0, leafLabels, q0, Finset.mem_Icc]; omega
  have he := rawCoverage_splitParent (q0 t) (fullAfterPairs0 t v) (anchor0 t) (anchor0_valid t)
    (by dsimp [anchor0]; omega) (leaf_positive_bound _ _ hC) (leaf_positive_bound _ _ hZ)
    (by simpa [fullAfterPairs0, fullParent, hC] using (afterPairs0_anchor t v).1)
    (by simpa [fullAfterPairs0, fullParent, hZ] using (afterPairs0_anchor t v).2)
    (fullAfterPairs0_coverage t v)
  simpa only [fullAfterPairs0, fullFinalParent0, finalParent0, fullParent_splitParent _ _ _ _ hC hZ] using he

theorem fullFinalParent1_coverage (t u : ℕ) : RawCoverage (q1 t) (fullFinalParent1 t u) := by
  have hC : (anchor1 t).C ∈ leafLabels (q1 t) := by simp only [anchor1, leafLabels, q1, Finset.mem_Icc]; omega
  have hZ : (anchor1 t).Z ∈ leafLabels (q1 t) := by simp only [anchor1, leafLabels, q1, Finset.mem_Icc]; omega
  have he := rawCoverage_splitParent (q1 t) (fullAfterPairs1 t u) (anchor1 t) (anchor1_valid t)
    (by dsimp [anchor1]; omega) (leaf_positive_bound _ _ hC) (leaf_positive_bound _ _ hZ)
    (by simpa [fullAfterPairs1, fullParent, hC] using (afterPairs1_anchor t u).1)
    (by simpa [fullAfterPairs1, fullParent, hZ] using (afterPairs1_anchor t u).2)
    (fullAfterPairs1_coverage t u)
  simpa only [fullAfterPairs1, fullFinalParent1, finalParent1, fullParent_splitParent _ _ _ _ hC hZ] using he

theorem fullFinalParent2_coverage (t v : ℕ) : RawCoverage (q2 t) (fullFinalParent2 t v) := by
  have hC : (anchor2 t).C ∈ leafLabels (q2 t) := by simp only [anchor2, leafLabels, q2, Finset.mem_Icc]; omega
  have hZ : (anchor2 t).Z ∈ leafLabels (q2 t) := by simp only [anchor2, leafLabels, q2, Finset.mem_Icc]; omega
  have he := rawCoverage_splitParent (q2 t) (fullAfterPairs2 t v) (anchor2 t) (anchor2_valid t)
    (by dsimp [anchor2]; omega) (leaf_positive_bound _ _ hC) (leaf_positive_bound _ _ hZ)
    (by simpa [fullAfterPairs2, fullParent, hC] using (afterPairs2_anchor t v).1)
    (by simpa [fullAfterPairs2, fullParent, hZ] using (afterPairs2_anchor t v).2)
    (fullAfterPairs2_coverage t v)
  simpa only [fullAfterPairs2, fullFinalParent2, finalParent2, fullParent_splitParent _ _ _ _ hC hZ] using he

theorem fullAlternateFinalParent_coverage (t : ℕ) : RawCoverage (q2 t) (fullAlternateFinalParent t) := by
  have hC : (alternateAnchor t).C ∈ leafLabels (q2 t) := by simp only [alternateAnchor, leafLabels, q2, Finset.mem_Icc]; omega
  have hZ : (alternateAnchor t).Z ∈ leafLabels (q2 t) := by simp only [alternateAnchor, leafLabels, q2, Finset.mem_Icc]; omega
  have he := rawCoverage_splitParent (q2 t) (fullAlternateAfterFirst t) (alternateAnchor t)
    (alternateAnchor_valid t) (by dsimp [alternateAnchor]; omega)
    (leaf_positive_bound _ _ hC) (leaf_positive_bound _ _ hZ)
    (by simpa [fullAlternateAfterFirst, fullParent, hC] using (alternateAfterFirst_anchor t).1)
    (by simpa [fullAlternateAfterFirst, fullParent, hZ] using (alternateAfterFirst_anchor t).2)
    (fullAlternateAfterFirst_coverage t)
  simpa only [fullAlternateAfterFirst, fullAlternateFinalParent, alternateFinalParent, fullParent_splitParent _ _ _ _ hC hZ] using he

/-! Positive coverage has Q source indices and Q target differences. Thus it
also supplies injectivity; no uniqueness of final differences is assumed. -/

def rawDifference (Q : ℕ) (p : ℕ → ℕ) (h : RawCoverage Q p) (k : Fin Q) : Fin Q :=
  ⟨Nat.dist (k.val+1) (p (k.val+1)) - 1, by
    have hr := (h (Nat.dist (k.val+1) (p (k.val+1)))).2
      ⟨k.val+1, by omega, by omega, rfl⟩
    omega⟩

theorem rawDifference_spec (Q : ℕ) (p : ℕ → ℕ) (h : RawCoverage Q p) (k : Fin Q) :
    (rawDifference Q p h k).val + 1 = Nat.dist (k.val+1) (p (k.val+1)) := by
  have hr := (h (Nat.dist (k.val+1) (p (k.val+1)))).2
    ⟨k.val+1, by omega, by omega, rfl⟩
  dsimp [rawDifference]
  omega

theorem rawDifference_surjective (Q : ℕ) (p : ℕ → ℕ) (h : RawCoverage Q p) :
    Function.Surjective (rawDifference Q p h) := by
  intro d
  obtain ⟨x,hx,hxb,he⟩ := (h (d.val+1)).1 (by omega)
  let k : Fin Q := ⟨x-1, by omega⟩
  refine ⟨k, Fin.ext ?_⟩
  have hs := rawDifference_spec Q p h k
  have hxpred : k.val+1=x := by dsimp only [k]; omega
  rw [hxpred, he] at hs
  exact Nat.add_right_cancel hs

theorem rawDifference_injective (Q : ℕ) (p : ℕ → ℕ) (h : RawCoverage Q p) :
    Function.Injective (rawDifference Q p h) :=
  (Finite.injective_iff_surjective).2 (rawDifference_surjective Q p h)

def NumericGracefulAt (Q : ℕ) (p : Fin (Q+1) → Fin (Q+1)) : Prop :=
  (∀ d : ℕ, (1≤d ∧ d≤Q) ↔ ∃ y : Fin (Q+1), y≠0 ∧ Nat.dist (p y).val y.val=d) ∧
  Function.Injective (fun y : {z : Fin (Q+1) // z≠0} => Nat.dist (p y.val).val y.val.val)

theorem numericGracefulAt_of_rawCoverage (Q : ℕ) (p : ℕ → ℕ)
    (hp : ∀ x ≤ Q, p x ≤ Q) (h : RawCoverage Q p) :
    NumericGracefulAt Q (liftParent Q p hp) := by
  constructor
  · intro d
    constructor
    · intro hd
      obtain ⟨x,hx,hxb,he⟩ := (h d).1 hd
      refine ⟨⟨x, by omega⟩, ?_, ?_⟩
      · intro hz
        have hv : x = 0 := by simpa using congrArg Fin.val hz
        omega
      · simpa [liftParent, Nat.dist_comm] using he
    · rintro ⟨y,hy,he⟩
      have hypos : 1 ≤ y.val := by
        have hyn : y.val ≠ 0 := by intro hz; exact hy (Fin.ext hz)
        omega
      exact (h d).2 ⟨y.val, hypos, by omega, by simpa [liftParent, Nat.dist_comm] using he⟩
  · intro y z he
    have hyp : 1 ≤ y.val.val := by
      have hyn : y.val.val ≠ 0 := by intro hz; exact y.property (Fin.ext hz)
      omega
    have hzp : 1 ≤ z.val.val := by
      have hzn : z.val.val ≠ 0 := by intro hz; exact z.property (Fin.ext hz)
      omega
    let a : Fin Q := ⟨y.val.val-1, by have hyb := y.val.isLt; omega⟩
    let b : Fin Q := ⟨z.val.val-1, by have hzb := z.val.isLt; omega⟩
    have ha : a.val+1=y.val.val := by dsimp [a]; omega
    have hb : b.val+1=z.val.val := by dsimp [b]; omega
    have he' : Nat.dist y.val.val (p y.val.val) = Nat.dist z.val.val (p z.val.val) := by
      simpa [liftParent, Nat.dist_comm] using he
    have hda := rawDifference_spec Q p h a
    have hdb := rawDifference_spec Q p h b
    rw [ha] at hda
    rw [hb] at hdb
    have hab : rawDifference Q p h a = rawDifference Q p h b := Fin.ext (by omega)
    have hi := rawDifference_injective Q p h hab
    have hiv := congrArg Fin.val hi
    apply Subtype.ext
    apply Fin.ext
    dsimp [a,b] at hiv
    omega

theorem numericGraceful_of_rawCoverage (u v : ℕ) (p : ℕ → ℕ)
    (hp : ∀ x ≤ q u v, p x ≤ q u v) (h : RawCoverage (q u v) p) :
    NumericGraceful (liftParent (q u v) p hp) :=
  numericGracefulAt_of_rawCoverage (q u v) p hp h

theorem finalNumericParent0_graceful (t v : ℕ) : NumericGracefulAt (q0 t) (finalNumericParent0 t v) :=
  numericGracefulAt_of_rawCoverage _ _ _ (fullFinalParent0_coverage t v)
theorem finalNumericParent1_graceful (t u : ℕ) : NumericGracefulAt (q1 t) (finalNumericParent1 t u) :=
  numericGracefulAt_of_rawCoverage _ _ _ (fullFinalParent1_coverage t u)
theorem finalNumericParent2_graceful (t v : ℕ) : NumericGracefulAt (q2 t) (finalNumericParent2 t v) :=
  numericGracefulAt_of_rawCoverage _ _ _ (fullFinalParent2_coverage t v)
theorem alternateFinalNumericParent_graceful (t : ℕ) : NumericGracefulAt (q2 t) (alternateFinalNumericParent t) :=
  numericGracefulAt_of_rawCoverage _ _ _ (fullAlternateFinalParent_coverage t)

theorem profile0OfCounts_numericGraceful (u v t : ℕ) (hq : q u v = q0 t)
    (hc : ∀ c, (Symbolic.fibre (q0 t) (finalParent0 t v) (internalNat0 t (twoCode c))).card =
      pendantCount u v c.1 c.2) : NumericGraceful (profile0OfCounts u v t hq hc).numericParent := by
  exact numericGraceful_of_rawCoverage u v (fullFinalParent0 t v)
    (by intro x hx; rw [hq]; exact fullFinalParent0_bound t v x)
    (by simpa only [hq] using fullFinalParent0_coverage t v)

theorem profile1OfCounts_numericGraceful (u v t : ℕ) (hq : q u v = q1 t)
    (hc : ∀ c, (Symbolic.fibre (q1 t) (finalParent1 t u) (internalNat1 t (twoCode c))).card =
      pendantCount u v c.1 c.2) : NumericGraceful (profile1OfCounts u v t hq hc).numericParent := by
  exact numericGraceful_of_rawCoverage u v (fullFinalParent1 t u)
    (by intro x hx; rw [hq]; exact fullFinalParent1_bound t u x)
    (by simpa only [hq] using fullFinalParent1_coverage t u)

theorem profile2OfCounts_numericGraceful (u v t : ℕ) (hq : q u v = q2 t)
    (hc : ∀ c, (Symbolic.fibre (q2 t) (finalParent2 t v) (internalNat2 t (twoCode c))).card =
      pendantCount u v c.1 c.2) : NumericGraceful (profile2OfCounts u v t hq hc).numericParent := by
  exact numericGraceful_of_rawCoverage u v (fullFinalParent2 t v)
    (by intro x hx; rw [hq]; exact fullFinalParent2_bound t v x)
    (by simpa only [hq] using fullFinalParent2_coverage t v)

theorem alternateProfileOfCounts_numericGraceful (u v t : ℕ) (hq : q u v = q2 t)
    (hc : ∀ c, (Symbolic.fibre (q2 t) (alternateFinalParent t) (alternateInternalNat t (twoCode c))).card =
      pendantCount u v c.1 c.2) : NumericGraceful (alternateProfileOfCounts u v t hq hc).numericParent := by
  exact numericGraceful_of_rawCoverage u v (fullAlternateFinalParent t)
    (by intro x hx; rw [hq]; exact fullAlternateFinalParent_bound t x)
    (by simpa only [hq] using fullAlternateFinalParent_coverage t)

theorem profile0_fiberCards (u v t : ℕ) (hu : 0<u) (hv : 0<v)
    (hq : q u v = q0 t) (hcase : 0<t ∨ 2≤u) :
    ∀ c, (Symbolic.fibre (q0 t) (finalParent0 t v) (internalNat0 t (twoCode c))).card =
      pendantCount u v c.1 c.2 := by
  have hd := finalParent0_distinguished_counts t u v hu hv hq hcase
  intro c
  fin_cases c <;> simp [internalNat0, twoCode, pick3, pendantCount, depthTwoCount] <;> first
  | exact hd.1
  | exact hd.2.1
  | exact hd.2.2.1
  | exact hd.2.2.2
  | apply finalParent0_ordinary_counts; simp

theorem profile1_fiberCards (u v t : ℕ) (hu : 0<u) (hv : 0<v)
    (hq : q u v = q1 t) :
    ∀ c, (Symbolic.fibre (q1 t) (finalParent1 t u) (internalNat1 t (twoCode c))).card =
      pendantCount u v c.1 c.2 := by
  have hd := finalParent1_distinguished_counts t u v hu hv hq
  intro c
  fin_cases c <;> simp [internalNat1, twoCode, pick3, pendantCount, depthTwoCount] <;> first
  | exact hd.1
  | exact hd.2.1
  | exact hd.2.2.1
  | exact hd.2.2.2
  | apply finalParent1_ordinary_counts; simp

theorem profile2_fiberCards (u v t : ℕ) (hu : 2≤u) (hv : 0<v)
    (hq : q u v = q2 t) :
    ∀ c, (Symbolic.fibre (q2 t) (finalParent2 t v) (internalNat2 t (twoCode c))).card =
      pendantCount u v c.1 c.2 := by
  have hd := finalParent2_distinguished_counts t u v hu hv hq
  intro c
  fin_cases c <;> simp [internalNat2, twoCode, pick3, pendantCount, depthTwoCount] <;> first
  | exact hd.1
  | exact hd.2.1
  | exact hd.2.2.1
  | exact hd.2.2.2
  | apply finalParent2_ordinary_counts; simp

theorem alternateProfile_fiberCards (v t : ℕ) (hv : 0<v) (hq : q 1 v = q2 t) :
    ∀ c, (Symbolic.fibre (q2 t) (alternateFinalParent t) (alternateInternalNat t (twoCode c))).card =
      pendantCount 1 v c.1 c.2 := by
  have hd := alternateFinalParent_distinguished_counts t v hv hq
  intro c
  fin_cases c <;> simp [alternateInternalNat, twoCode, pick3, pendantCount, depthTwoCount] <;> first
  | exact hd.1
  | exact hd.2.1
  | exact hd.2.2.1
  | exact hd.2.2.2
  | apply alternateFinalParent_ordinary_counts; simp

def profile0 (u v t : ℕ) (hu : 0<u) (hv : 0<v)
    (hq : q u v = q0 t) (hcase : 0<t ∨ 2≤u) : ProfileFrame u v :=
  profile0OfCounts u v t hq (profile0_fiberCards u v t hu hv hq hcase)
def profile1 (u v t : ℕ) (hu : 0<u) (hv : 0<v) (hq : q u v = q1 t) : ProfileFrame u v :=
  profile1OfCounts u v t hq (profile1_fiberCards u v t hu hv hq)
def profile2 (u v t : ℕ) (hu : 2≤u) (hv : 0<v) (hq : q u v = q2 t) : ProfileFrame u v :=
  profile2OfCounts u v t hq (profile2_fiberCards u v t hu hv hq)
def alternateProfile (v t : ℕ) (hv : 0<v) (hq : q 1 v = q2 t) : ProfileFrame 1 v :=
  alternateProfileOfCounts 1 v t hq (alternateProfile_fiberCards v t hv hq)

theorem profile0_parent_val (u v t : ℕ) (hu : 0<u) (hv : 0<v)
    (hq : q u v=q0 t) (hcase : 0<t ∨ 2≤u) (y : Fin (q u v+1)) :
    ((profile0 u v t hu hv hq hcase).numericParent y).val = fullFinalParent0 t v y.val := rfl
theorem profile1_parent_val (u v t : ℕ) (hu : 0<u) (hv : 0<v)
    (hq : q u v=q1 t) (y : Fin (q u v+1)) :
    ((profile1 u v t hu hv hq).numericParent y).val = fullFinalParent1 t u y.val := rfl
theorem profile2_parent_val (u v t : ℕ) (hu : 2≤u) (hv : 0<v)
    (hq : q u v=q2 t) (y : Fin (q u v+1)) :
    ((profile2 u v t hu hv hq).numericParent y).val = fullFinalParent2 t v y.val := rfl
theorem alternateProfile_parent_val (v t : ℕ) (hv : 0<v) (hq : q 1 v=q2 t)
    (y : Fin (q 1 v+1)) :
    ((alternateProfile v t hv hq).numericParent y).val = fullAlternateFinalParent t y.val := rfl

theorem profile0_numericGraceful (u v t : ℕ) (hu : 0<u) (hv : 0<v)
    (hq : q u v = q0 t) (hcase : 0<t ∨ 2≤u) :
    NumericGraceful (profile0 u v t hu hv hq hcase).numericParent :=
  profile0OfCounts_numericGraceful u v t hq _
theorem profile1_numericGraceful (u v t : ℕ) (hu : 0<u) (hv : 0<v) (hq : q u v = q1 t) :
    NumericGraceful (profile1 u v t hu hv hq).numericParent :=
  profile1OfCounts_numericGraceful u v t hq _
theorem profile2_numericGraceful (u v t : ℕ) (hu : 2≤u) (hv : 0<v) (hq : q u v = q2 t) :
    NumericGraceful (profile2 u v t hu hv hq).numericParent :=
  profile2OfCounts_numericGraceful u v t hq _
theorem alternateProfile_numericGraceful (v t : ℕ) (hv : 0<v) (hq : q 1 v = q2 t) :
    NumericGraceful (alternateProfile v t hv hq).numericParent :=
  alternateProfileOfCounts_numericGraceful 1 v t hq _

theorem standard0_constructed (u v t : ℕ) (hu : 0<u) (hv : 0<v)
    (hq : q u v = q0 t) (hcase : 0<t ∨ 2≤u) :
    ∃ f : Vertex u v → Fin (q u v+1), RootZeroGraceful u v f := by
  let F := profile0 u v t hu hv hq hcase
  exact ⟨F.realization, rootZeroGraceful_of_profile F (profile0_numericGraceful u v t hu hv hq hcase)⟩
theorem standard1_constructed (u v t : ℕ) (hu : 0<u) (hv : 0<v) (hq : q u v = q1 t) :
    ∃ f : Vertex u v → Fin (q u v+1), RootZeroGraceful u v f := by
  let F := profile1 u v t hu hv hq
  exact ⟨F.realization, rootZeroGraceful_of_profile F (profile1_numericGraceful u v t hu hv hq)⟩
theorem standard2_constructed (u v t : ℕ) (hu : 2≤u) (hv : 0<v) (hq : q u v = q2 t) :
    ∃ f : Vertex u v → Fin (q u v+1), RootZeroGraceful u v f := by
  let F := profile2 u v t hu hv hq
  exact ⟨F.realization, rootZeroGraceful_of_profile F (profile2_numericGraceful u v t hu hv hq)⟩
theorem alternate_constructed (v t : ℕ) (hv : 0<v) (hq : q 1 v = q2 t) :
    ∃ f : Vertex 1 v → Fin (q 1 v+1), RootZeroGraceful 1 v f := by
  let F := alternateProfile v t hv hq
  exact ⟨F.realization, rootZeroGraceful_of_profile F (alternateProfile_numericGraceful v t hv hq)⟩

end Partials.Graceful.NumericConstruction
