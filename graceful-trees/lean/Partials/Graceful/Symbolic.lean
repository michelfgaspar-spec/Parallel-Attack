import Partials.Graceful.Model
import Partials.Graceful.Operations
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Tauto

set_option maxHeartbeats 2000000

/-!
Symbolic constructions for manuscript Sections 2--6, included in the build.
The base difference proofs use explicit bijections of normalized label indices;
base gracefulness is proved rather than assumed. Realization.lean and
NumericConstruction.lean realize these parents on `Vertex u v`;
ManuscriptFormulas.lean connects the affine expressions to the printed formulas.
-/
namespace Partials.Graceful.Symbolic

def q0 (t : ℕ) : ℕ := 27 + 6 * t
def q1 (t : ℕ) : ℕ := 25 + 6 * t
def q2 (t : ℕ) : ℕ := 29 + 6 * t

structure Anchor where
  A : ℕ
  B : ℕ
  C : ℕ
  Z : ℕ
  deriving DecidableEq

def Anchor.Valid (a : Anchor) : Prop :=
  a.A + 2 * a.B = 3 * a.C ∧ a.Z + a.B = 2 * a.C

def anchor0 (t : ℕ) : Anchor := ⟨26 + 6*t, 5, 12 + 2*t, 19 + 4*t⟩
def anchor1 (t : ℕ) : Anchor := ⟨1, 22 + 6*t, 15 + 4*t, 8 + 2*t⟩
def anchor2 (t : ℕ) : Anchor := ⟨29 + 6*t, 2, 11 + 2*t, 20 + 4*t⟩
def alternateAnchor (t : ℕ) : Anchor := ⟨2, 26 + 6*t, 18 + 4*t, 10 + 2*t⟩

theorem anchor0_valid (t : ℕ) : (anchor0 t).Valid := by
  dsimp [Anchor.Valid, anchor0]; constructor <;> omega
theorem anchor1_valid (t : ℕ) : (anchor1 t).Valid := by
  dsimp [Anchor.Valid, anchor1]; constructor <;> omega
theorem anchor2_valid (t : ℕ) : (anchor2 t).Valid := by
  dsimp [Anchor.Valid, anchor2]; constructor <;> omega
theorem alternateAnchor_valid (t : ℕ) : (alternateAnchor t).Valid := by
  dsimp [Anchor.Valid, alternateAnchor]; constructor <;> omega

theorem order0 (t : ℕ) :
    6 < 7 ∧ 7 < 8 ∧ 8 < 9+2*t ∧ 9+2*t < 12+2*t ∧
    12+2*t < 14+3*t ∧ 14+3*t < 16+4*t ∧ 16+4*t < 19+4*t ∧
    19+4*t < 20+6*t ∧ 20+6*t < 21+6*t ∧ 21+6*t < 22+6*t := by omega
theorem order1 (t : ℕ) :
    6 < 7 ∧ 7 < 8+2*t ∧ 8+2*t < 10+2*t ∧ 10+2*t < 11+2*t ∧
    11+2*t < 13+3*t ∧ 13+3*t < 15+4*t ∧ 15+4*t < 16+4*t ∧
    16+4*t < 18+4*t ∧ 18+4*t < 19+6*t ∧ 19+6*t < 20+6*t := by omega
theorem order2 (t : ℕ) :
    6 < 8+2*t ∧ 8+2*t < 11+2*t ∧ 11+2*t < 12+3*t ∧
    12+3*t < 13+3*t ∧ 13+3*t < 14+3*t ∧ 14+3*t < 15+3*t ∧
    15+3*t < 16+3*t ∧ 16+3*t < 17+4*t ∧ 17+4*t < 20+4*t ∧
    20+4*t < 22+6*t ∧ 22+6*t < 23+6*t ∧ 23+6*t < 24+6*t := by omega
theorem alternateOrder (t : ℕ) :
    6 < 7 ∧ 7 < 8 ∧ 8 < 9+2*t ∧ 9+2*t < 10+2*t ∧
    10+2*t < 12+2*t ∧ 12+2*t < 18+4*t ∧ 18+4*t < 20+4*t ∧
    20+4*t < 23+6*t ∧ 23+6*t < 24+6*t := by omega

def leafLabels (Q : ℕ) : Finset ℕ := Finset.Icc 6 (Q-5)

/-- Table `tab:q0`, in affine form. -/
def baseParent0 (t x : ℕ) : ℕ :=
  if x = 22+6*t then 2
  else if x = 6 then 25+6*t
  else if x = 21+6*t then 3
  else if x = 7 then 24+6*t
  else if x = 20+6*t then 4
  else if x = 8 ∨ x = 14+3*t then 23+6*t
  else 5

/-- Table `tab:q1`, in affine form. -/
def baseParent1 (t x : ℕ) : ℕ :=
  if x = 15+4*t ∨ x = 8+2*t ∨ x = 7 ∨ x = 18+4*t then 22+6*t
  else if x = 20+6*t then 2
  else if x = 6 then 23+6*t
  else if x = 19+6*t then 3
  else if x = 10+2*t then 21+6*t
  else if x = 11+2*t then 5
  else 4

/-- Equation `eq:q2assignment`, in affine form. -/
def baseParent2 (t x : ℕ) : ℕ :=
  if x = 23+6*t then 3
  else if x = 22+6*t ∨ x = 12+3*t then 26+6*t
  else if x = 6 then 27+6*t
  else if x = 14+3*t then 4
  else if x = 16+3*t then 5
  else if x = 13+3*t then 25+6*t
  else 2

/-- Equation `eq:alternateassignment`, in affine form. -/
def alternateBaseParent (t x : ℕ) : ℕ :=
  if x = 18+4*t ∨ x = 10+2*t ∨ x = 7 ∨ x = 12+2*t then 26+6*t
  else if x = 23+6*t then 1
  else if x = 6 then 27+6*t
  else if x = 8 then 5
  else if x = 9+2*t then 3
  else if x = 20+4*t then 25+6*t
  else 4

/-! Explicit normalized index bijections. The source's cycles are expanded
as total functions; their inverses also account for each boundary replacement.
This proves the interval/cycle claims without assuming a graceful base. -/
def index0 (t x : ℕ) : ℕ :=
  if x = 22+6*t then 25+6*t else if x = 6 then 24+6*t
  else if x = 21+6*t then 23+6*t else if x = 7 then 22+6*t
  else if x = 20+6*t then 21+6*t else if x = 8 then 20+6*t else x
def inverseIndex0 (t y : ℕ) : ℕ :=
  if y = 25+6*t then 22+6*t else if y = 24+6*t then 6
  else if y = 23+6*t then 21+6*t else if y = 22+6*t then 7
  else if y = 21+6*t then 20+6*t else if y = 20+6*t then 8 else y

def index1 (t x : ℕ) : ℕ :=
  if x = 15+4*t then 11+2*t else if x = 8+2*t then 18+4*t
  else if x = 7 then 19+6*t else if x = 18+4*t then 8+2*t
  else if x = 20+6*t then 22+6*t else if x = 6 then 21+6*t
  else if x = 19+6*t then 20+6*t else if x = 10+2*t then 15+4*t
  else if x = 11+2*t then 10+2*t else x
def inverseIndex1 (t y : ℕ) : ℕ :=
  if y = 11+2*t then 15+4*t else if y = 18+4*t then 8+2*t
  else if y = 19+6*t then 7 else if y = 8+2*t then 18+4*t
  else if y = 22+6*t then 20+6*t else if y = 21+6*t then 6
  else if y = 20+6*t then 19+6*t else if y = 15+4*t then 10+2*t
  else if y = 10+2*t then 11+2*t else y

def index2 (t x : ℕ) : ℕ :=
  if x = 23+6*t then 22+6*t else if x = 22+6*t then 6
  else if x = 6 then 23+6*t else if x = 14+3*t then 12+3*t
  else if x = 12+3*t then 16+3*t else if x = 16+3*t then 13+3*t
  else if x = 13+3*t then 14+3*t else x
def inverseIndex2 (t y : ℕ) : ℕ :=
  if y = 22+6*t then 23+6*t else if y = 6 then 22+6*t
  else if y = 23+6*t then 6 else if y = 12+3*t then 14+3*t
  else if y = 16+3*t then 12+3*t else if y = 13+3*t then 16+3*t
  else if y = 14+3*t then 13+3*t else y

def alternateIndex (t x : ℕ) : ℕ :=
  if x = 18+4*t then 12+2*t else if x = 12+2*t then 18+4*t
  else if x = 10+2*t then 20+4*t else if x = 20+4*t then 9+2*t
  else if x = 9+2*t then 10+2*t else if x = 23+6*t then 26+6*t
  else if x = 6 then 25+6*t else if x = 7 then 23+6*t
  else if x = 8 then 7 else x
def alternateInverseIndex (t y : ℕ) : ℕ :=
  if y = 12+2*t then 18+4*t else if y = 18+4*t then 12+2*t
  else if y = 20+4*t then 10+2*t else if y = 9+2*t then 20+4*t
  else if y = 10+2*t then 9+2*t else if y = 26+6*t then 23+6*t
  else if y = 25+6*t then 6 else if y = 23+6*t then 7
  else if y = 7 then 8 else y

/-- A finite-set bijection of indices, strictly weaker than graph
gracefulness. Each concrete instance is proved below from its two functions. -/
structure IndexBijection (source target : Finset ℕ) (forward inverse : ℕ → ℕ) : Prop where
  forward_mem : ∀ x ∈ source, forward x ∈ target
  inverse_mem : ∀ y ∈ target, inverse y ∈ source
  left_inverse : ∀ x ∈ source, inverse (forward x) = x
  right_inverse : ∀ y ∈ target, forward (inverse y) = y

def indices0 (t : ℕ) : Finset ℕ := Finset.Icc 9 (25+6*t)
def indices1 (t : ℕ) : Finset ℕ := Finset.Icc 8 (22+6*t)
def indices2 (t : ℕ) : Finset ℕ := Finset.Icc 6 (24+6*t)
def alternateIndices (t : ℕ) : Finset ℕ := {7} ∪ Finset.Icc 9 (26+6*t)

theorem index0_bijection (t : ℕ) :
    IndexBijection (leafLabels (q0 t)) (indices0 t) (index0 t) (inverseIndex0 t) := by
  constructor
  · intro x hx
    simp only [leafLabels, q0, Finset.mem_Icc] at hx
    simp only [index0, indices0, Finset.mem_Icc]
    split_ifs <;> omega
  · intro y hy
    simp only [indices0, Finset.mem_Icc] at hy
    simp only [inverseIndex0, leafLabels, q0, Finset.mem_Icc]
    split_ifs <;> omega
  · intro x hx
    simp only [leafLabels, q0, Finset.mem_Icc] at hx
    simp only [index0]
    split_ifs <;> simp only [inverseIndex0] <;> split_ifs <;> omega
  · intro y hy
    simp only [indices0, Finset.mem_Icc] at hy
    simp only [inverseIndex0]
    split_ifs <;> simp only [index0] <;> split_ifs <;> omega

theorem index1_bijection (t : ℕ) :
    IndexBijection (leafLabels (q1 t)) (indices1 t) (index1 t) (inverseIndex1 t) := by
  constructor
  · intro x hx
    simp only [leafLabels, q1, Finset.mem_Icc] at hx
    simp only [index1, indices1, Finset.mem_Icc]
    split_ifs <;> omega
  · intro y hy
    simp only [indices1, Finset.mem_Icc] at hy
    simp only [inverseIndex1, leafLabels, q1, Finset.mem_Icc]
    split_ifs <;> omega
  · intro x hx
    simp only [leafLabels, q1, Finset.mem_Icc] at hx
    simp only [index1]
    split_ifs <;> simp only [inverseIndex1] <;> split_ifs <;> omega
  · intro y hy
    simp only [indices1, Finset.mem_Icc] at hy
    simp only [inverseIndex1]
    split_ifs <;> simp only [index1] <;> split_ifs <;> omega

theorem index2_bijection (t : ℕ) :
    IndexBijection (leafLabels (q2 t)) (indices2 t) (index2 t) (inverseIndex2 t) := by
  constructor
  · intro x hx
    simp only [leafLabels, q2, Finset.mem_Icc] at hx
    simp only [index2, indices2, Finset.mem_Icc]
    split_ifs <;> omega
  · intro y hy
    simp only [indices2, Finset.mem_Icc] at hy
    simp only [inverseIndex2, leafLabels, q2, Finset.mem_Icc]
    split_ifs <;> omega
  · intro x hx
    simp only [leafLabels, q2, Finset.mem_Icc] at hx
    simp only [index2]
    split_ifs <;> simp only [inverseIndex2] <;> split_ifs <;> omega
  · intro y hy
    simp only [indices2, Finset.mem_Icc] at hy
    simp only [inverseIndex2]
    split_ifs <;> simp only [index2] <;> split_ifs <;> omega

theorem alternateIndex_bijection (t : ℕ) :
    IndexBijection (leafLabels (q2 t)) (alternateIndices t)
      (alternateIndex t) (alternateInverseIndex t) := by
  constructor
  · intro x hx
    simp only [leafLabels, q2, Finset.mem_Icc] at hx
    simp only [alternateIndex, alternateIndices, Finset.mem_union,
      Finset.mem_singleton, Finset.mem_Icc]
    split_ifs <;> omega
  · intro y hy
    simp only [alternateIndices, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_Icc] at hy
    simp only [alternateInverseIndex, leafLabels, q2, Finset.mem_Icc]
    split_ifs <;> omega
  · intro x hx
    simp only [leafLabels, q2, Finset.mem_Icc] at hx
    simp only [alternateIndex]
    split_ifs <;> simp only [alternateInverseIndex] <;> split_ifs <;> omega
  · intro y hy
    simp only [alternateIndices, Finset.mem_union, Finset.mem_singleton,
      Finset.mem_Icc] at hy
    simp only [alternateInverseIndex]
    split_ifs <;> simp only [alternateIndex] <;> split_ifs <;> omega

theorem normalized0 (t x : ℕ) (hx : x ∈ leafLabels (q0 t)) :
    5 + Nat.dist x (baseParent0 t x) = index0 t x := by
  simp only [leafLabels, q0, Finset.mem_Icc] at hx
  simp only [baseParent0, index0]
  split_ifs <;> simp only [Nat.dist] <;> omega
theorem normalized1 (t x : ℕ) (hx : x ∈ leafLabels (q1 t)) :
    4 + Nat.dist x (baseParent1 t x) = index1 t x := by
  simp only [leafLabels, q1, Finset.mem_Icc] at hx
  simp only [baseParent1, index1]
  split_ifs <;> simp only [Nat.dist] <;> omega
theorem normalized2 (t x : ℕ) (hx : x ∈ leafLabels (q2 t)) :
    2 + Nat.dist x (baseParent2 t x) = index2 t x := by
  simp only [leafLabels, q2, Finset.mem_Icc] at hx
  simp only [baseParent2, index2]
  split_ifs <;> simp only [Nat.dist] <;> omega
theorem alternateNormalized (t x : ℕ) (hx : x ∈ leafLabels (q2 t)) :
    4 + Nat.dist x (alternateBaseParent t x) = alternateIndex t x := by
  simp only [leafLabels, q2, Finset.mem_Icc] at hx
  simp only [alternateBaseParent, alternateIndex]
  split_ifs <;> simp only [Nat.dist] <;> omega

theorem normalized_difference_mem_iff
    (source target : Finset ℕ) (forward inverse parent : ℕ → ℕ) (offset d : ℕ)
    (h : IndexBijection source target forward inverse)
    (hformula : ∀ x ∈ source, offset + Nat.dist x (parent x) = forward x) :
    offset+d ∈ target ↔ ∃ x ∈ source, Nat.dist x (parent x) = d := by
  constructor
  · intro hd
    have hx := h.inverse_mem (offset+d) hd
    refine ⟨inverse (offset+d), hx, ?_⟩
    have he := hformula (inverse (offset+d)) hx
    rw [h.right_inverse (offset+d) hd] at he
    exact Nat.add_left_cancel he
  · rintro ⟨x, hx, he⟩
    have hm := h.forward_mem x hx
    rw [← hformula x hx, he] at hm
    exact hm

theorem normalized_difference_injective
    (source target : Finset ℕ) (forward inverse parent : ℕ → ℕ) (offset : ℕ)
    (h : IndexBijection source target forward inverse)
    (hformula : ∀ x ∈ source, offset + Nat.dist x (parent x) = forward x)
    (x y : ℕ) (hx : x ∈ source) (hy : y ∈ source)
    (he : Nat.dist x (parent x) = Nat.dist y (parent y)) : x = y := by
  have hf : forward x = forward y := by
    rw [← hformula x hx, ← hformula y hy, he]
  have hi := congrArg inverse hf
  simpa only [h.left_inverse x hx, h.left_inverse y hy] using hi

theorem baseDifference0 (t d : ℕ) :
    (∃ x ∈ leafLabels (q0 t), Nat.dist x (baseParent0 t x) = d) ↔
      4 ≤ d ∧ d ≤ q0 t-7 := by
  have h := normalized_difference_mem_iff _ _ _ _ _ 5 d
    (index0_bijection t) (normalized0 t)
  simp only [indices0, Finset.mem_Icc] at h
  constructor
  · intro hd
    have hi := h.mpr hd
    dsimp [q0]
    omega
  · intro hd
    apply h.mp
    dsimp [q0] at hd
    omega
theorem baseDifference1 (t d : ℕ) :
    (∃ x ∈ leafLabels (q1 t), Nat.dist x (baseParent1 t x) = d) ↔
      4 ≤ d ∧ d ≤ q1 t-7 := by
  have h := normalized_difference_mem_iff _ _ _ _ _ 4 d
    (index1_bijection t) (normalized1 t)
  simp only [indices1, Finset.mem_Icc] at h
  constructor
  · intro hd
    have hi := h.mpr hd
    dsimp [q1]
    omega
  · intro hd
    apply h.mp
    dsimp [q1] at hd
    omega
theorem baseDifference2 (t d : ℕ) :
    (∃ x ∈ leafLabels (q2 t), Nat.dist x (baseParent2 t x) = d) ↔
      4 ≤ d ∧ d ≤ q2 t-7 := by
  have h := normalized_difference_mem_iff _ _ _ _ _ 2 d
    (index2_bijection t) (normalized2 t)
  simp only [indices2, Finset.mem_Icc] at h
  constructor
  · intro hd
    have hi := h.mpr hd
    dsimp [q2]
    omega
  · intro hd
    apply h.mp
    dsimp [q2] at hd
    omega
theorem alternateBaseDifference (t d : ℕ) :
    (∃ x ∈ leafLabels (q2 t), Nat.dist x (alternateBaseParent t x) = d) ↔
      d = 3 ∨ (5 ≤ d ∧ d ≤ q2 t-7) := by
  have h := normalized_difference_mem_iff _ _ _ _ _ 4 d
    (alternateIndex_bijection t) (alternateNormalized t)
  simp only [alternateIndices, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_Icc] at h
  constructor
  · intro hd
    have hi := h.mpr hd
    dsimp [q2]
    omega
  · intro hd
    apply h.mp
    dsimp [q2] at hd
    omega

theorem baseDifference0_unique (t x y : ℕ)
    (hx : x ∈ leafLabels (q0 t)) (hy : y ∈ leafLabels (q0 t))
    (he : Nat.dist x (baseParent0 t x) = Nat.dist y (baseParent0 t y)) : x = y :=
  normalized_difference_injective _ _ _ _ _ 5 (index0_bijection t) (normalized0 t) x y hx hy he
theorem baseDifference1_unique (t x y : ℕ)
    (hx : x ∈ leafLabels (q1 t)) (hy : y ∈ leafLabels (q1 t))
    (he : Nat.dist x (baseParent1 t x) = Nat.dist y (baseParent1 t y)) : x = y :=
  normalized_difference_injective _ _ _ _ _ 4 (index1_bijection t) (normalized1 t) x y hx hy he
theorem baseDifference2_unique (t x y : ℕ)
    (hx : x ∈ leafLabels (q2 t)) (hy : y ∈ leafLabels (q2 t))
    (he : Nat.dist x (baseParent2 t x) = Nat.dist y (baseParent2 t y)) : x = y :=
  normalized_difference_injective _ _ _ _ _ 2 (index2_bijection t) (normalized2 t) x y hx hy he
theorem alternateBaseDifference_unique (t x y : ℕ)
    (hx : x ∈ leafLabels (q2 t)) (hy : y ∈ leafLabels (q2 t))
    (he : Nat.dist x (alternateBaseParent t x) = Nat.dist y (alternateBaseParent t y)) : x = y :=
  normalized_difference_injective _ _ _ _ _ 4
    (alternateIndex_bijection t) (alternateNormalized t) x y hx hy he

/-! The prescribed first transfers and exact eligible reflection starts. -/
def moveTwo (parent : ℕ → ℕ) (x y recipient : ℕ) : ℕ → ℕ :=
  fun z => if z = x ∨ z = y then recipient else parent z
def afterFirst0 (t : ℕ) : ℕ → ℕ :=
  if t = 0 then moveTwo (baseParent0 t) 13 17 (q0 t-2)
  else moveTwo (baseParent0 t) (9+2*t) (21+4*t) (q0 t-2)
def afterFirst1 (t : ℕ) : ℕ → ℕ :=
  moveTwo (baseParent1 t) (13+3*t) (14+3*t) (q1 t-2)
def afterFirst2 (t : ℕ) : ℕ → ℕ :=
  moveTwo (baseParent2 t) (8+2*t) (19+4*t) (q2 t-4)
def alternateAfterFirst (t : ℕ) : ℕ → ℕ :=
  moveTwo (alternateBaseParent t) (14+3*t) (17+3*t) (q2 t-2)

theorem firstPair0_sum (t : ℕ) : (9+2*t)+(21+4*t)=5+(q0 t-2) := by dsimp [q0]; omega
theorem firstPair0_small_sum : 13+17=5+(q0 0-2) := by decide
theorem firstPair1_sum (t : ℕ) : (13+3*t)+(14+3*t)=4+(q1 t-2) := by dsimp [q1]; omega
theorem firstPair2_sum (t : ℕ) : (8+2*t)+(19+4*t)=2+(q2 t-4) := by dsimp [q2]; omega
theorem alternateFirstPair_sum (t : ℕ) : (14+3*t)+(17+3*t)=4+(q2 t-2) := by dsimp [q2]; omega

def eligiblePairStarts (Q sum donor : ℕ) (parent : ℕ → ℕ) (a : Anchor) : Finset ℕ :=
  (leafLabels Q).filter fun x =>
    x < sum-x ∧ sum-x ∈ leafLabels Q ∧
    parent x = donor ∧ parent (sum-x) = donor ∧
    x ≠ a.C ∧ x ≠ a.Z ∧ sum-x ≠ a.C ∧ sum-x ≠ a.Z

theorem afterFirst0_donor (t : ℕ) (ht : 0 < t) (x : ℕ) :
    afterFirst0 t x = 5 ↔
    x ≠ 22+6*t ∧ x ≠ 6 ∧ x ≠ 21+6*t ∧ x ≠ 7 ∧
    x ≠ 20+6*t ∧ x ≠ 8 ∧ x ≠ 14+3*t ∧
    x ≠ 9+2*t ∧ x ≠ 21+4*t := by
  have ht0 : t ≠ 0 := by omega
  simp only [afterFirst0, ht0, if_false, moveTwo, baseParent0, q0]
  split_ifs <;> omega
theorem afterFirst0_zero_donor (x : ℕ) :
    afterFirst0 0 x = 5 ↔
    x ≠ 22 ∧ x ≠ 6 ∧ x ≠ 21 ∧ x ≠ 7 ∧ x ≠ 20 ∧
    x ≠ 8 ∧ x ≠ 14 ∧ x ≠ 13 ∧ x ≠ 17 := by
  simp only [afterFirst0, if_pos rfl, moveTwo, baseParent0, q0]
  norm_num
  split_ifs <;> omega
theorem afterFirst1_donor (t x : ℕ) :
    afterFirst1 t x = 4 ↔
    x ≠ 15+4*t ∧ x ≠ 8+2*t ∧ x ≠ 7 ∧ x ≠ 18+4*t ∧
    x ≠ 20+6*t ∧ x ≠ 6 ∧ x ≠ 19+6*t ∧ x ≠ 10+2*t ∧
    x ≠ 11+2*t ∧ x ≠ 13+3*t ∧ x ≠ 14+3*t := by
  simp only [afterFirst1, moveTwo, baseParent1, q1]
  split_ifs <;> omega
theorem afterFirst2_donor (t x : ℕ) :
    afterFirst2 t x = 2 ↔
    x ≠ 23+6*t ∧ x ≠ 22+6*t ∧ x ≠ 12+3*t ∧ x ≠ 6 ∧
    x ≠ 14+3*t ∧ x ≠ 16+3*t ∧ x ≠ 13+3*t ∧
    x ≠ 8+2*t ∧ x ≠ 19+4*t := by
  simp only [afterFirst2, moveTwo, baseParent2, q2]
  split_ifs <;> omega

def starts0 (t : ℕ) : Finset ℕ :=
  (((Finset.Icc 9 (13+3*t)).erase (7+2*t)).erase (9+2*t)).erase (12+2*t)
def starts1 (t : ℕ) : Finset ℕ :=
  (((Finset.Icc 8 (11+3*t)).erase (8+2*t)).erase (10+2*t)).erase (11+2*t)
def starts2 (t : ℕ) : Finset ℕ :=
  (((Finset.Icc 7 (11+3*t)).erase (8+2*t)).erase (9+2*t)).erase (11+2*t)

theorem eligible0_exact (t : ℕ) (ht : 0 < t) :
    eligiblePairStarts (q0 t) (q0 t+1) 5 (afterFirst0 t) (anchor0 t) = starts0 t := by
  ext x
  simp only [eligiblePairStarts, Finset.mem_filter, afterFirst0_donor t ht,
    leafLabels, q0, anchor0, starts0, Finset.mem_erase, Finset.mem_Icc]
  omega
theorem eligible0_zero_exact :
    eligiblePairStarts (q0 0) (q0 0+1) 5 (afterFirst0 0) (anchor0 0) = {10} := by
  ext x
  simp only [eligiblePairStarts, Finset.mem_filter, afterFirst0_zero_donor,
    leafLabels, q0, anchor0, Finset.mem_singleton, Finset.mem_Icc]
  omega
theorem eligible1_exact (t : ℕ) :
    eligiblePairStarts (q1 t) (q1 t+1) 4 (afterFirst1 t) (anchor1 t) = starts1 t := by
  ext x
  simp only [eligiblePairStarts, Finset.mem_filter, afterFirst1_donor,
    leafLabels, q1, anchor1, starts1, Finset.mem_erase, Finset.mem_Icc]
  omega
theorem eligible2_exact (t : ℕ) :
    eligiblePairStarts (q2 t) (q2 t-1) 2 (afterFirst2 t) (anchor2 t) = starts2 t := by
  ext x
  simp only [eligiblePairStarts, Finset.mem_filter, afterFirst2_donor,
    leafLabels, q2, anchor2, starts2, Finset.mem_erase, Finset.mem_Icc]
  omega

theorem card_erase_three (s : Finset ℕ) (a b c : ℕ)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s)
    (hba : b ≠ a) (hca : c ≠ a) (hcb : c ≠ b) :
    (((s.erase a).erase b).erase c).card = s.card-1-1-1 := by
  have hb' : b ∈ s.erase a := by simp only [Finset.mem_erase]; exact ⟨hba, hb⟩
  have hc' : c ∈ (s.erase a).erase b := by
    simp only [Finset.mem_erase]; exact ⟨hcb, hca, hc⟩
  rw [Finset.card_erase_of_mem hc', Finset.card_erase_of_mem hb', Finset.card_erase_of_mem ha]

theorem starts0_card (t : ℕ) (ht : 0 < t) : (starts0 t).card = 2+3*t := by
  unfold starts0
  rw [card_erase_three]
  · have hI : (Finset.Icc 9 (13+3*t)).card = (13+3*t+1)-9 := by simp
    rw [hI]; omega
  all_goals (try simp only [Finset.mem_Icc]) <;> omega
theorem starts1_card (t : ℕ) : (starts1 t).card = 1+3*t := by
  unfold starts1
  rw [card_erase_three]
  · have hI : (Finset.Icc 8 (11+3*t)).card = (11+3*t+1)-8 := by simp
    rw [hI]; omega
  all_goals (try simp only [Finset.mem_Icc]) <;> omega
theorem starts2_card (t : ℕ) : (starts2 t).card = 2+3*t := by
  unfold starts2
  rw [card_erase_three]
  · have hI : (Finset.Icc 7 (11+3*t)).card = (11+3*t+1)-7 := by simp
    rw [hI]; omega
  all_goals (try simp only [Finset.mem_Icc]) <;> omega

theorem eligible0_card (t : ℕ) (ht : 0 < t) :
    (eligiblePairStarts (q0 t) (q0 t+1) 5 (afterFirst0 t) (anchor0 t)).card = 2+3*t := by
  rw [eligible0_exact t ht, starts0_card t ht]
theorem eligible0_zero_card :
    (eligiblePairStarts (q0 0) (q0 0+1) 5 (afterFirst0 0) (anchor0 0)).card = 1 := by
  rw [eligible0_zero_exact]; simp
theorem eligible1_card (t : ℕ) :
    (eligiblePairStarts (q1 t) (q1 t+1) 4 (afterFirst1 t) (anchor1 t)).card = 1+3*t := by
  rw [eligible1_exact, starts1_card]
theorem eligible2_card (t : ℕ) :
    (eligiblePairStarts (q2 t) (q2 t-1) 2 (afterFirst2 t) (anchor2 t)).card = 2+3*t := by
  rw [eligible2_exact, starts2_card]

def selected0 (t v : ℕ) : Finset ℕ := Operations.firstK
  (eligiblePairStarts (q0 t) (q0 t+1) 5 (afterFirst0 t) (anchor0 t)) (v-1)
def selected1 (t u : ℕ) : Finset ℕ := Operations.firstK
  (eligiblePairStarts (q1 t) (q1 t+1) 4 (afterFirst1 t) (anchor1 t)) (u-1)
def selected2 (t v : ℕ) : Finset ℕ := Operations.firstK
  (eligiblePairStarts (q2 t) (q2 t-1) 2 (afterFirst2 t) (anchor2 t)) (v-1)

theorem selected0_card (t u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hq : q u v = q0 t) (hcase : 0 < t ∨ 2 ≤ u) :
    (selected0 t v).card = v-1 := by
  unfold selected0
  apply Operations.firstK_card
  by_cases ht : t = 0
  · subst t
    rw [eligible0_zero_card]
    dsimp [q, q0] at hq
    omega
  · have ht' : 0 < t := by omega
    rw [eligible0_card t ht']
    dsimp [q, q0] at hq
    omega
theorem selected1_card (t u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hq : q u v = q1 t) : (selected1 t u).card = u-1 := by
  unfold selected1
  apply Operations.firstK_card
  rw [eligible1_card]
  dsimp [q, q1] at hq
  omega
theorem selected2_card (t u v : ℕ) (hu : 2 ≤ u) (hv : 0 < v)
    (hq : q u v = q2 t) : (selected2 t v).card = v-1 := by
  unfold selected2
  apply Operations.firstK_card
  rw [eligible2_card]
  dsimp [q, q2] at hq
  omega

def moveSelectedPairs (parent : ℕ → ℕ) (sum recipient : ℕ) (starts : Finset ℕ) : ℕ → ℕ :=
  fun x => if x ∈ starts ∨ sum-x ∈ starts then recipient else parent x
def afterPairs0 (t v : ℕ) : ℕ → ℕ :=
  moveSelectedPairs (afterFirst0 t) (q0 t+1) (q0 t-4) (selected0 t v)
def afterPairs1 (t u : ℕ) : ℕ → ℕ :=
  moveSelectedPairs (afterFirst1 t) (q1 t+1) (q1 t-3) (selected1 t u)
def afterPairs2 (t v : ℕ) : ℕ → ℕ :=
  moveSelectedPairs (afterFirst2 t) (q2 t-1) (q2 t-3) (selected2 t v)
def splitParent (parent : ℕ → ℕ) (a : Anchor) : ℕ → ℕ :=
  fun x => if x = a.C then a.A else if x = a.Z then a.C else parent x
def finalParent0 (t v : ℕ) : ℕ → ℕ := splitParent (afterPairs0 t v) (anchor0 t)
def finalParent1 (t u : ℕ) : ℕ → ℕ := splitParent (afterPairs1 t u) (anchor1 t)
def finalParent2 (t v : ℕ) : ℕ → ℕ := splitParent (afterPairs2 t v) (anchor2 t)
def alternateFinalParent (t : ℕ) : ℕ → ℕ :=
  splitParent (alternateAfterFirst t) (alternateAnchor t)

/-- Ten skeleton edges, Table `tab:skeleton` and equation `eq:alternate`. -/
def skeleton0 (Q : ℕ) : List (ℕ × ℕ) :=
  [(0,Q),(0,1),(0,Q-1),(Q,2),(Q,Q-2),(Q,3),
   (1,Q-3),(1,4),(1,Q-4),(Q-1,5)]
def skeleton1 (Q : ℕ) : List (ℕ × ℕ) :=
  [(0,Q),(0,1),(0,Q-1),(Q,2),(Q,Q-2),(Q,3),
   (1,Q-3),(Q-1,4),(Q-1,Q-4),(Q-1,5)]
def skeleton2 (Q : ℕ) : List (ℕ × ℕ) :=
  [(0,Q),(0,1),(0,Q-1),(Q,2),(1,Q-2),(1,3),(1,Q-3),
   (Q-1,4),(Q-1,Q-4),(Q-1,5)]
def alternateSkeleton (Q : ℕ) : List (ℕ × ℕ) :=
  [(0,Q),(0,2),(0,Q-1),(Q,3),(Q,4),(Q,Q-4),
   (2,Q-3),(Q-1,1),(Q-1,5),(Q-1,Q-2)]

def edgeDifferences (edges : List (ℕ × ℕ)) : List ℕ :=
  edges.map fun e => Nat.dist e.1 e.2
theorem skeleton0_differences (t : ℕ) :
    edgeDifferences (skeleton0 (q0 t)) =
    [27+6*t,1,26+6*t,25+6*t,2,24+6*t,23+6*t,3,22+6*t,21+6*t] := by
  simp only [edgeDifferences, skeleton0, q0, List.map_cons, List.map_nil,
    Nat.dist, Prod.fst, Prod.snd]
  simp only [List.cons.injEq, eq_self_iff_true, and_true, true_and]
  omega
theorem skeleton1_differences (t : ℕ) :
    edgeDifferences (skeleton1 (q1 t)) =
    [25+6*t,1,24+6*t,23+6*t,2,22+6*t,21+6*t,20+6*t,3,19+6*t] := by
  simp only [edgeDifferences, skeleton1, q1, List.map_cons, List.map_nil,
    Nat.dist, Prod.fst, Prod.snd]
  simp only [List.cons.injEq, eq_self_iff_true, and_true, true_and]
  omega
theorem skeleton2_differences (t : ℕ) :
    edgeDifferences (skeleton2 (q2 t)) =
    [29+6*t,1,28+6*t,27+6*t,26+6*t,2,25+6*t,24+6*t,3,23+6*t] := by
  simp only [edgeDifferences, skeleton2, q2, List.map_cons, List.map_nil,
    Nat.dist, Prod.fst, Prod.snd]
  simp only [List.cons.injEq, eq_self_iff_true, and_true, true_and]
  omega
theorem alternateSkeleton_differences (t : ℕ) :
    edgeDifferences (alternateSkeleton (q2 t)) =
    [29+6*t,2,28+6*t,26+6*t,25+6*t,4,24+6*t,27+6*t,23+6*t,1] := by
  simp only [edgeDifferences, alternateSkeleton, q2, List.map_cons,
    List.map_nil, Nat.dist, Prod.fst, Prod.snd]
  simp only [List.cons.injEq, eq_self_iff_true, and_true, true_and]
  omega

def edgesFromParent (Q : ℕ) (skeleton : List (ℕ × ℕ)) (parent : ℕ → ℕ) : List (ℕ × ℕ) :=
  skeleton ++ ((leafLabels Q).sort (· ≤ ·)).map (fun x => (parent x,x))
def finalEdges0 (t v : ℕ) : List (ℕ × ℕ) :=
  edgesFromParent (q0 t) (skeleton0 (q0 t)) (finalParent0 t v)
def finalEdges1 (t u : ℕ) : List (ℕ × ℕ) :=
  edgesFromParent (q1 t) (skeleton1 (q1 t)) (finalParent1 t u)
def finalEdges2 (t v : ℕ) : List (ℕ × ℕ) :=
  edgesFromParent (q2 t) (skeleton2 (q2 t)) (finalParent2 t v)
def alternateFinalEdges (t : ℕ) : List (ℕ × ℕ) :=
  edgesFromParent (q2 t) (alternateSkeleton (q2 t)) (alternateFinalParent t)

/-! Exact finite parent fibres. Erasure lists retain a constructive count
proof even for the growing donor fibre. -/
def fibre (Q : ℕ) (parent : ℕ → ℕ) (p : ℕ) : Finset ℕ :=
  (leafLabels Q).filter fun x => parent x = p

def eraseList (s : Finset ℕ) : List ℕ → Finset ℕ
  | [] => s
  | a :: xs => eraseList (s.erase a) xs

theorem mem_eraseList (s : Finset ℕ) (xs : List ℕ) (x : ℕ) :
    x ∈ eraseList s xs ↔ x ∈ s ∧ x ∉ xs := by
  induction xs generalizing s with
  | nil => simp [eraseList]
  | cons a xs ih =>
    simp only [eraseList, ih, Finset.mem_erase, List.mem_cons, not_or]
    tauto

theorem card_eraseList (s : Finset ℕ) (xs : List ℕ)
    (hn : xs.Nodup) (hm : ∀ a ∈ xs, a ∈ s) :
    (eraseList s xs).card = s.card-xs.length := by
  induction xs generalizing s with
  | nil => simp [eraseList]
  | cons a xs ih =>
    have hna := (List.nodup_cons.mp hn).1
    have hnx := (List.nodup_cons.mp hn).2
    have ha : a ∈ s := hm a (by simp)
    have hmx : ∀ b ∈ xs, b ∈ s.erase a := by
      intro b hb
      refine Finset.mem_erase.mpr ⟨?_, hm b (by simp [hb])⟩
      intro hba
      exact hna (by simpa [hba] using hb)
    rw [eraseList, ih (s.erase a) hnx hmx, Finset.card_erase_of_mem ha]
    simp only [List.length_cons]
    omega

def exceptions0 (t : ℕ) : List ℕ :=
  [22+6*t,6,21+6*t,7,20+6*t,8,14+3*t]
def exceptions1 (t : ℕ) : List ℕ :=
  [15+4*t,8+2*t,7,18+4*t,20+6*t,6,19+6*t,10+2*t,11+2*t]
def exceptions2 (t : ℕ) : List ℕ :=
  [23+6*t,22+6*t,12+3*t,6,14+3*t,16+3*t,13+3*t]
def alternateExceptions (t : ℕ) : List ℕ :=
  [18+4*t,10+2*t,7,12+2*t,23+6*t,6,8,9+2*t,20+4*t]

def baseFibre0 (t p : ℕ) : Finset ℕ :=
  if p = 5 then eraseList (leafLabels (q0 t)) (exceptions0 t)
  else if p = 2 then {22+6*t}
  else if p = 3 then {21+6*t}
  else if p = 4 then {20+6*t}
  else if p = 25+6*t then {6}
  else if p = 24+6*t then {7}
  else if p = 23+6*t then {8,14+3*t}
  else ∅
def baseFibre1 (t p : ℕ) : Finset ℕ :=
  if p = 4 then eraseList (leafLabels (q1 t)) (exceptions1 t)
  else if p = 22+6*t then {7,8+2*t,15+4*t,18+4*t}
  else if p = 2 then {20+6*t}
  else if p = 3 then {19+6*t}
  else if p = 23+6*t then {6}
  else if p = 21+6*t then {10+2*t}
  else if p = 5 then {11+2*t}
  else ∅
def baseFibre2 (t p : ℕ) : Finset ℕ :=
  if p = 2 then eraseList (leafLabels (q2 t)) (exceptions2 t)
  else if p = 26+6*t then {12+3*t,22+6*t}
  else if p = 3 then {23+6*t}
  else if p = 27+6*t then {6}
  else if p = 4 then {14+3*t}
  else if p = 5 then {16+3*t}
  else if p = 25+6*t then {13+3*t}
  else ∅
def alternateBaseFibre (t p : ℕ) : Finset ℕ :=
  if p = 4 then eraseList (leafLabels (q2 t)) (alternateExceptions t)
  else if p = 26+6*t then {7,10+2*t,12+2*t,18+4*t}
  else if p = 1 then {23+6*t}
  else if p = 27+6*t then {6}
  else if p = 5 then {8}
  else if p = 3 then {9+2*t}
  else if p = 25+6*t then {20+4*t}
  else ∅

theorem baseFibre0_exact (t p : ℕ) :
    fibre (q0 t) (baseParent0 t) p = baseFibre0 t p := by
  ext x
  simp only [fibre]
  rw [Finset.mem_filter]
  by_cases hx0 : x = 22+6*t
  · subst x
    by_cases hp : p = 2
    · subst p
      simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0] <;> omega
    · simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hp] <;> omega
  · by_cases hx1 : x = 6
    · subst x
      by_cases hp : p = 25+6*t
      · subst p
        simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hx0] <;> omega
      · simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hx0, hp] <;> omega
    · by_cases hx2 : x = 21+6*t
      · subst x
        by_cases hp : p = 3
        · subst p
          simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hx0, hx1] <;> omega
        · simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hx0, hx1, hp] <;> omega
      · by_cases hx3 : x = 7
        · subst x
          by_cases hp : p = 24+6*t
          · subst p
            simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hx0, hx1, hx2] <;> omega
          · simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hx0, hx1, hx2, hp] <;> omega
        · by_cases hx4 : x = 20+6*t
          · subst x
            by_cases hp : p = 4
            · subst p
              simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hx0, hx1, hx2, hx3] <;> omega
            · simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hx0, hx1, hx2, hx3, hp] <;> omega
          · by_cases hx5 : x = 8
            · subst x
              by_cases hp : p = 23+6*t
              · subst p
                simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hx0, hx1, hx2, hx3, hx4] <;> omega
              · simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hx0, hx1, hx2, hx3, hx4, hp] <;> omega
            · by_cases hx6 : x = 14+3*t
              · subst x
                by_cases hp : p = 23+6*t
                · subst p
                  simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hx0, hx1, hx2, hx3, hx4, hx5] <;> omega
                · simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hx0, hx1, hx2, hx3, hx4, hx5, hp] <;> omega
              · by_cases hp : p = 5
                · subst p
                  simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hx0, hx1, hx2, hx3, hx4, hx5, hx6] <;> omega
                · simp (disch := omega) [baseParent0, baseFibre0, mem_ite, mem_eraseList, exceptions0, leafLabels, q0, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hp] <;> omega

theorem baseFibre1_exact (t p : ℕ) :
    fibre (q1 t) (baseParent1 t) p = baseFibre1 t p := by
  ext x
  simp only [fibre]
  rw [Finset.mem_filter]
  by_cases hx0 : x = 15+4*t
  · subst x
    by_cases hp : p = 22+6*t
    · subst p
      simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1] <;> omega
    · simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hp] <;> omega
  · by_cases hx1 : x = 8+2*t
    · subst x
      by_cases hp : p = 22+6*t
      · subst p
        simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0] <;> omega
      · simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hp] <;> omega
    · by_cases hx2 : x = 7
      · subst x
        by_cases hp : p = 22+6*t
        · subst p
          simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1] <;> omega
        · simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hp] <;> omega
      · by_cases hx3 : x = 18+4*t
        · subst x
          by_cases hp : p = 22+6*t
          · subst p
            simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hx2] <;> omega
          · simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hx2, hp] <;> omega
        · by_cases hx4 : x = 20+6*t
          · subst x
            by_cases hp : p = 2
            · subst p
              simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hx2, hx3] <;> omega
            · simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hx2, hx3, hp] <;> omega
          · by_cases hx5 : x = 6
            · subst x
              by_cases hp : p = 23+6*t
              · subst p
                simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hx2, hx3, hx4] <;> omega
              · simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hx2, hx3, hx4, hp] <;> omega
            · by_cases hx6 : x = 19+6*t
              · subst x
                by_cases hp : p = 3
                · subst p
                  simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hx2, hx3, hx4, hx5] <;> omega
                · simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hx2, hx3, hx4, hx5, hp] <;> omega
              · by_cases hx7 : x = 10+2*t
                · subst x
                  by_cases hp : p = 21+6*t
                  · subst p
                    simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hx2, hx3, hx4, hx5, hx6] <;> omega
                  · simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hp] <;> omega
                · by_cases hx8 : x = 11+2*t
                  · subst x
                    by_cases hp : p = 5
                    · subst p
                      simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7] <;> omega
                    · simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hp] <;> omega
                  · by_cases hp : p = 4
                    · subst p
                      simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8] <;> omega
                    · simp (disch := omega) [baseParent1, baseFibre1, mem_ite, mem_eraseList, exceptions1, leafLabels, q1, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hp] <;> omega

theorem baseFibre2_exact (t p : ℕ) :
    fibre (q2 t) (baseParent2 t) p = baseFibre2 t p := by
  ext x
  simp only [fibre]
  rw [Finset.mem_filter]
  by_cases hx0 : x = 23+6*t
  · subst x
    by_cases hp : p = 3
    · subst p
      simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2] <;> omega
    · simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hp] <;> omega
  · by_cases hx1 : x = 22+6*t
    · subst x
      by_cases hp : p = 26+6*t
      · subst p
        simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hx0] <;> omega
      · simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hx0, hp] <;> omega
    · by_cases hx2 : x = 12+3*t
      · subst x
        by_cases hp : p = 26+6*t
        · subst p
          simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hx0, hx1] <;> omega
        · simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hx0, hx1, hp] <;> omega
      · by_cases hx3 : x = 6
        · subst x
          by_cases hp : p = 27+6*t
          · subst p
            simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hx0, hx1, hx2] <;> omega
          · simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hx0, hx1, hx2, hp] <;> omega
        · by_cases hx4 : x = 14+3*t
          · subst x
            by_cases hp : p = 4
            · subst p
              simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hx0, hx1, hx2, hx3] <;> omega
            · simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hx0, hx1, hx2, hx3, hp] <;> omega
          · by_cases hx5 : x = 16+3*t
            · subst x
              by_cases hp : p = 5
              · subst p
                simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hx0, hx1, hx2, hx3, hx4] <;> omega
              · simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hx0, hx1, hx2, hx3, hx4, hp] <;> omega
            · by_cases hx6 : x = 13+3*t
              · subst x
                by_cases hp : p = 25+6*t
                · subst p
                  simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hx0, hx1, hx2, hx3, hx4, hx5] <;> omega
                · simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hx0, hx1, hx2, hx3, hx4, hx5, hp] <;> omega
              · by_cases hp : p = 2
                · subst p
                  simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hx0, hx1, hx2, hx3, hx4, hx5, hx6] <;> omega
                · simp (disch := omega) [baseParent2, baseFibre2, mem_ite, mem_eraseList, exceptions2, leafLabels, q2, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hp] <;> omega

theorem alternateBaseFibre_exact (t p : ℕ) :
    fibre (q2 t) (alternateBaseParent t) p = alternateBaseFibre t p := by
  ext x
  simp only [fibre]
  rw [Finset.mem_filter]
  by_cases hx0 : x = 18+4*t
  · subst x
    by_cases hp : p = 26+6*t
    · subst p
      simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2] <;> omega
    · simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hp] <;> omega
  · by_cases hx1 : x = 10+2*t
    · subst x
      by_cases hp : p = 26+6*t
      · subst p
        simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0] <;> omega
      · simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hp] <;> omega
    · by_cases hx2 : x = 7
      · subst x
        by_cases hp : p = 26+6*t
        · subst p
          simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1] <;> omega
        · simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hp] <;> omega
      · by_cases hx3 : x = 12+2*t
        · subst x
          by_cases hp : p = 26+6*t
          · subst p
            simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hx2] <;> omega
          · simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hx2, hp] <;> omega
        · by_cases hx4 : x = 23+6*t
          · subst x
            by_cases hp : p = 1
            · subst p
              simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hx2, hx3] <;> omega
            · simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hx2, hx3, hp] <;> omega
          · by_cases hx5 : x = 6
            · subst x
              by_cases hp : p = 27+6*t
              · subst p
                simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hx2, hx3, hx4] <;> omega
              · simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hx2, hx3, hx4, hp] <;> omega
            · by_cases hx6 : x = 8
              · subst x
                by_cases hp : p = 5
                · subst p
                  simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hx2, hx3, hx4, hx5] <;> omega
                · simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hx2, hx3, hx4, hx5, hp] <;> omega
              · by_cases hx7 : x = 9+2*t
                · subst x
                  by_cases hp : p = 3
                  · subst p
                    simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hx2, hx3, hx4, hx5, hx6] <;> omega
                  · simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hp] <;> omega
                · by_cases hx8 : x = 20+4*t
                  · subst x
                    by_cases hp : p = 25+6*t
                    · subst p
                      simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7] <;> omega
                    · simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hp] <;> omega
                  · by_cases hp : p = 4
                    · subst p
                      simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8] <;> omega
                    · simp (disch := omega) [alternateBaseParent, alternateBaseFibre, mem_ite, mem_eraseList, alternateExceptions, leafLabels, q2, hx0, hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8, hp] <;> omega

theorem base0_donor_card (t : ℕ) : (fibre (q0 t) (baseParent0 t) 5).card = 10+6*t := by
  rw [baseFibre0_exact]
  simp only [baseFibre0, ite_true]
  rw [card_eraseList]
  · have hI : (leafLabels (q0 t)).card = (q0 t-5+1)-6 := by simp [leafLabels]
    rw [hI]
    simp only [exceptions0, List.length_cons, List.length_nil, q0]
    omega
  · simp only [exceptions0, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_or, not_false_eq_true, and_true]
    omega
  · intro a ha
    simp only [exceptions0, List.mem_cons, List.not_mem_nil] at ha
    simp only [leafLabels, q0, Finset.mem_Icc]
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse <;> first | contradiction | omega
theorem base1_donor_card (t : ℕ) : (fibre (q1 t) (baseParent1 t) 4).card = 6+6*t := by
  rw [baseFibre1_exact]
  simp only [baseFibre1, ite_true]
  rw [card_eraseList]
  · have hI : (leafLabels (q1 t)).card = (q1 t-5+1)-6 := by simp [leafLabels]
    rw [hI]
    simp only [exceptions1, List.length_cons, List.length_nil, q1]
    omega
  · simp only [exceptions1, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_or, not_false_eq_true, and_true]
    omega
  · intro a ha
    simp only [exceptions1, List.mem_cons, List.not_mem_nil] at ha
    simp only [leafLabels, q1, Finset.mem_Icc]
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse <;> first | contradiction | omega
theorem base2_donor_card (t : ℕ) : (fibre (q2 t) (baseParent2 t) 2).card = 12+6*t := by
  rw [baseFibre2_exact]
  simp only [baseFibre2, ite_true]
  rw [card_eraseList]
  · have hI : (leafLabels (q2 t)).card = (q2 t-5+1)-6 := by simp [leafLabels]
    rw [hI]
    simp only [exceptions2, List.length_cons, List.length_nil, q2]
    omega
  · simp only [exceptions2, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_or, not_false_eq_true, and_true]
    omega
  · intro a ha
    simp only [exceptions2, List.mem_cons, List.not_mem_nil] at ha
    simp only [leafLabels, q2, Finset.mem_Icc]
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse <;> first | contradiction | omega
theorem alternateBase_donor_card (t : ℕ) :
    (fibre (q2 t) (alternateBaseParent t) 4).card = 10+6*t := by
  rw [alternateBaseFibre_exact]
  simp only [alternateBaseFibre, ite_true]
  rw [card_eraseList]
  · have hI : (leafLabels (q2 t)).card = (q2 t-5+1)-6 := by simp [leafLabels]
    rw [hI]
    simp only [alternateExceptions, List.length_cons, List.length_nil, q2]
    omega
  · simp only [alternateExceptions, List.nodup_cons, List.mem_cons, List.not_mem_nil,
      List.nodup_nil, not_or, not_false_eq_true, and_true]
    omega
  · intro a ha
    simp only [alternateExceptions, List.mem_cons, List.not_mem_nil] at ha
    simp only [leafLabels, q2, Finset.mem_Icc]
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hfalse <;> first | contradiction | omega

theorem card_four_ordered (a b c d : ℕ) (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ({a,b,c,d} : Finset ℕ).card = 4 := by
  have hab' : a ≠ b := by omega
  have hac' : a ≠ c := by omega
  have had' : a ≠ d := by omega
  have hbc' : b ≠ c := by omega
  have hbd' : b ≠ d := by omega
  have hcd' : c ≠ d := by omega
  simp [hab', hac', had', hbc', hbd', hcd']

/-- All non-donor base fibre sizes, including empty fibres at arbitrary
other labels. This is useful for excluding the future depth-two label C. -/
theorem base0_nondonor_card (t p : ℕ) (hp : p ≠ 5) :
    (fibre (q0 t) (baseParent0 t) p).card =
      if p = 23+6*t then 2
      else if p = 2 ∨ p = 3 ∨ p = 4 ∨ p = 25+6*t ∨ p = 24+6*t then 1 else 0 := by
  have htwo : ({8,14+3*t} : Finset ℕ).card = 2 := by
    have hne : 8 ≠ 14+3*t := by omega
    simp [hne]
  rw [baseFibre0_exact]
  simp only [baseFibre0, hp, if_false]
  split_ifs <;> simp_all <;> omega
theorem base1_nondonor_card (t p : ℕ) (hp : p ≠ 4) :
    (fibre (q1 t) (baseParent1 t) p).card =
      if p = 22+6*t then 4
      else if p = 2 ∨ p = 3 ∨ p = 23+6*t ∨ p = 21+6*t ∨ p = 5 then 1 else 0 := by
  have hfour : ({7,8+2*t,15+4*t,18+4*t} : Finset ℕ).card = 4 :=
    card_four_ordered _ _ _ _ (by omega) (by omega) (by omega)
  rw [baseFibre1_exact]
  simp only [baseFibre1, hp, if_false]
  split_ifs <;> simp_all <;> omega
theorem base2_nondonor_card (t p : ℕ) (hp : p ≠ 2) :
    (fibre (q2 t) (baseParent2 t) p).card =
      if p = 26+6*t then 2
      else if p = 3 ∨ p = 27+6*t ∨ p = 4 ∨ p = 5 ∨ p = 25+6*t then 1 else 0 := by
  have htwo : ({12+3*t,22+6*t} : Finset ℕ).card = 2 := by
    have hne : 12+3*t ≠ 22+6*t := by omega
    simp [hne]
  rw [baseFibre2_exact]
  simp only [baseFibre2, hp, if_false]
  split_ifs <;> simp_all <;> omega
theorem alternateBase_nondonor_card (t p : ℕ) (hp : p ≠ 4) :
    (fibre (q2 t) (alternateBaseParent t) p).card =
      if p = 26+6*t then 4
      else if p = 1 ∨ p = 27+6*t ∨ p = 5 ∨ p = 3 ∨ p = 25+6*t then 1 else 0 := by
  have hfour : ({7,10+2*t,12+2*t,18+4*t} : Finset ℕ).card = 4 :=
    card_four_ordered _ _ _ _ (by omega) (by omega) (by omega)
  rw [alternateBaseFibre_exact]
  simp only [alternateBaseFibre, hp, if_false]
  split_ifs <;> simp_all <;> omega

/-! Generic fibre arithmetic for concrete finite reparenting. -/
def reparentSet (parent : ℕ → ℕ) (leaves : Finset ℕ) (recipient : ℕ) : ℕ → ℕ :=
  fun x => if x ∈ leaves then recipient else parent x

theorem reparentSet_donor_fibre (Q donor recipient : ℕ) (parent : ℕ → ℕ)
    (leaves : Finset ℕ) (hneq : recipient ≠ donor) :
    fibre Q (reparentSet parent leaves recipient) donor = fibre Q parent donor \ leaves := by
  ext x
  simp only [fibre]
  simp only [Finset.mem_filter]
  simp only [ reparentSet, Finset.mem_filter, Finset.mem_sdiff]
  by_cases hx : x ∈ leaves <;> simp [hx, hneq] <;> tauto

theorem reparentSet_recipient_fibre (Q donor recipient : ℕ) (parent : ℕ → ℕ)
    (leaves : Finset ℕ) (hneq : recipient ≠ donor)
    (hsub : leaves ⊆ fibre Q parent donor) :
    fibre Q (reparentSet parent leaves recipient) recipient = fibre Q parent recipient ∪ leaves := by
  ext x
  simp only [fibre]
  simp only [Finset.mem_filter]
  simp only [ reparentSet, Finset.mem_filter, Finset.mem_union]
  by_cases hx : x ∈ leaves
  · have hmem := Finset.mem_filter.mp (hsub hx)
    simp [hx, hmem.1]
  · simp [hx]

theorem reparentSet_other_fibre (Q donor recipient p : ℕ) (parent : ℕ → ℕ)
    (leaves : Finset ℕ) (hpr : p ≠ recipient) (hpd : p ≠ donor)
    (hsub : leaves ⊆ fibre Q parent donor) :
    fibre Q (reparentSet parent leaves recipient) p = fibre Q parent p := by
  ext x
  simp only [fibre]
  simp only [Finset.mem_filter]
  simp only [ reparentSet, Finset.mem_filter]
  by_cases hx : x ∈ leaves
  · have hmem := Finset.mem_filter.mp (hsub hx)
    simp [hx, hmem.2, Ne.symm hpr, Ne.symm hpd]
  · simp [hx]

theorem reparentSet_donor_card (Q donor recipient : ℕ) (parent : ℕ → ℕ)
    (leaves : Finset ℕ) (hneq : recipient ≠ donor)
    (hsub : leaves ⊆ fibre Q parent donor) :
    (fibre Q (reparentSet parent leaves recipient) donor).card =
      (fibre Q parent donor).card-leaves.card := by
  rw [reparentSet_donor_fibre Q donor recipient parent leaves hneq,
    Finset.card_sdiff_of_subset hsub]

theorem reparentSet_recipient_card (Q donor recipient : ℕ) (parent : ℕ → ℕ)
    (leaves : Finset ℕ) (hneq : recipient ≠ donor)
    (hsub : leaves ⊆ fibre Q parent donor) :
    (fibre Q (reparentSet parent leaves recipient) recipient).card =
      (fibre Q parent recipient).card+leaves.card := by
  rw [reparentSet_recipient_fibre Q donor recipient parent leaves hneq hsub]
  apply Finset.card_union_of_disjoint
  apply Finset.disjoint_left.mpr
  intro x hx hl
  have hr := (Finset.mem_filter.mp hx).2
  have hd := (Finset.mem_filter.mp (hsub hl)).2
  exact hneq (hr.symm.trans hd)

theorem moveTwo_eq_reparentSet (parent : ℕ → ℕ) (x y recipient : ℕ) :
    moveTwo parent x y recipient = reparentSet parent {x,y} recipient := by
  funext z
  simp only [moveTwo, reparentSet, Finset.mem_insert, Finset.mem_singleton]

theorem firstPair0_available (t : ℕ) (ht : 0 < t) :
    9+2*t ∈ leafLabels (q0 t) ∧ 21+4*t ∈ leafLabels (q0 t) ∧
    baseParent0 t (9+2*t) = 5 ∧ baseParent0 t (21+4*t) = 5 ∧
    9+2*t ≠ 21+4*t := by
  have hx : 9+2*t ∈ fibre (q0 t) (baseParent0 t) 5 := by
    rw [baseFibre0_exact]
    simp [baseFibre0, mem_eraseList, exceptions0, leafLabels, q0]
    omega
  have hy : 21+4*t ∈ fibre (q0 t) (baseParent0 t) 5 := by
    rw [baseFibre0_exact]
    simp [baseFibre0, mem_eraseList, exceptions0, leafLabels, q0]
    omega
  exact ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hy).1,
    (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2, by omega⟩

theorem firstPair0_zero_available :
    13 ∈ leafLabels (q0 0) ∧ 17 ∈ leafLabels (q0 0) ∧
    baseParent0 0 13 = 5 ∧ baseParent0 0 17 = 5 ∧ (13 : ℕ) ≠ 17 := by decide
theorem firstPair1_available (t : ℕ) :
    13+3*t ∈ leafLabels (q1 t) ∧ 14+3*t ∈ leafLabels (q1 t) ∧
    baseParent1 t (13+3*t) = 4 ∧ baseParent1 t (14+3*t) = 4 ∧
    13+3*t ≠ 14+3*t := by
  have hx : 13+3*t ∈ fibre (q1 t) (baseParent1 t) 4 := by
    rw [baseFibre1_exact]
    simp [baseFibre1, mem_eraseList, exceptions1, leafLabels, q1]
    omega
  have hy : 14+3*t ∈ fibre (q1 t) (baseParent1 t) 4 := by
    rw [baseFibre1_exact]
    simp [baseFibre1, mem_eraseList, exceptions1, leafLabels, q1]
    omega
  exact ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hy).1,
    (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2, by omega⟩

theorem firstPair2_available (t : ℕ) :
    8+2*t ∈ leafLabels (q2 t) ∧ 19+4*t ∈ leafLabels (q2 t) ∧
    baseParent2 t (8+2*t) = 2 ∧ baseParent2 t (19+4*t) = 2 ∧
    8+2*t ≠ 19+4*t := by
  have hx : 8+2*t ∈ fibre (q2 t) (baseParent2 t) 2 := by
    rw [baseFibre2_exact]
    simp [baseFibre2, mem_eraseList, exceptions2, leafLabels, q2]
    omega
  have hy : 19+4*t ∈ fibre (q2 t) (baseParent2 t) 2 := by
    rw [baseFibre2_exact]
    simp [baseFibre2, mem_eraseList, exceptions2, leafLabels, q2]
    omega
  exact ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hy).1,
    (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2, by omega⟩

theorem alternateFirstPair_available (t : ℕ) :
    14+3*t ∈ leafLabels (q2 t) ∧ 17+3*t ∈ leafLabels (q2 t) ∧
    alternateBaseParent t (14+3*t) = 4 ∧ alternateBaseParent t (17+3*t) = 4 ∧
    14+3*t ≠ 17+3*t := by
  have hx : 14+3*t ∈ fibre (q2 t) (alternateBaseParent t) 4 := by
    rw [alternateBaseFibre_exact]
    simp [alternateBaseFibre, mem_eraseList, alternateExceptions, leafLabels, q2]
    omega
  have hy : 17+3*t ∈ fibre (q2 t) (alternateBaseParent t) 4 := by
    rw [alternateBaseFibre_exact]
    simp [alternateBaseFibre, mem_eraseList, alternateExceptions, leafLabels, q2]
    omega
  exact ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hy).1,
    (Finset.mem_filter.mp hx).2, (Finset.mem_filter.mp hy).2, by omega⟩

theorem pair_subset_fibre (Q donor x y : ℕ) (parent : ℕ → ℕ)
    (hx : x ∈ leafLabels Q) (hy : y ∈ leafLabels Q)
    (hpx : parent x = donor) (hpy : parent y = donor) :
    ({x,y} : Finset ℕ) ⊆ fibre Q parent donor := by
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact Finset.mem_filter.mpr ⟨hx, hpx⟩
  · exact Finset.mem_filter.mpr ⟨hy, hpy⟩

theorem afterFirst0_counts (t : ℕ) :
    (fibre (q0 t) (afterFirst0 t) 5).card = 8+6*t ∧
    (fibre (q0 t) (afterFirst0 t) (q0 t-2)).card = 3 ∧
    (fibre (q0 t) (afterFirst0 t) (q0 t-4)).card = 2 := by
  have hQ : (fibre (q0 t) (baseParent0 t) (q0 t-2)).card = 1 := by
    have h := base0_nondonor_card t (q0 t-2) (by dsimp [q0]; omega)
    have he : q0 t-2 ≠ 23+6*t := by dsimp [q0]; omega
    rw [if_neg he] at h
    have ho : q0 t-2 = 2 ∨ q0 t-2 = 3 ∨ q0 t-2 = 4 ∨ q0 t-2 = 25+6*t ∨ q0 t-2 = 24+6*t := by
      right; right; right; left; dsimp [q0]; omega
    rw [if_pos ho] at h
    exact h
  have hP : (fibre (q0 t) (baseParent0 t) (q0 t-4)).card = 2 := by
    have h := base0_nondonor_card t (q0 t-4) (by dsimp [q0]; omega)
    have he : q0 t-4 = 23+6*t := by dsimp [q0]; omega
    rw [if_pos he] at h
    exact h
  by_cases ht : t = 0
  · subst t
    rcases firstPair0_zero_available with ⟨hx,hy,hpx,hpy,hxy⟩
    have hs := pair_subset_fibre _ _ _ _ _ hx hy hpx hpy
    have hc : ({13,17} : Finset ℕ).card = 2 := by decide
    simp only [afterFirst0, if_pos rfl, if_true, moveTwo_eq_reparentSet]
    constructor
    · rw [reparentSet_donor_card _ _ _ _ _ (by dsimp [q0]; omega) hs,
        base0_donor_card, hc]
    · constructor
      · rw [reparentSet_recipient_card _ _ _ _ _ (by dsimp [q0]; omega) hs, hQ, hc]
      · rw [reparentSet_other_fibre _ 5 _ _ _ _ (by dsimp [q0]; omega)
          (by dsimp [q0]; omega) hs, hP]
  · have ht' : 0 < t := by omega
    rcases firstPair0_available t ht' with ⟨hx,hy,hpx,hpy,hxy⟩
    have hs := pair_subset_fibre _ _ _ _ _ hx hy hpx hpy
    have hc : ({9+2*t,21+4*t} : Finset ℕ).card = 2 := by simp [hxy]
    simp only [afterFirst0, ht, if_false, moveTwo_eq_reparentSet]
    constructor
    · rw [reparentSet_donor_card _ _ _ _ _ (by dsimp [q0]; omega) hs,
        base0_donor_card, hc]
      omega
    · constructor
      · rw [reparentSet_recipient_card _ _ _ _ _ (by dsimp [q0]; omega) hs, hQ, hc]
      · rw [reparentSet_other_fibre _ 5 _ _ _ _ (by dsimp [q0]; omega)
          (by dsimp [q0]; omega) hs, hP]

theorem afterFirst1_counts (t : ℕ) :
    (fibre (q1 t) (afterFirst1 t) 4).card = 4+6*t ∧
    (fibre (q1 t) (afterFirst1 t) (q1 t-2)).card = 3 ∧
    (fibre (q1 t) (afterFirst1 t) (q1 t-3)).card = 4 := by
  rcases firstPair1_available t with ⟨hx,hy,hpx,hpy,hxy⟩
  have hs := pair_subset_fibre _ _ _ _ _ hx hy hpx hpy
  have hc : ({13+3*t,14+3*t} : Finset ℕ).card = 2 := by simp [hxy]
  have hQ : (fibre (q1 t) (baseParent1 t) (q1 t-2)).card = 1 := by
    have h := base1_nondonor_card t (q1 t-2) (by dsimp [q1]; omega)
    have he : q1 t-2 ≠ 22+6*t := by dsimp [q1]; omega
    rw [if_neg he] at h
    have ho : q1 t-2 = 2 ∨ q1 t-2 = 3 ∨ q1 t-2 = 23+6*t ∨ q1 t-2 = 21+6*t ∨ q1 t-2 = 5 := by
      right; right; left; dsimp [q1]; omega
    rw [if_pos ho] at h
    exact h
  have hB : (fibre (q1 t) (baseParent1 t) (q1 t-3)).card = 4 := by
    have h := base1_nondonor_card t (q1 t-3) (by dsimp [q1]; omega)
    have he : q1 t-3 = 22+6*t := by dsimp [q1]; omega
    rw [if_pos he] at h
    exact h
  simp only [afterFirst1, moveTwo_eq_reparentSet]
  constructor
  · rw [reparentSet_donor_card _ _ _ _ _ (by dsimp [q1]; omega) hs,
      base1_donor_card, hc]
    omega
  · constructor
    · rw [reparentSet_recipient_card _ _ _ _ _ (by dsimp [q1]; omega) hs, hQ, hc]
    · rw [reparentSet_other_fibre _ 4 _ _ _ _ (by dsimp [q1]; omega)
        (by dsimp [q1]; omega) hs, hB]

theorem afterFirst2_counts (t : ℕ) :
    (fibre (q2 t) (afterFirst2 t) 2).card = 10+6*t ∧
    (fibre (q2 t) (afterFirst2 t) (q2 t-4)).card = 3 ∧
    (fibre (q2 t) (afterFirst2 t) (q2 t-3)).card = 2 := by
  rcases firstPair2_available t with ⟨hx,hy,hpx,hpy,hxy⟩
  have hs := pair_subset_fibre _ _ _ _ _ hx hy hpx hpy
  have hc : ({8+2*t,19+4*t} : Finset ℕ).card = 2 := by simp [hxy]
  have hQ : (fibre (q2 t) (baseParent2 t) (q2 t-4)).card = 1 := by
    have h := base2_nondonor_card t (q2 t-4) (by dsimp [q2]; omega)
    have he : q2 t-4 ≠ 26+6*t := by dsimp [q2]; omega
    rw [if_neg he] at h
    have ho : q2 t-4 = 3 ∨ q2 t-4 = 27+6*t ∨ q2 t-4 = 4 ∨ q2 t-4 = 5 ∨ q2 t-4 = 25+6*t := by
      right; right; right; right; dsimp [q2]; omega
    rw [if_pos ho] at h
    exact h
  have hP : (fibre (q2 t) (baseParent2 t) (q2 t-3)).card = 2 := by
    have h := base2_nondonor_card t (q2 t-3) (by dsimp [q2]; omega)
    have he : q2 t-3 = 26+6*t := by dsimp [q2]; omega
    rw [if_pos he] at h
    exact h
  simp only [afterFirst2, moveTwo_eq_reparentSet]
  constructor
  · rw [reparentSet_donor_card _ _ _ _ _ (by dsimp [q2]; omega) hs,
      base2_donor_card, hc]
    omega
  · constructor
    · rw [reparentSet_recipient_card _ _ _ _ _ (by dsimp [q2]; omega) hs, hQ, hc]
    · rw [reparentSet_other_fibre _ 2 _ _ _ _ (by dsimp [q2]; omega)
        (by dsimp [q2]; omega) hs, hP]

theorem alternateAfterFirst_counts (t : ℕ) :
    (fibre (q2 t) (alternateAfterFirst t) 4).card = 8+6*t ∧
    (fibre (q2 t) (alternateAfterFirst t) (q2 t-2)).card = 3 ∧
    (fibre (q2 t) (alternateAfterFirst t) (q2 t-3)).card = 4 := by
  rcases alternateFirstPair_available t with ⟨hx,hy,hpx,hpy,hxy⟩
  have hs := pair_subset_fibre _ _ _ _ _ hx hy hpx hpy
  have hc : ({14+3*t,17+3*t} : Finset ℕ).card = 2 := by simp [hxy]
  have hQ : (fibre (q2 t) (alternateBaseParent t) (q2 t-2)).card = 1 := by
    have h := alternateBase_nondonor_card t (q2 t-2) (by dsimp [q2]; omega)
    have he : q2 t-2 ≠ 26+6*t := by dsimp [q2]; omega
    rw [if_neg he] at h
    have ho : q2 t-2 = 1 ∨ q2 t-2 = 27+6*t ∨ q2 t-2 = 5 ∨ q2 t-2 = 3 ∨ q2 t-2 = 25+6*t := by
      right; left; dsimp [q2]; omega
    rw [if_pos ho] at h
    exact h
  have hB : (fibre (q2 t) (alternateBaseParent t) (q2 t-3)).card = 4 := by
    have h := alternateBase_nondonor_card t (q2 t-3) (by dsimp [q2]; omega)
    have he : q2 t-3 = 26+6*t := by dsimp [q2]; omega
    rw [if_pos he] at h
    exact h
  simp only [alternateAfterFirst, moveTwo_eq_reparentSet]
  constructor
  · rw [reparentSet_donor_card _ _ _ _ _ (by dsimp [q2]; omega) hs,
      alternateBase_donor_card, hc]
    omega
  · constructor
    · rw [reparentSet_recipient_card _ _ _ _ _ (by dsimp [q2]; omega) hs, hQ, hc]
    · rw [reparentSet_other_fibre _ 4 _ _ _ _ (by dsimp [q2]; omega)
        (by dsimp [q2]; omega) hs, hB]

/-! The selected starts give an actual disjoint finite set of pendant labels,
with both members at the donor and neither reserved anchor among them. -/
theorem eligible_start_valid (Q S donor : ℕ) (parent : ℕ → ℕ) (a : Anchor)
    (x : ℕ) (hx : x ∈ eligiblePairStarts Q S donor parent a) :
    2*x < S ∧ 0 < x := by
  rcases Finset.mem_filter.mp hx with ⟨hxI, hlt, hrest⟩
  have hx6 := (Finset.mem_Icc.mp hxI).1
  omega

theorem eligible_pairs_subset_fibre (Q S donor : ℕ) (parent : ℕ → ℕ)
    (a : Anchor) (starts : Finset ℕ)
    (hsub : starts ⊆ eligiblePairStarts Q S donor parent a) :
    Operations.reflectionPairs S starts ⊆ fibre Q parent donor := by
  intro x hx
  obtain ⟨b, hb, hxb | hxb⟩ := (Operations.reflectionPairs_mem S x starts).1 hx
  · rcases Finset.mem_filter.mp (hsub hb) with
      ⟨hbI, hlt, hmateI, hparent, hmateParent, hC, hZ, hmC, hmZ⟩
    subst x
    exact Finset.mem_filter.mpr ⟨hbI, hparent⟩
  · rcases Finset.mem_filter.mp (hsub hb) with
      ⟨hbI, hlt, hmateI, hparent, hmateParent, hC, hZ, hmC, hmZ⟩
    subst x
    exact Finset.mem_filter.mpr ⟨hmateI, hmateParent⟩

theorem eligible_pairs_avoid_anchor (Q S donor : ℕ) (parent : ℕ → ℕ)
    (a : Anchor) (starts : Finset ℕ)
    (hsub : starts ⊆ eligiblePairStarts Q S donor parent a) :
    a.C ∉ Operations.reflectionPairs S starts ∧ a.Z ∉ Operations.reflectionPairs S starts := by
  constructor
  · intro hx
    obtain ⟨b, hb, hxb | hxb⟩ := (Operations.reflectionPairs_mem S a.C starts).1 hx
    · rcases Finset.mem_filter.mp (hsub hb) with
        ⟨hbI, hlt, hmateI, hparent, hmateParent, hC, hZ, hmC, hmZ⟩
      exact hC hxb.symm
    · rcases Finset.mem_filter.mp (hsub hb) with
        ⟨hbI, hlt, hmateI, hparent, hmateParent, hC, hZ, hmC, hmZ⟩
      exact hmC hxb.symm
  · intro hx
    obtain ⟨b, hb, hxb | hxb⟩ := (Operations.reflectionPairs_mem S a.Z starts).1 hx
    · rcases Finset.mem_filter.mp (hsub hb) with
        ⟨hbI, hlt, hmateI, hparent, hmateParent, hC, hZ, hmC, hmZ⟩
      exact hZ hxb.symm
    · rcases Finset.mem_filter.mp (hsub hb) with
        ⟨hbI, hlt, hmateI, hparent, hmateParent, hC, hZ, hmC, hmZ⟩
      exact hmZ hxb.symm

theorem moveSelectedPairs_eq_reparentSet (Q S donor recipient : ℕ)
    (parent : ℕ → ℕ) (a : Anchor) (starts : Finset ℕ)
    (hsub : starts ⊆ eligiblePairStarts Q S donor parent a) :
    moveSelectedPairs parent S recipient starts =
      reparentSet parent (Operations.reflectionPairs S starts) recipient := by
  have hv : ∀ x ∈ starts, 2*x < S := by
    intro x hx
    exact (eligible_start_valid Q S donor parent a x (hsub hx)).1
  have hp : ∀ x ∈ starts, 0 < x := by
    intro x hx
    exact (eligible_start_valid Q S donor parent a x (hsub hx)).2
  funext x
  simp only [moveSelectedPairs, reparentSet,
    Operations.reflectionPairs_mem_iff S starts hv hp x]

theorem eligible_pairs_card (Q S donor : ℕ) (parent : ℕ → ℕ)
    (a : Anchor) (starts : Finset ℕ)
    (hsub : starts ⊆ eligiblePairStarts Q S donor parent a) :
    (Operations.reflectionPairs S starts).card = 2*starts.card := by
  apply Operations.reflectionPairs_card
  intro x hx
  exact (eligible_start_valid Q S donor parent a x (hsub hx)).1

theorem selected0_subset (t v : ℕ) :
    selected0 t v ⊆ eligiblePairStarts (q0 t) (q0 t+1) 5 (afterFirst0 t) (anchor0 t) :=
  Operations.firstK_subset _ _
theorem selected1_subset (t u : ℕ) :
    selected1 t u ⊆ eligiblePairStarts (q1 t) (q1 t+1) 4 (afterFirst1 t) (anchor1 t) :=
  Operations.firstK_subset _ _
theorem selected2_subset (t v : ℕ) :
    selected2 t v ⊆ eligiblePairStarts (q2 t) (q2 t-1) 2 (afterFirst2 t) (anchor2 t) :=
  Operations.firstK_subset _ _

theorem afterPairs0_counts (t u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hq : q u v = q0 t) (hcase : 0 < t ∨ 2 ≤ u) :
    (fibre (q0 t) (afterPairs0 t v) 5).card = 2*u+2 ∧
    (fibre (q0 t) (afterPairs0 t v) (q0 t-4)).card = 2*v ∧
    (fibre (q0 t) (afterPairs0 t v) (q0 t-2)).card = 3 := by
  have hs := selected0_subset t v
  have hsub := eligible_pairs_subset_fibre _ _ _ _ _ _ hs
  have hc := eligible_pairs_card _ _ _ _ _ _ hs
  rw [selected0_card t u v hu hv hq hcase] at hc
  have hf := afterFirst0_counts t
  simp only [afterPairs0]
  rw [moveSelectedPairs_eq_reparentSet _ _ _ _ _ _ _ hs]
  constructor
  · rw [reparentSet_donor_card _ _ _ _ _ (by dsimp [q0]; omega) hsub, hf.1, hc]
    dsimp [q, q0] at hq
    omega
  · constructor
    · rw [reparentSet_recipient_card _ _ _ _ _ (by dsimp [q0]; omega) hsub, hf.2.2, hc]
      omega
    · rw [reparentSet_other_fibre _ 5 _ _ _ _ (by dsimp [q0]; omega)
        (by dsimp [q0]; omega) hsub, hf.2.1]

theorem afterPairs1_counts (t u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hq : q u v = q1 t) :
    (fibre (q1 t) (afterPairs1 t u) (q1 t-3)).card = 2*u+2 ∧
    (fibre (q1 t) (afterPairs1 t u) 4).card = 2*v ∧
    (fibre (q1 t) (afterPairs1 t u) (q1 t-2)).card = 3 := by
  have hs := selected1_subset t u
  have hsub := eligible_pairs_subset_fibre _ _ _ _ _ _ hs
  have hc := eligible_pairs_card _ _ _ _ _ _ hs
  rw [selected1_card t u v hu hv hq] at hc
  have hf := afterFirst1_counts t
  simp only [afterPairs1]
  rw [moveSelectedPairs_eq_reparentSet _ _ _ _ _ _ _ hs]
  constructor
  · rw [reparentSet_recipient_card _ _ _ _ _ (by dsimp [q1]; omega) hsub, hf.2.2, hc]
    omega
  · constructor
    · rw [reparentSet_donor_card _ _ _ _ _ (by dsimp [q1]; omega) hsub, hf.1, hc]
      dsimp [q, q1] at hq
      omega
    · rw [reparentSet_other_fibre _ 4 _ _ _ _ (by dsimp [q1]; omega)
        (by dsimp [q1]; omega) hsub, hf.2.1]

theorem afterPairs2_counts (t u v : ℕ) (hu : 2 ≤ u) (hv : 0 < v)
    (hq : q u v = q2 t) :
    (fibre (q2 t) (afterPairs2 t v) 2).card = 2*u+2 ∧
    (fibre (q2 t) (afterPairs2 t v) (q2 t-3)).card = 2*v ∧
    (fibre (q2 t) (afterPairs2 t v) (q2 t-4)).card = 3 := by
  have hs := selected2_subset t v
  have hsub := eligible_pairs_subset_fibre _ _ _ _ _ _ hs
  have hc := eligible_pairs_card _ _ _ _ _ _ hs
  rw [selected2_card t u v hu hv hq] at hc
  have hf := afterFirst2_counts t
  simp only [afterPairs2]
  rw [moveSelectedPairs_eq_reparentSet _ _ _ _ _ _ _ hs]
  constructor
  · rw [reparentSet_donor_card _ _ _ _ _ (by dsimp [q2]; omega) hsub, hf.1, hc]
    dsimp [q, q2] at hq
    omega
  · constructor
    · rw [reparentSet_recipient_card _ _ _ _ _ (by dsimp [q2]; omega) hsub, hf.2.2, hc]
      omega
    · rw [reparentSet_other_fibre _ 2 _ _ _ _ (by dsimp [q2]; omega)
        (by dsimp [q2]; omega) hsub, hf.2.1]

theorem afterFirst0_anchor (t : ℕ) :
    (anchor0 t).C ∈ leafLabels (q0 t) ∧ (anchor0 t).Z ∈ leafLabels (q0 t) ∧
    afterFirst0 t (anchor0 t).C = (anchor0 t).B ∧
    afterFirst0 t (anchor0 t).Z = (anchor0 t).B ∧ (anchor0 t).C ≠ (anchor0 t).Z := by
  by_cases ht : t = 0
  · subst t
    decide
  · have htpos : 0 < t := by omega
    have hC := (afterFirst0_donor t htpos (anchor0 t).C).2 (by dsimp [anchor0]; omega)
    have hZ := (afterFirst0_donor t htpos (anchor0 t).Z).2 (by dsimp [anchor0]; omega)
    refine ⟨?_, ?_, hC, hZ, ?_⟩
    all_goals simp only [anchor0, leafLabels, q0, Finset.mem_Icc]
    all_goals omega

theorem afterFirst1_anchor (t : ℕ) :
    (anchor1 t).C ∈ leafLabels (q1 t) ∧ (anchor1 t).Z ∈ leafLabels (q1 t) ∧
    afterFirst1 t (anchor1 t).C = (anchor1 t).B ∧
    afterFirst1 t (anchor1 t).Z = (anchor1 t).B ∧ (anchor1 t).C ≠ (anchor1 t).Z := by
  simp (disch := omega) [afterFirst1, moveTwo, baseParent1, leafLabels, anchor1, q1, Finset.mem_Icc]
  all_goals omega
theorem afterFirst2_anchor (t : ℕ) :
    (anchor2 t).C ∈ leafLabels (q2 t) ∧ (anchor2 t).Z ∈ leafLabels (q2 t) ∧
    afterFirst2 t (anchor2 t).C = (anchor2 t).B ∧
    afterFirst2 t (anchor2 t).Z = (anchor2 t).B ∧ (anchor2 t).C ≠ (anchor2 t).Z := by
  have hC := (afterFirst2_donor t (anchor2 t).C).2 (by dsimp [anchor2]; omega)
  have hZ := (afterFirst2_donor t (anchor2 t).Z).2 (by dsimp [anchor2]; omega)
  refine ⟨?_, ?_, hC, hZ, ?_⟩
  all_goals simp only [anchor2, leafLabels, q2, Finset.mem_Icc]
  all_goals omega

theorem alternateAfterFirst_anchor (t : ℕ) :
    (alternateAnchor t).C ∈ leafLabels (q2 t) ∧ (alternateAnchor t).Z ∈ leafLabels (q2 t) ∧
    alternateAfterFirst t (alternateAnchor t).C = (alternateAnchor t).B ∧
    alternateAfterFirst t (alternateAnchor t).Z = (alternateAnchor t).B ∧
    (alternateAnchor t).C ≠ (alternateAnchor t).Z := by
  simp (disch := omega) [alternateAfterFirst, moveTwo, alternateBaseParent, leafLabels,
    alternateAnchor, q2, Finset.mem_Icc]
  all_goals omega

theorem moveSelectedPairs_anchor (Q S donor recipient : ℕ) (parent : ℕ → ℕ)
    (a : Anchor) (starts : Finset ℕ)
    (hsub : starts ⊆ eligiblePairStarts Q S donor parent a) :
    moveSelectedPairs parent S recipient starts a.C = parent a.C ∧
    moveSelectedPairs parent S recipient starts a.Z = parent a.Z := by
  have havoid := eligible_pairs_avoid_anchor _ _ _ _ _ _ hsub
  rw [moveSelectedPairs_eq_reparentSet _ _ _ _ _ _ _ hsub]
  simp only [reparentSet, havoid.1, havoid.2, if_false, and_self]

theorem afterPairs0_anchor (t v : ℕ) :
    afterPairs0 t v (anchor0 t).C = (anchor0 t).B ∧
    afterPairs0 t v (anchor0 t).Z = (anchor0 t).B := by
  have hm := moveSelectedPairs_anchor _ _ _ (q0 t-4) _ _ _ (selected0_subset t v)
  have ha := afterFirst0_anchor t
  simpa only [afterPairs0, ha.2.2.1, ha.2.2.2.1] using hm
theorem afterPairs1_anchor (t u : ℕ) :
    afterPairs1 t u (anchor1 t).C = (anchor1 t).B ∧
    afterPairs1 t u (anchor1 t).Z = (anchor1 t).B := by
  have hm := moveSelectedPairs_anchor _ _ _ (q1 t-3) _ _ _ (selected1_subset t u)
  have ha := afterFirst1_anchor t
  simpa only [afterPairs1, ha.2.2.1, ha.2.2.2.1] using hm
theorem afterPairs2_anchor (t v : ℕ) :
    afterPairs2 t v (anchor2 t).C = (anchor2 t).B ∧
    afterPairs2 t v (anchor2 t).Z = (anchor2 t).B := by
  have hm := moveSelectedPairs_anchor _ _ _ (q2 t-3) _ _ _ (selected2_subset t v)
  have ha := afterFirst2_anchor t
  simpa only [afterPairs2, ha.2.2.1, ha.2.2.2.1] using hm

theorem afterPairs0_avoids_C (t v x : ℕ) : afterPairs0 t v x ≠ (anchor0 t).C := by
  simp only [afterPairs0, moveSelectedPairs, afterFirst0, ite_apply, moveTwo, baseParent0, anchor0, q0]
  simp only [ne_eq, ite_eq_iff]
  omega
theorem afterPairs1_avoids_C (t u x : ℕ) : afterPairs1 t u x ≠ (anchor1 t).C := by
  unfold afterPairs1
  dsimp only [q1]
  dsimp only [moveSelectedPairs, afterFirst1, moveTwo, baseParent1, anchor1, q1]
  simp only [ne_eq, ite_eq_iff]
  omega
theorem afterPairs2_avoids_C (t v x : ℕ) : afterPairs2 t v x ≠ (anchor2 t).C := by
  unfold afterPairs2
  dsimp only [q2]
  dsimp only [moveSelectedPairs, afterFirst2, moveTwo, baseParent2, anchor2, q2]
  simp only [ne_eq, ite_eq_iff]
  omega
theorem alternateAfterFirst_avoids_C (t x : ℕ) :
    alternateAfterFirst t x ≠ (alternateAnchor t).C := by
  simp only [alternateAfterFirst, moveTwo, alternateBaseParent, alternateAnchor, q2]
  simp only [ne_eq, ite_eq_iff]
  omega

theorem splitParent_donor_fibre (Q : ℕ) (parent : ℕ → ℕ) (a : Anchor)
    (hAB : a.A ≠ a.B) (hCB : a.C ≠ a.B) :
    fibre Q (splitParent parent a) a.B = ((fibre Q parent a.B).erase a.C).erase a.Z := by
  ext x
  simp only [fibre]
  simp only [Finset.mem_filter]
  simp only [ Finset.mem_filter, splitParent, Finset.mem_erase, Finset.mem_filter]
  by_cases hxC : x = a.C <;> by_cases hxZ : x = a.Z <;>
    simp_all [hAB, hCB]

theorem splitParent_donor_card (Q : ℕ) (parent : ℕ → ℕ) (a : Anchor)
    (hAB : a.A ≠ a.B) (hCB : a.C ≠ a.B) (hCZ : a.C ≠ a.Z)
    (hC : a.C ∈ leafLabels Q) (hZ : a.Z ∈ leafLabels Q)
    (hpC : parent a.C = a.B) (hpZ : parent a.Z = a.B) :
    (fibre Q (splitParent parent a) a.B).card = (fibre Q parent a.B).card-2 := by
  have hCm : a.C ∈ fibre Q parent a.B := Finset.mem_filter.mpr ⟨hC,hpC⟩
  have hZm : a.Z ∈ (fibre Q parent a.B).erase a.C := by
    exact Finset.mem_erase.mpr ⟨Ne.symm hCZ, Finset.mem_filter.mpr ⟨hZ,hpZ⟩⟩
  rw [splitParent_donor_fibre _ _ _ hAB hCB,
    Finset.card_erase_of_mem hZm, Finset.card_erase_of_mem hCm]
  omega

theorem splitParent_C_fibre (Q : ℕ) (parent : ℕ → ℕ) (a : Anchor)
    (hAC : a.A ≠ a.C) (hCZ : a.C ≠ a.Z) (hZ : a.Z ∈ leafLabels Q)
    (havoid : ∀ x ∈ leafLabels Q, parent x ≠ a.C) :
    fibre Q (splitParent parent a) a.C = {a.Z} := by
  ext x
  simp only [fibre]
  simp only [Finset.mem_filter]
  simp only [ Finset.mem_filter, splitParent, Finset.mem_singleton, Finset.mem_filter]
  by_cases hxC : x = a.C
  · subst x
    simp [hAC, hCZ]
  · by_cases hxZ : x = a.Z
    · subst x
      simp [Ne.symm hCZ, hZ]
    · simp only [hxC, hxZ, if_false]
      constructor
      · rintro ⟨hx,hp⟩
        exact False.elim (havoid x hx hp)
      · intro hx
        exact hx.elim

theorem splitParent_other_fibre (Q p : ℕ) (parent : ℕ → ℕ) (a : Anchor)
    (hpA : p ≠ a.A) (hpC : p ≠ a.C) (hpB : p ≠ a.B)
    (hparentC : parent a.C = a.B) (hparentZ : parent a.Z = a.B) :
    fibre Q (splitParent parent a) p = fibre Q parent p := by
  ext x
  simp only [fibre]
  simp only [Finset.mem_filter]
  simp only [ Finset.mem_filter, splitParent]
  by_cases hxC : x = a.C
  · subst x
    simp [Ne.symm hpA, hparentC, Ne.symm hpB]
  · by_cases hxZ : x = a.Z
    · subst x
      simp [hxC, Ne.symm hpC, hparentZ, Ne.symm hpB]
    · simp [hxC,hxZ]

theorem finalParent0_distinguished_counts (t u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hq : q u v = q0 t) (hcase : 0 < t ∨ 2 ≤ u) :
    (fibre (q0 t) (finalParent0 t v) 5).card = 2*u ∧
    (fibre (q0 t) (finalParent0 t v) (q0 t-4)).card = 2*v ∧
    (fibre (q0 t) (finalParent0 t v) (q0 t-2)).card = 3 ∧
    (fibre (q0 t) (finalParent0 t v) (anchor0 t).C).card = 1 := by
  have hf := afterPairs0_counts t u v hu hv hq hcase
  have ha := afterFirst0_anchor t
  have hp := afterPairs0_anchor t v
  unfold finalParent0
  constructor
  · change (fibre (q0 t) (splitParent (afterPairs0 t v) (anchor0 t)) (anchor0 t).B).card = _
    rw [splitParent_donor_card _ _ _ (by dsimp [anchor0]; omega)
      (by dsimp [anchor0]; omega) ha.2.2.2.2 ha.1 ha.2.1 hp.1 hp.2]
    change (fibre (q0 t) (afterPairs0 t v) 5).card-2 = _
    rw [hf.1]; omega
  · constructor
    · rw [splitParent_other_fibre _ _ _ _ (by dsimp [anchor0,q0]; omega)
        (by dsimp [anchor0,q0]; omega) (by dsimp [anchor0,q0]; omega) hp.1 hp.2, hf.2.1]
    · constructor
      · rw [splitParent_other_fibre _ _ _ _ (by dsimp [anchor0,q0]; omega)
          (by dsimp [anchor0,q0]; omega) (by dsimp [anchor0,q0]; omega) hp.1 hp.2, hf.2.2]
      · rw [splitParent_C_fibre _ _ _ (by dsimp [anchor0]; omega)
          ha.2.2.2.2 ha.2.1 (by intro x hx; exact afterPairs0_avoids_C t v x)]
        simp

theorem finalParent1_distinguished_counts (t u v : ℕ) (hu : 0 < u) (hv : 0 < v)
    (hq : q u v = q1 t) :
    (fibre (q1 t) (finalParent1 t u) (q1 t-3)).card = 2*u ∧
    (fibre (q1 t) (finalParent1 t u) 4).card = 2*v ∧
    (fibre (q1 t) (finalParent1 t u) (q1 t-2)).card = 3 ∧
    (fibre (q1 t) (finalParent1 t u) (anchor1 t).C).card = 1 := by
  have hf := afterPairs1_counts t u v hu hv hq
  have ha := afterFirst1_anchor t
  have hp := afterPairs1_anchor t u
  unfold finalParent1
  constructor
  · have hb : q1 t-3 = (anchor1 t).B := by dsimp [q1,anchor1]; omega
    rw [hb, splitParent_donor_card _ _ _ (by dsimp [anchor1]; omega)
      (by dsimp [anchor1]; omega) ha.2.2.2.2 ha.1 ha.2.1 hp.1 hp.2, ← hb, hf.1]
    omega
  · constructor
    · rw [splitParent_other_fibre _ _ _ _ (by dsimp [anchor1,q1]; omega)
        (by dsimp [anchor1,q1]; omega) (by dsimp [anchor1,q1]; omega) hp.1 hp.2, hf.2.1]
    · constructor
      · rw [splitParent_other_fibre _ _ _ _ (by dsimp [anchor1,q1]; omega)
          (by dsimp [anchor1,q1]; omega) (by dsimp [anchor1,q1]; omega) hp.1 hp.2, hf.2.2]
      · rw [splitParent_C_fibre _ _ _ (by dsimp [anchor1]; omega)
          ha.2.2.2.2 ha.2.1 (by intro x hx; exact afterPairs1_avoids_C t u x)]
        simp

theorem finalParent2_distinguished_counts (t u v : ℕ) (hu : 2 ≤ u) (hv : 0 < v)
    (hq : q u v = q2 t) :
    (fibre (q2 t) (finalParent2 t v) 2).card = 2*u ∧
    (fibre (q2 t) (finalParent2 t v) (q2 t-3)).card = 2*v ∧
    (fibre (q2 t) (finalParent2 t v) (q2 t-4)).card = 3 ∧
    (fibre (q2 t) (finalParent2 t v) (anchor2 t).C).card = 1 := by
  have hf := afterPairs2_counts t u v hu hv hq
  have ha := afterFirst2_anchor t
  have hp := afterPairs2_anchor t v
  unfold finalParent2
  constructor
  · change (fibre (q2 t) (splitParent (afterPairs2 t v) (anchor2 t)) (anchor2 t).B).card = _
    rw [splitParent_donor_card _ _ _ (by dsimp [anchor2]; omega)
      (by dsimp [anchor2]; omega) ha.2.2.2.2 ha.1 ha.2.1 hp.1 hp.2]
    change (fibre (q2 t) (afterPairs2 t v) 2).card-2 = _
    rw [hf.1]; omega
  · constructor
    · rw [splitParent_other_fibre _ _ _ _ (by dsimp [anchor2,q2]; omega)
        (by dsimp [anchor2,q2]; omega) (by dsimp [anchor2,q2]; omega) hp.1 hp.2, hf.2.1]
    · constructor
      · rw [splitParent_other_fibre _ _ _ _ (by dsimp [anchor2,q2]; omega)
          (by dsimp [anchor2,q2]; omega) (by dsimp [anchor2,q2]; omega) hp.1 hp.2, hf.2.2]
      · rw [splitParent_C_fibre _ _ _ (by dsimp [anchor2]; omega)
          ha.2.2.2.2 ha.2.1 (by intro x hx; exact afterPairs2_avoids_C t v x)]
        simp

theorem alternateFinalParent_distinguished_counts (t v : ℕ) (hv : 0 < v)
    (hq : q 1 v = q2 t) :
    (fibre (q2 t) (alternateFinalParent t) (q2 t-3)).card = 2 ∧
    (fibre (q2 t) (alternateFinalParent t) 4).card = 2*v ∧
    (fibre (q2 t) (alternateFinalParent t) (q2 t-2)).card = 3 ∧
    (fibre (q2 t) (alternateFinalParent t) (alternateAnchor t).C).card = 1 := by
  have hf := alternateAfterFirst_counts t
  have ha := alternateAfterFirst_anchor t
  unfold alternateFinalParent
  constructor
  · have hb : q2 t-3 = (alternateAnchor t).B := by dsimp [q2,alternateAnchor]; omega
    rw [hb, splitParent_donor_card _ _ _ (by dsimp [alternateAnchor]; omega)
      (by dsimp [alternateAnchor]; omega) ha.2.2.2.2 ha.1 ha.2.1 ha.2.2.1 ha.2.2.2.1,
      ← hb, hf.2.2]
  · constructor
    · rw [splitParent_other_fibre _ _ _ _ (by dsimp [alternateAnchor,q2]; omega)
        (by dsimp [alternateAnchor,q2]; omega) (by dsimp [alternateAnchor,q2]; omega)
        ha.2.2.1 ha.2.2.2.1, hf.1]
      dsimp [q,q2] at hq
      omega
    · constructor
      · rw [splitParent_other_fibre _ _ _ _ (by dsimp [alternateAnchor,q2]; omega)
          (by dsimp [alternateAnchor,q2]; omega) (by dsimp [alternateAnchor,q2]; omega)
          ha.2.2.1 ha.2.2.2.1, hf.2.1]
      · rw [splitParent_C_fibre _ _ _ (by dsimp [alternateAnchor]; omega)
          ha.2.2.2.2 ha.2.1 (by intro x hx; exact alternateAfterFirst_avoids_C t x)]
        simp

/-! The four ordinary one-leaf stars are unchanged by both transfer stages
and the anchor split. These are exact parent-fibre statements, not a premise
that the constructed graph already has the desired profile. -/
theorem afterFirst0_other_fibre (t p : ℕ) (hpB : p ≠ 5)
    (hpQ : p ≠ q0 t-2) :
    fibre (q0 t) (afterFirst0 t) p = fibre (q0 t) (baseParent0 t) p := by
  by_cases ht : t = 0
  · subst t
    rcases firstPair0_zero_available with ⟨hx,hy,hpx,hpy,hxy⟩
    have hs := pair_subset_fibre _ _ _ _ _ hx hy hpx hpy
    simp only [afterFirst0, if_pos rfl, if_true, moveTwo_eq_reparentSet]
    exact reparentSet_other_fibre _ 5 _ _ _ _ hpQ hpB hs
  · have ht' : 0 < t := by omega
    rcases firstPair0_available t ht' with ⟨hx,hy,hpx,hpy,hxy⟩
    have hs := pair_subset_fibre _ _ _ _ _ hx hy hpx hpy
    simp only [afterFirst0, ht, if_false, moveTwo_eq_reparentSet]
    exact reparentSet_other_fibre _ 5 _ _ _ _ hpQ hpB hs

theorem afterFirst1_other_fibre (t p : ℕ) (hpP : p ≠ 4)
    (hpQ : p ≠ q1 t-2) :
    fibre (q1 t) (afterFirst1 t) p = fibre (q1 t) (baseParent1 t) p := by
  rcases firstPair1_available t with ⟨hx,hy,hpx,hpy,hxy⟩
  have hs := pair_subset_fibre _ _ _ _ _ hx hy hpx hpy
  simp only [afterFirst1, moveTwo_eq_reparentSet]
  exact reparentSet_other_fibre _ 4 _ _ _ _ hpQ hpP hs

theorem afterFirst2_other_fibre (t p : ℕ) (hpB : p ≠ 2)
    (hpQ : p ≠ q2 t-4) :
    fibre (q2 t) (afterFirst2 t) p = fibre (q2 t) (baseParent2 t) p := by
  rcases firstPair2_available t with ⟨hx,hy,hpx,hpy,hxy⟩
  have hs := pair_subset_fibre _ _ _ _ _ hx hy hpx hpy
  simp only [afterFirst2, moveTwo_eq_reparentSet]
  exact reparentSet_other_fibre _ 2 _ _ _ _ hpQ hpB hs

theorem alternateAfterFirst_other_fibre (t p : ℕ) (hpP : p ≠ 4)
    (hpQ : p ≠ q2 t-2) :
    fibre (q2 t) (alternateAfterFirst t) p = fibre (q2 t) (alternateBaseParent t) p := by
  rcases alternateFirstPair_available t with ⟨hx,hy,hpx,hpy,hxy⟩
  have hs := pair_subset_fibre _ _ _ _ _ hx hy hpx hpy
  simp only [alternateAfterFirst, moveTwo_eq_reparentSet]
  exact reparentSet_other_fibre _ 4 _ _ _ _ hpQ hpP hs

theorem afterPairs0_other_fibre (t v p : ℕ) (hpB : p ≠ 5)
    (hpP : p ≠ q0 t-4) (hpQ : p ≠ q0 t-2) :
    fibre (q0 t) (afterPairs0 t v) p = fibre (q0 t) (baseParent0 t) p := by
  have hs := selected0_subset t v
  have hsub := eligible_pairs_subset_fibre _ _ _ _ _ _ hs
  simp only [afterPairs0]
  rw [moveSelectedPairs_eq_reparentSet _ _ _ _ _ _ _ hs,
    reparentSet_other_fibre _ 5 _ _ _ _ hpP hpB hsub,
    afterFirst0_other_fibre t p hpB hpQ]

theorem afterPairs1_other_fibre (t u p : ℕ) (hpB : p ≠ q1 t-3)
    (hpP : p ≠ 4) (hpQ : p ≠ q1 t-2) :
    fibre (q1 t) (afterPairs1 t u) p = fibre (q1 t) (baseParent1 t) p := by
  have hs := selected1_subset t u
  have hsub := eligible_pairs_subset_fibre _ _ _ _ _ _ hs
  simp only [afterPairs1]
  rw [moveSelectedPairs_eq_reparentSet _ _ _ _ _ _ _ hs,
    reparentSet_other_fibre _ 4 _ _ _ _ hpB hpP hsub,
    afterFirst1_other_fibre t p hpP hpQ]

theorem afterPairs2_other_fibre (t v p : ℕ) (hpB : p ≠ 2)
    (hpP : p ≠ q2 t-3) (hpQ : p ≠ q2 t-4) :
    fibre (q2 t) (afterPairs2 t v) p = fibre (q2 t) (baseParent2 t) p := by
  have hs := selected2_subset t v
  have hsub := eligible_pairs_subset_fibre _ _ _ _ _ _ hs
  simp only [afterPairs2]
  rw [moveSelectedPairs_eq_reparentSet _ _ _ _ _ _ _ hs,
    reparentSet_other_fibre _ 2 _ _ _ _ hpP hpB hsub,
    afterFirst2_other_fibre t p hpB hpQ]

theorem finalParent0_ordinary_counts (t v p : ℕ)
    (hp : p = 2 ∨ p = 3 ∨ p = 4 ∨ p = q0 t-3) :
    (fibre (q0 t) (finalParent0 t v) p).card = 1 := by
  have ha := afterPairs0_anchor t v
  unfold finalParent0
  rw [splitParent_other_fibre (q0 t) p (afterPairs0 t v) (anchor0 t)
    (by dsimp [anchor0,q0] at hp ⊢; omega)
    (by dsimp [anchor0,q0] at hp ⊢; omega) (by dsimp [anchor0,q0] at hp ⊢; omega)
    ha.1 ha.2,
    afterPairs0_other_fibre t v p (by dsimp [q0] at hp; omega)
      (by dsimp [q0] at hp ⊢; omega) (by dsimp [q0] at hp ⊢; omega)]
  have h := base0_nondonor_card t p (by dsimp [q0] at hp; omega)
  dsimp [q0] at hp
  split_ifs at h <;> omega

theorem finalParent1_ordinary_counts (t u p : ℕ)
    (hp : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = q1 t-4) :
    (fibre (q1 t) (finalParent1 t u) p).card = 1 := by
  have ha := afterPairs1_anchor t u
  unfold finalParent1
  rw [splitParent_other_fibre (q1 t) p (afterPairs1 t u) (anchor1 t)
    (by dsimp [anchor1,q1] at hp ⊢; omega)
    (by dsimp [anchor1,q1] at hp ⊢; omega) (by dsimp [anchor1,q1] at hp ⊢; omega)
    ha.1 ha.2,
    afterPairs1_other_fibre t u p (by dsimp [q1] at hp ⊢; omega)
      (by dsimp [q1] at hp; omega) (by dsimp [q1] at hp ⊢; omega)]
  have h := base1_nondonor_card t p (by dsimp [q1] at hp; omega)
  dsimp [q1] at hp
  split_ifs at h <;> omega

theorem finalParent2_ordinary_counts (t v p : ℕ)
    (hp : p = 3 ∨ p = 4 ∨ p = 5 ∨ p = q2 t-2) :
    (fibre (q2 t) (finalParent2 t v) p).card = 1 := by
  have ha := afterPairs2_anchor t v
  unfold finalParent2
  rw [splitParent_other_fibre (q2 t) p (afterPairs2 t v) (anchor2 t)
    (by dsimp [anchor2,q2] at hp ⊢; omega)
    (by dsimp [anchor2,q2] at hp ⊢; omega) (by dsimp [anchor2,q2] at hp ⊢; omega)
    ha.1 ha.2,
    afterPairs2_other_fibre t v p (by dsimp [q2] at hp; omega)
      (by dsimp [q2] at hp ⊢; omega) (by dsimp [q2] at hp ⊢; omega)]
  have h := base2_nondonor_card t p (by dsimp [q2] at hp; omega)
  dsimp [q2] at hp
  split_ifs at h <;> omega

theorem alternateFinalParent_ordinary_counts (t p : ℕ)
    (hp : p = 1 ∨ p = 3 ∨ p = 5 ∨ p = q2 t-4) :
    (fibre (q2 t) (alternateFinalParent t) p).card = 1 := by
  have ha := alternateAfterFirst_anchor t
  unfold alternateFinalParent
  rw [splitParent_other_fibre (q2 t) p (alternateAfterFirst t) (alternateAnchor t)
    (by dsimp [alternateAnchor,q2] at hp ⊢; omega)
    (by dsimp [alternateAnchor,q2] at hp ⊢; omega)
    (by dsimp [alternateAnchor,q2] at hp ⊢; omega) ha.2.2.1 ha.2.2.2.1,
    alternateAfterFirst_other_fibre t p (by dsimp [q2] at hp; omega)
      (by dsimp [q2] at hp ⊢; omega)]
  have h := alternateBase_nondonor_card t p (by dsimp [q2] at hp; omega)
  dsimp [q2] at hp
  split_ifs at h <;> omega

/-! A is a depth-one label. Its fibre below contains only the promoted
internal vertex C; C must be excluded from the final pendant partition. -/
theorem splitParent_A_fibre (Q : ℕ) (parent : ℕ → ℕ) (a : Anchor)
    (hCA : a.C ≠ a.A) (hCZ : a.C ≠ a.Z) (hC : a.C ∈ leafLabels Q)
    (havoid : ∀ x ∈ leafLabels Q, parent x ≠ a.A) :
    fibre Q (splitParent parent a) a.A = {a.C} := by
  ext x
  simp only [fibre]
  simp only [Finset.mem_filter]
  simp only [ Finset.mem_filter, splitParent, Finset.mem_singleton, Finset.mem_filter]
  by_cases hxC : x = a.C
  · subst x
    simp [hC]
  · by_cases hxZ : x = a.Z
    · subst x
      simp [Ne.symm hCZ, hCA]
    · simp only [hxC, hxZ, if_false]
      constructor
      · rintro ⟨hx,hp⟩
        exact False.elim (havoid x hx hp)
      · intro hx
        exact hx.elim

theorem finalParent0_A_fibre (t v : ℕ) :
    fibre (q0 t) (finalParent0 t v) (anchor0 t).A = {(anchor0 t).C} := by
  unfold finalParent0
  apply splitParent_A_fibre _ _ _ (by dsimp [anchor0]; omega)
    (afterFirst0_anchor t).2.2.2.2 (afterFirst0_anchor t).1
  intro x hx
  simp only [afterPairs0, moveSelectedPairs, afterFirst0, ite_apply, moveTwo, baseParent0, anchor0, q0]
  simp only [ne_eq, ite_eq_iff]
  omega

theorem finalParent1_A_fibre (t u : ℕ) :
    fibre (q1 t) (finalParent1 t u) (anchor1 t).A = {(anchor1 t).C} := by
  unfold finalParent1
  apply splitParent_A_fibre _ _ _ (by dsimp [anchor1]; omega)
    (afterFirst1_anchor t).2.2.2.2 (afterFirst1_anchor t).1
  intro x hx
  unfold afterPairs1
  dsimp only [q1]
  dsimp only [moveSelectedPairs, afterFirst1, moveTwo, baseParent1, anchor1, q1]
  simp only [ne_eq, ite_eq_iff]
  omega

theorem finalParent2_A_fibre (t v : ℕ) :
    fibre (q2 t) (finalParent2 t v) (anchor2 t).A = {(anchor2 t).C} := by
  unfold finalParent2
  apply splitParent_A_fibre _ _ _ (by dsimp [anchor2]; omega)
    (afterFirst2_anchor t).2.2.2.2 (afterFirst2_anchor t).1
  intro x hx
  unfold afterPairs2
  dsimp only [q2]
  dsimp only [moveSelectedPairs, afterFirst2, moveTwo, baseParent2, anchor2, q2]
  simp only [ne_eq, ite_eq_iff]
  omega

theorem alternateFinalParent_A_fibre (t : ℕ) :
    fibre (q2 t) (alternateFinalParent t) (alternateAnchor t).A = {(alternateAnchor t).C} := by
  unfold alternateFinalParent
  apply splitParent_A_fibre _ _ _ (by dsimp [alternateAnchor]; omega)
    (alternateAfterFirst_anchor t).2.2.2.2 (alternateAfterFirst_anchor t).1
  intro x hx
  simp only [alternateAfterFirst, moveTwo, alternateBaseParent, alternateAnchor, q2]
  simp only [ne_eq, ite_eq_iff]
  omega

end Partials.Graceful.Symbolic
