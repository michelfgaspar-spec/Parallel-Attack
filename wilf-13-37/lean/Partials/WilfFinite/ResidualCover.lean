import Partials.WilfFinite.ResidualLabeling

/-! A genuine finite, locally indexed contradiction object for Cover/Pack.
Acceptance contains every required child, never an assumed universal Wilf
coverage field. Local semantic retention is separately proved/instantiated;
the concrete residual enumerator adapter remains an explicit duty. UNCOMPILED. -/
namespace Partials.WilfFinite.Forest
universe u v
open Partials.WilfStructural.Packing

inductive ResidualStage
  | depth | profile | rectangle | profileRefinement | allocation
  | allocationRefinement | tuple | ranked | labeling | packing
  deriving DecidableEq

/-- Stages of the historical nested loops. Repeated refinement, labels and
packing are local recursions; stationary refinement passes to its next stage. -/
def StageEdge : ResidualStage → ResidualStage → Prop
  | .depth,.profile => True
  | .profile,.rectangle => True
  | .rectangle,.profileRefinement => True
  | .profileRefinement,.profileRefinement => True
  | .profileRefinement,.allocation => True
  | .allocation,.allocation => True
  | .allocation,.allocationRefinement => True
  | .allocationRefinement,.allocationRefinement => True
  | .allocationRefinement,.tuple => True
  | .tuple,.ranked => True
  | .ranked,.labeling => True
  | .labeling,.labeling => True
  | .labeling,.packing => True
  | .packing,.packing => True
  | _,_ => False

structure LocalDomainModel (X State : Type*) where
  region : State → X → Prop
  bad : X → Prop
  children : State → List State
  rank : State → ℕ
  child_decrease : ∀ s b, b ∈ children s → rank b < rank s

/-- One-step witness retention, to be established for each actual filter,
composition choice, quota branch, and split. It is NOT a certificate field.
The model adapter must not instantiate it by the desired universal conclusion. -/
def LocalRetention {X State : Type*} (M : LocalDomainModel X State) : Prop :=
  ∀ s x, M.region s x → M.bad x →
    ∃ b ∈ M.children s, M.region b x

mutual
  inductive ClosedStage {X : Type u} {State : Type v} (M : LocalDomainModel X State) : State → Prop
    | contradiction {s : State}
        (reason : ∀ x, M.region s x → ¬ M.bad x) : ClosedStage M s
    | expanded {s : State}
        (nonempty : M.children s ≠ [])
        (required : AllStagesClosed M (M.children s)) : ClosedStage M s

  inductive AllStagesClosed {X : Type u} {State : Type v} (M : LocalDomainModel X State) :
      List State → Prop
    | nil : AllStagesClosed M []
    | cons {s : State} {states : List State}
        (here : ClosedStage M s) (following : AllStagesClosed M states) :
        AllStagesClosed M (s::states)
end

theorem all_closed_member {X State : Type*} (M : LocalDomainModel X State)
    (states : List State) (h : AllStagesClosed M states) (s : State)
    (hs : s ∈ states) : ClosedStage M s := by
  induction states with
  | nil => simp at hs
  | cons head tail ih =>
    cases h with
    | cons here following =>
      rcases List.mem_cons.mp hs with hhead | htail
      · simpa [hhead] using here
      · exact ih following htail

/-- All local expansion children must be supplied. The rank induction uses
only that indexed finite object and separately established one-step retention. -/
theorem closed_stage_sound {X State : Type*} (M : LocalDomainModel X State)
    (retain : LocalRetention M) (s : State) (tree : ClosedStage M s) :
    ∀ x, M.region s x → ¬ M.bad x := by
  have sound : ∀ n : ℕ, ∀ s, M.rank s=n → ClosedStage M s →
      ∀ x, M.region s x → ¬ M.bad x := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro s hn hs x hx hbad
      cases hs with
      | contradiction reason => exact reason x hx hbad
      | expanded nonempty required =>
        obtain ⟨b,hb,hbx⟩ := retain s x hx hbad
        have hclosed := all_closed_member M (M.children s) required b hb
        exact ih (M.rank b) (by simpa [hn] using M.child_decrease s b hb)
          b rfl hclosed x hbx hbad
  exact sound (M.rank s) s rfl tree

theorem retained_counterexample_cannot_close {S X State : Type*}
    (M : LocalDomainModel X State) (root : State) (retain : LocalRetention M)
    (violation : S → Prop)
    (model : ∀ s, violation s → ∃ x, M.region root x ∧ M.bad x)
    (tree : ClosedStage M root) : ∀ s, ¬ violation s := by
  intro s hs
  obtain ⟨x,hroot,hbad⟩ := model s hs
  exact closed_stage_sound M retain root tree x hroot hbad

def leftBox {s : ℕ} (B : Box s) (i : Fin s) (z : ℤ) : Box s :=
  ⟨B.lower,Function.update B.upper i z⟩

def rightBox {s : ℕ} (B : Box s) (i : Fin s) (z : ℤ) : Box s :=
  ⟨Function.update B.lower i (z+1),B.upper⟩

theorem box_split_covers {s : ℕ} (B : Box s) (i : Fin s) (z : ℤ)
    (x : Fin s → ℤ) (hx : B.Contains x) :
    (leftBox B i z).Contains x ∨ (rightBox B i z).Contains x := by
  by_cases hleft : x i ≤ z
  · left
    intro j
    by_cases hji : j=i
    · subst j; simpa [leftBox] using And.intro (hx i).1 hleft
    · simpa [leftBox,Function.update_of_ne hji] using hx j
  · right
    intro j
    by_cases hji : j=i
    · subst j
      have hr : z+1 ≤ x i := by omega
      simpa [rightBox] using And.intro hr (hx i).2
    · simpa [rightBox,Function.update_of_ne hji] using hx j

theorem box_split_disjoint {s : ℕ} (B : Box s) (i : Fin s) (z : ℤ)
    (x : Fin s → ℤ) :
    ¬ ((leftBox B i z).Contains x ∧ (rightBox B i z).Contains x) := by
  intro h
  have hl := (h.1 i).2
  have hr := (h.2 i).1
  simp only [leftBox,rightBox,Function.update_self] at hl hr
  omega

theorem midpoint_children_shorten (L U : ℤ) (h : L < U) :
    let z := (L+U)/2
    L ≤ z ∧ z < U ∧ z-L < U-L ∧ U-(z+1) < U-L := by
  have hm := midpoint_strict L U h
  dsimp
  omega

/-- A passing singleton, a resource stop and a missing child have no constructor
in ClosedStage. In particular, no 'CLOSED' assertion bypasses a contradiction
or a complete indexed expansion. Empty zero-coordinate boxes are not leaves
of contradiction unless an independent necessary test actually excludes them. -/
inductive StopReason
  | singleton | resource | missingChild | malformed | unfinishedShard
  deriving DecidableEq

def Unresolved (_ : StopReason) : Prop := True

/-- Parameter preservation required by the historical Pack recursion. Only box
and its consequent bounds change; q,h,K,s,e,delta,m,rho retain their identities. -/
structure PackParameters where
  q : ℕ
  h : Allocation
  K : ℕ
  s : ℕ
  e : ℤ
  delta : ℤ
  m : ℤ
  rho : ℤ

def SamePackParameters (a b : PackParameters) : Prop := a=b

theorem split_preserves_parameters (p : PackParameters) : SamePackParameters p p := rfl

/-- Exact concrete adapters still needed for pseudocode Cover(n): domains must
be the complete weighted profiles/rectangle/compositions/tuples/labels, every
discard a named applicable contradiction, and both pack children required.
This proposition is deliberately not inhabited by historical aggregate counts. -/
def ResidualControlCorrespondence {X State : Type*} (M : LocalDomainModel X State)
    (stage : State → ResidualStage) : Prop :=
  (∀ a b, b ∈ M.children a → StageEdge (stage a) (stage b)) ∧ LocalRetention M

end Partials.WilfFinite.Forest
