import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Fin.VecNotation
import Partials.Parity.Model

/-! R7 blind literal original27-vertex two-fragment architecture.
Finite count/legality proof text has not been evaluated. All menus and both
arms remain present independently of the chosen complete policy. -/
namespace Partials.Parity.Tie

inductive Fragment | a | b deriving DecidableEq

instance fragmentFintype : Fintype Fragment where
  elems := {.a, .b}
  complete := by intro x; cases x <;> simp
inductive Port | iL | iR | oL | oR deriving DecidableEq

instance portFintype : Fintype Port where
  elems := {.iL, .iR, .oL, .oR}
  complete := by intro x; cases x <;> simp
inductive Menu | a03 | a11 | a12 | b02 | b11 deriving DecidableEq

instance menuFintype : Fintype Menu where
  elems := {.a03, .a11, .a12, .b02, .b11}
  complete := by intro x; cases x <;> simp

def Menu.fragment : Menu → Fragment
  | .a03 | .a11 | .a12 => .a
  | _ => .b
def Menu.hub : Menu → Fin 2
  | .a03 | .b02 => 0
  | _ => 1
def Menu.q : Menu → ℕ
  | .a03 => 3
  | .a11 | .b11 => 1
  | .a12 | .b02 => 2

inductive Vertex
  | port (f : Fragment) (p : Port)
  | hub (f : Fragment) (h : Fin 2)
  | menu (m : Menu)
  | rightArm (m : Menu)
  | leftArm (m : Menu)
  deriving DecidableEq, Fintype

def priority : Vertex → ℕ
  | .rightArm m => 4 * m.q
  | .leftArm m => 4 * m.q + 1
  | _ => 0
def evenOwned : Vertex → Bool
  | .menu _ => false
  | _ => true

def edge (feedback : Bool) : Vertex → Vertex → Prop
  | .port f .iL, v => v = .hub f 0
  | .port f .iR, v => v = .hub f 1
  | .port f p, v => if feedback then
      match f,p with
      | .a,.oR => v = .port .b .iL
      | .b,.oL => v = .port .a .iR
      | .b,.oR => v = .port .a .iL
      | _,_ => v = .port f p
    else v = .port f p
  | .hub f h, v => ∃ m : Menu, m.fragment = f ∧ m.hub = h ∧ v = .menu m
  | .menu m, v => v = .rightArm m ∨ v = .leftArm m
  | .rightArm m, v => if m.hub = 0 then v = .hub m.fragment 1
      else v = .port m.fragment .oR
  | .leftArm m, v => if m.hub = 0 then v = .port m.fragment .oL
      else v = .hub m.fragment 0

def chosenMenu (new : Bool) (f : Fragment) (h : Fin 2) : Menu :=
  match f with
  | .a => if h = 0 then .a03 else if new then .a12 else .a11
  | .b => if h = 0 then .b02 else .b11

def chosenMove (feedback new : Bool) : Vertex → Vertex
  | .port f .iL => .hub f 0
  | .port f .iR => .hub f 1
  | .port f p => if feedback then
      match f,p with
      | .a,.oR => .port .b .iL
      | .b,.oL => .port .a .iR
      | .b,.oR => .port .a .iL
      | _,_ => .port f p
    else .port f p
  | .hub f h => .menu (chosenMenu new f h)
  | .menu m => .rightArm m
  | .rightArm m => if m.hub = 0 then .hub m.fragment 1 else .port m.fragment .oR
  | .leftArm m => if m.hub = 0 then .port m.fragment .oL else .hub m.fragment 0

instance edgeDecidable (feedback : Bool) (v w : Vertex) : Decidable (edge feedback v w) := by
  cases v with
  | port f p => cases f <;> cases p <;> unfold edge <;> infer_instance
  | hub f h => unfold edge; infer_instance
  | menu m => unfold edge; infer_instance
  | rightArm m => unfold edge; infer_instance
  | leftArm m => unfold edge; infer_instance

def globalArena : Arena Vertex (Fin 1) where
  edge := edge true
  even := evenOwned
  priority := priority
  exitVertex := fun _ => .port .a .oL
  exit_injective := by intro x y _; exact Subsingleton.elim x y
  total := by decide
  exit_zero := by decide
  exit_sink := by decide

def localArena (f : Fragment) : Arena Vertex (Fin 2) where
  edge := edge false
  even := evenOwned
  priority := priority
  exitVertex := fun o => if o = 0 then .port f .oL else .port f .oR
  exit_injective := by cases f <;> decide
  total := by decide
  exit_zero := by cases f <;> decide
  exit_sink := by cases f <;> decide

def globalPolicy (new : Bool) : EvenPolicy globalArena where
  move := chosenMove true new
  legal_even := by
    change ∀ v, evenOwned v = true → edge true v (chosenMove true new v)
    cases new <;> decide
def localPolicy (f : Fragment) (new : Bool) : EvenPolicy (localArena f) where
  move := chosenMove false new
  legal_even := by
    change ∀ v, evenOwned v = true → edge false v (chosenMove false new v)
    cases f <;> cases new <;> decide

def localStart (f : Fragment) : Fin 2 → Vertex :=
  fun i => if i = 0 then .port f .iL else .port f .iR
def globalStarts : Fin 4 → Vertex :=
  ![.port .a .iL, .port .b .iR, .port .a .iR, .port .b .iL]

theorem original_count : Fintype.card Vertex = 27 := by decide
theorem one_changed_even_choice (v : Vertex) :
    chosenMove true false v ≠ chosenMove true true v ↔ v = .hub .a 1 := by
  fin_cases v <;> decide
theorem original_priority_bound (v : Vertex) : priority v ≤ 13 := by
  fin_cases v <;> decide

def LosingCycle (new : Bool) : List Vertex :=
  [.hub .a 1, .menu (chosenMenu new .a 1), .rightArm (chosenMenu new .a 1),
   .port .a .oR, .port .b .iL, .hub .b 0, .menu .b02, .leftArm .b02,
   .port .b .oL, .port .a .iR, .hub .a 1]

def WinningCycle (new : Bool) : List Vertex :=
  [.hub .a 0, .menu .a03, .rightArm .a03, .hub .a 1,
   .menu (chosenMenu new .a 1), .leftArm (chosenMenu new .a 1), .hub .a 0]

def UnitEndpointNeighbor (a b : ℕ × ℕ) : Prop :=
  (a.1 = b.1 ∧ Nat.dist a.2 b.2 = 1) ∨
  (a.2 = b.2 ∧ Nat.dist a.1 b.1 = 1)
def AdmittedEndpointsA (s t : ℕ) : Prop := s = 3 ∧ 1 ≤ t ∧ t ≤ 2 ∧ t < s
def AdmittedEndpointsB (s t : ℕ) : Prop := s = 2 ∧ t = 1

theorem only_legal_A_neighbor (s t : ℕ) :
    AdmittedEndpointsA s t ∧ UnitEndpointNeighbor (3,1) (s,t) ↔ s = 3 ∧ t = 2 := by
  simp only [AdmittedEndpointsA, UnitEndpointNeighbor, Nat.dist]
  omega

end Partials.Parity.Tie
