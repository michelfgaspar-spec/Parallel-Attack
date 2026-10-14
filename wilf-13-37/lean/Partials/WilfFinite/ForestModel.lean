import Partials.WilfFinite.Core

/-! R10 blind source, UNCOMPILED. The checker has its own additive-expression
semantics and positive-summand primitive test. No target/Wilf assertion occurs
in a state field. Concrete membership, byte parsing and producer correspondence
remain duties; this file supplies their precise mathematical objects. -/
namespace Partials.WilfFinite.Forest
open Partials.WilfFinite.Core

structure Label where
  c : ℕ
  m : ℕ
  G : List ℕ
  deriving DecidableEq

inductive Generated (G : List ℕ) : ℕ → Prop
  | zero : Generated G 0
  | add {x g : ℕ} : Generated G x → g ∈ G → Generated G (x+g)

theorem generated_add {G : List ℕ} {x y : ℕ}
    (hx : Generated G x) (hy : Generated G y) : Generated G (x+y) := by
  induction hy with
  | zero => simpa using hx
  | @add y g hy hg ih => simpa [Nat.add_assoc] using Generated.add ih hg

theorem generated_mono {G H : List ℕ} (hsub : ∀ g ∈ G, g ∈ H)
    {x : ℕ} (hx : Generated G x) : Generated H x := by
  induction hx with
  | zero => exact Generated.zero
  | @add x g hx hg ih => exact Generated.add ih (hsub g hg)

noncomputable def rebuiltLeft (l : Label) : Finset ℕ := by
  classical
  exact (Finset.range l.c).filter (Generated l.G)

theorem mem_rebuiltLeft (l : Label) (x : ℕ) :
    x ∈ rebuiltLeft l ↔ x < l.c ∧ Generated l.G x := by
  classical
  simp [rebuiltLeft]

def Member (l : Label) (x : ℕ) : Prop :=
  Generated l.G x ∧ x < l.c ∨ l.c ≤ x

def Primitive (l : Label) (x : ℕ) : Prop :=
  0 < x ∧ Member l x ∧
    ¬ ∃ y : ℕ, 0 < y ∧ y < x ∧ Member l y ∧ Member l (x-y)

noncomputable def rebuiltPrimitives (l : Label) : Finset ℕ := by
  classical
  exact (Finset.range (l.c+l.m)).filter (Primitive l)

def PrimitiveListCorrect (l : Label) : Prop :=
  l.G.Pairwise (· < ·) ∧
    ∀ x, x ∈ l.G ↔ x ∈ rebuiltPrimitives l ∧ x < l.c

def CanonicalLabel (l : Label) : Prop :=
  2 ≤ l.c ∧ l.c-1 ∉ rebuiltLeft l

noncomputable def canonicalState (l : Label) (h : CanonicalLabel l) :
    CanonicalState := ⟨l.c, {
  left := rebuiltLeft l
  c_two := h.1
  below := by intro x hx; exact ((mem_rebuiltLeft l x).1 hx).1
  zero := (mem_rebuiltLeft l 0).2 ⟨by have hc := h.1; omega, Generated.zero⟩
  gap := h.2
  closed := by
    intro x hx y hy hxy
    exact (mem_rebuiltLeft l _).2 ⟨hxy, generated_add
      ((mem_rebuiltLeft l x).1 hx).2 ((mem_rebuiltLeft l y).1 hy).2⟩ }⟩

theorem canonicalState_key (l : Label) (h : CanonicalLabel l) :
    key (canonicalState l h) = (l.c, rebuiltLeft l) := rfl

theorem independent_membership (l : Label) (h : CanonicalLabel l) (x : ℕ) :
    x ∈ (semigroup (canonicalState l h)).carrier ↔ Member l x := by
  change (x ∈ rebuiltLeft l ∨ l.c ≤ x) ↔ _
  rw [mem_rebuiltLeft]
  simp [Member, and_comm]

def greatest : List ℕ → ℕ
  | [] => 0
  | a::G => max a (greatest G)

theorem greatest_append_one (G : List ℕ) (a : ℕ) :
    greatest (G++[a]) = max (greatest G) a := by
  induction G with
  | nil => simp [greatest]
  | cons g G ih =>
    simp only [List.cons_append, greatest, ih]
    exact (max_assoc g (greatest G) a).symm

def append (l : Label) (a : ℕ) : Label := ⟨l.c,l.m,l.G++[a]⟩

noncomputable def gaps (l : Label) : List ℕ := by
  classical
  exact (List.range l.c).filter (fun a => greatest l.G < a ∧ a ∉ rebuiltLeft l)

theorem mem_gaps (l : Label) (a : ℕ) : a ∈ gaps l ↔
    a < l.c ∧ greatest l.G < a ∧ a ∉ rebuiltLeft l := by
  classical
  simp [gaps]

theorem gaps_nodup (l : Label) : (gaps l).Nodup := by
  classical
  exact (List.nodup_range (n := l.c)).filter _

theorem append_injective (l : Label) : Function.Injective (append l) := by
  intro a b h
  have hG := congrArg Label.G h
  have hs : [a] = [b] := List.append_cancel_left hG
  simpa using hs

structure Fields where
  L : Finset ℕ
  G : List ℕ
  c : ℕ
  m : ℕ
  k : ℕ
  ell : ℕ
  right : ℕ
  e : ℕ
  q : ℕ
  rho : ℕ
  W0 : ℤ
  W : ℤ
  deriving DecidableEq

noncomputable def reconstruct (l : Label) : Fields := by
  classical
  let P := rebuiltPrimitives l
  let ell := (P.filter (fun x => x < l.c)).card
  let right := (P.filter (fun x => l.c ≤ x)).card
  let k := (rebuiltLeft l).card
  let q := (l.c+l.m-1)/l.m
  exact ⟨rebuiltLeft l,l.G,l.c,l.m,k,ell,right,ell+right,q,q*l.m-l.c,
    (k : ℤ)*ell+(q : ℤ)*right-l.c,(k : ℤ)*(ell+right)-l.c⟩

theorem full_primitive_partition (l : Label) :
    (reconstruct l).e = (rebuiltPrimitives l).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := rebuiltPrimitives l) (p := fun x => x < l.c)
  simpa only [reconstruct, not_lt] using h

theorem reconstructed_wilf_difference (l : Label) :
    (reconstruct l).W - (reconstruct l).W0 =
      ((reconstruct l).k-(reconstruct l).q : ℤ)*(reconstruct l).right := by
  simp only [reconstruct]
  push_cast
  ring

structure Output where
  identity : ℕ × Finset ℕ
  fields : Fields
  deriving DecidableEq

noncomputable def exactOutput (l : Label) : Output :=
  ⟨(l.c,rebuiltLeft l),reconstruct l⟩

def NeedsOutput (p : Parameters) (l : Label) : Prop :=
  l.c-1 ∉ rebuiltLeft l ∧ (reconstruct l).k ≤ p.v ∧
  p.u ≤ (reconstruct l).k ∧ (reconstruct l).W0 < 0

noncomputable def expectedOutput (p : Parameters) (l : Label) : Option Output := by
  classical
  exact if NeedsOutput p l then some (exactOutput l) else none

structure Tail where
  gamma : ℕ
  h : ℕ
  delta : ℤ
  firstGap : ℕ
  deriving DecidableEq

def gamma (l : Label) : ℕ := (l.G[1]?).getD 0
def tailThreshold (l : Label) : ℕ := l.c+l.m-gamma l
noncomputable def tailDelta (l : Label) : ℤ :=
  (reconstruct l).k+(reconstruct l).ell+1-(reconstruct l).q
def TailGuard (l : Label) : Prop :=
  2 ≤ (reconstruct l).ell ∧ 0 ≤ (reconstruct l).W0+tailDelta l

noncomputable def tailGaps (l : Label) : List ℕ := by
  classical
  exact if TailGuard l then (gaps l).filter (fun a => tailThreshold l ≤ a) else []

noncomputable def tailRecord (l : Label) : Option Tail :=
  (tailGaps l).head?.map (fun a => ⟨gamma l,tailThreshold l,tailDelta l,a⟩)

inductive Reason
  | noncanonical | rankUpper | product | exhausted | expansion (tail : Option Tail)
  deriving DecidableEq

def ProductGuard (l : Label) : Prop :=
  l.c ≤ ((reconstruct l).k+1)*((reconstruct l).ell+1)

noncomputable def expandedGaps (l : Label) : List ℕ := by
  classical
  exact (gaps l).filter (fun a => a ∉ tailGaps l)

noncomputable def expectedReason (p : Parameters) (l : Label) : Reason := by
  classical
  exact if l.c-1 ∈ rebuiltLeft l then .noncanonical
    else if p.v < (reconstruct l).k then .rankUpper
    else if ProductGuard l then .product
    else if expandedGaps l = [] ∧ tailRecord l = none then .exhausted
    else .expansion (tailRecord l)

noncomputable def requiredChildren (p : Parameters) (l : Label) : List Label := by
  classical
  exact if l.c-1 ∈ rebuiltLeft l ∨ p.v < (reconstruct l).k ∨ ProductGuard l
    then [] else (expandedGaps l).map (append l)

def rank (l : Label) : ℕ := l.c-1-greatest l.G

theorem required_child_gap (p : Parameters) (l b : Label)
    (hb : b ∈ requiredChildren p l) :
    ∃ a ∈ gaps l, b = append l a := by
  classical
  unfold requiredChildren at hb
  split_ifs at hb with ht
  · simp at hb
  · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    have ha' : a ∈ gaps l := (List.mem_filter.mp ha).1
    exact ⟨a,ha',rfl⟩

theorem child_rank_decreases (p : Parameters) (l b : Label)
    (hb : b ∈ requiredChildren p l) : rank b < rank l := by
  obtain ⟨a,ha,rfl⟩ := required_child_gap p l b hb
  have hh := (mem_gaps l a).1 ha
  simp only [rank,append,greatest_append_one,max_eq_right (le_of_lt hh.2.1)]
  omega

theorem requiredChildren_nodup (p : Parameters) (l : Label) :
    (requiredChildren p l).Nodup := by
  classical
  unfold requiredChildren
  split_ifs
  · simp
  · exact ((gaps_nodup l).filter _).map (append_injective l)

theorem every_unpruned_gap_child (p : Parameters) (l : Label) (a : ℕ)
    (hcanonical : l.c-1 ∉ rebuiltLeft l) (hrank : (reconstruct l).k ≤ p.v)
    (hproduct : ¬ ProductGuard l) (hgap : a ∈ gaps l)
    (htail : a ∉ tailGaps l) : append l a ∈ requiredChildren p l := by
  classical
  have hterminal : ¬ (l.c-1 ∈ rebuiltLeft l ∨ p.v < (reconstruct l).k ∨ ProductGuard l) := by
    rintro (hc | hr | hp)
    · exact hcanonical hc
    · exact not_lt_of_ge hrank hr
    · exact hproduct hp
  simp only [requiredChildren,if_neg hterminal]
  exact List.mem_map.mpr ⟨a,List.mem_filter.mpr ⟨hgap,by simpa using htail⟩,rfl⟩

theorem threshold_equality_in_tail (l : Label) (hguard : TailGuard l)
    (hgap : tailThreshold l ∈ gaps l) : tailThreshold l ∈ tailGaps l := by
  classical
  simp [tailGaps,hguard,hgap]

theorem product_precedes_tail (p : Parameters) (l : Label)
    (hc : l.c-1 ∉ rebuiltLeft l) (hr : (reconstruct l).k ≤ p.v)
    (hp : ProductGuard l) : expectedReason p l = .product := by
  classical
  simp [expectedReason,hc,not_lt_of_ge hr,hp]

def normalizeReasonAlias (name : String) : String :=
  if name="NONCANONICAL_SEED" ∨ name="NONCANONICAL_CHILD" then "NONCANONICAL"
  else if name="LARGE_TAIL" then "TAIL"
  else if name="CANDIDATES_EXHAUSTED" then "EXHAUSTED" else name

/-- Sorting uses the original integer order; generated integers between h and
the first eligible gap never create artificial children or alter the tail start.
Formal List.Pairwise/range-filter API elaboration is a later source duty. -/
def GapOrderTarget : Prop := ∀ l, (gaps l).Pairwise (· < ·)

/-- Filtering the natural range retains its strict order. This discharges only
the local gap-order API duty, independently of PRIMARY model correspondence. -/
theorem gaps_strict_order : GapOrderTarget := by
  intro l
  classical
  exact List.Pairwise.filter _ List.pairwise_lt_range

end Partials.WilfFinite.Forest
