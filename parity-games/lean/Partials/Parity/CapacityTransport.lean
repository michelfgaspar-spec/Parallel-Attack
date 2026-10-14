import Partials.Parity.Model

/-! Capacity/rank source for compilation.tex P1-D08, P1-L05 and P1-L06.
`capGap` counts FREE integer slots, hence the essential minus one. The
syntactic policy below contains every original hub and router. No reachable
sub-policy or independent row witness is substituted for that object. -/

namespace Partials.Parity.CompilerSource

def freeSlots (a b : Int) : Int := b - a - 1
def capGap (r : Nat) (a b : Int) : Int := min (freeSlots a b) (r : Int)

theorem freeSlots_nonnegative {a b : Int} (hab : a < b) :
    0 ≤ freeSlots a b := by unfold freeSlots; omega

theorem capGap_zero {a b : Int} (hab : a < b) : capGap 0 a b = 0 := by
  unfold capGap
  exact min_eq_right (freeSlots_nonnegative hab)

theorem capGap_saturated_iff (r : Nat) (a b : Int) :
    capGap r a b = (r : Int) ↔ (r : Int) ≤ freeSlots a b := by
  constructor
  · intro h
    have hbound : capGap r a b ≤ freeSlots a b := min_le_left _ _
    rw [h] at hbound
    exact hbound
  · intro h
    exact min_eq_right h

theorem capGap_unsaturated_iff (r : Nat) (a b c : Int) (hc : c < (r : Int)) :
    capGap r a b = c ↔ freeSlots a b = c := by
  unfold capGap
  rcases le_total (freeSlots a b) (r : Int) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    constructor <;> intro heq <;> omega

/-- Equality of capped capacities transports any k≤r hidden classes. -/
theorem same_cap_fits (r k : Nat) (a b a' b' : Int)
    (hk : k ≤ r) (hold : (k : Int) ≤ freeSlots a b)
    (hcap : capGap r a b = capGap r a' b') :
    (k : Int) ≤ freeSlots a' b' := by
  have hkr : (k : Int) ≤ (r : Int) := by omega
  have hmin : (k : Int) ≤ capGap r a b := le_min hold hkr
  rw [hcap] at hmin
  exact le_trans hmin (min_le_left _ _)

def rankedSlot (a : Int) (rank : Nat) : Int := a + (rank : Int) + 1

theorem rankedSlot_inside (a b : Int) (k rank : Nat)
    (hrank : rank < k) (hfit : (k : Int) ≤ freeSlots a b) :
    a < rankedSlot a rank ∧ rankedSlot a rank < b := by
  unfold rankedSlot freeSlots at *
  omega

theorem rankedSlot_strictMono (a : Int) : StrictMono (rankedSlot a) := by
  intro i j hij
  unfold rankedSlot
  omega

theorem rankedSlot_injective (a : Int) : Function.Injective (rankedSlot a) :=
  (rankedSlot_strictMono a).injective

/-- Exactly the two DBM alternatives in P1-D08; r=0 is saturated and
requires b>a rather than a fictitious empty-gap equality. -/
def GapCase (r : Nat) (c a b : Int) : Prop :=
  (c < (r : Int) ∧ b - a = c + 1) ∨
  (c = (r : Int) ∧ (r : Int) + 1 ≤ b - a)

theorem actual_gap_case (r : Nat) (a b : Int) (hab : a < b) :
    GapCase r (capGap r a b) a b := by
  unfold GapCase capGap freeSlots
  rcases lt_or_ge (b - a - 1) (r : Int) with h | h
  · left
    rw [min_eq_left (by omega)]
    omega
  · right
    rw [min_eq_right h]
    omega

structure IntervalMenus (Hub : Type*) where
  lower : Hub → Int
  upper : Hub → Int
  next : Hub → Hub → Prop

/-- Router identities and unreachable choices are retained literally.
For a concrete grammar the Nat move code must decode to an ORIGINAL legal
successor; no selected-graph policy domain is used for admission. -/
structure RankPolicy (Hub Router : Type*) where
  hubChoice : Hub → Int
  routerMove : Router → Nat

def RankPolicyAdmitted {H R : Type*} (M : IntervalMenus H)
    (routerLegal : R → Nat → Prop) (σ : RankPolicy H R) : Prop :=
  (∀ h, M.lower h ≤ σ.hubChoice h ∧ σ.hubChoice h ≤ M.upper h) ∧
  (∀ a b, M.next a b → σ.hubChoice b < σ.hubChoice a) ∧
  ∀ r, routerLegal r (σ.routerMove r)

def rankTransport {H R : Type*} (f : Int → Int)
    (σ : RankPolicy H R) : RankPolicy H R :=
  ⟨fun h => f (σ.hubChoice h), σ.routerMove⟩

/-- The finite level set contains endpoint constants, visible anchors and
selected-q classes of ONE complete original policy. -/
def IncreasingOn (levels : Set Int) (f : Int → Int) : Prop :=
  ∀ a ∈ levels, ∀ b ∈ levels, a < b → f a < f b

theorem monotone_on_of_increasing {levels : Set Int} {f : Int → Int}
    (hf : IncreasingOn levels f) {a b : Int}
    (ha : a ∈ levels) (hb : b ∈ levels) (hab : a ≤ b) : f a ≤ f b := by
  rcases lt_or_eq_of_le hab with h | h
  · exact le_of_lt (hf a ha b hb h)
  · subst b
    exact le_rfl

theorem rankTransport_admitted {H R : Type*}
    (M : IntervalMenus H) (routerLegal : R → Nat → Prop)
    (σ : RankPolicy H R) (levels : Set Int) (f : Int → Int)
    (hadmitted : RankPolicyAdmitted M routerLegal σ)
    (hf : IncreasingOn levels f)
    (hselected : ∀ h, σ.hubChoice h ∈ levels)
    (hlower : ∀ h, M.lower h ∈ levels ∧ f (M.lower h) = M.lower h)
    (hupper : ∀ h, M.upper h ∈ levels ∧ f (M.upper h) = M.upper h) :
    RankPolicyAdmitted M routerLegal (rankTransport f σ) := by
  rcases hadmitted with ⟨hmenu, hdecrease, hrouter⟩
  refine ⟨?_, ?_, hrouter⟩
  · intro h
    have hlo := monotone_on_of_increasing hf (hlower h).1
      (hselected h) (hmenu h).1
    have hup := monotone_on_of_increasing hf (hselected h)
      (hupper h).1 (hmenu h).2
    rw [(hlower h).2] at hlo
    rw [(hupper h).2] at hup
    exact ⟨hlo, hup⟩
  · intro a b hab
    exact hf (σ.hubChoice b) (hselected b) (σ.hubChoice a)
      (hselected a) (hdecrease a b hab)

theorem rankTransport_router_unchanged {H R : Type*}
    (σ : RankPolicy H R) (f : Int → Int) (r : R) :
    (rankTransport f σ).routerMove r = σ.routerMove r := rfl

def encodedPriority (q epsilon : Int) : Int := 4 * q + epsilon

theorem encodedPriority_separates (q q' epsilon epsilon' : Int)
    (h : q < q') (he : 0 ≤ epsilon ∧ epsilon ≤ 1)
    (he' : 0 ≤ epsilon' ∧ epsilon' ≤ 1) :
    encodedPriority q epsilon < encodedPriority q' epsilon' := by
  unfold encodedPriority
  omega

theorem encodedPriority_parity (q epsilon : Int) :
    encodedPriority q epsilon % 2 = epsilon % 2 := by
  unfold encodedPriority
  omega

/-- A usable general minimum-image lemma. The order-equivalence premise is
restricted to the actual raw set, rather than a false global claim about an
arbitrarily extended rank map on every integer. -/
theorem minRow_image {Exit : Type*} (raw : Set (Outcome Exit))
    (f : Outcome Exit → Outcome Exit)
    (horder : ∀ x ∈ raw, ∀ y ∈ raw,
      OutcomeLE (f x) (f y) ↔ OutcomeLE x y) :
    MinRow (f '' raw) = f '' MinRow raw := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hmin⟩
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    intro y hy hyx
    have hfyx := (horder y hy x hx).mpr hyx
    have hfxy := hmin (f y) ⟨y, hy, rfl⟩ hfyx
    exact (horder x hx y hy).mp hfxy
  · rintro ⟨x, ⟨hx, hmin⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, ?_⟩
    rintro z ⟨y, hy, rfl⟩ hfyx
    have hyx := (horder y hy x hx).mp hfyx
    exact (horder x hx y hy).mpr (hmin y hy hyx)

/-- Fine remaining capacity duty: finite hidden classes must be classified
against the actual sorted constants/visible anchors, injected by the proved
rankedSlot map, and glued consistently with classes equal to anchors.
Its inputs are individual finite level data, never an attained-cell oracle. -/
def RankMapConstructionDuty (levels anchors : Finset Int)
    (anchorImage : Int → Int) (visibleImage : Int → Int)
    (r : Nat) : Prop :=
  ∃ f : Int → Int,
    IncreasingOn (↑levels : Set Int) f ∧
    (∀ a ∈ anchors, f a = anchorImage a) ∧
    (∀ a ∈ levels, a ∉ anchors →
      f a = visibleImage a ∨
      ∃ left rank, rank < r ∧ f a = rankedSlot left rank)

/-- Permitted starts enter only ports/routers, selected menus have their
hub as sole predecessor, and original Even choices are fixed. Proving this
gate excludes unselected menu/arm vertices from every evaluated history;
it does NOT discard unreachable choices from the complete original policy. -/
def SelectedStartHistoryGateDuty {V Exit Start : Type*}
    (A : Arena V Exit) (σ : EvenPolicy A) (starts : Start → V)
    (selected : Set V) : Prop :=
  (∀ i, starts i ∈ selected) ∧
  (∀ o, A.exitVertex o ∈ selected) ∧
  ∀ i path, path 0 = starts i → Compatible A σ path →
    ∀ n, path n ∈ selected

def supportPath {V : Type*} {selected : Set V}
    (path : Nat → {v : V // v ∈ selected}) : Nat → V :=
  fun n => (path n).val

def SelectedPriorityRelabelling (alphabet : Set Nat) (f : Nat → Nat) : Prop :=
  f 0 = 0 ∧
  (∀ p ∈ alphabet, f p % 2 = p % 2) ∧
  ∀ p ∈ alphabet, ∀ q ∈ alphabet, p < q ↔ f p < f q

/-- The required normalization is a bijection BETWEEN SELECTED SUPPORT
SUBTYPES, possibly in different original carriers. Base hubs/ports/routers,
chosen menus/arms and exits form these supports. No permutation or global
priority law is demanded on unselected original vertices. All recurrence
and first-exit equivalences are restricted to the actual selected alphabet,
so arbitrary extensions of a finite rank map cannot introduce collisions.
This is an open primitive history duty, not cell attainability. -/
def SelectedHistoryTransportDuty {V W Exit Start : Type*}
    (A : Arena V Exit) (A' : Arena W Exit)
    (σ : EvenPolicy A) (σ' : EvenPolicy A')
    (starts : Start → V) (starts' : Start → W)
    (selected : Set V) (selected' : Set W)
    (vertexMap : {v : V // v ∈ selected} → {w : W // w ∈ selected'})
    (priorityMap : Nat → Nat) : Prop :=
  SelectedStartHistoryGateDuty A σ starts selected ∧
  SelectedStartHistoryGateDuty A' σ' starts' selected' ∧
  Function.Bijective vertexMap ∧
  SelectedPriorityRelabelling (A.priority '' selected) priorityMap ∧
  (∀ v : {v : V // v ∈ selected},
    A'.priority (vertexMap v).val = priorityMap (A.priority v.val)) ∧
  (∀ i (hi : starts i ∈ selected),
    (vertexMap ⟨starts i, hi⟩).val = starts' i) ∧
  (∀ o (ho : A.exitVertex o ∈ selected),
    (vertexMap ⟨A.exitVertex o, ho⟩).val = A'.exitVertex o) ∧
  (∀ path : Nat → {v : V // v ∈ selected},
    Compatible A σ (supportPath path) ↔
      Compatible A' σ' (supportPath (fun n => vertexMap (path n)))) ∧
  (∀ (path : Nat → {v : V // v ∈ selected}) n o p,
    p ∈ A.priority '' selected →
    (FirstExit A (supportPath path) n o p ↔
      FirstExit A' (supportPath (fun n => vertexMap (path n))) n o (priorityMap p))) ∧
  (∀ (path : Nat → {v : V // v ∈ selected}) p,
    p ∈ A.priority '' selected →
    (Recurs A (supportPath path) p ↔
      Recurs A' (supportPath (fun n => vertexMap (path n))) (priorityMap p)))

end Partials.Parity.CompilerSource
