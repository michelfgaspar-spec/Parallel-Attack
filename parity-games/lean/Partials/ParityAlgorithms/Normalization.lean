import Partials.ParityAlgorithms.OrderedSyntax

/-! Structural four-phase normalizer and lower antichain algebra for P3.
The procedures are definitions, with no scientific execution or theorem
promotion. Desired literal-arena correspondence and R01--R19 derivation are
explicit unfinished duties, rather than inputs to a claimed completeness proof. -/
namespace Partials.ParityAlgorithms
open Partials.Parity

abbrev Row (Exit : Type*) := Set (Outcome Exit)
abbrev FrontDownset (Exit : Type*) := Set (Row Exit)

def rowMeet {Exit : Type*} (r s : Row Exit) : Row Exit := MinRow (r ∪ s)

def prefixOutcome {Exit : Type*} (r : Priority5) : Outcome Exit → Outcome Exit
  | .bottom => .bottom
  | .top => .top
  | .halt o p => .halt o (max r.val p)

def rowPrefix {Exit : Type*} (r : Priority5) (s : Row Exit) : Row Exit :=
  MinRow (prefixOutcome r '' s)

theorem prefixOutcome_monotone {Exit : Type*} (r : Priority5)
    {a b : Outcome Exit} (h : OutcomeLE a b) :
    OutcomeLE (prefixOutcome r a) (prefixOutcome r b) := by
  cases a <;> cases b <;> simp_all [prefixOutcome, OutcomeLE]
  exact numerical_max_priority_monotone_left h.2 r.val

theorem minRow_idempotent {Exit : Type*} (r : Row Exit) :
    MinRow (MinRow r) = MinRow r := by
  apply Set.Subset.antisymm (minRow_subset _)
  intro x hx
  exact ⟨hx, fun y hy hyx => hx.2 y hy.1 hyx⟩

/-- Minima recover every finite set up to the predecessor preorder. -/
theorem minRow_predecessor_equivalence {Exit : Type*} (r : Row Exit)
    (hf : r.Finite) : RowLE (MinRow r) r ∧ RowLE r (MinRow r) := by
  constructor
  · intro x hx
    exact finite_minRow_below r hf hx
  · intro x hx
    exact ⟨x, hx.1, outcomeLE_refl x⟩

theorem finite_minima_equal_of_mutual {Exit : Type*} {r s : Row Exit}
    (hr : r.Finite) (hs : s.Finite) (hrs : RowLE r s) (hsr : RowLE s r) :
    MinRow r = MinRow s := by
  have er := minRow_predecessor_equivalence r hr
  have es := minRow_predecessor_equivalence s hs
  exact rowLE_antisymm (minRow_antichain _) (minRow_antichain _)
    (rowLE_trans er.1 (rowLE_trans hrs es.2))
    (rowLE_trans es.1 (rowLE_trans hsr er.2))

theorem rowLE_union {Exit : Type*} {x r s : Row Exit} :
    RowLE x (r ∪ s) ↔ RowLE x r ∧ RowLE x s := by
  constructor
  · intro h
    exact ⟨fun a ha => h a (Or.inl ha), fun a ha => h a (Or.inr ha)⟩
  · rintro ⟨hr, hs⟩ a (ha | ha)
    · exact hr a ha
    · exact hs a ha

theorem rowMeet_greatest_lower_bound {Exit : Type*} {r s x : Row Exit}
    (hr : r.Finite) (hs : s.Finite) :
    RowLE x (rowMeet r s) ↔ RowLE x r ∧ RowLE x s := by
  have eqv := minRow_predecessor_equivalence (r ∪ s) (hr.union hs)
  constructor
  · intro h
    exact rowLE_union.mp (rowLE_trans h eqv.1)
  · intro h
    exact rowLE_trans (rowLE_union.mpr h) eqv.2

theorem rowMeet_monotone {Exit : Type*} {r r' s s' : Row Exit}
    (hr : r.Finite) (hs : s.Finite) (hr' : r'.Finite) (hs' : s'.Finite)
    (hrr : RowLE r r') (hss : RowLE s s') :
    RowLE (rowMeet r s) (rowMeet r' s') := by
  apply (rowMeet_greatest_lower_bound hr' hs').mpr
  have h := (rowMeet_greatest_lower_bound hr hs).mp (rowLE_refl (rowMeet r s))
  exact ⟨rowLE_trans h.1 hrr, rowLE_trans h.2 hss⟩

theorem minRow_union_minima {Exit : Type*} (r s : Row Exit)
    (hr : r.Finite) (hs : s.Finite) :
    MinRow (r ∪ s) = MinRow (MinRow r ∪ MinRow s) := by
  apply finite_minima_equal_of_mutual (hr.union hs)
    ((hr.subset (minRow_subset r)).union (hs.subset (minRow_subset s)))
  · intro x hx
    rcases hx with hx | hx
    · exact ⟨x, Or.inl hx.1, outcomeLE_refl x⟩
    · exact ⟨x, Or.inr hx.1, outcomeLE_refl x⟩
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨y, hy, hyx⟩ := finite_minRow_below r hr hx
      exact ⟨y, Or.inl hy, hyx⟩
    · obtain ⟨y, hy, hyx⟩ := finite_minRow_below s hs hx
      exact ⟨y, Or.inr hy, hyx⟩

theorem minRow_monotone_image {Exit : Type*} (r : Priority5)
    (u : Row Exit) (hu : u.Finite) :
    MinRow (prefixOutcome r '' u) = MinRow (prefixOutcome r '' MinRow u) := by
  apply finite_minima_equal_of_mutual (hu.image _) ((hu.subset (minRow_subset u)).image _)
  · rintro x ⟨y, hy, rfl⟩
    exact ⟨prefixOutcome r y, ⟨y, hy.1, rfl⟩, outcomeLE_refl _⟩
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hzy⟩ := finite_minRow_below u hu hy
    exact ⟨prefixOutcome r z, ⟨z, hz, rfl⟩, prefixOutcome_monotone r hzy⟩

theorem rowPrefix_monotone {Exit : Type*} (r : Priority5)
    {u v : Row Exit} (hu : u.Finite) (h : RowLE u v) :
    RowLE (rowPrefix r u) (rowPrefix r v) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx.1
  obtain ⟨z, hz, hzy⟩ := h y hy
  obtain ⟨w, hw, hwz⟩ := finite_minRow_below (prefixOutcome r '' u)
    (hu.image _) ⟨z, hz, rfl⟩
  exact ⟨w, hw, outcomeLE_trans hwz (prefixOutcome_monotone r hzy)⟩

def principalRow {Exit : Type*} (r : Row Exit) : FrontDownset Exit := {x | RowLE x r}

def downsetPrefix {Exit : Type*} (p : Priority5) (d : FrontDownset Exit) : FrontDownset Exit :=
  {x | ∃ r ∈ d, r.Finite ∧ RowLE x (rowPrefix p r)}

def algebraDenotation {Exit : Type*} : Term Exit → FrontDownset Exit
  | .atom a => principalRow {a.outcome}
  | .prefix r x => downsetPrefix r (algebraDenotation x)
  | .even x y => algebraDenotation x ∪ algebraDenotation y
  | .odd x y => algebraDenotation x ∩ algebraDenotation y
  | .leaf .even o p q _ => principalRow {Outcome.halt o q.val} ∪ principalRow {(omegaAtom p).outcome}
  | .leaf .odd o p q _ => principalRow {Outcome.halt o q.val} ∩
      (principalRow {Outcome.halt o (priorityJoin p q).val} ∩ principalRow {(omegaAtom p).outcome})

/-- R01--R09 hold in the downset lattice, independently of graph equality. -/
theorem algebra_even_comm {Exit : Type*} (x y : Term Exit) :
    algebraDenotation (.even x y) = algebraDenotation (.even y x) := Set.union_comm _ _
theorem algebra_even_assoc {Exit : Type*} (x y z : Term Exit) :
    algebraDenotation (.even (.even x y) z) = algebraDenotation (.even x (.even y z)) := Set.union_assoc _ _ _
theorem algebra_even_idempotent {Exit : Type*} (x : Term Exit) :
    algebraDenotation (.even x x) = algebraDenotation x := Set.union_self _
theorem algebra_odd_comm {Exit : Type*} (x y : Term Exit) :
    algebraDenotation (.odd x y) = algebraDenotation (.odd y x) := Set.inter_comm _ _
theorem algebra_odd_assoc {Exit : Type*} (x y z : Term Exit) :
    algebraDenotation (.odd (.odd x y) z) = algebraDenotation (.odd x (.odd y z)) := Set.inter_assoc _ _ _
theorem algebra_odd_idempotent {Exit : Type*} (x : Term Exit) :
    algebraDenotation (.odd x x) = algebraDenotation x := Set.inter_self _
theorem algebra_absorption_even {Exit : Type*} (x y : Term Exit) :
    algebraDenotation (.even x (.odd x y)) = algebraDenotation x := by
  ext r
  change (r ∈ algebraDenotation x ∨ r ∈ algebraDenotation x ∧ r ∈ algebraDenotation y) ↔ _
  constructor
  · rintro (h | ⟨h, _⟩) <;> exact h
  · intro h; exact Or.inl h
theorem algebra_absorption_odd {Exit : Type*} (x y : Term Exit) :
    algebraDenotation (.odd x (.even x y)) = algebraDenotation x := by
  ext r
  change (r ∈ algebraDenotation x ∧ (r ∈ algebraDenotation x ∨ r ∈ algebraDenotation y)) ↔ _
  constructor
  · intro h; exact h.1
  · intro h; exact ⟨h, Or.inl h⟩
theorem algebra_distributivity {Exit : Type*} (x y z : Term Exit) :
    algebraDenotation (.odd x (.even y z)) = algebraDenotation (.even (.odd x y) (.odd x z)) := by
  ext r
  simp [algebraDenotation, and_or_left]

/-- Phase 1 precedes duplication, and deletes every L leaf. -/
def removeFeedback {Exit : Type*} : Term Exit → Term Exit
  | .atom a => .atom a
  | .prefix r x => .prefix r (removeFeedback x)
  | .even x y => .even (removeFeedback x) (removeFeedback y)
  | .odd x y => .odd (removeFeedback x) (removeFeedback y)
  | .leaf .even o p q _ => .even (.atom (.halt o q)) (.atom (omegaAtom p))
  | .leaf .odd o p q _ => .odd (.atom (.halt o q))
      (.odd (.atom (.halt o (priorityJoin p q))) (.atom (omegaAtom p)))

theorem removeFeedback_no_leaf {Exit : Type*} (x : Term Exit) :
    (removeFeedback x).leafCount = 0 := by
  induction x with
  | atom a => rfl
  | «prefix» r x ih => simpa [removeFeedback, Term.leafCount] using ih
  | even x y ihx ihy => simp [removeFeedback, Term.leafCount, ihx, ihy]
  | odd x y ihx ihy => simp [removeFeedback, Term.leafCount, ihx, ihy]
  | leaf owner o p q hp => cases owner <;> rfl

/-- The first phase has an actual R17/R18 derivation inside the original
one-leaf budget. This does not assert physical arena/Q correspondence. -/
theorem removeFeedback_derivation {Exit : Type*} (x : Term Exit)
    (h : x.leafCount ≤ 1) : Derivation x (removeFeedback x) := by
  induction x with
  | atom a => exact Derivation.refl _
  | «prefix» r x ih => exact Derivation.prefix r (ih h)
  | even x y ihx ihy =>
    have hx : x.leafCount ≤ 1 := by simp only [Term.leafCount] at h; omega
    have hy : y.leafCount ≤ 1 := by simp only [Term.leafCount] at h; omega
    exact Derivation.trans
      (Derivation.even_left y h (by rw [removeFeedback_no_leaf]; omega) (ihx hx))
      (Derivation.even_right (removeFeedback x)
        (by rw [removeFeedback_no_leaf]; omega)
        (by rw [removeFeedback_no_leaf, removeFeedback_no_leaf]; omega) (ihy hy))
  | odd x y ihx ihy =>
    have hx : x.leafCount ≤ 1 := by simp only [Term.leafCount] at h; omega
    have hy : y.leafCount ≤ 1 := by simp only [Term.leafCount] at h; omega
    exact Derivation.trans
      (Derivation.odd_left y h (by rw [removeFeedback_no_leaf]; omega) (ihx hx))
      (Derivation.odd_right (removeFeedback x)
        (by rw [removeFeedback_no_leaf]; omega)
        (by rw [removeFeedback_no_leaf, removeFeedback_no_leaf]; omega) (ihy hy))
  | leaf owner o p q hp =>
    cases owner
    · exact Derivation.step (Equation.r17 o p q hp)
    · exact Derivation.step (Equation.r18 o p q hp)

/-- Accumulated finite prefixes use numerical max, not source-order join. -/
def pushPrefixes {Exit : Type*} (r : Priority5) : Term Exit → Term Exit
  | .atom a => .atom (atomPrefix r a)
  | .prefix s x => pushPrefixes (priorityJoin r s) x
  | .even x y => .even (pushPrefixes r x) (pushPrefixes r y)
  | .odd x y => .odd (pushPrefixes r x) (pushPrefixes r y)
  | .leaf a o p q h => .prefix r (.leaf a o p q h) -- excluded after Phase 1

def PrefixFree {Exit : Type*} : Term Exit → Prop
  | .atom _ => True
  | .prefix _ _ => False
  | .even x y | .odd x y => PrefixFree x ∧ PrefixFree y
  | .leaf _ _ _ _ _ => False

theorem pushPrefixes_prefixFree {Exit : Type*} (x : Term Exit)
    (h : x.leafCount = 0) (r : Priority5) : PrefixFree (pushPrefixes r x) := by
  induction x generalizing r with
  | atom a => trivial
  | «prefix» s x ih => exact ih h _
  | even x y ihx ihy =>
    have hx : x.leafCount = 0 := by simp [Term.leafCount] at h; omega
    have hy : y.leafCount = 0 := by simp [Term.leafCount] at h; omega
    exact ⟨ihx hx r, ihy hy r⟩
  | odd x y ihx ihy =>
    have hx : x.leafCount = 0 := by simp [Term.leafCount] at h; omega
    have hy : y.leafCount = 0 := by simp [Term.leafCount] at h; omega
    exact ⟨ihx hx r, ihy hy r⟩
  | leaf a o p q hp => simp [Term.leafCount] at h

def rowProduct {Exit : Type*} (xs ys : List (List (Atom Exit))) : List (List (Atom Exit)) :=
  xs.flatMap fun x => ys.map fun y => x ++ y

/-- Phase 3 materializes finite Cartesian products; no polynomial bound. -/
def distribute {Exit : Type*} : Term Exit → List (List (Atom Exit))
  | .atom a => [[a]]
  | .even x y => distribute x ++ distribute y
  | .odd x y => rowProduct (distribute x) (distribute y)
  | .prefix r x => (distribute x).map (List.map (atomPrefix r))
  | .leaf .even o p q _ => [[.halt o q], [omegaAtom p]]
  | .leaf .odd o p q _ => [[.halt o q, .halt o (priorityJoin p q), omegaAtom p]]

/-- Phase 4 is explicit finite guarded pruning, then caller-declared sorting. -/
def pruneAtoms {Exit : Type*} [DecidableEq Exit] (r : List (Atom Exit)) : List (Atom Exit) :=
  r.eraseDups.filter fun a => !(r.any fun b => decide (atomLE b a ∧ ¬ atomLE a b))

def pruneRows {Exit : Type*} [DecidableEq Exit] (rs : List (List (Atom Exit))) : List (List (Atom Exit)) :=
  let rows := (rs.map pruneAtoms).eraseDups
  rows.filter fun r => !(rows.any fun s => (s.all fun b => r.any fun a => decide (atomLE a b)) && !(r.all fun b => s.any fun a => decide (atomLE a b)))

/-- Serialization is a supplied total order on indexed typed atoms/lists;
its consistency with the canonical record is an explicit duty below. -/
def normalRows {Exit : Type*} [DecidableEq Exit]
    (sortAtoms : List (Atom Exit) → List (Atom Exit))
    (sortRows : List (List (Atom Exit)) → List (List (Atom Exit))) (x : Term Exit) :=
  -- Equivalent rows can have different atom-list orders before serialization.
  -- Remove duplicates again after the canonical atom sort makes them literal.
  sortRows (((pruneRows (distribute (pushPrefixes 0 (removeFeedback x)))).map sortAtoms).eraseDups)

structure CanonicalDescription (q i : Nat) where
  /- Fin indexes retain ordered ports, including unused declared exits. -/
  rows : Fin i → List (List (Atom (Fin q)))

/-- Exact missing steps, none assumed by an unconditional completeness claim. -/
def NormalizationDerivationDuty {Exit : Type*} [DecidableEq Exit]
    (sortAtoms : List (Atom Exit) → List (Atom Exit))
    (sortRows : List (List (Atom Exit)) → List (List (Atom Exit))) : Prop :=
  (∀ r, (sortAtoms r).Perm r) ∧ (∀ rs, (sortRows rs).Perm rs) ∧
  ∀ x, x.leafCount ≤ 1 → ∃ nf : Term Exit,
    Derivation x nf ∧ distribute nf = normalRows sortAtoms sortRows x ∧ PrefixFree nf

/-- Construct actual literal arenas and all-history strategy restriction /
extension at each disjoint constructor; identify Q with the computed finite
front. No desired Q identity is used as proof of this obligation. -/
def CanonicalPruningDuty : Prop :=
  ∀ q : Nat, 1 ≤ q → q ≤ 2 →
    ∀ x : Term (Fin q), x.leafCount ≤ 1 →
      ∃ rows : List (List (Atom (Fin q))), rows = pruneRows
        (distribute (pushPrefixes 0 (removeFeedback x))) ∧
        rows ≠ [] ∧ ∀ r ∈ rows, minimizedAtomList r

/- The duty above certifies only the finite front output; the concrete edge
arena builder, history-space bijections and Q equality remain prose duties.
Bidirectional rewrite confluence/termination and graph policy correspondence
are deliberately absent from the source claims. -/
end Partials.ParityAlgorithms
