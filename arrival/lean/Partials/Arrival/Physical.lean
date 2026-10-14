import Partials.Arrival.Interface

/-! R3 source proposal, not executed or kernel checked.
The constructors below denote actual physical vertices; a boundary is a
nonsink here. `a i`, `b i`, `c i`, `lower i` have manuscript indices i+1.
Only the two `sink` constructors are original sinks. -/
namespace Partials.Arrival.Physical

inductive Vertex (k : ℕ) where
  | a (i : Fin k)
  | b (i : Fin (k - 1))
  | c (i : Fin (k - 2))
  | boundary (t : NamedOutput)
  | lower (j : Fin (k + 3))
  | sink (s : Bool)
  deriving DecidableEq, Fintype

def source (hk : 3 ≤ k) : Vertex k := .a ⟨k - 1, by omega⟩
def nearSource (hk : 3 ≤ k) : Vertex k := .a ⟨k - 2, by omega⟩
def lowerOne (k : ℕ) : Vertex k := .lower ⟨0, by omega⟩
def lowerTop (k : ℕ) : Vertex k := .lower ⟨k + 2, by omega⟩
def IsSink : Vertex k → Prop
  | .sink _ => True
  | _ => False

instance (k : ℕ) : DecidablePred (IsSink (k := k)) := by
  intro v
  cases v <;> dsimp [IsSink] <;> infer_instance

def sinkEquiv (k : ℕ) : {v : Vertex k // IsSink v} ≃ Bool where
  toFun v := match v with
    | ⟨.sink s, _⟩ => s
    | ⟨.a _, h⟩ => False.elim h
    | ⟨.b _, h⟩ => False.elim h
    | ⟨.c _, h⟩ => False.elim h
    | ⟨.boundary _, h⟩ => False.elim h
    | ⟨.lower _, h⟩ => False.elim h
  invFun s := ⟨.sink s, trivial⟩
  left_inv := by
    rintro ⟨v, hv⟩
    cases v <;> first | rfl | exact False.elim hv
  right_inv := by intro s; rfl

theorem original_sink_count (k : ℕ) : Fintype.card {v : Vertex k // IsSink v} = 2 := by
  rw [Fintype.card_congr (sinkEquiv k)]
  exact Fintype.card_bool

/-- False is the first (even) next slot, true the second (odd) slot. -/
def next (hk : 3 ≤ k) : Vertex k → Bool → Vertex k
  | .a i, false =>
    if h : i.val = 0 then .boundary .a0
    else .a ⟨i.val - 1, by have := i.isLt; omega⟩
  | .a i, true =>
    if h : i.val + 1 < k then .a ⟨i.val + 1, h⟩
    else .b ⟨k - 2, by omega⟩
  | .b i, false =>
    if h : i.val = 0 then source hk
    else .b ⟨i.val - 1, by have := i.isLt; omega⟩
  | .b i, true =>
    if h : i.val = 0 then .boundary .c0
    else .c ⟨i.val - 1, by have := i.isLt; omega⟩
  | .c i, false =>
    if h : i.val = 0 then .boundary .b0
    else .b ⟨i.val - 1, by have := i.isLt; omega⟩
  | .c i, true =>
    if h : i.val = 0 then .boundary .c0
    else .c ⟨i.val - 1, by have := i.isLt; omega⟩
  | .boundary _, false => nearSource hk
  | .boundary _, true => lowerTop k
  | .lower j, false =>
    if h : j.val = 0 then .sink false else source hk
  | .lower j, true =>
    if h : j.val = 0 then .sink true
    else .lower ⟨j.val - 1, by have := j.isLt; omega⟩
  | .sink s, _ => .sink s

def network (hk : 3 ≤ k) : Partials.Interface.OrderedRotorNetwork (Vertex k) where
  slotCount := fun _ => 2
  slots_positive := fun _ => by decide
  successor := fun v slot => next hk v (decide (slot.val = 1))
  sink := IsSink
  sink_fixed := by
    intro v hv slot
    cases v <;> simp_all [IsSink, next]

theorem network_binary (hk : 3 ≤ k) :
    Partials.Interface.IsBinaryRotorNetwork (network hk) := by
  intro v
  rfl

theorem network_even_successor (hk : 3 ≤ k) (v : Vertex k) :
    (network hk).successor v ⟨0, by change 0 < 2; decide⟩ = next hk v false := by rfl

theorem network_odd_successor (hk : 3 ≤ k) (v : Vertex k) :
    (network hk).successor v ⟨1, by change 1 < 2; decide⟩ = next hk v true := by rfl

theorem next_distinct (hk : 3 ≤ k) (v : Vertex k) (hv : ¬ IsSink v) :
    next hk v false ≠ next hk v true := by
  cases v <;> simp_all only [IsSink, not_true_eq_false]
  all_goals simp only [next]
  all_goals try split_ifs
  all_goals simp_all [source, nearSource, lowerTop]
  all_goals intro h
  all_goals simp only [Vertex.a.injEq] at h
  all_goals have hh := congrArg Fin.val h
  all_goals simp only [Fin.val_mk] at hh
  all_goals omega

/-- The sum equivalence exposes the finite cardinality without counting a
cut boundary as an original sink. -/
def vertexEquiv (k : ℕ) : Vertex k ≃
    (Fin k ⊕ (Fin (k - 1) ⊕ (Fin (k - 2) ⊕
      (NamedOutput ⊕ (Fin (k + 3) ⊕ Bool))))) where
  toFun
    | .a i => .inl i
    | .b i => .inr (.inl i)
    | .c i => .inr (.inr (.inl i))
    | .boundary t => .inr (.inr (.inr (.inl t)))
    | .lower j => .inr (.inr (.inr (.inr (.inl j))))
    | .sink s => .inr (.inr (.inr (.inr (.inr s))))
  invFun
    | .inl i => .a i
    | .inr (.inl i) => .b i
    | .inr (.inr (.inl i)) => .c i
    | .inr (.inr (.inr (.inl t))) => .boundary t
    | .inr (.inr (.inr (.inr (.inl j)))) => .lower j
    | .inr (.inr (.inr (.inr (.inr s)))) => .sink s
  left_inv := by intro v; cases v <;> rfl
  right_inv := by
    intro v
    rcases v with i | i | i | t | j | s <;> rfl

theorem vertex_count (hk : 3 ≤ k) : Fintype.card (Vertex k) = 4 * k + 5 := by
  rw [Fintype.card_congr (vertexEquiv k)]
  have hc : Fintype.card NamedOutput = 3 := by decide
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool, hc]
  omega

def nonSinkEquiv (k : ℕ) : {v : Vertex k // ¬ IsSink v} ≃
    (Fin k ⊕ (Fin (k - 1) ⊕ (Fin (k - 2) ⊕
      (NamedOutput ⊕ Fin (k + 3))))) where
  toFun v := match v with
    | ⟨.a i, _⟩ => .inl i
    | ⟨.b i, _⟩ => .inr (.inl i)
    | ⟨.c i, _⟩ => .inr (.inr (.inl i))
    | ⟨.boundary t, _⟩ => .inr (.inr (.inr (.inl t)))
    | ⟨.lower j, _⟩ => .inr (.inr (.inr (.inr j)))
    | ⟨.sink _, h⟩ => False.elim (h trivial)
  invFun
    | .inl i => ⟨.a i, by simp [IsSink]⟩
    | .inr (.inl i) => ⟨.b i, by simp [IsSink]⟩
    | .inr (.inr (.inl i)) => ⟨.c i, by simp [IsSink]⟩
    | .inr (.inr (.inr (.inl t))) => ⟨.boundary t, by simp [IsSink]⟩
    | .inr (.inr (.inr (.inr j))) => ⟨.lower j, by simp [IsSink]⟩
  left_inv := by
    rintro ⟨v, hv⟩
    cases v <;> first | rfl | exact False.elim (hv trivial)
  right_inv := by
    intro v
    rcases v with i | i | i | t | j <;> rfl

theorem nonsink_count (hk : 3 ≤ k) :
    Fintype.card {v : Vertex k // ¬ IsSink v} = 4 * k + 3 := by
  rw [Fintype.card_congr (nonSinkEquiv k)]
  have hc : Fintype.card NamedOutput = 3 := by decide
  simp only [Fintype.card_sum, Fintype.card_fin, hc]
  omega

def distance : Vertex k → ℕ
  | .sink _ => 0
  | .lower j => j.val + 1
  | .boundary _ => k + 4
  | .a i => k + 5 + i.val
  | .b i => k + 5 + i.val
  | .c i => k + 5 + i.val

def Edge (hk : 3 ≤ k) (v w : Vertex k) : Prop :=
  ∃ slot : Bool, next hk v slot = w

theorem edge_decreases_at_most_one (hk : 3 ≤ k) {v w : Vertex k}
    (h : Edge hk v w) : distance v ≤ distance w + 1 := by
  obtain ⟨slot, rfl⟩ := h
  cases v <;> cases slot <;> simp only [next]
  all_goals try split_ifs
  all_goals simp_all [distance, source, nearSource, lowerTop]
  all_goals omega

theorem nonsink_descent (hk : 3 ≤ k) (v : Vertex k) (hv : ¬ IsSink v) :
    ∃ w, Edge hk v w ∧ distance v = distance w + 1 := by
  cases v with
  | a i =>
    refine ⟨next hk (.a i) false, ⟨false, rfl⟩, ?_⟩
    simp only [next]
    split_ifs <;> simp_all [distance] <;> omega
  | b i =>
    by_cases hi : i.val = 0
    · exact ⟨.boundary .c0, ⟨true, by simp [next, hi]⟩,
        by simp [distance, hi]⟩
    · refine ⟨next hk (.b i) false, ⟨false, rfl⟩, ?_⟩
      simp [next, hi, distance]
      omega
  | c i =>
    refine ⟨next hk (.c i) false, ⟨false, rfl⟩, ?_⟩
    simp only [next]
    split_ifs <;> simp_all [distance] <;> omega
  | boundary t =>
    exact ⟨lowerTop k, ⟨true, rfl⟩, by simp [distance, lowerTop]⟩
  | lower j =>
    by_cases hj : j.val = 0
    · exact ⟨.sink true, ⟨true, by simp [next, hj]⟩, by simp [distance, hj]⟩
    · refine ⟨.lower ⟨j.val - 1, by have := j.isLt; omega⟩,
        ⟨true, by simp [next, hj]⟩, ?_⟩
      simp only [distance]
      omega
  | sink s => exact False.elim (hv trivial)

inductive Walk (hk : 3 ≤ k) : Vertex k → Vertex k → ℕ → Prop where
  | nil (v) : Walk hk v v 0
  | cons {u v w n} : Edge hk u v → Walk hk v w n → Walk hk u w (n + 1)

def Reachable (hk : 3 ≤ k) (v w : Vertex k) : Prop := ∃ n, Walk hk v w n

theorem Walk.append (p : Walk hk u v n) (q : Walk hk v w m) :
    Walk hk u w (n + m) := by
  induction p with
  | nil => simpa using q
  | cons h p ih =>
    convert Walk.cons h (ih q) using 1 <;> omega

theorem Reachable.refl (v : Vertex k) : Reachable hk v v := ⟨0, .nil v⟩
theorem Reachable.single (h : Edge hk v w) : Reachable hk v w :=
  ⟨1, .cons h (.nil w)⟩
theorem Reachable.trans (h : Reachable hk u v) (h' : Reachable hk v w) :
    Reachable hk u w := by
  obtain ⟨n, p⟩ := h
  obtain ⟨m, q⟩ := h'
  exact ⟨n + m, p.append q⟩

theorem walk_distance_bound (p : Walk hk v w n) : distance v ≤ distance w + n := by
  induction p with
  | nil => omega
  | cons h p ih =>
    have hlocal := edge_decreases_at_most_one hk h
    omega

theorem sink_path_exact (hk : 3 ≤ k) (v : Vertex k) :
    ∃ s, Walk hk v (.sink s) (distance v) := by
  suffices h : ∀ n, ∀ v : Vertex k, distance v = n →
      ∃ s, Walk hk v (.sink s) n by exact h _ v rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v hn
    by_cases hv : IsSink v
    · cases v with
      | sink s =>
        have hz : n = 0 := by simpa [distance] using hn.symm
        subst n
        exact ⟨s, Walk.nil _⟩
      | a i => exact False.elim hv
      | b i => exact False.elim hv
      | c i => exact False.elim hv
      | boundary t => exact False.elim hv
      | lower j => exact False.elim hv
    · obtain ⟨w, he, hd⟩ := nonsink_descent hk v hv
      have hw : distance w < n := by omega
      obtain ⟨s, p⟩ := ih (distance w) hw w rfl
      exact ⟨s, by simpa [← hn, hd] using Walk.cons he p⟩

/-- The natural `distance` is a shortest distance to either original sink. -/
theorem true_shortest_distance (hk : 3 ≤ k) (v : Vertex k) :
    (∃ s, Walk hk v (.sink s) (distance v)) ∧
    (∀ s n, Walk hk v (.sink s) n → distance v ≤ n) := by
  refine ⟨sink_path_exact hk v, ?_⟩
  intro s n p
  simpa [distance] using walk_distance_bound p

private theorem chain_reachable (hk : 3 ≤ k) (n : ℕ) (hn : 0 < n)
    (tag : Fin n → Vertex k)
    (hd : ∀ i : Fin n, 0 < i.val →
      Edge hk (tag i) (tag ⟨i.val - 1, by have := i.isLt; omega⟩))
    (i : Fin n) : Reachable hk (tag ⟨n - 1, by omega⟩) (tag i) := by
  have aux : ∀ r, ∀ i : Fin n, i.val + r = n - 1 →
      Reachable hk (tag ⟨n - 1, by omega⟩) (tag i) := by
    intro r
    induction r with
    | zero =>
      intro i hi
      have he : i = ⟨n - 1, by omega⟩ := Fin.ext (by omega)
      rw [he]
      exact Reachable.refl _
    | succ r ih =>
      intro i hi
      let j : Fin n := ⟨i.val + 1, by omega⟩
      have hj : j.val + r = n - 1 := by dsimp [j]; omega
      have hpos : 0 < j.val := by dsimp [j]; omega
      have he : (⟨j.val - 1, by have := j.isLt; omega⟩ : Fin n) = i := by
        apply Fin.ext
        simp [j]
      exact (ih j hj).trans (by simpa [he] using Reachable.single (hd j hpos))
  exact aux (n - 1 - i.val) i (by have := i.isLt; omega)

theorem source_reaches_every_vertex (hk : 3 ≤ k) (v : Vertex k) :
    Reachable hk (source hk) v := by
  have ha : ∀ i : Fin k, Reachable hk (source hk) (.a i) := by
    intro i
    apply chain_reachable hk k (by omega) Vertex.a _ i
    intro j hj
    exact ⟨false, by simp [next, show j.val ≠ 0 by omega]⟩
  have hbtop : Reachable hk (source hk) (.b ⟨k - 2, by omega⟩) :=
    Reachable.single ⟨true, by
      simp [next, source, show ¬ (k - 1 + 1 < k) by omega]⟩
  have hb : ∀ i : Fin (k - 1), Reachable hk (source hk) (.b i) := by
    intro i
    refine hbtop.trans ?_
    have hc := chain_reachable hk (k - 1) (by omega) Vertex.b
      (fun j hj => ⟨false, by simp [next, show j.val ≠ 0 by omega]⟩) i
    simpa only [show k - 1 - 1 = k - 2 by omega] using hc
  have hc : ∀ i : Fin (k - 2), Reachable hk (source hk) (.c i) := by
    intro i
    let j : Fin (k - 1) := ⟨i.val + 1, by have := i.isLt; omega⟩
    refine (hb j).trans (Reachable.single ⟨true, ?_⟩)
    simp [next, j]
  have ht : ∀ t, Reachable hk (source hk) (.boundary t) := by
    intro t
    cases t with
    | a0 => exact (ha ⟨0, by omega⟩).trans (Reachable.single ⟨false, by simp [next]⟩)
    | b0 => exact (hc ⟨0, by omega⟩).trans (Reachable.single ⟨false, by simp [next]⟩)
    | c0 => exact (hb ⟨0, by omega⟩).trans (Reachable.single ⟨true, by simp [next]⟩)
  have hlt : Reachable hk (source hk) (lowerTop k) :=
    (ht .a0).trans (Reachable.single ⟨true, rfl⟩)
  have hl : ∀ j : Fin (k + 3), Reachable hk (source hk) (.lower j) := by
    intro j
    refine hlt.trans ?_
    have hchain := chain_reachable hk (k + 3) (by omega) Vertex.lower
      (fun i hi => ⟨true, by simp [next, show i.val ≠ 0 by omega]⟩) j
    simpa [lowerTop] using hchain
  cases v with
  | a i => exact ha i
  | b i => exact hb i
  | c i => exact hc i
  | boundary t => exact ht t
  | lower j => exact hl j
  | sink s =>
    cases s
    · exact (hl ⟨0, by omega⟩).trans (Reachable.single ⟨false, by simp [next]⟩)
    · exact (hl ⟨0, by omega⟩).trans (Reachable.single ⟨true, by simp [next]⟩)

/-- Distinct places in one distance level. This code is deliberately not a
global injection: upper a/b/c may share a distance, and sinks use 0/1. -/
def layerCode : Vertex k → Fin 3
  | .a _ => 0
  | .b _ => 1
  | .c _ => 2
  | .lower _ => 0
  | .boundary .a0 => 0
  | .boundary .b0 => 1
  | .boundary .c0 => 2
  | .sink false => 0
  | .sink true => 1

theorem same_distance_layerCode (v w : Vertex k)
    (hd : distance v = distance w) (hc : layerCode v = layerCode w) : v = w := by
  cases v <;> cases w
  all_goals try cases_type* NamedOutput Bool
  all_goals simp_all [distance, layerCode]
  all_goals first | rfl | omega | (apply Fin.ext; omega) |
    (congr 1; apply Fin.ext; omega)

theorem width_at_most_three (k n : ℕ) :
    Fintype.card {v : Vertex k // distance v = n} ≤ 3 := by
  let f : {v : Vertex k // distance v = n} → Fin 3 := fun v => layerCode v.val
  have hf : Function.Injective f := by
    intro v w h
    apply Subtype.ext
    exact same_distance_layerCode v.val w.val
      (v.property.trans w.property.symm) h
  simpa using Fintype.card_le_of_injective f hf

/-! Small self-contained legal-execution vocabulary. This is not an arbitrary
Even policy. Each step uses the current rotor slot, then toggles precisely the
departing vertex. The complete all-even run is not assumed to exist. -/
structure Configuration (k : ℕ) where
  position : Vertex k
  phase : Vertex k → Bool

def allEvenSource (hk : 3 ≤ k) : Configuration k := ⟨source hk, fun _ => false⟩

structure Event (k : ℕ) where
  «from» : Vertex k
  «to» : Vertex k
  slot : Bool
  deriving DecidableEq

def fire (hk : 3 ≤ k) (C : Configuration k) : Configuration k :=
  ⟨next hk C.position (C.phase C.position),
    fun v => if v = C.position then !(C.phase v) else C.phase v⟩

def firingEvent (hk : 3 ≤ k) (C : Configuration k) : Event k :=
  ⟨C.position, (fire hk C).position, C.phase C.position⟩

inductive Execution (hk : 3 ≤ k) : Configuration k → Configuration k →
    List (Event k) → Prop where
  | nil (C) : Execution hk C C []
  | cons {C D events} : ¬ IsSink C.position →
      Execution hk (fire hk C) D events →
      Execution hk C D (firingEvent hk C :: events)

def CompleteAllEven (hk : 3 ≤ k) (D : Configuration k) (events : List (Event k)) : Prop :=
  Execution hk (allEvenSource hk) D events ∧ IsSink D.position

theorem first_lower_departure_zero (hk : 3 ≤ k) (C : Configuration k)
    (hp : C.position = lowerOne k) (hr : C.phase (lowerOne k) = false) :
    (fire hk C).position = .sink false := by
  change next hk C.position (C.phase C.position) = .sink false
  rw [hp, hr]
  simp [lowerOne, next]

/-- First-visit preservation is an operational lemma, not a count law. -/
theorem phase_unchanged_when_unvisited {k : ℕ} {hk : 3 ≤ k}
    {C D : Configuration k} {events : List (Event k)}
    (p : Execution hk C D events) (v : Vertex k)
    (h : ∀ e ∈ events, e.from ≠ v) : D.phase v = C.phase v := by
  revert h
  induction p with
  | nil => intro h; rfl
  | @cons C D events hns p ih =>
    intro h
    have hp : C.position ≠ v := by
      simpa [firingEvent] using h (firingEvent hk C) (by simp)
    have ht : ∀ e ∈ events, e.from ≠ v := by
      intro e he
      exact h e (by simp [he])
    rw [ih ht]
    simp [fire, Ne.symm hp]

theorem nonsink_next_one_iff (hk : 3 ≤ k) (v : Vertex k) (slot : Bool)
    (hv : ¬ IsSink v) :
    next hk v slot = .sink true ↔ v = lowerOne k ∧ slot = true := by
  cases v <;> cases slot <;> simp only [next]
  all_goals try split_ifs
  all_goals simp_all [IsSink, lowerOne, source, nearSource, lowerTop]
  all_goals first | (apply Fin.ext; omega) | (simp only [Fin.ext_iff]; omega)

def ZeroInvariant (C : Configuration k) : Prop :=
  C.position ≠ .sink true ∧
    (C.position = .sink false ∨ C.phase (lowerOne k) = false)

theorem allEven_zeroInvariant (hk : 3 ≤ k) : ZeroInvariant (allEvenSource hk) := by
  simp [ZeroInvariant, allEvenSource, source]

theorem fire_zeroInvariant {k : ℕ} {C : Configuration k} {hk : 3 ≤ k}
    (h : ZeroInvariant C) (hns : ¬ IsSink C.position) :
    ZeroInvariant (fire hk C) := by
  have hnotzero : C.position ≠ .sink false := by
    intro hp
    exact hns (by simp [hp, IsSink])
  have hr : C.phase (lowerOne k) = false := h.2.resolve_left hnotzero
  have hnotone : (fire hk C).position ≠ .sink true := by
    intro hone
    obtain ⟨hp, hphase⟩ := (nonsink_next_one_iff hk C.position
      (C.phase C.position) hns).mp hone
    have : C.phase C.position = false := by simpa [hp] using hr
    simp_all
  refine ⟨hnotone, ?_⟩
  by_cases hp : C.position = lowerOne k
  · exact Or.inl (first_lower_departure_zero hk C hp hr)
  · right
    simp [fire, Ne.symm hp, hr]

theorem execution_zeroInvariant (p : Execution hk C D events)
    (h : ZeroInvariant C) : ZeroInvariant D := by
  revert h
  induction p with
  | nil => intro h; exact h
  | cons hns p ih =>
    intro h
    exact ih (fire_zeroInvariant h hns)

/-- Every finite legal all-even source execution that has reached a sink has
reached sink 0. Termination/existence is a separate duty. -/
theorem complete_allEven_terminal_zero (hk : 3 ≤ k) {D : Configuration k}
    {events : List (Event k)} (h : CompleteAllEven hk D events) :
    D.position = .sink false := by
  have hi := execution_zeroInvariant h.1 (allEven_zeroInvariant hk)
  rcases h with ⟨_, hs⟩
  cases hp : D.position with
  | a i => exact False.elim (by simpa [hp, IsSink] using hs)
  | b i => exact False.elim (by simpa [hp, IsSink] using hs)
  | c i => exact False.elim (by simpa [hp, IsSink] using hs)
  | boundary t => exact False.elim (by simpa [hp, IsSink] using hs)
  | lower j => exact False.elim (by simpa [hp, IsSink] using hs)
  | sink s =>
    cases s with
    | false => rfl
    | true => exact False.elim (hi.1 hp)

def IsBoundaryDeparture (e : Event k) : Bool :=
  match e.from with | .boundary _ => true | _ => false

/-- Exact pending trajectory statement: the b_1→a_k event is internal, and
exactly one boundary departure precedes it, so it lies in excursion two. -/
def SecondExcursionFeedback (hk : 3 ≤ k) (events : List (Event k)) : Prop :=
  ∃ pre post, events = pre ++
    (⟨.b ⟨0, by omega⟩, source hk, false⟩ : Event k) :: post ∧
    (pre.filter IsBoundaryDeparture).length = 1

def IsExternalE (hk : 3 ≤ k) (e : Event k) : Bool :=
  match e.from with
  | .lower j => decide (0 < j.val) && decide (e.to = source hk)
  | _ => false

def IsExternalF (hk : 3 ≤ k) (e : Event k) : Bool :=
  match e.from with
  | .boundary _ => decide (e.to = nearSource hk)
  | _ => false

def externalBatch (hk : 3 ≤ k) (events : List (Event k)) : Batch :=
  ⟨1 + (events.filter (IsExternalE hk)).length,
    (events.filter (IsExternalF hk)).length⟩

theorem initial_source_externalE_positive (hk : 3 ≤ k) (events : List (Event k)) :
    0 < (externalBatch hk events).N := by
  simp [externalBatch]

theorem feedback_is_not_external_entry (hk : 3 ≤ k) :
    let e : Event k := ⟨.b ⟨0, by omega⟩, source hk, false⟩
    IsExternalE hk e = false ∧ IsExternalF hk e = false := by
  exact ⟨rfl, rfl⟩

def boundaryReturns (events : List (Event k)) : NamedCounts :=
  let count (t : NamedOutput) :=
    (events.filter (fun e => decide (e.to = .boundary t))).length
  ⟨count .a0, count .b0, count .c0⟩

/- The following are specifications of unfinished operational duties, not
axioms, structure fields, or exported theorems asserting those conclusions. -/
def TerminationDuty (hk : 3 ≤ k) : Prop :=
  ∃ D events, CompleteAllEven hk D events

def TerminalZeroDuty (hk : 3 ≤ k) : Prop :=
  ∀ D events, CompleteAllEven hk D events → D.position = .sink false

theorem terminalZeroDuty (hk : 3 ≤ k) : TerminalZeroDuty hk := by
  intro D events h
  exact complete_allEven_terminal_zero hk h

def BothPortsDuty (hk : 3 ≤ k) : Prop :=
  ∀ D events, CompleteAllEven hk D events →
    0 < (externalBatch hk events).N ∧ 0 < (externalBatch hk events).M

def SecondExcursionDuty (hk : 3 ≤ k) : Prop :=
  ∀ D events, CompleteAllEven hk D events → SecondExcursionFeedback hk events

end Partials.Arrival.Physical
