import Partials.Parity.Model

/-! Integral DBM source, compilation.tex P1-L07 (lines 487--529).
Exact elimination and one-variable extension are proved below as unexecuted
Lean text. Shortest-path feasibility and the executable graph decoder remain
explicit duties. There is no real relaxation or integer-programming oracle. -/

namespace Partials.Parity.CompilerSource

structure DifferenceBound (Variable : Type*) where
  left : Variable
  right : Variable
  constant : Int

def BoundSatisfied {V : Type*} (x : V → Int) (b : DifferenceBound V) : Prop :=
  x b.left - x b.right ≤ b.constant

abbrev DBM (V : Type*) := List (DifferenceBound V)

def DBMSatisfied {V : Type*} (constraints : DBM V) (x : V → Int) : Prop :=
  ∀ b ∈ constraints, BoundSatisfied x b

theorem dbm_intersection_exact {V : Type*} (a b : DBM V) (x : V → Int) :
    DBMSatisfied (a ++ b) x ↔ DBMSatisfied a x ∧ DBMSatisfied b x := by
  simp only [DBMSatisfied, List.mem_append]
  constructor
  · intro h
    exact ⟨fun c hc => h c (Or.inl hc), fun c hc => h c (Or.inr hc)⟩
  · rintro ⟨ha, hb⟩ c (hc | hc)
    · exact ha c hc
    · exact hb c hc

def BetweenLists (lower upper : List Int) (z : Int) : Prop :=
  (∀ l ∈ lower, l ≤ z) ∧ ∀ u ∈ upper, z ≤ u

def PairBounds (lower upper : List Int) : Prop :=
  ∀ l ∈ lower, ∀ u ∈ upper, l ≤ u

/-- Empty upper lists give zero. With only upper bounds, repeated `min`
constructs a finite endpoint; this does not presume a lower bound exists. -/
def onlyUpperWitness : List Int → Int
  | [] => 0
  | u :: us => min u (onlyUpperWitness us)

theorem onlyUpperWitness_valid (upper : List Int) :
    ∀ u ∈ upper, onlyUpperWitness upper ≤ u := by
  induction upper with
  | nil => simp
  | cons a as ih =>
      intro u hu
      simp only [List.mem_cons] at hu
      rcases hu with rfl | hu
      · exact min_le_left _ _
      · exact le_trans (min_le_right _ _) (ih u hu)

/-- Repeated `max` extends the one-sided witness. This works when either
side, both sides, or neither side is present. -/
def intervalWitness (lower upper : List Int) : Int :=
  lower.foldr max (onlyUpperWitness upper)

theorem intervalWitness_valid (lower upper : List Int)
    (hpair : PairBounds lower upper) :
    BetweenLists lower upper (intervalWitness lower upper) := by
  revert hpair
  induction lower with
  | nil =>
      intro hpair
      exact ⟨by simp, onlyUpperWitness_valid upper⟩
  | cons a as ih =>
      intro hpair
      have htail : PairBounds as upper := by
        intro l hl u hu
        exact hpair l (by simp [hl]) u hu
      obtain ⟨hlo, hup⟩ := ih htail
      constructor
      · intro l hl
        simp only [List.mem_cons] at hl
        rcases hl with rfl | hl
        · exact le_max_left _ _
        · exact le_trans (hlo l hl) (le_max_right _ _)
      · intro u hu
        exact max_le (hpair a (by simp) u hu) (hup u hu)

theorem between_iff_pairBounds (lower upper : List Int) :
    (∃ z : Int, BetweenLists lower upper z) ↔ PairBounds lower upper := by
  constructor
  · rintro ⟨z, hlo, hup⟩ l hl u hu
    exact le_trans (hlo l hl) (hup u hu)
  · intro h
    exact ⟨intervalWitness lower upper, intervalWitness_valid lower upper h⟩

/-- A frame retains all bounds away from z. A lower pair `(j,a)` encodes
`x_j-z ≤ a`; an upper pair `(k,b)` encodes `z-x_k ≤ b`.
Self-bounds `z-z ≤ c` are retained separately and require `0 ≤ c`. -/
structure EliminationFrame (V : Type*) where
  retained : DBM V
  lower : List (V × Int)
  upper : List (V × Int)
  selfBounds : List Int

def lowerEndpoints {V : Type*} (F : EliminationFrame V) (x : V → Int) : List Int :=
  F.lower.map (fun ja => x ja.1 - ja.2)

def upperEndpoints {V : Type*} (F : EliminationFrame V) (x : V → Int) : List Int :=
  F.upper.map (fun kb => x kb.1 + kb.2)

def FrameSatisfied {V : Type*} (F : EliminationFrame V) (x : V → Int)
    (z : Int) : Prop :=
  DBMSatisfied F.retained x ∧
  (∀ c ∈ F.selfBounds, 0 ≤ c) ∧
  BetweenLists (lowerEndpoints F x) (upperEndpoints F x) z

def ProjectedFrame {V : Type*} (F : EliminationFrame V) (x : V → Int) : Prop :=
  DBMSatisfied F.retained x ∧
  (∀ c ∈ F.selfBounds, 0 ≤ c) ∧
  PairBounds (lowerEndpoints F x) (upperEndpoints F x)

theorem one_variable_projection_exact {V : Type*} (F : EliminationFrame V)
    (x : V → Int) :
    (∃ z : Int, FrameSatisfied F x z) ↔ ProjectedFrame F x := by
  constructor
  · rintro ⟨z, hr, hs, hz⟩
    exact ⟨hr, hs, (between_iff_pairBounds _ _).mp ⟨z, hz⟩⟩
  · rintro ⟨hr, hs, hp⟩
    exact ⟨intervalWitness (lowerEndpoints F x) (upperEndpoints F x),
      hr, hs, intervalWitness_valid _ _ hp⟩

theorem paired_bound_is_difference (xj xk a b : Int) :
    xj - a ≤ xk + b ↔ xj - xk ≤ a + b := by omega

theorem projected_frame_recovery {V : Type*} (F : EliminationFrame V)
    (x : V → Int) (h : ProjectedFrame F x) :
    FrameSatisfied F x
      (intervalWitness (lowerEndpoints F x) (upperEndpoints F x)) := by
  exact ⟨h.1, h.2.1, intervalWitness_valid _ _ h.2.2⟩

/-- Eliminations compose by existential reassociation; reconstruction is
necessarily in reverse elimination order and shares the retained tuple. -/
theorem two_stage_extension {X Z W : Type*}
    (R : X → Z → W → Prop) (middle : X → Z → Prop)
    (outer : X → Prop)
    (hfirst : ∀ x z, middle x z ↔ ∃ w, R x z w)
    (hsecond : ∀ x, outer x ↔ ∃ z, middle x z) :
    ∀ x, outer x ↔ ∃ z w, R x z w := by
  intro x
  rw [hsecond]
  simp only [hfirst]

/-- The constraint-graph convention is k→j for x_j-x_k≤c. A concrete
finite graph must prove path telescoping, shortest integral potentials and
negative-cycle detection. This target imports none of those facts. -/
def DBMPotentialDuty {V : Type*} [Fintype V] (zero : V)
    (negativeCycle : DBM V → Prop) : Prop :=
  ∀ constraints : DBM V,
    (∃ x : V → Int, x zero = 0 ∧ DBMSatisfied constraints x) ↔
      ¬ negativeCycle constraints

/-- Decoder must split every actual bound into exactly one frame case;
in particular anchor coordinates and nonnegative self-bounds cannot vanish. -/
def EliminationDecoderDuty {V : Type*}
    (decode : DBM (Option V) → EliminationFrame V) : Prop :=
  ∀ constraints x z,
    DBMSatisfied constraints (fun v => match v with
      | none => z
      | some i => x i) ↔ FrameSatisfied (decode constraints) x z

end Partials.Parity.CompilerSource
