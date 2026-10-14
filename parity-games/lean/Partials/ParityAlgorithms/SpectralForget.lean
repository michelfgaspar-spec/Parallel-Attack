import Partials.ParityAlgorithms.ReturnSpectra

/-! P6-F/N/R/C/rho on full attained spectra. Formula source and weighted
boundary-path lemmas are supplied; the original-walk decomposition/infinite
block bridge remains an exact duty. No desired forget/reconstruction identity
is used as an axiom or as proof of its own target. -/
namespace Partials.ParityAlgorithms.Spectra
open Partials.Parity
open Partials.ParityAlgorithms

variable {V EdgeId : Type*} [DecidableEq V]

def forgetWeight (h : Record V EdgeId) (z u v : V) (p : Priority5) : Prop :=
  p ∈ h.spectrum u v ∨ ∃ a ∈ h.spectrum u z, ∃ b ∈ h.spectrum z v,
    ∃ c : Priority5, (c = 0 ∨ c ∈ h.spectrum z z) ∧ p = priorityJoin a (priorityJoin c b)

def forgetNoReturn (h : Record V EdgeId) (z u : V) (e : Fin 2) : Prop :=
  h.noReturn u e ∨ ((h.spectrum u z).Nonempty ∧
    (h.noReturn z e ∨ ∃ p ∈ h.spectrum z z, p.val % 2 = e.val))

noncomputable def forgetRecord (h : Record V EdgeId) (z : V) : Record V EdgeId where
  boundary := h.boundary.erase z
  beta v := if v ∈ h.boundary.erase z then h.beta v else none
  spectrum u v := {p | u ∈ h.boundary.erase z ∧ v ∈ h.boundary.erase z ∧ forgetWeight h z u v p}
  noReturn u e := u ∈ h.boundary.erase z ∧ forgetNoReturn h z u e

theorem forget_keeps_old_weight (h : Record V EdgeId) (z u v : V) (p : Priority5)
    (hu : u ∈ h.boundary.erase z) (hv : v ∈ h.boundary.erase z)
    (hp : p ∈ h.spectrum u v) : p ∈ (forgetRecord h z).spectrum u v :=
  ⟨hu,hv,Or.inl hp⟩

theorem forget_keeps_old_noReturn (h : Record V EdgeId) (z u : V) (e : Fin 2)
    (hu : u ∈ h.boundary.erase z) (he : h.noReturn u e) :
    (forgetRecord h z).noReturn u e := ⟨hu,Or.inl he⟩

theorem forget_zero_is_no_middle_loop (h : Record V EdgeId) (z u v : V)
    (a b : Priority5) (ha : a ∈ h.spectrum u z) (hb : b ∈ h.spectrum z v) :
    forgetWeight h z u v (priorityJoin a b) := by
  refine Or.inr ⟨a,ha,b,hb,0,Or.inl rfl,?_⟩
  rw [priorityJoin_zero]

theorem boundaryEdge_restrict {G : VertexArena V EdgeId} (σ : OriginalPolicy G)
    (c : Finset V) (z v : V) (hv : v ∈ c.erase z) :
    boundaryEdge σ (c.erase z) v = boundaryEdge σ c v := by
  classical
  have hvc : v ∈ c := Finset.mem_of_mem_erase hv
  by_cases he : G.even v = true
  · simp [boundaryEdge, hv, hvc, he]
  · simp [boundaryEdge, he]

/-- Reflexive paths are auxiliary; they are never inserted in spectrum. -/
inductive ThresholdReach (h : Record V EdgeId) (p : Nat) : V → V → Prop where
  | refl (u) : ThresholdReach h p u u
  | step {u v w} (a : Priority5) (ha : a ∈ h.spectrum u v) (bound : a.val ≤ p)
      (tail : ThresholdReach h p v w) : ThresholdReach h p u w

inductive BoundaryPath (h : Record V EdgeId) : V → V → Nat → Bool → Prop where
  | nil (u) : BoundaryPath h u u 0 false
  | cons {u v w b positive} (a : Priority5) (ha : a ∈ h.spectrum u v)
      (tail : BoundaryPath h v w b positive) : BoundaryPath h u w (max a.val b) true

theorem boundaryPath_append (h : Record V EdgeId) {u v w : V} {a b : Nat} {s t : Bool}
    (ha : BoundaryPath h u v a s) (hb : BoundaryPath h v w b t) :
    BoundaryPath h u w (max a b) (s || t) := by
  induction ha with
  | nil u => simpa using hb
  | @cons u x v c positive p hp tail ih =>
    simpa [max_assoc] using BoundaryPath.cons p hp (ih hb)

theorem thresholdReach_path (h : Record V EdgeId) (p : Nat) {u v : V}
    (hr : ThresholdReach h p u v) :
    ∃ m s, BoundaryPath h u v m s ∧ m ≤ p := by
  induction hr with
  | refl u => exact ⟨0,false,BoundaryPath.nil u,Nat.zero_le p⟩
  | @step u v w a ha hbound tail ih =>
    obtain ⟨m,s,hm,hmp⟩ := ih
    exact ⟨max a.val m,true,BoundaryPath.cons a ha hm,max_le hbound hmp⟩

theorem boundaryPath_threshold (h : Record V EdgeId) {u v : V} {m p : Nat} {s : Bool}
    (hp : BoundaryPath h u v m s) (hmp : m ≤ p) : ThresholdReach h p u v := by
  induction hp with
  | nil u => exact ThresholdReach.refl u
  | cons a ha tail ih =>
    exact ThresholdReach.step a ha (le_trans (le_max_left _ _) hmp)
      (ih (le_trans (le_max_right _ _) hmp))

def repeatedWeights (h : Record V EdgeId) (u v : V) : Set Priority5 :=
  {p | ∃ x y, ThresholdReach h p.val u x ∧ p ∈ h.spectrum x y ∧ ThresholdReach h p.val y v}

/-- The designated edge forces positivity even for empty auxiliary paths. -/
theorem repeatedWeight_positive_path (h : Record V EdgeId) (u v : V) (p : Priority5)
    (hp : p ∈ repeatedWeights h u v) : BoundaryPath h u v p.val true := by
  obtain ⟨x,y,hux,hxy,hyv⟩ := hp
  obtain ⟨a,s,ha,hab⟩ := thresholdReach_path h p.val hux
  obtain ⟨b,t,hb,hbb⟩ := thresholdReach_path h p.val hyv
  have middle : BoundaryPath h x y p.val true := by
    simpa using BoundaryPath.cons p hxy (BoundaryPath.nil y)
  have joined := boundaryPath_append h (boundaryPath_append h ha middle) hb
  simpa [max_eq_right hab, max_eq_left hbb] using joined

/-- Every positive boundary path has a marked edge attaining its maximum;
its surrounding paths are threshold-bounded, with no empty-return artifact. -/
theorem positive_path_repeatedWeight (h : Record V EdgeId) {u v : V} {m : Nat}
    (hp : BoundaryPath h u v m true) :
    ∃ p : Priority5, p.val = m ∧ p ∈ repeatedWeights h u v := by
  have aux : ∀ {u v : V} {m : Nat} {positive : Bool},
      BoundaryPath h u v m positive → positive = true →
      ∃ p : Priority5, p.val = m ∧ p ∈ repeatedWeights h u v := by
    intro u v m positive path
    induction path with
    | nil u => intro hfalse; cases hfalse
    | @cons u x v b positive a ha tail ih =>
      intro _
      by_cases hab : b ≤ a.val
      · refine ⟨a,(max_eq_left hab).symm, u,x,ThresholdReach.refl u,ha,?_⟩
        exact boundaryPath_threshold h tail hab
      · have hba : a.val ≤ b := by omega
        cases positive with
        | false =>
          cases tail with
          | nil => omega
        | true =>
          obtain ⟨p,hpval,y,z,hxy,hyz,hzv⟩ := ih rfl
          refine ⟨p,by rw [max_eq_right hba]; exact hpval, y,z,?_,hyz,hzv⟩
          apply ThresholdReach.step a ha
          · simpa [hpval] using hba
          · exact hxy
  exact aux hp rfl

def unrestrictedReach (h : Record V EdgeId) : V → V → Prop := ThresholdReach h 4

def rawClosedFlag (h : Record V EdgeId) (u : V) (e : Fin 2) : Prop :=
  (∃ x, unrestrictedReach h u x ∧ h.noReturn x e) ∨
  ∃ x y p, unrestrictedReach h u x ∧ p ∈ h.spectrum x y ∧
    ThresholdReach h p.val y x ∧ p.val % 2 = e.val

noncomputable def reconstruct (h : Record V EdgeId) : MinimumKey V EdgeId where
  beta := h.beta
  first u v := minimumWeight (h.spectrum u v)
  repeated u v := minimumWeight (repeatedWeights h u v)
  noReturn := h.noReturn
  closedLoses u := u ∈ h.boundary ∧ rawClosedFlag h u 1

def ExactForgetTarget {G : VertexArena V EdgeId} (σ : OriginalPolicy G)
    (b : Finset V) (z : V) : Prop :=
  forgetRecord (attainedRecord σ b) z = attainedRecord σ (b.erase z)

def ExactReconstructionTarget {G : VertexArena V EdgeId}
    (σ : OriginalPolicy G) (c : Finset V) : Prop :=
  reconstruct (attainedRecord σ c) = trueKey σ c

/-- Primitive finite-block facts needed in the source recurrence argument.
These are bounds/attainment/coverage for actual finite maxima, with no
uniform block-length bound and no parity/recurrence conclusion assumed. -/
structure FiniteBlockMaxima (f : Nat → Nat) where
  start : Nat → Nat
  zero : start 0 = 0
  increasing : StrictMono start
  index_bound : ∀ i, i ≤ start i
  maximum : Nat → Nat
  dominates : ∀ i k, start i ≤ k → k ≤ start (i+1) → f k ≤ maximum i
  attained : ∀ i, ∃ k, start i ≤ k ∧ k ≤ start (i+1) ∧ f k = maximum i
  covers : ∀ k, ∃ i, start i ≤ k ∧ k ≤ start (i+1)

/-- Late maxima ≤ r follow from late original priorities ≤ r, even for
unbounded positive block lengths. -/
theorem block_eventual_bound (f : Nat → Nat) (b : FiniteBlockMaxima f)
    (r cutoff : Nat) (bound : ∀ k, cutoff ≤ k → f k ≤ r) :
    ∀ i, cutoff ≤ i → b.maximum i ≤ r := by
  intro i hi
  obtain ⟨k,hleft,hright,hvalue⟩ := b.attained i
  have hlate : cutoff ≤ k := le_trans hi (le_trans (b.index_bound i) hleft)
  simpa [hvalue] using bound k hlate

/-- Recurring r in the original stream gives arbitrarily late blocks with
maximum ≥r. A finite prefix of blocks cannot contain infinitely many visits. -/
theorem recurring_priority_late_block (f : Nat → Nat) (b : FiniteBlockMaxima f)
    (r : Nat) (hr : PriorityRecurs f r) (n : Nat) :
    ∃ i, n ≤ i ∧ r ≤ b.maximum i := by
  obtain ⟨k,hk,hvalue⟩ := hr (b.start n + 1)
  obtain ⟨i,hle,hright⟩ := b.covers k
  have hni : n ≤ i := by
    by_contra h
    have hin : i+1 ≤ n := by omega
    have htimes : b.start (i+1) ≤ b.start n := b.increasing.monotone hin
    omega
  exact ⟨i,hni,by rw [← hvalue]; exact b.dominates i k hle hright⟩

/-- Repeated maximum r supplies original r arbitrarily late, since every
block attains its finite maximum after its increasing starting time. -/
theorem recurring_block_priority (f : Nat → Nat) (b : FiniteBlockMaxima f)
    (r : Nat) (hr : PriorityRecurs b.maximum r) : PriorityRecurs f r := by
  intro n
  obtain ⟨i,hi,hmax⟩ := hr n
  obtain ⟨k,hleft,hright,hvalue⟩ := b.attained i
  exact ⟨k,le_trans hi (le_trans (b.index_bound i) hleft),hvalue.trans hmax⟩

/-- The central P6-L02 recurrent-maximum result is proved once an original
late bound is established. The finite-alphabet eventual-bound extraction
and construction of these actual block maxima are separate source duties. -/
theorem block_recurrent_maximum (f : Nat → Nat) (b : FiniteBlockMaxima f)
    (r cutoff : Nat) (hr : PriorityRecurs f r)
    (bound : ∀ k, cutoff ≤ k → f k ≤ r) :
    GreatestPriorityRecurs b.maximum r := by
  constructor
  · intro n
    obtain ⟨i,hi,hrmax⟩ := recurring_priority_late_block f b r hr (max n cutoff)
    have hcut : cutoff ≤ i := le_trans (le_max_right n cutoff) hi
    have hn : n ≤ i := le_trans (le_max_left n cutoff) hi
    exact ⟨i,hn,Nat.le_antisymm (block_eventual_bound f b r cutoff bound i hcut) hrmax⟩
  · intro q hq
    obtain ⟨i,hi,hvalue⟩ := hq cutoff
    simpa [hvalue] using block_eventual_bound f b r cutoff bound i hi

/-- This is a target only; the concrete walk/block lemmas below must be
proved before P6-T2/T3 can be promoted. No headline is a premise to itself. -/
def BoundedForgetReconstructionTarget {G : VertexArena V EdgeId} [Fintype V]
    [Fintype EdgeId] (σ : OriginalPolicy G) (f : LegalForget G) : Prop :=
  ExactForgetTarget σ f.old f.forgotten ∧
  ExactReconstructionTarget σ (f.old.erase f.forgotten) ∧
  reconstruct (forgetRecord (attainedRecord σ f.old) f.forgotten) =
    trueKey σ (f.old.erase f.forgotten)

/-- Primitive positive-walk split/splice obligation: prove finite walk
concatenation with max of *all* endpoint-inclusive priorities, split at all
successive boundary times, and preserve the same original selected edge at
all revisits. Then finite old z-loop maxima collapse to either neutral 0 or
one attained old loop weight. This is a quantified source goal, not data. -/
def FirstReturnDecompositionDuty {G : VertexArena V EdgeId} (σ : OriginalPolicy G)
    (b : Finset V) (z : V) : Prop :=
  ∀ u v p, u ∈ b.erase z → v ∈ b.erase z →
    FirstReturn σ (b.erase z) u v p ↔ forgetWeight (attainedRecord σ b) z u v p

/-- Infinite source bridge: histories with no/last/infinitely many z visits
must be decomposed and conversely expanded. Each block is finite positive;
lengths can be unbounded, and shared endpoints occur at most twice. Prove
recurrent original max = greatest recurrent block max, then select witnesses
by finite edge type under the unchanged original policy. -/
def InfiniteBoundaryBridgeDuty {G : VertexArena V EdgeId} (σ : OriginalPolicy G)
    (b : Finset V) (z : V) : Prop :=
  ∀ u e, u ∈ b.erase z →
    NoReturn σ (b.erase z) u e ↔ forgetNoReturn (attainedRecord σ b) z u e

/-- Marked finite path deletion and recurrent-vertex cycle deletion must
supply short original witnesses; true bits alone never certify false bits. -/
def ShortWitnessDuty {V EdgeId : Type*} [Fintype V] [DecidableEq V]
    {G : VertexArena V EdgeId} (σ : OriginalPolicy G) (c : Finset V) : Prop :=
  ∀ u v p, FirstReturn σ c u v p →
    ∃ w : Walk σ, w.Positive ∧ w.vertex 0 = u ∧ w.vertex w.length = v ∧
      w.weight = p.val ∧ w.length ≤ 2 * Fintype.card V ∧
      ∀ k, 0 < k → k < w.length → w.vertex k ∉ c

theorem spectral_record_bits_cap (q : Nat) (hq : q ≤ 3) : 5*q*q+2*q ≤ 51 := by
  have hc : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> norm_num

theorem spectral_weighted_edges_cap (q : Nat) (hq : q ≤ 3) : 5*q*q ≤ 45 := by
  have hc : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> norm_num

theorem spectral_witness_occurrences_cap (q n : Nat) (hq : q ≤ 3) (hn : n ≤ 12) :
    5*q*q*(2*n) + 2*q*(2*n-1) ≤ 1218 := by
  have hc : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> omega

theorem forget_finite_expansion_cap (n : Nat) (hn : n ≤ 12) : 6*n ≤ 72 := by omega
theorem forget_lasso_stem_cap (n : Nat) (hn : n ≤ 12) : 3*n-1 ≤ 35 := by omega
theorem reconstruction_return_cap (q n : Nat) (hq : q ≤ 3) (hn : n ≤ 12) :
    2*n*(2*q-1) ≤ 120 := by
  have hc : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> omega

end Partials.ParityAlgorithms.Spectra
