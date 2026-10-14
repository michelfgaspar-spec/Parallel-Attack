import Partials.UnitDistance.LineHit

/-! R6 blind source. The ordered-extension induction adapts R5
Partials/Cap/LinkCertificate.lean, with empty root and domain 0 <= x < 21.
The stored 379 rows, 4095 functionals, masks and checker acceptance are NOT
proved by defining these interfaces. No certificate has been replayed. -/
namespace Partials.UnitDistance

variable {V : Type*} [AddCommGroup V] [DecidableEq V]

noncomputable def annihilatedLines (F : CommonBinaryLineFamily V)
    (h : V →+ ZMod 2) : Finset (Fin 21) := by
  classical
  exact Finset.univ.filter (AnnihilatesLine F h)

theorem line_hit_complement_iff (F : CommonBinaryLineFamily V)
    (D : Finset (Fin 21)) :
    LineHit F (Finset.univ \ D) ↔
      ∀ h : V →+ ZMod 2, h ≠ 0 → ¬ annihilatedLines F h ⊆ D := by
  classical
  constructor
  · intro hhit h h0 hsub
    obtain ⟨i, hi, hai⟩ := hhit h h0
    have himask : i ∈ annihilatedLines F h := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hai⟩
    exact (Finset.mem_sdiff.mp hi).2 (hsub himask)
  · intro hav h h0
    obtain ⟨i, himask, hiD⟩ := Finset.not_subset.mp (hav h h0)
    exact ⟨i, Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiD⟩,
      (Finset.mem_filter.mp himask).2⟩

abbrev DeletionHypergraph := Finset (Finset ℕ)

def DeletionIndependent (H : DeletionHypergraph) (D : Finset ℕ) : Prop :=
  ∀ e ∈ H, ¬ e ⊆ D

instance deletionIndependentDecidable (H : DeletionHypergraph) (D : Finset ℕ) :
    Decidable (DeletionIndependent H D) := by
  unfold DeletionIndependent
  infer_instance

theorem deletion_independent_subset (H : DeletionHypergraph)
    {D E : Finset ℕ} (hsub : D ⊆ E) (hE : DeletionIndependent H E) :
    DeletionIndependent H D := by
  intro e he hes
  exact hE e he (hes.trans hsub)

/-- Two independently admitted directions of the minimal-mask reduction.
Every original nonzero-functional mask contains a retained forbidden mask;
every retained forbidden mask is an original mask. Inclusion-minimality and
the 63/133 size counts are additional finite targets. -/
structure MaskReductionDuty (A : Type*) [DecidableEq A]
    (nonzero : Finset A) (mask : A → Finset ℕ) (H : DeletionHypergraph) : Prop where
  below_original : ∀ a ∈ nonzero, ∃ e ∈ H, e ⊆ mask a
  original_origin : ∀ e ∈ H, ∃ a ∈ nonzero, e = mask a

theorem minimal_masks_avoidance_iff {A : Type*} [DecidableEq A]
    (nonzero : Finset A) (mask : A → Finset ℕ) (H : DeletionHypergraph)
    (R : MaskReductionDuty A nonzero mask H) (D : Finset ℕ) :
    DeletionIndependent H D ↔ ∀ a ∈ nonzero, ¬ mask a ⊆ D := by
  constructor
  · intro hind a ha hbad
    obtain ⟨e, he, hemask⟩ := R.below_original a ha
    exact hind e he (hemask.trans hbad)
  · intro hav e he hbad
    obtain ⟨a, ha, hea⟩ := R.original_origin e he
    exact hav a ha (by simpa only [← hea] using hbad)

def DeletionBounded (n : ℕ) (D : Finset ℕ) : Prop := ∀ x ∈ D, x < n

instance deletionBoundedDecidable (n : ℕ) (D : Finset ℕ) :
    Decidable (DeletionBounded n D) := by
  unfold DeletionBounded
  infer_instance

def IncreasingDeletionClosed (H : DeletionHypergraph)
    (family : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ D ∈ family, ∀ x : ℕ, x < n → (∀ y ∈ D, y < x) →
    DeletionIndependent H (insert x D) → insert x D ∈ family

/-- Every independent set is obtained by increasing extensions from EMPTY.
The strict-order guard is vacuous at empty, so every domain element is
eligible for the first extension. -/
theorem independent_mem_of_empty_ordered_extensions
    (H : DeletionHypergraph) (family : Finset (Finset ℕ)) (n : ℕ)
    (hbase : (∅ : Finset ℕ) ∈ family)
    (hstep : IncreasingDeletionClosed H family n)
    (D : Finset ℕ) (hind : DeletionIndependent H D)
    (hbound : DeletionBounded n D) : D ∈ family := by
  have aux : ∀ m : ℕ, m ≤ n → ∀ E : Finset ℕ,
      DeletionIndependent H E → DeletionBounded m E → E ∈ family := by
    intro m
    induction m with
    | zero =>
        intro hm E hE hb
        have hnil : E = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          have hbad := hb x hx
          omega
        simpa only [hnil] using hbase
    | succ m ih =>
        intro hm E hE hb
        by_cases hmem : m ∈ E
        · have hsub : E.erase m ⊆ E := by
            intro x hx
            exact (Finset.mem_erase.mp hx).2
          have hbound' : DeletionBounded m (E.erase m) := by
            intro x hx
            have hxne := (Finset.mem_erase.mp hx).1
            have hxb := hb x (Finset.mem_erase.mp hx).2
            omega
          have hprev : E.erase m ∈ family :=
            ih (by omega) (E.erase m) (deletion_independent_subset H hsub hE) hbound'
          have hcurrent : DeletionIndependent H (insert m (E.erase m)) := by
            simpa only [Finset.insert_erase hmem] using hE
          have hnext := hstep (E.erase m) hprev m (by omega) hbound' hcurrent
          simpa only [Finset.insert_erase hmem] using hnext
        · have hbound' : DeletionBounded m E := by
            intro x hx
            have hxb := hb x hx
            have hxne : x ≠ m := by
              intro he
              subst x
              exact hmem hx
            omega
          exact ih (by omega) E hE hbound'
  exact aux n (le_refl n) D hind hbound

theorem deletion_certificate_complete_iff
    (H : DeletionHypergraph) (family : Finset (Finset ℕ)) (n : ℕ)
    (hbase : (∅ : Finset ℕ) ∈ family)
    (hvalid : ∀ D ∈ family, DeletionIndependent H D ∧ DeletionBounded n D)
    (hstep : IncreasingDeletionClosed H family n) (D : Finset ℕ) :
    D ∈ family ↔ DeletionIndependent H D ∧ DeletionBounded n D := by
  constructor
  · exact hvalid D
  · intro hd
    exact independent_mem_of_empty_ordered_extensions H family n hbase hstep D hd.1 hd.2

/-- Finite structural acceptance interface: all rows, all permitted increasing
extensions, the empty row and domain bounds are tested. This is separate from
the upstream computation of every functional mask. -/
def certificateChecks (H : DeletionHypergraph)
    (family : Finset (Finset ℕ)) (n : ℕ) : Bool :=
  decide ((∅ : Finset ℕ) ∈ family ∧
    (∀ D ∈ family, DeletionIndependent H D ∧ DeletionBounded n D) ∧
    (∀ D ∈ family, ∀ x ∈ Finset.range n,
      (∀ y ∈ D, y < x) → DeletionIndependent H (insert x D) → insert x D ∈ family))

theorem certificateChecks_sound (H : DeletionHypergraph)
    (family : Finset (Finset ℕ)) (n : ℕ) (h : certificateChecks H family n = true)
    (D : Finset ℕ) :
    D ∈ family ↔ DeletionIndependent H D ∧ DeletionBounded n D := by
  have hc : (∅ : Finset ℕ) ∈ family ∧
      (∀ E ∈ family, DeletionIndependent H E ∧ DeletionBounded n E) ∧
      (∀ E ∈ family, ∀ x ∈ Finset.range n,
        (∀ y ∈ E, y < x) → DeletionIndependent H (insert x E) → insert x E ∈ family) :=
    of_decide_eq_true h
  apply deletion_certificate_complete_iff H family n hc.1 hc.2.1
  intro E hE x hx hgreater hind
  exact hc.2.2 E hE x (Finset.mem_range.mpr hx) hgreater hind

def deletionRankCount (family : Finset (Finset ℕ)) (k : ℕ) : ℕ :=
  (family.filter (fun D => D.card = k)).card

def retainedLines (D : Finset ℕ) : Finset ℕ := Finset.range 21 \ D

def retainedRankCount (family : Finset (Finset ℕ)) (m : ℕ) : ℕ :=
  (family.filter (fun D => (retainedLines D).card = m)).card

theorem bounded_subset_range (D : Finset ℕ) (n : ℕ) (hb : DeletionBounded n D) :
    D ⊆ Finset.range n := by
  intro x hx
  exact Finset.mem_range.mpr (hb x hx)

theorem retained_card (D : Finset ℕ) (hb : DeletionBounded 21 D) :
    (retainedLines D).card = 21 - D.card := by
  rw [retainedLines, Finset.card_sdiff_of_subset (bounded_subset_range D 21 hb)]
  simp

theorem retained_injective_on_bounded (D E : Finset ℕ)
    (hD : DeletionBounded 21 D) (hE : DeletionBounded 21 E)
    (he : retainedLines D = retainedLines E) : D = E := by
  apply Finset.ext
  intro x
  constructor
  · intro hx
    by_contra hxe
    have hretE : x ∈ retainedLines E :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (hD x hx), hxe⟩
    have hretD : x ∈ retainedLines D := by rw [he]; exact hretE
    exact (Finset.mem_sdiff.mp hretD).2 hx
  · intro hx
    by_contra hxd
    have hretD : x ∈ retainedLines D :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr (hE x hx), hxd⟩
    have hretE : x ∈ retainedLines E := by rw [← he]; exact hretD
    exact (Finset.mem_sdiff.mp hretE).2 hx

/-- Because bounded complementation is injective, these counts describe
distinct retained selections, rather than repeated deletion presentations. -/
theorem retained_rank_transport (family : Finset (Finset ℕ))
    (hb : ∀ D ∈ family, DeletionBounded 21 D) (m : ℕ) (hm : m ≤ 21) :
    retainedRankCount family m = deletionRankCount family (21 - m) := by
  have hfilters : family.filter (fun D => (retainedLines D).card = m) =
      family.filter (fun D => D.card = 21 - m) := by
    apply Finset.ext
    intro D
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hD, hc⟩
      have hsmall : D.card ≤ 21 := by
        have hh := Finset.card_le_card (bounded_subset_range D 21 (hb D hD))
        simpa using hh
      rw [retained_card D (hb D hD)] at hc
      exact ⟨hD, by omega⟩
    · rintro ⟨hD, hc⟩
      rw [retained_card D (hb D hD)]
      exact ⟨hD, by omega⟩
  exact congrArg Finset.card hfilters

/-- Frozen numerical acceptance targets, not asserted truths. Acceptance of
the actual decoded family and every mask/functional correspondence is still
required before applying the conditional threshold/count results. -/
structure DeletionStatisticsDuty (family : Finset (Finset ℕ)) : Prop where
  total : family.card = 379
  rank0 : deletionRankCount family 0 = 1
  rank1 : deletionRankCount family 1 = 21
  rank2 : deletionRankCount family 2 = 147
  rank3 : deletionRankCount family 3 = 210
  max_rank : ∀ D ∈ family, D.card ≤ 3

theorem independent_retains_at_least_eighteen
    (H : DeletionHypergraph) (family : Finset (Finset ℕ))
    (hcheck : certificateChecks H family 21 = true)
    (stats : DeletionStatisticsDuty family) (D : Finset ℕ)
    (hind : DeletionIndependent H D) (hb : DeletionBounded 21 D) :
    18 ≤ (retainedLines D).card := by
  have hD := (certificateChecks_sound H family 21 hcheck D).2 ⟨hind, hb⟩
  have hsmall := stats.max_rank D hD
  rw [retained_card D hb]
  omega

theorem accepted_family_has_eighteen_selection
    (H : DeletionHypergraph) (family : Finset (Finset ℕ))
    (hcheck : certificateChecks H family 21 = true)
    (stats : DeletionStatisticsDuty family) :
    ∃ D : Finset ℕ, DeletionIndependent H D ∧ DeletionBounded 21 D ∧
      (retainedLines D).card = 18 := by
  have hpos : 0 < (family.filter (fun D => D.card = 3)).card := by
    change 0 < deletionRankCount family 3
    rw [stats.rank3]
    norm_num
  obtain ⟨D, hD⟩ := Finset.card_pos.mp hpos
  obtain ⟨hmem, hthree⟩ := Finset.mem_filter.mp hD
  obtain ⟨hind, hb⟩ := (certificateChecks_sound H family 21 hcheck D).1 hmem
  refine ⟨D, hind, hb, ?_⟩
  rw [retained_card D hb, hthree]

theorem retained_rank_counts (family : Finset (Finset ℕ))
    (hb : ∀ D ∈ family, DeletionBounded 21 D)
    (stats : DeletionStatisticsDuty family) :
    retainedRankCount family 18 = 210 ∧ retainedRankCount family 19 = 147 ∧
      retainedRankCount family 20 = 21 ∧ retainedRankCount family 21 = 1 := by
  constructor
  · rw [retained_rank_transport family hb 18 (by omega)]
    exact stats.rank3
  · constructor
    · rw [retained_rank_transport family hb 19 (by omega)]
      exact stats.rank2
    · constructor
      · rw [retained_rank_transport family hb 20 (by omega)]
        exact stats.rank1
      · rw [retained_rank_transport family hb 21 (by omega)]
        exact stats.rank0

end Partials.UnitDistance
