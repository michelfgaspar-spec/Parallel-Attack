import Partials.UnitDistance.DataAdmissions
import Partials.UnitDistance.DeletionCertificate

/-! BLIND concrete mask adapters and conditional admission. These predicates
have not been evaluated. Raw bounds/duplicates must be checked first. -/
namespace Partials.UnitDistance.CertificateData

def naturalMask (mask : ℕ) : Finset ℕ :=
  (Finset.range 21).filter (fun i => (mask / 2 ^ i) % 2 = 1)

def forbiddenRows : DeletionHypergraph :=
  (Data.rawForbiddenMasks.map naturalMask).toFinset

def deletionFamily : Finset (Finset ℕ) :=
  (Data.rawDeletionMasks.map naturalMask).toFinset

def finalDeleted : Finset (Fin 21) :=
  Finset.univ.filter (fun i => i.val ∈ Data.finalDeletedIndices)

def finalRetained : Finset (Fin 21) := Finset.univ \ finalDeleted

structure NonzeroFunctionalEnumerationDuty where
  functional : Fin 4095 → (BinaryCode →+ ZMod 2)
  nonzero : ∀ a, functional a ≠ 0
  exhaustive : ∀ h : BinaryCode →+ ZMod 2, h ≠ 0 → ∃ a, functional a = h
  unique : Function.Injective functional

noncomputable def functionalMask (F : CommonBinaryLineFamily BinaryCode)
    (E : NonzeroFunctionalEnumerationDuty) (a : Fin 4095) : Finset ℕ :=
  (annihilatedLines F (E.functional a)).image Fin.val

structure LineLiteralMeaningDuty (F : CommonBinaryLineFamily BinaryCode) : Prop where
  exact_lines : ∀ i : Fin 21, lineAt F i =
    ((Data.rawLineRows.getD i.val []).map DataAdmissions.decodeBinaryLabel).toFinset
  disjoint : ∀ i j, i ≠ j → Disjoint (lineAt F i) (lineAt F j)
  retained_directions : lineDirections F finalRetained =
    (Data.finalDirections.map DataAdmissions.decodeBinaryLabel).toFinset

/-- This duty names exact mathematical leaves, not a threshold or colouring
conclusion. Minimal reduction is two actual containment/origin directions. -/
structure ExactDeletionAdmissionDuty (F : CommonBinaryLineFamily BinaryCode) where
  raw : DataAdmissions.ExactRawAcceptanceDuty
  characters : NonzeroFunctionalEnumerationDuty
  reduction : MaskReductionDuty (Fin 4095) Finset.univ
    (functionalMask F characters) forbiddenRows
  certificate : certificateChecks forbiddenRows deletionFamily 21 = true
  statistics : DeletionStatisticsDuty deletionFamily
  final_independent : DeletionIndependent forbiddenRows (finalDeleted.image Fin.val)

theorem independent_mask_gives_line_hit (F : CommonBinaryLineFamily BinaryCode)
    (E : NonzeroFunctionalEnumerationDuty)
    (R : MaskReductionDuty (Fin 4095) Finset.univ (functionalMask F E) forbiddenRows)
    (D : Finset (Fin 21))
    (hind : DeletionIndependent forbiddenRows (D.image Fin.val)) :
    LineHit F (Finset.univ \ D) := by
  apply (line_hit_complement_iff F D).2
  intro h h0 hsub
  obtain ⟨a, ha⟩ := E.exhaustive h h0
  have hav := (minimal_masks_avoidance_iff Finset.univ
    (functionalMask F E) forbiddenRows R (D.image Fin.val)).1 hind a (Finset.mem_univ a)
  apply hav
  unfold functionalMask
  rw [ha]
  exact Finset.image_subset_image hsub

theorem final_line_hit_from_actual_admission (F : CommonBinaryLineFamily BinaryCode)
    (D : ExactDeletionAdmissionDuty F) : LineHit F finalRetained := by
  exact independent_mask_gives_line_hit F D.characters D.reduction finalDeleted D.final_independent

theorem exact_deletion_family_from_actual_admission
    (F : CommonBinaryLineFamily BinaryCode) (D : ExactDeletionAdmissionDuty F)
    (s : Finset ℕ) :
    s ∈ deletionFamily ↔ DeletionIndependent forbiddenRows s ∧ DeletionBounded 21 s := by
  exact certificateChecks_sound forbiddenRows deletionFamily 21 D.certificate s

theorem final_quotient_obstruction (F : CommonBinaryLineFamily BinaryCode)
    (D : ExactDeletionAdmissionDuty F) (spectral : SpectralRatioDuty F finalRetained) :
    NoFourCayleyColouring F finalRetained := by
  exact line_hit_no_four_colour F finalRetained
    (final_line_hit_from_actual_admission F D) spectral

end Partials.UnitDistance.CertificateData
