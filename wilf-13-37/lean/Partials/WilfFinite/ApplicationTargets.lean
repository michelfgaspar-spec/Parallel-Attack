import Partials.WilfFinite.Applications

/-! Conditional mathematical/import/data interfaces, plus literal SOURCE
REPORTS. A transcribed report is not proof, a certificate, or an executed check.
These declarations and their APIs remain uncompiled. -/
namespace Partials.WilfFinite.Application
open Partials.WilfStructural.Foundation
open Partials.WilfStructural.Packing

def BoundedWilf (C u v : ℕ) : Prop := ∀ d : Data,
  d.c ≤ C → u ≤ n d → n d ≤ v → 0 ≤ W d
def Residual14To37 : Prop := ∀ d : Data,
  14 ≤ n d → n d ≤ 37 → 200 < d.c → 0 ≤ W d
def Full13To37 : Prop := ∀ d : Data, 13 ≤ n d → n d ≤ 37 → 0 ≤ W d

/-- A complete, proof-relevant residual cover and actual retention map suffice.
No execution-report Boolean or declared absence of unresolved leaves is used. -/
theorem residual_closed_cover_conditional {X : Type*}
    (region bad : X → Prop)
    (retain : ∀ d : Data, 14 ≤ n d → n d ≤ 37 → 200 < d.c → W d < 0 →
      ∃ x, region x ∧ bad x)
    (cover : ClosedCover bad region) : Residual14To37 := by
  intro d h14 h37 hc
  by_contra h
  obtain ⟨x,hregion,hbad⟩ := retain d h14 h37 hc (by omega)
  exact closed_cover_sound bad region cover x hregion hbad

theorem thirteen_from_scoped_200 (H : ThirteenInputs)
    (low : BoundedWilf 200 13 37) (d : Data) (hn : n d=13) : 0 ≤ W d := by
  by_contra h
  have hc := (thirteen_conductor_conditional H d hn (by omega)).2.2
  have hw := low d (by omega) (by omega) (by omega)
  omega

theorem cardinality_application_conditional (H : ThirteenInputs)
    (low : BoundedWilf 200 13 37) (residual : Residual14To37) : Full13To37 := by
  intro d h13 h37
  by_cases hn : n d=13
  · exact thirteen_from_scoped_200 H low d hn
  · by_cases hc : d.c ≤ 200
    · exact low d hc h13 h37
    · exact residual d (by omega) h37 (by omega)

theorem bacher_scoped (H200 : ExternalConductor200) : BoundedWilf 200 13 37 := by
  intro d hc _ _
  exact H200 d hc

/-- Abstract protocol interface: independent soundness must connect a real
PRIMARY normal-form checker and exact canonical reconstruction to Data.
No artifact or acceptance predicate inhabitant is supplied in R10. -/
def PrimaryAcceptanceSoundness {Cert : Type*}
    (accept : ℕ → ℕ → ℕ → Cert → Prop) : Prop :=
  ∀ C u v cert, accept C u v cert → BoundedWilf C u v

theorem scoped_primary_replaces_bacher {Cert : Type*}
    (accept : ℕ → ℕ → ℕ → Cert → Prop) (sound : PrimaryAcceptanceSoundness accept)
    (cert : Cert) (accepted : accept 200 13 37 cert)
    (H : ThirteenInputs) (residual : Residual14To37) : Full13To37 :=
  cardinality_application_conditional H (sound 200 13 37 cert accepted) residual

theorem all_rank_primary_restricts (h : BoundedWilf 200 1 100) :
    BoundedWilf 200 13 37 := by
  intro d hc h13 h37
  exact h d hc (by omega) (by omega)

/-- The structural cutoff and independent bounded verification may replace
both low-conductor and residual-cover inputs. H37=1292 is authored arithmetic,
not a traversal, evaluated certificate, or existence assertion. -/
theorem cutoff_37_value : ((37 : ℤ)-3)*(37+1)=1292 := by ring

theorem single_cutoff_application_conditional (quad : QuadraticTarget)
    (finite : BoundedWilf 1292 13 37) : Full13To37 := by
  intro d h13 h37
  by_contra h
  have hcZ := quadratic_cutoff_conditional quad d 37 h37 (by omega)
  norm_num at hcZ
  have hc : d.c ≤ 1292 := by exact_mod_cast hcZ
  have hw := finite d hc h13 h37
  omega

structure SourceReport where
  claim_id : String
  passage : String
  text : String

def reportedClosure : SourceReport := ⟨"WILF-U51","computation.tex:14-20",
  "SOURCE REPORT: n=14..37 all branches excluded; no omitted or unresolved child; no node/depth/time limit; maximum splitting depth ten."⟩
def reportedStages : SourceReport := ⟨"WILF-U52","computation.tex:31-51",
  "SOURCE REPORT: 14..32 closed at profile refinement; 33..37 used allocations, tuples, all-degree labels and matching; every listed singleton excluded."⟩
def reportedTotals : SourceReport := ⟨"WILF-U53","computation.tex:56-67",
  "SOURCE REPORT: profiles 55,569; rectangles 819,595; retained 2,535; allocations 26,525; refined 219; tuples 3,414; roots 2,726; quota rejections 4,231,199; propagation rejections 1,339,441; labels 4,042,141; splits 755; boxes 4,043,651; matching contradictions 4,042,896. No counter identity evaluated here."⟩
def reportedValidationLimits : SourceReport := ⟨"WILF-U54","computation.tex:69-80",
  "SOURCE REPORT: validator did not regenerate every label-eligibility, rank, propagation or candidate-graph step. Second complete run used the same implementation and scientific kernels. Additional reconstruction scopes were 14..32 first stages, 33..36 reached stages, n=37 tuple/label/packing decisions. This is not an independent second implementation."⟩
def reportedRegimes : SourceReport := ⟨"WILF-U55","computation.tex:82-100",
  "SOURCE REPORT: initial bounds 74..196 for 14..21 after early-empty exclusion; four n=21 q=4 profiles had alpha1=0; n=22 maximum endpoint 215; rectangles 120 at n=22 and 43,390 at n=32; allocations first reached n=33, retained profiles 60 to 1,216 through n=37. These thresholds are not derived in R10."⟩
def reportedRawCaps : SourceReport := ⟨"WILF-U57","implementation-notes.tex:33-68",
  "SOURCE REPORT: n33 IDs144,145 Q6 t3 Mmax37 m36 raw16/13; n37 IDs35,36 Q4 t3 Mmax58 m57 raw35/34. Comparisons: 1,992 reached cap calls at n33 and 26,846 selected-cap calls over 1,469 tuples at n37. Masked final F,N and exclusions were reported equal; no raw cap or reached-call comparison validated here."⟩
def reportedPublicationAssets : SourceReport := ⟨"WILF-U58","implementation-notes.tex:70-82",
  "SOURCE REPORT: private michelfgaspar-spec/wilf-13-37 release publication-v1 commit38cd478c9d2d4958304735a1b4295bcd7b7ffe55; 24 manifests and96 compressed logs unchanged; no full rerun. Source archive alone is not an execution certificate. Publication code SHA256 ed087d4656a37f2a542b75e74127e7bdeb1db1437b532a6713e4600aa9b2bd57; execution tar2b35ab015cc3cc1faf295e96135f34d1799a7396cf7983ff5f8fcaab5ad606a4; historical source35396d4e988aa470ea4a98535ea53c4058b796f22011714a661d0c2f1b992ff6. No repository, archive claim or log validated here."⟩
def reportedFirstReason : SourceReport := ⟨"WILF-U63","implementation-notes.tex:25-31",
  "SOURCE REPORT: tuple921 reached ranked counting with empty interval; zero eligible versus h[2,3]=1 excluded it. Recorded first reason was selected-prefix, while printed procedure excludes empty box earlier. Local emptiness proof does not authenticate reaching the tuple or recorded timing."⟩
def primaryHistoricalBoundary : SourceReport := ⟨"WILF-U56","computation.tex:125-144",
  "SOURCE EXCLUSION: residual profile traversal is distinct from PRIMARY full-label normal-form forest. No VERIFIED(200,13,37), VERIFIED(200,1,100) or accepted H37 traversal is supplied. Their conditional scopes are different."⟩

end Partials.WilfFinite.Application
