import Partials.Covering.Certificates

noncomputable section
namespace Partials.Covering.Restricted

/-! Literal transcription of frozen JSON strings. Only static text/JSON transcription ran; no geometry, certificate,
manuscript generator or rational calculation was executed. These are retained
numerical-premise domains, not checked geometric certificates. -/
structure VerticalBox where
  y3lo : ℚ
  y3hi : ℚ
  y5lo : ℚ
  y5hi : ℚ

def VerticalBox.contains (r : VerticalBox) (y : ℝ × ℝ) : Prop :=
  (r.y3lo : ℝ) ≤ y.1 ∧ y.1 ≤ (r.y3hi : ℝ) ∧
    (r.y5lo : ℝ) ≤ y.2 ∧ y.2 ≤ (r.y5hi : ℝ)

def certifiedABoxes : Fin 33 → VerticalBox :=
  ![⟨(-7 : ℚ) / 512, (0 : ℚ), (21 : ℚ) / 2560, (63 : ℚ) / 5120⟩,
    ⟨(0 : ℚ), (7 : ℚ) / 512, (21 : ℚ) / 5120, (21 : ℚ) / 2560⟩,
    ⟨(0 : ℚ), (7 : ℚ) / 512, (21 : ℚ) / 2560, (63 : ℚ) / 5120⟩,
    ⟨(-7 : ℚ) / 512, (-7 : ℚ) / 1024, (0 : ℚ), (21 : ℚ) / 5120⟩,
    ⟨(-7 : ℚ) / 512, (-7 : ℚ) / 1024, (21 : ℚ) / 5120, (21 : ℚ) / 2560⟩,
    ⟨(7 : ℚ) / 1024, (7 : ℚ) / 512, (0 : ℚ), (21 : ℚ) / 5120⟩,
    ⟨(-7 : ℚ) / 1024, (-7 : ℚ) / 2048, (21 : ℚ) / 5120, (21 : ℚ) / 2560⟩,
    ⟨(-7 : ℚ) / 1024, (-7 : ℚ) / 2048, (21 : ℚ) / 10240, (21 : ℚ) / 5120⟩,
    ⟨(-7 : ℚ) / 2048, (0 : ℚ), (21 : ℚ) / 5120, (63 : ℚ) / 10240⟩,
    ⟨(-7 : ℚ) / 2048, (0 : ℚ), (63 : ℚ) / 10240, (21 : ℚ) / 2560⟩,
    ⟨(21 : ℚ) / 2048, (7 : ℚ) / 512, (-21 : ℚ) / 5120, (-21 : ℚ) / 10240⟩,
    ⟨(7 : ℚ) / 2048, (7 : ℚ) / 1024, (21 : ℚ) / 10240, (21 : ℚ) / 5120⟩,
    ⟨(-21 : ℚ) / 2048, (-7 : ℚ) / 1024, (-21 : ℚ) / 5120, (-21 : ℚ) / 10240⟩,
    ⟨(-21 : ℚ) / 2048, (-7 : ℚ) / 1024, (-21 : ℚ) / 10240, (0 : ℚ)⟩,
    ⟨(-7 : ℚ) / 1024, (-7 : ℚ) / 2048, (-21 : ℚ) / 5120, (-21 : ℚ) / 10240⟩,
    ⟨(-7 : ℚ) / 1024, (-7 : ℚ) / 2048, (-21 : ℚ) / 10240, (0 : ℚ)⟩,
    ⟨(-7 : ℚ) / 2048, (0 : ℚ), (21 : ℚ) / 10240, (21 : ℚ) / 5120⟩,
    ⟨(7 : ℚ) / 2048, (7 : ℚ) / 1024, (-21 : ℚ) / 5120, (-21 : ℚ) / 10240⟩,
    ⟨(7 : ℚ) / 2048, (7 : ℚ) / 1024, (-21 : ℚ) / 10240, (0 : ℚ)⟩,
    ⟨(7 : ℚ) / 1024, (21 : ℚ) / 2048, (-21 : ℚ) / 5120, (-21 : ℚ) / 10240⟩,
    ⟨(7 : ℚ) / 1024, (21 : ℚ) / 2048, (-21 : ℚ) / 10240, (0 : ℚ)⟩,
    ⟨(21 : ℚ) / 2048, (7 : ℚ) / 512, (-21 : ℚ) / 10240, (0 : ℚ)⟩,
    ⟨(0 : ℚ), (7 : ℚ) / 2048, (21 : ℚ) / 10240, (21 : ℚ) / 5120⟩,
    ⟨(7 : ℚ) / 2048, (7 : ℚ) / 1024, (0 : ℚ), (21 : ℚ) / 10240⟩,
    ⟨(-7 : ℚ) / 512, (-49 : ℚ) / 4096, (-21 : ℚ) / 5120, (-21 : ℚ) / 10240⟩,
    ⟨(-49 : ℚ) / 4096, (-21 : ℚ) / 2048, (-21 : ℚ) / 5120, (-21 : ℚ) / 10240⟩,
    ⟨(-7 : ℚ) / 512, (-49 : ℚ) / 4096, (-21 : ℚ) / 10240, (0 : ℚ)⟩,
    ⟨(-49 : ℚ) / 4096, (-21 : ℚ) / 2048, (-21 : ℚ) / 10240, (0 : ℚ)⟩,
    ⟨(-7 : ℚ) / 2048, (-7 : ℚ) / 4096, (-21 : ℚ) / 5120, (-21 : ℚ) / 10240⟩,
    ⟨(7 : ℚ) / 4096, (7 : ℚ) / 2048, (0 : ℚ), (21 : ℚ) / 10240⟩,
    ⟨(-7 : ℚ) / 4096, (0 : ℚ), (-21 : ℚ) / 5120, (-63 : ℚ) / 20480⟩,
    ⟨(-7 : ℚ) / 1024, (-21 : ℚ) / 4096, (21 : ℚ) / 20480, (21 : ℚ) / 10240⟩,
    ⟨(-21 : ℚ) / 4096, (-7 : ℚ) / 2048, (21 : ℚ) / 20480, (21 : ℚ) / 10240⟩]

def residualABoxes : Fin 24 → VerticalBox :=
  ![⟨(0 : ℚ), (7 : ℚ) / 4096, (-21 : ℚ) / 5120, (-21 : ℚ) / 10240⟩,
    ⟨(7 : ℚ) / 4096, (7 : ℚ) / 2048, (-21 : ℚ) / 5120, (-21 : ℚ) / 10240⟩,
    ⟨(0 : ℚ), (7 : ℚ) / 4096, (-21 : ℚ) / 10240, (0 : ℚ)⟩,
    ⟨(7 : ℚ) / 4096, (7 : ℚ) / 2048, (-21 : ℚ) / 10240, (0 : ℚ)⟩,
    ⟨(0 : ℚ), (7 : ℚ) / 4096, (0 : ℚ), (21 : ℚ) / 10240⟩,
    ⟨(-4 : ℚ) / 25, (-7 : ℚ) / 512, (-9 : ℚ) / 100, (0 : ℚ)⟩,
    ⟨(-4 : ℚ) / 25, (-7 : ℚ) / 512, (0 : ℚ), (9 : ℚ) / 100⟩,
    ⟨(7 : ℚ) / 512, (4 : ℚ) / 25, (-9 : ℚ) / 100, (0 : ℚ)⟩,
    ⟨(7 : ℚ) / 512, (4 : ℚ) / 25, (0 : ℚ), (9 : ℚ) / 100⟩,
    ⟨(-7 : ℚ) / 512, (7 : ℚ) / 512, (-9 : ℚ) / 100, (-2409 : ℚ) / 51200⟩,
    ⟨(-7 : ℚ) / 512, (7 : ℚ) / 512, (-2409 : ℚ) / 51200, (-21 : ℚ) / 5120⟩,
    ⟨(-7 : ℚ) / 512, (7 : ℚ) / 512, (63 : ℚ) / 5120, (2619 : ℚ) / 51200⟩,
    ⟨(-7 : ℚ) / 512, (7 : ℚ) / 512, (2619 : ℚ) / 51200, (9 : ℚ) / 100⟩,
    ⟨(-7 : ℚ) / 4096, (0 : ℚ), (-63 : ℚ) / 20480, (-21 : ℚ) / 10240⟩,
    ⟨(-7 : ℚ) / 2048, (-7 : ℚ) / 4096, (-21 : ℚ) / 10240, (-21 : ℚ) / 20480⟩,
    ⟨(-7 : ℚ) / 2048, (-7 : ℚ) / 4096, (-21 : ℚ) / 20480, (0 : ℚ)⟩,
    ⟨(-7 : ℚ) / 4096, (0 : ℚ), (-21 : ℚ) / 10240, (-21 : ℚ) / 20480⟩,
    ⟨(-7 : ℚ) / 4096, (0 : ℚ), (-21 : ℚ) / 20480, (0 : ℚ)⟩,
    ⟨(-7 : ℚ) / 1024, (-21 : ℚ) / 4096, (0 : ℚ), (21 : ℚ) / 20480⟩,
    ⟨(-21 : ℚ) / 4096, (-7 : ℚ) / 2048, (0 : ℚ), (21 : ℚ) / 20480⟩,
    ⟨(-7 : ℚ) / 2048, (-7 : ℚ) / 4096, (0 : ℚ), (21 : ℚ) / 20480⟩,
    ⟨(-7 : ℚ) / 2048, (-7 : ℚ) / 4096, (21 : ℚ) / 20480, (21 : ℚ) / 10240⟩,
    ⟨(-7 : ℚ) / 4096, (0 : ℚ), (0 : ℚ), (21 : ℚ) / 20480⟩,
    ⟨(-7 : ℚ) / 4096, (0 : ℚ), (21 : ℚ) / 20480, (21 : ℚ) / 10240⟩]

def bBoxes : Fin 2 → VerticalBox :=
  ![⟨(-2049 : ℚ) / 1000000, (-1849 : ℚ) / 1000000, (-353 : ℚ) / 500000, (-253 : ℚ) / 500000⟩,
    ⟨(-9733 : ℚ) / 1000000, (-9533 : ℚ) / 1000000, (-9191 : ℚ) / 1000000, (-8991 : ℚ) / 1000000⟩]

def certifiedAUnion : Set (ℝ × ℝ) := {y | ∃ i : Fin 33, (certifiedABoxes i).contains y}
def residualAUnion : Set (ℝ × ℝ) := {y | ∃ i : Fin 24, (residualABoxes i).contains y}
def verticalRoot : Set (ℝ × ℝ) := {y | |y.1| ≤ d3 ∧ |y.2| ≤ d5}
def aAngles : Set ℝ := Set.Icc (49 / 10000) (37 / 5000)
def bAngles : Fin 2 → Set ℝ :=
  ![Set.Icc (101 / 10000) (111 / 10000), Set.Icc (99 / 1000) (101 / 1000)]

def aLower : ℝ := (7066509152093031907521708022648249429166828567 : ℝ) / 8467935872589912289148000000000000000000000000
def bLower : Fin 2 → ℝ := ![(24707539363566811556476314338146172242425147 : ℝ) / 29599681178827368387400000000000000000000000, (2274999337145235700196364014004767848092664997 : ℝ) / 2724179336032307676194000000000000000000000000]
def pilotLower : ℝ := (210803804668486022720529125627485392569560569 : ℝ) / 252709525095029507606875000000000000000000000
def pilotAngles : Set ℝ := Set.Icc (fundamentalEnd - 9 / 1000) (fundamentalEnd - 1 / 125)

/-- Explicit inherited numerical premise. Every horizontal coordinate is
unrestricted, while the 33 closed vertical cells and angle interval remain. -/
def ANumericalPremise : Prop :=
  ∀ y ∈ certifiedAUnion, ∀ φ ∈ aAngles, ∀ x3 x5 : ℝ,
    aLower ≤ H (point x3 y.1) (point x5 y.2) φ

def BNumericalPremise : Prop :=
  ∀ i : Fin 2, ∀ y, (bBoxes i).contains y → ∀ φ ∈ bAngles i, ∀ x3 x5 : ℝ,
    bLower i ≤ H (point x3 y.1) (point x5 y.2) φ

/-- OPEN: actual decoded/admitted points, selected cycles, determinant signs,
identities and Bernstein coefficients must instantiate the soundness theorem
on each cell. The stored summaries alone do not discharge this premise. -/
def ACertificateInterpretationDuty : Prop := ANumericalPremise

def BCertificateInterpretationDuty : Prop := BNumericalPremise

/-- Exact closed obligation cover; shared certified faces are not thereby
labelled uncovered. This finite-real coverage duty is not proved here. -/
def ResidualCoverDuty : Prop :=
  ∀ y ∈ verticalRoot, y ∈ certifiedAUnion ∨ y ∈ residualAUnion

/-- The endpoint pilot has all translation quantifiers but is below tau.
Its reflection argument concerns admitted inner polygons only. -/
def EndpointPilotDuty : Prop :=
  ∀ φ ∈ pilotAngles, ∀ t3 t5 : Plane, pilotLower ≤ H t3 t5 φ

theorem a_lower_above_tau : tau < aLower := by norm_num [tau, aLower]
theorem b_lowers_above_tau (i : Fin 2) : tau < bLower i := by
  fin_cases i <;> norm_num [tau, bLower]
theorem pilot_below_tau : pilotLower < tau := by norm_num [pilotLower, tau]

theorem a_cell_y3_upper (i : Fin 33) : (certifiedABoxes i).y3hi ≤ (7 / 512 : ℚ) := by
  fin_cases i <;> norm_num [certifiedABoxes]

theorem a_union_y3_upper {y : ℝ × ℝ} (hy : y ∈ certifiedAUnion) : y.1 ≤ 7 / 512 := by
  obtain ⟨i, hi⟩ := hy
  have hq := a_cell_y3_upper i
  have hr : ((certifiedABoxes i).y3hi : ℝ) ≤ 7 / 512 := by
    have hc : ((certifiedABoxes i).y3hi : ℝ) ≤ ((7 / 512 : ℚ) : ℝ) :=
      Rat.cast_le.mpr hq
    norm_num at hc
    exact hc
  exact hi.2.1.trans hr

/-- Concrete missing vertical coverage, not a counterexample to H>=tau. -/
theorem a_union_does_not_exhaust_vertical_root :
    ((1 / 10 : ℝ), (0 : ℝ)) ∈ verticalRoot ∧
      ((1 / 10 : ℝ), (0 : ℝ)) ∉ certifiedAUnion := by
  constructor
  · norm_num [verticalRoot, d3, d5]
  · intro h
    have hu := a_union_y3_upper h
    norm_num at hu

def pilotHaloRadius : ℝ := (min pilotLower L3 - tau) / C

theorem pilot_halo_negative : pilotHaloRadius < 0 := by
  norm_num [pilotHaloRadius, pilotLower, L3, tau, C]

end Partials.Covering.Restricted
end
