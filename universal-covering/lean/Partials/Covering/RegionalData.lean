import Partials.Covering.Model

noncomputable section

/-! R4 BLIND / UNCHECKED SOURCE. Rational literals are copied verbatim from
data/R11-regional-premises.json and data/C-halos.json, with display bindings in
generated/definitions.tex and generated/radius-brackets.tex. `norm_num` below
is source text only: no tactic, arithmetic replay or generator was executed.
The three RegionalPremise propositions remain inherited numerical assumptions;
proving rational relations does not prove their geometric claims.
-/
namespace Partials.Covering

def Lzero : ℝ :=
  132361967655820912325627055417873955278897039211817233290204139458654665516684963208962537 /
  158612070477469540568684743141758900701012750000000000000000000000000000000000000000000000

def Lten : ℝ :=
  7953493215663286747783882734009188849615837363 /
  9530786886710063553288000000000000000000000000

def Lend : ℝ :=
  10763674065381881926232790864007209754079720740089112809269902630385888994751263305559157220541 /
  12896863427523737699213753454177288325305459210500000000000000000000000000000000000000000000000

def etaZero : ℝ := (Lzero - tau) / C
def etaTen : ℝ := (Lten - tau) / C
def etaEnd : ℝ := (Lend - tau) / C

def IZero : Set ℝ := Set.Icc 0 (3 / 1250)
def ITen : Set ℝ := Set.Icc (99 / 10000) (101 / 10000)
def IEnd : Set ℝ := Set.Icc (fundamentalEnd - 1 / 125) fundamentalEnd

/-- Only these three all-translation propositions are the application leaves. -/
def InheritedRegionalPremises : Prop :=
  RegionalPremise 0 (3 / 1250) Lzero ∧
  RegionalPremise (99 / 10000) (101 / 10000) Lten ∧
  RegionalPremise (fundamentalEnd - 1 / 125) fundamentalEnd Lend

def aZero : ℝ := 3 / 1250 + etaZero
def aTen : ℝ := 99 / 10000 - etaTen
def bTen : ℝ := 101 / 10000 + etaTen
def aEnd : ℝ := fundamentalEnd - 1 / 125 - etaEnd

def firstGapWidth : ℝ := 3 / 400 - etaZero - etaTen
def secondGapWidth : ℝ := fundamentalEnd - 181 / 10000 - etaTen - etaEnd
def addedLength : ℝ := etaZero + 2 * etaTen + etaEnd
def sourceLength : ℝ := 53 / 5000
def coveredLength : ℝ := sourceLength + addedLength
def remainingLength : ℝ := fundamentalEnd - coveredLength

theorem C_normalized_source_literal : C = (1067517 : ℝ) / 437500 := by
  norm_num [C]

theorem regional_constant_order :
    (tau < Lzero ∧ Lzero < L3) ∧ (tau < Lten ∧ Lten < L3) ∧
      (tau < Lend ∧ Lend < L3) := by
  norm_num [tau, L3, Lzero, Lten, Lend]

theorem eta_exact_source_literals :
    etaZero =
      1363896608065047417460862533068507313295357720633031428976210582658616794742462737759 /
      2709137306238349624628170095111376582394288445468000000000000000000000000000000000000000000 ∧
    etaTen =
      8802705516365559886027757666388958801501 /
      3970449570708318795791354496000000000000000000 ∧
    etaEnd =
      8690745793259713672395245473838526286205202488039664889318412701222963258843138914100543787 /
      220281935288957726359225095138287620818641726400245256000000000000000000000000000000000000000000 := by
  norm_num [etaZero, etaTen, etaEnd, Lzero, Lten, Lend, tau, C]

theorem eta_source_brackets :
    (100688629 / 200000000000000 < etaZero ∧
      etaZero < 251721573 / 500000000000000) ∧
    (2217055111 / 1000000000000000 < etaTen ∧
      etaTen < 277131889 / 125000000000000) ∧
    (19726415109 / 500000000000000 < etaEnd ∧
      etaEnd < 39452830219 / 1000000000000000) := by
  norm_num [etaZero, etaTen, etaEnd, Lzero, Lten, Lend, tau, C]

theorem eta_positive_and_small :
    (0 < etaZero ∧ etaZero < 1 / 1000000) ∧
    (0 < etaTen ∧ etaTen < 1 / 100000) ∧
    (0 < etaEnd ∧ etaEnd < 1 / 10000) := by
  norm_num [etaZero, etaTen, etaEnd, Lzero, Lten, Lend, tau, C]

theorem regional_intervals_nonempty :
    (0 : ℝ) ≤ 3 / 1250 ∧ (99 : ℝ) / 10000 ≤ 101 / 10000 ∧
      fundamentalEnd - 1 / 125 ≤ fundamentalEnd := by
  constructor
  · norm_num
  constructor
  · norm_num
  · linarith

theorem fundamentalEnd_gt_one_fifth : (1 : ℝ) / 5 < fundamentalEnd := by
  dsimp [fundamentalEnd]
  linarith [Real.pi_gt_three]

theorem gap_width_identities :
    aTen - aZero = firstGapWidth ∧ aEnd - bTen = secondGapWidth := by
  constructor <;> dsimp [aTen, aZero, aEnd, bTen, firstGapWidth, secondGapWidth] <;> ring

theorem gap_widths_positive :
    7 / 1000 < firstGapWidth ∧ 9 / 50 < secondGapWidth := by
  rcases eta_positive_and_small with ⟨h0, h10, he⟩
  have hp := fundamentalEnd_gt_one_fifth
  dsimp [firstGapWidth, secondGapWidth]
  constructor <;> linarith [h0.2, h10.2, he.2]

theorem halo_endpoints_order :
    0 < aZero ∧ aZero < aTen ∧ aTen < bTen ∧ bTen < aEnd ∧
      aEnd < fundamentalEnd := by
  rcases eta_positive_and_small with ⟨h0, h10, he⟩
  rcases gap_widths_positive with ⟨hw1, hw2⟩
  rcases gap_width_identities with ⟨hgap1, hgap2⟩
  dsimp [aZero, aTen, bTen, aEnd] at *
  constructor
  · linarith [h0.1]
  constructor
  · linarith
  constructor
  · linarith [h10.1]
  constructor
  · linarith
  · linarith [he.1]

theorem source_component_lengths :
    (3 / 1250 - 0 : ℝ) + (101 / 10000 - 99 / 10000) +
      (fundamentalEnd - (fundamentalEnd - 1 / 125)) = sourceLength := by
  dsimp [sourceLength]
  ring

theorem covered_component_lengths :
    (aZero - 0) + (bTen - aTen) + (fundamentalEnd - aEnd) = coveredLength := by
  dsimp [aZero, bTen, aTen, aEnd, coveredLength, sourceLength, addedLength]
  ring

theorem added_component_lengths :
    (aZero - 3 / 1250) + (99 / 10000 - aTen) +
      (bTen - 101 / 10000) + ((fundamentalEnd - 1 / 125) - aEnd) = addedLength := by
  dsimp [aZero, aTen, bTen, aEnd, addedLength]
  ring

theorem length_accounting : coveredLength - sourceLength = addedLength ∧
    firstGapWidth + secondGapWidth = remainingLength ∧
    coveredLength + remainingLength = fundamentalEnd := by
  dsimp [coveredLength, sourceLength, addedLength, firstGapWidth,
    secondGapWidth, remainingLength]
  constructor
  · ring
  constructor <;> ring

theorem firstGap_exact_source_literal :
    firstGapWidth =
      24197666688410783209198286319222895650399423519141033346676996869358735341692546441308590859915387113491724801 /
      3227526289074186031837733664022652511800878471446962836109176237512348000000000000000000000000000000000000000000 := by
  norm_num [firstGapWidth, etaZero, etaTen, Lzero, Lten, tau, C]

theorem secondGap_exact_source_affine_pi :
    secondGapWidth = fundamentalEnd -
      4760964190893700705017981441355738248174588068411595914689419824720718475522440451109621744377021749401236281477707 /
      262432522528889136586164208009343370445820439010260727593261709968753150216000000000000000000000000000000000000000000 := by
  norm_num [secondGapWidth, etaTen, etaEnd, Lten, Lend, tau, C] <;> ring

theorem length_source_literals :
    addedLength =
      1478198557507044381260940076348177696541006918005516513504284051000262126964740214136771054920904455751761535442961242994947733029933675538650751811774523 /
      33299972607145821373275154252360560565406139190361266264803267089195745047717354884892737748375286567242385843265003200000000000000000000000000000000000000000 ∧
    coveredLength =
      354457908193252750937977575151370119689846082335834938920418915196475159632768701993999791187698942068521051474051995162994947733029933675538650751811774523 /
      33299972607145821373275154252360560565406139190361266264803267089195745047717354884892737748375286567242385843265003200000000000000000000000000000000000000000 := by
  norm_num [addedLength, coveredLength, sourceLength, etaZero, etaTen, etaEnd,
    Lzero, Lten, Lend, tau, C]

end Partials.Covering
end
