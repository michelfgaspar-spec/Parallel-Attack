import Partials.Cap.DataAdmissions
import Partials.Cap.LinkCertificate
import Partials.Cap.Symmetry

/-! Literal alternate-certificate adapters; actual row/orbit/count admission
remains explicit and unevaluated. No second vertex is normalized. -/
namespace Partials.Cap.LinkData

noncomputable section
open Partials.Cap

def obstructionRows : List (Certificate.ObstructionRow Vertex) :=
  Data.rawLinkOrbits.map (fun r =>
    ⟨r.representative.toFinset.image (fun v : ℕ => (v : Vertex)),
      r.forbiddenTriple.toFinset.image (fun v : ℕ => (v : Vertex))⟩)
def multiplierAction (j : Fin 8) (v : Vertex) : Vertex := (3 : Vertex) ^ j.val * v
def CanonicalLinkRows : Prop :=
  Data.rawLinkOrbits.length = 24 ∧
  ∀ r ∈ Data.rawLinkOrbits,
    r.representative.Pairwise (fun x y => x < y) ∧
    r.forbiddenTriple.Pairwise (fun x y => x < y) ∧
    r.representative.length = 5 ∧ r.forbiddenTriple.length = 3 ∧ r.orbitSize = 8 ∧
    (∀ v ∈ r.representative, 1 ≤ v ∧ v < 41) ∧
    (∀ v ∈ r.forbiddenTriple, v ∈ r.representative)

instance canonicalLinkRows_decidable : Decidable CanonicalLinkRows := by
  unfold CanonicalLinkRows
  infer_instance
def canonicalRowsCheck : Bool := decide CanonicalLinkRows
theorem canonicalRowsCheck_sound (h : canonicalRowsCheck = true) : CanonicalLinkRows := by
  simpa [canonicalRowsCheck] using h

variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

def ExactLinkCoverageDuty (z : K) : Prop :=
  Certificate.RepresentativeEdgeDuty (discriminantHypergraph z) obstructionRows ∧
  Certificate.LinkFiveOrbitCoverageDuty (discriminantHypergraph z) 0 obstructionRows multiplierAction

theorem edge_transport_from_geometric_symmetry {z : K} (ho : ThreeOrderDuty)
    (ha : ExponentActionDuty z) (hf : CubeFrobeniusDuty K) :
    Certificate.EdgeTransportDuty (discriminantHypergraph z) multiplierAction := by
  intro j e he
  have h := affine_hypergraph_symmetry ho ha hf 0 j
  have he' : e.image (affine 0 j) ∈ discriminantHypergraph z := by
    rw [← h.graph_image]
    exact Finset.mem_image.mpr ⟨e, he, rfl⟩
  have hfun : affine 0 j = multiplierAction j := by
    funext v
    simp [affine, multiplierAction]
  rw [hfun] at he'
  exact he'

theorem alternate_upper_from_exact_link {z : K} (ho : ThreeOrderDuty)
    (ha : ExponentActionDuty z) (hf : CubeFrobeniusDuty K)
    (hcover : ExactLinkCoverageDuty z) (T : Finset Vertex)
    (hind : Independent (discriminantHypergraph z) T) : T.card ≤ 5 := by
  have hrooting := Certificate.rooting_from_translation_invariance
    (discriminantHypergraph z) (fun a s hind =>
      (independent_translate_iff ho ha hf a s).mpr hind)
  exact Certificate.card_le_five_from_link (discriminantHypergraph z) 0 obstructionRows
    multiplierAction hcover.1 (edge_transport_from_geometric_symmetry ho ha hf) hcover.2 hrooting T hind

def LinkStatisticsDuty (z : K) : Prop :=
  let L := Certificate.linkAt (discriminantHypergraph z) 0
  let family := (Finset.univ : Finset (Finset Vertex)).filter
    (fun T => (0 : Vertex) ∉ T ∧ Independent L T)
  L.card = 420 ∧ family.card = 2361 ∧
    (∀ k : Fin 6, (family.filter (fun T => T.card = k.val)).card =
      (![1, 40, 360, 960, 808, 192] : Fin 6 → ℕ) k) ∧
    (∀ T ∈ family, T.card ≤ 5) ∧ (family.filter (fun T => T.card = 5)).card = 192

end
end Partials.Cap.LinkData
