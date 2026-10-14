import Partials.UnitDistance.Targets
import Partials.UnitDistance.Network

/-! BLIND conditional assembly. Desired physical non-four-colourability is
derived through the independent Cayley spectral argument and transported
external seed. All concrete admissions remain explicit and uninstantiated. -/
noncomputable section
namespace Partials.UnitDistance.Assembly

local instance : DecidableEq ℂ := Classical.decEq _

theorem quotient_obstruction_from_line_hit
    (F : CommonBinaryLineFamily BinaryCode) (S : Finset (Fin 21))
    (hhit : LineHit F S) (hspectral : SpectralRatioDuty F S) :
    ¬ ∃ c : BinaryCode → Colour4,
      LiftProperQuotient (fun a b => a + b ∈ lineDirections F S) c := by
  exact line_hit_no_four_colour F S hhit hspectral

theorem physical_obstruction_from_explicit_network {I : Type*}
    (G1 G : PhysicalGraph) (occurrences : I → GadgetOccurrence)
    (hseed : ExternalSeedForce G1) (hnet : NetworkAdmission G1 G occurrences)
    (F : CommonBinaryLineFamily BinaryCode) (S : Finset (Fin 21))
    (hhit : LineHit F S) (hspectral : SpectralRatioDuty F S)
    (hlifts : ∀ a b, a + b ∈ lineDirections F S →
      UnorderedLiftWitness G occurrences a b) : NoFourColouring G := by
  exact finite_unordered_lift_obstruction G1 G occurrences hseed hnet
    (fun a b => a + b ∈ lineDirections F S) hlifts
    (quotient_obstruction_from_line_hit F S hhit hspectral)

theorem main_from_named_primitive_and_data_admissions {I : Type*}
    (G1 G : PhysicalGraph) (occurrences : I → GadgetOccurrence)
    (hseed : ExternalSeedForce G1) (hnet : NetworkAdmission G1 G occurrences)
    (F : CommonBinaryLineFamily BinaryCode) (S : Finset (Fin 21))
    (hhit : LineHit F S) (hspectral : SpectralRatioDuty F S)
    (hlifts : ∀ a b, a + b ∈ lineDirections F S →
      UnorderedLiftWitness G occurrences a b)
    (hunit : IsSelectedUnitGraph G)
    (hmodule : ∀ z ∈ G.vertices, z ∈ M2)
    (haccount : Counts.BlockAccountingDuty G 3437445 1460199)
    (hheight : ∀ z ∈ G.vertices, ∃ anchor offset : IntegerCode,
      Height49AtMost anchor 3087 ∧ Height49AtMost offset 217 ∧
      z = point49 (anchor + offset)) : Targets.MainConclusion := by
  have hn := physical_obstruction_from_explicit_network G1 G occurrences
    hseed hnet F S hhit hspectral hlifts
  obtain ⟨hv, he⟩ := Counts.bounds_from_block_accounting G 3437445 1460199 haccount
  norm_num only [Nat.cast_ofNat] at hv he
  obtain ⟨av, ae⟩ := Counts.final_budget_arithmetic
  rw [av] at hv
  rw [ae] at he
  exact ⟨G, hunit, hmodule, hn, by exact_mod_cast hv, by exact_mod_cast he,
    Height.graph_height_from_offsets G hheight⟩

/-- Adding all incidental unit pairs preserves the obstruction, by restricting
the same colouring to the selected edges. The selected-edge numerical bound
does not become a bound on this larger graph. -/
theorem obstruction_preserved_by_extra_edges (G H : PhysicalGraph)
    (hGH : ∀ e ∈ G.edges, e ∈ H.edges) (hno : NoFourColouring G) :
    NoFourColouring H := by
  rintro ⟨c, hc⟩
  exact hno ⟨c, restrict_proper G H hGH c hc⟩

/-- R1's finite oriented-edge consumer is exactly the selected graph only
after endpoint injections/deduplication have been proved. -/
structure SharedGraphAdapterDuty {V E : Type*} [Fintype V] [Fintype E]
    (source : Partials.Interface.FiniteEdgeGraph V E) (physical : PhysicalGraph) where
  decode : V → ℂ
  decode_injective : Function.Injective decode
  vertices_exact : physical.vertices = Finset.univ.image decode
  edges_exact : physical.edges = Finset.univ.image
    (fun e => (decode (source.ends e).1, decode (source.ends e).2))

theorem shared_proper_iff_physical {V E : Type*} [Fintype V] [Fintype E]
    (source : Partials.Interface.FiniteEdgeGraph V E) (physical : PhysicalGraph)
    (d : SharedGraphAdapterDuty source physical) (c : ℂ → Colour4) :
    ProperPhysical physical c ↔ Partials.Interface.ProperColoring source (c ∘ d.decode) := by
  classical
  constructor
  · intro hp e
    apply hp (d.decode (source.ends e).1, d.decode (source.ends e).2)
    rw [d.edges_exact]
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ e, rfl⟩
  · intro hp edge he
    rw [d.edges_exact] at he
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp he
    exact hp e

end Partials.UnitDistance.Assembly

end
