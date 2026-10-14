import Partials.UnitDistance.Model

/-! Blind source for main.tex lines 208–301. Not compiled or evaluated.
The imported Haugland terminal theorem and exact transported-source geometry
are separate inputs. In particular a retained SAT status UNKNOWN is not an
UNSAT proof. All consequences below are necessary colouring constraints. -/
namespace Partials.UnitDistance

noncomputable def gadgetA (x u : ℂ) : ℂ := x
noncomputable def gadgetB (x u : ℂ) : ℂ := x + 2 * u
noncomputable def gadgetC (x u : ℂ) : ℂ := x + u
noncomputable def gadgetD (x u : ℂ) : ℂ := x + rho * u
noncomputable def gadgetE (x u : ℂ) : ℂ := x + (1 + rho) * u

def SkeletonColourConstraints (a b c d e : Colour4) : Prop :=
  c ≠ d ∧ c ≠ e ∧ d ≠ e ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ e

/-- Finite four-palette pigeonhole reasoning. `fin_cases` is unexecuted
source; this theorem does not invoke a seed SAT solver. -/
theorem fourth_colour_unique (a b c d e : Colour4)
    (h : SkeletonColourConstraints a b c d e)
    (hae : a ≠ e) (hdb : d ≠ b) : a = b := by
  rcases h with ⟨hcd, hce, hde, hac, had, hbc, hbe⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    fin_cases e <;> simp_all

def VirtualBoundaryRelation (a b : Colour4) : Prop :=
  ∃ c d e : Colour4,
    SkeletonColourConstraints a b c d e ∧ a ≠ e ∧ d ≠ b

theorem virtual_relation_eq (a b : Colour4) :
    VirtualBoundaryRelation a b ↔ a = b := by
  constructor
  · rintro ⟨c, d, e, h, hae, hdb⟩
    exact fourth_colour_unique a b c d e h hae hdb
  · intro h
    subst b
    fin_cases a <;> unfold VirtualBoundaryRelation SkeletonColourConstraints <;> decide

/-- Source adapters may choose either orientation for the one retained
unordered edge. This preserves colour semantics after deduplication. -/
def SelectedUndirectedEdge (G : PhysicalGraph) (a b : ℂ) : Prop :=
  (a, b) ∈ G.edges ∨ (b, a) ∈ G.edges

theorem proper_selected_undirected (G : PhysicalGraph) (c : ℂ → Colour4)
    (hc : ProperPhysical G c) (a b : ℂ) (he : SelectedUndirectedEdge G a b) :
    c a ≠ c b := by
  rcases he with he | he
  · exact hc (a, b) he
  · exact Ne.symm (hc (b, a) he)

theorem transported_external_force (G1 : PhysicalGraph)
    (hseed : ExternalSeedForce G1) (F : ℂ → ℂ) (a b : ℂ)
    (hzero : F 0 = a) (hterminal : F delta = b)
    (G : PhysicalGraph)
    (hcopy : ∀ e ∈ G1.edges, SelectedUndirectedEdge G (F e.1) (F e.2))
    (c : ℂ → Colour4) (hc : ProperPhysical G c) : c a ≠ c b := by
  have hproper : ProperPhysical G1 (fun z ↦ c (F z)) := by
    intro e he
    exact proper_selected_undirected G c hc (F e.1) (F e.2) (hcopy e he)
  have hf := hseed (fun z ↦ c (F z)) hproper
  simpa only [hzero, hterminal] using hf

theorem seedTransport_third (i : UnitIndex) (z : ℂ)
    (hj : i.1.val = 2) : seedTransport i z = -(indexedUnit i) * star z := by
  simp only [seedTransport, if_pos hj]

theorem seedTransport_other (i : UnitIndex) (z : ℂ)
    (hj : i.1.val ≠ 2) : seedTransport i z = indexedUnit i * z := by
  simp only [seedTransport, if_neg hj]

/-- Primitive source/geometry duties for a transported seed. The reflected
third-shell membership is stated explicitly; neither a colouring implication
nor a final obstruction/count is a field of this structure. -/
structure SeedApplicabilityDuty (G1 : PhysicalGraph) : Prop where
  source_points : ∀ z ∈ G1.vertices, z ∈ M1
  source_units : IsSelectedUnitGraph G1
  source_terminals : 0 ∈ G1.vertices ∧ delta ∈ G1.vertices
  transport_zero : ∀ i : UnitIndex, seedTransport i 0 = 0
  transport_terminal : ∀ i : UnitIndex,
    seedTransport i delta = indexedUnit i * delta
  transport_isometry : ∀ i : UnitIndex, ∀ a b : ℂ,
    UnitDistance a b → UnitDistance (seedTransport i a) (seedTransport i b)
  transport_membership : ∀ i : UnitIndex, ∀ z ∈ M1, seedTransport i z ∈ M2
  reflected_third_shell : ∀ i : UnitIndex, i.1.val = 2 →
    ∀ z ∈ M1, -(indexedUnit i) * star z ∈ M2

/-- Exact seven-edge and seed-image admission for the physical gadget.
First/second terminal identities are cyclotomic algebra duties, not supplied
colour inequalities. Point identification and unordered-edge deduplication
remain in the concrete consumer adapter. -/
structure EqualityGadgetAdmission (G1 G : PhysicalGraph) (x u : ℂ)
    (first second : UnitIndex) : Prop where
  first_direction : indexedUnit first = rho⁻¹ * u
  second_direction : indexedUnit second = -rho * u
  first_zero : x + seedTransport first 0 = gadgetA x u
  first_terminal : x + seedTransport first delta = gadgetE x u
  second_zero : gadgetD x u + seedTransport second 0 = gadgetD x u
  second_terminal : gadgetD x u + seedTransport second delta = gadgetB x u
  edge_CD : SelectedUndirectedEdge G (gadgetC x u) (gadgetD x u)
  edge_CE : SelectedUndirectedEdge G (gadgetC x u) (gadgetE x u)
  edge_DE : SelectedUndirectedEdge G (gadgetD x u) (gadgetE x u)
  edge_AC : SelectedUndirectedEdge G (gadgetA x u) (gadgetC x u)
  edge_AD : SelectedUndirectedEdge G (gadgetA x u) (gadgetD x u)
  edge_BC : SelectedUndirectedEdge G (gadgetB x u) (gadgetC x u)
  edge_BE : SelectedUndirectedEdge G (gadgetB x u) (gadgetE x u)
  first_edges : ∀ e ∈ G1.edges,
    SelectedUndirectedEdge G (x + seedTransport first e.1) (x + seedTransport first e.2)
  second_edges : ∀ e ∈ G1.edges,
    SelectedUndirectedEdge G (gadgetD x u + seedTransport second e.1)
      (gadgetD x u + seedTransport second e.2)

theorem equality_gadget_forces (G1 G : PhysicalGraph) (x u : ℂ)
    (first second : UnitIndex) (hseed : ExternalSeedForce G1)
    (h : EqualityGadgetAdmission G1 G x u first second)
    (c : ℂ → Colour4) (hc : ProperPhysical G c) :
    c (gadgetA x u) = c (gadgetB x u) := by
  have hae := transported_external_force G1 hseed
    (fun z ↦ x + seedTransport first z) (gadgetA x u) (gadgetE x u)
    h.first_zero h.first_terminal G h.first_edges c hc
  have hdb := transported_external_force G1 hseed
    (fun z ↦ gadgetD x u + seedTransport second z)
    (gadgetD x u) (gadgetB x u) h.second_zero h.second_terminal
    G h.second_edges c hc
  apply fourth_colour_unique
    (c (gadgetA x u)) (c (gadgetB x u))
    (c (gadgetC x u)) (c (gadgetD x u)) (c (gadgetE x u))
  · exact ⟨proper_selected_undirected G c hc _ _ h.edge_CD,
      proper_selected_undirected G c hc _ _ h.edge_CE,
      proper_selected_undirected G c hc _ _ h.edge_DE,
      proper_selected_undirected G c hc _ _ h.edge_AC,
      proper_selected_undirected G c hc _ _ h.edge_AD,
      proper_selected_undirected G c hc _ _ h.edge_BC,
      proper_selected_undirected G c hc _ _ h.edge_BE⟩
  · exact hae
  · exact hdb

def PhysicalTerminalRelation (G : PhysicalGraph) (a b : ℂ)
    (ca cb : Colour4) : Prop :=
  ∃ c : ℂ → Colour4, ProperPhysical G c ∧ c a = ca ∧ c b = cb

/-- Subset EQ only. No extension witness, nonemptiness or equivalence with
the virtual relation is asserted for the actual seed interiors. -/
theorem physical_gadget_relation_subset_eq (G1 G : PhysicalGraph)
    (x u : ℂ) (first second : UnitIndex) (hseed : ExternalSeedForce G1)
    (h : EqualityGadgetAdmission G1 G x u first second)
    (ca cb : Colour4)
    (hr : PhysicalTerminalRelation G (gadgetA x u) (gadgetB x u) ca cb) :
    ca = cb := by
  rcases hr with ⟨c, hc, ha, hb⟩
  rw [← ha, ← hb]
  exact equality_gadget_forces G1 G x u first second hseed h c hc

end Partials.UnitDistance
