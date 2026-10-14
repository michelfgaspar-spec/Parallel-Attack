import Partials.UnitDistance.EqualityGadget

/-! Blind source for main.tex lem:network and prop:finite-obstruction.
Not compiled. Every implication restricts one hypothetical global colouring;
no independently chosen local extension witnesses are assembled. -/
namespace Partials.UnitDistance

structure GadgetOccurrence where
  anchor : ℂ
  direction : UnitIndex
  firstSeedDirection : UnitIndex
  secondSeedDirection : UnitIndex

noncomputable def occurrenceUnit (o : GadgetOccurrence) : ℂ := indexedUnit o.direction
noncomputable def occurrenceEnd (o : GadgetOccurrence) : ℂ := o.anchor + 2 * occurrenceUnit o

structure NetworkAdmission {I : Type*} (G1 G : PhysicalGraph)
    (occurrences : I → GadgetOccurrence) where
  localGraph : I → PhysicalGraph
  localAdmission : ∀ i, EqualityGadgetAdmission G1 (localGraph i)
    (occurrences i).anchor (occurrenceUnit (occurrences i))
    (occurrences i).firstSeedDirection (occurrences i).secondSeedDirection
  selected_inclusion : ∀ i e, e ∈ (localGraph i).edges → e ∈ G.edges

def CoordinateAdjacent (edges : Set (ℂ × ℂ)) (a b : ℂ) : Prop :=
  (a, b) ∈ edges ∨ (b, a) ∈ edges

inductive CoordinateWalk (edges : Set (ℂ × ℂ)) : ℂ → ℂ → Prop
  | refl (a : ℂ) : CoordinateWalk edges a a
  | step {a b c : ℂ} : CoordinateWalk edges a b →
      CoordinateAdjacent edges b c → CoordinateWalk edges a c

theorem coordinate_walk_mono (E F : Set (ℂ × ℂ)) (hEF : E ⊆ F)
    {a b : ℂ} (h : CoordinateWalk E a b) : CoordinateWalk F a b := by
  induction h with
  | refl => exact .refl _
  | step hwalk hedge ih =>
    apply CoordinateWalk.step ih
    rcases hedge with hedge | hedge
    · exact Or.inl (hEF hedge)
    · exact Or.inr (hEF hedge)

def OccurrenceEdges {I : Type*} (occurrences : I → GadgetOccurrence) : Set (ℂ × ℂ) :=
  {e | ∃ i, e = ((occurrences i).anchor, occurrenceEnd (occurrences i))}

theorem restrict_proper (G H : PhysicalGraph)
    (hGH : ∀ e ∈ G.edges, e ∈ H.edges)
    (c : ℂ → Colour4) (hc : ProperPhysical H c) : ProperPhysical G c := by
  intro e he
  exact hc e (hGH e he)

theorem network_edge_colour {I : Type*} (G1 G : PhysicalGraph)
    (occurrences : I → GadgetOccurrence)
    (hseed : ExternalSeedForce G1) (hnet : NetworkAdmission G1 G occurrences)
    (c : ℂ → Colour4) (hc : ProperPhysical G c)
    {a b : ℂ} (h : CoordinateAdjacent (OccurrenceEdges occurrences) a b) :
    c a = c b := by
  have hlocal : ∀ i, c (occurrences i).anchor = c (occurrenceEnd (occurrences i)) := by
    intro i
    exact equality_gadget_forces G1 (hnet.localGraph i)
      (occurrences i).anchor (occurrenceUnit (occurrences i))
      (occurrences i).firstSeedDirection (occurrences i).secondSeedDirection
      hseed (hnet.localAdmission i) c
      (restrict_proper (hnet.localGraph i) G (hnet.selected_inclusion i) c hc)
  rcases h with ⟨i, he⟩ | ⟨i, he⟩
  · have ha := congrArg Prod.fst he
    have hb := congrArg Prod.snd he
    simpa only [Prod.fst, Prod.snd] using
      (congrArg c ha).trans ((hlocal i).trans (congrArg c hb).symm)
  · have hb := congrArg Prod.fst he
    have ha := congrArg Prod.snd he
    simpa only [Prod.fst, Prod.snd] using
      (congrArg c ha).trans ((hlocal i).symm.trans (congrArg c hb).symm)

theorem network_constant_on_walk {I : Type*} (G1 G : PhysicalGraph)
    (occurrences : I → GadgetOccurrence)
    (hseed : ExternalSeedForce G1) (hnet : NetworkAdmission G1 G occurrences)
    (c : ℂ → Colour4) (hc : ProperPhysical G c)
    {a b : ℂ} (hwalk : CoordinateWalk (OccurrenceEdges occurrences) a b) :
    c a = c b := by
  induction hwalk with
  | refl => rfl
  | step hwalk hedge ih =>
    exact ih.trans (network_edge_colour G1 G occurrences hseed hnet c hc hedge)

/-- Preserving required forest paths suffices. The exact terminal relation
and the complete colouring set of an older geometric network need not be
preserved by removing redundant occurrences. -/
theorem retained_forest_implication {I : Type*} (G1 G : PhysicalGraph)
    (retained : I → GadgetOccurrence)
    (hseed : ExternalSeedForce G1) (hnet : NetworkAdmission G1 G retained)
    (c : ℂ → Colour4) (hc : ProperPhysical G c)
    (a b : ℂ) (hpath : CoordinateWalk (OccurrenceEdges retained) a b) :
    c a = c b :=
  network_constant_on_walk G1 G retained hseed hnet c hc hpath

def LiftProperQuotient (edge : BinaryCode → BinaryCode → Prop)
    (colour : BinaryCode → Colour4) : Prop :=
  ∀ a b, edge a b → colour a ≠ colour b

/-- The fixed recipe stores one lift per unordered quotient edge, oriented
by a<b. An arbitrary ordered adjacency therefore has a forward OR reversed
witness. Reversal does not request a second geometric gadget occurrence. -/
def UnorderedLiftWitness {I : Type*} (G : PhysicalGraph)
    (occurrences : I → GadgetOccurrence) (a b : BinaryCode) : Prop :=
  (∃ p : ℂ, CoordinateWalk (OccurrenceEdges occurrences) («section» b) p ∧
    SelectedUndirectedEdge G («section» a) p) ∨
  (∃ p : ℂ, CoordinateWalk (OccurrenceEdges occurrences) («section» a) p ∧
    SelectedUndirectedEdge G («section» b) p)

theorem unordered_lifts_give_quotient_colouring {I : Type*}
    (G1 G : PhysicalGraph) (occurrences : I → GadgetOccurrence)
    (hseed : ExternalSeedForce G1) (hnet : NetworkAdmission G1 G occurrences)
    (edge : BinaryCode → BinaryCode → Prop)
    (hlifts : ∀ a b, edge a b → UnorderedLiftWitness G occurrences a b)
    (c : ℂ → Colour4) (hc : ProperPhysical G c) :
    LiftProperQuotient edge (fun a ↦ c («section» a)) := by
  intro a b hab
  rcases hlifts a b hab with ⟨p, hpath, hedge⟩ | ⟨p, hpath, hedge⟩
  · have heq := network_constant_on_walk G1 G occurrences hseed hnet c hc hpath
    have hne := proper_selected_undirected G c hc («section» a) p hedge
    simpa only [← heq] using hne
  · have heq := network_constant_on_walk G1 G occurrences hseed hnet c hc hpath
    have hne := proper_selected_undirected G c hc («section» b) p hedge
    have hreverse : c («section» b) ≠ c («section» a) := by
      simpa only [← heq] using hne
    exact Ne.symm hreverse

/-- Concrete assembly interface: one of the frozen 110592 a<b lifts covers
each ordered quotient adjacency, with reversal of the resulting inequality
when needed. No additional physical occurrences are required. -/
theorem finite_unordered_lift_obstruction {I : Type*}
    (G1 G : PhysicalGraph) (occurrences : I → GadgetOccurrence)
    (hseed : ExternalSeedForce G1) (hnet : NetworkAdmission G1 G occurrences)
    (edge : BinaryCode → BinaryCode → Prop)
    (hlifts : ∀ a b, edge a b → UnorderedLiftWitness G occurrences a b)
    (hquotient : ¬ ∃ colour : BinaryCode → Colour4, LiftProperQuotient edge colour) :
    NoFourColouring G := by
  rintro ⟨c, hc⟩
  exact hquotient ⟨fun a ↦ c («section» a),
    unordered_lifts_give_quotient_colouring G1 G occurrences hseed hnet
      edge hlifts c hc⟩

/-- Stronger directed helper. Its premise requests a forward lift for EVERY
ordered adjacency and is not the frozen a<b recipe's concrete interface.
Use UnorderedLiftWitness for that recipe. -/
theorem lifted_unit_edges_give_quotient_colouring {I : Type*}
    (G1 G : PhysicalGraph) (occurrences : I → GadgetOccurrence)
    (hseed : ExternalSeedForce G1) (hnet : NetworkAdmission G1 G occurrences)
    (edge : BinaryCode → BinaryCode → Prop) (endpoint : BinaryCode → BinaryCode → ℂ)
    (hpaths : ∀ a b, edge a b →
      CoordinateWalk (OccurrenceEdges occurrences) («section» b) (endpoint a b))
    (hedges : ∀ a b, edge a b → («section» a, endpoint a b) ∈ G.edges)
    (c : ℂ → Colour4) (hc : ProperPhysical G c) :
    LiftProperQuotient edge (fun a ↦ c («section» a)) := by
  intro a b hab
  have heq := network_constant_on_walk G1 G occurrences hseed hnet c hc (hpaths a b hab)
  have hne := hc («section» a, endpoint a b) (hedges a b hab)
  simpa only [← heq] using hne

/-- Stronger directed assembly helper, with the same ordered-lift caveat as
lifted_unit_edges_give_quotient_colouring. The independent quotient obstruction
is consumed after deriving its colouring; it is not the physical headline. -/
theorem finite_lift_obstruction {I : Type*}
    (G1 G : PhysicalGraph) (occurrences : I → GadgetOccurrence)
    (hseed : ExternalSeedForce G1) (hnet : NetworkAdmission G1 G occurrences)
    (edge : BinaryCode → BinaryCode → Prop) (endpoint : BinaryCode → BinaryCode → ℂ)
    (hpaths : ∀ a b, edge a b →
      CoordinateWalk (OccurrenceEdges occurrences) («section» b) (endpoint a b))
    (hedges : ∀ a b, edge a b → («section» a, endpoint a b) ∈ G.edges)
    (hquotient : ¬ ∃ colour : BinaryCode → Colour4, LiftProperQuotient edge colour) :
    NoFourColouring G := by
  rintro ⟨c, hc⟩
  exact hquotient ⟨fun a ↦ c («section» a),
    lifted_unit_edges_give_quotient_colouring G1 G occurrences hseed hnet
      edge endpoint hpaths hedges c hc⟩

end Partials.UnitDistance
