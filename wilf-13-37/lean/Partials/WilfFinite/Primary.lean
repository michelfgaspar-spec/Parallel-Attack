import Partials.WilfFinite.PrefixPruning

/-! Exact abstract PRIMARY control flow, not the historical residual-profile
program. Relations describe mathematical calls without executing a traversal.
Full exactness remains an open interface in PrefixTargets; supporting label,
measure and finiteness propositions have separate P4 inhabitants.
The output record derives all fields from one immutable canonical state. -/
namespace Partials.WilfFinite.Prefix

structure OutputRecord where
  state : Core.CanonicalState
  G : List ℕ
  m : ℕ
  k : ℕ
  ell : ℕ
  r : ℕ
  e : ℕ
  q : ℕ
  rho : ℕ
  W0 : ℤ
  W : ℤ

noncomputable def currentRecord (s : PrefixState) : OutputRecord :=
  ⟨s.canonical,s.G,s.m,k s,ell s,r s,e s,q s,rho s,W0 s,W s⟩

def outputKey (o : OutputRecord) : ℕ × Finset ℕ := Core.key o.state
def OutputPredicate (p : Core.Parameters) (s : PrefixState) : Prop :=
  Core.InTarget p s.canonical ∧ W0 s<0
def ProductGate (s : PrefixState) : Prop := c s≤(k s+1)*(ell s+1)
noncomputable def TailGate (s : PrefixState) (a : ℕ) : Prop :=
  ∃ gamma : ℕ, s.G[1]?=some gamma ∧ c s+s.m≤a+gamma ∧ 0≤W0 s+Delta s

inductive NodeExit where
  | rankUpper | product | expand
inductive CandidateAction where
  | alreadyGenerated | largeTail | reconstruct

structure NodePlan where
  output : Option OutputRecord
  exit : NodeExit

/-- Upper rank first; current output next; product exit last. W itself is not
tested. Both low-cardinality and nonnegative-W0 nodes can reach `expand`. -/
noncomputable def nodePlan (p : Core.Parameters) (s : PrefixState) : NodePlan := by
  classical
  exact if p.v<k s then ⟨none,.rankUpper⟩ else
    ⟨if OutputPredicate p s then some (currentRecord s) else none,
      if ProductGate s then .product else .expand⟩

noncomputable def candidateAction (s : PrefixState) (a : ℕ) : CandidateAction := by
  classical
  exact if a∈Core.left s.canonical then .alreadyGenerated else
    if TailGate s a then .largeTail else .reconstruct

theorem current_output_before_product (p : Core.Parameters) (s : PrefixState)
    (ho : OutputPredicate p s) : (nodePlan p s).output=some (currentRecord s) := by
  classical
  have hupper : ¬p.v<k s := by
    have hk := ho.1.2.2
    change k s≤p.v at hk
    omega
  simp [nodePlan,hupper,ho]

theorem product_exit_after_output (p : Core.Parameters) (s : PrefixState)
    (hupper : k s≤p.v) (hprod : ProductGate s) :
    (nodePlan p s).exit=.product := by
  classical
  simp [nodePlan,show ¬p.v<k s by omega,hprod]

/-- With the two specified exit conditions absent, expansion is independent
of the current W0 sign and of the lower output-cardinality bound. -/
theorem node_expands (p : Core.Parameters) (s : PrefixState)
    (hupper : k s≤p.v) (hprod : ¬ProductGate s) :
    (nodePlan p s).exit=.expand := by
  classical
  simp [nodePlan, show ¬p.v<k s by omega, hprod]

theorem generated_candidate_precedes_tail (s : PrefixState) (a : ℕ)
    (ha : a∈Core.left s.canonical) : candidateAction s a=.alreadyGenerated := by
  classical
  simp [candidateAction,ha]

theorem seed_has_no_second_gate (s : PrefixState) (hs : ∃ m, s.G=[m]) (a : ℕ) :
    ¬TailGate s a := by
  obtain ⟨m,hm⟩ := hs
  rintro ⟨gamma,hgamma,_,_⟩
  simp [hm] at hgamma

def Seed (p : Core.Parameters) (s : PrefixState) : Prop :=
  c s≤p.C ∧ s.G=[s.m]

/-- The ordinary account includes every integer conductor 2 through C,
independently of whether the nonordinary multiplicity range is empty. -/
def OrdinaryAccount (p : Core.Parameters) (a : Core.CanonicalState) : Prop :=
  ∃ (c : ℕ) (hc : 2≤c), c≤p.C ∧ a=ordinaryCanonical c hc

theorem ordinary_account_all_conductors (p : Core.Parameters) (c : ℕ)
    (hc : 2≤c) (hC : c≤p.C) : OrdinaryAccount p (ordinaryCanonical c hc) :=
  ⟨c,hc,hC,rfl⟩

/-- Finite increasing candidate loop: all earlier non-generated candidates
must pass the suffix gate. This captures LARGE_TAIL returning from the entire
remaining suffix, and does not replace it by a single-candidate skip. -/
noncomputable def CandidateReachable (s : PrefixState) (a : ℕ) : Prop :=
  b s<a ∧ a<c s ∧ a∉Core.left s.canonical ∧
  ∀ d : ℕ, b s<d → d≤a → d∉Core.left s.canonical → ¬TailGate s d

theorem tail_gate_upward (s : PrefixState) (a z : ℕ)
    (ha : TailGate s a) (haz : a≤z) : TailGate s z := by
  obtain ⟨gamma,hgamma,hbound,hguard⟩ := ha
  exact ⟨gamma,hgamma,by omega,hguard⟩

/-- An earlier nongenerated LARGE_TAIL candidate ends the entire suffix.
This is the actual CandidateReachable predicate, not a single-value skip. -/
theorem tail_stops_candidate_suffix (s : PrefixState) (a z : ℕ)
    (hba : b s<a) (hagap : a∉Core.left s.canonical)
    (htail : TailGate s a) (haz : a≤z) : ¬CandidateReachable s z := by
  intro hz
  exact hz.2.2.2 a hba haz hagap htail

inductive Visited (p : Core.Parameters) : PrefixState → Prop
  | seed {s : PrefixState} : Seed p s → Visited p s
  | child {s t : PrefixState} {a : ℕ} : Visited p s → k s≤p.v →
      ¬ProductGate s → CandidateReachable s a → Child s t a → Visited p t

def Emits (p : Core.Parameters) (s : PrefixState) : Prop :=
  Visited p s ∧ OutputPredicate p s

noncomputable def primaryRecords (p : Core.Parameters) : Set OutputRecord :=
  {o | ∃ s : PrefixState, Emits p s ∧ o=currentRecord s}

theorem emitted_record_fields (p : Core.Parameters) (o : OutputRecord)
    (ho : o∈primaryRecords p) :
    ∃ s : PrefixState, Visited p s ∧ OutputPredicate p s ∧
      o.state=s.canonical ∧ o.G=s.G ∧ o.m=s.m ∧ o.k=k s ∧
      o.ell=ell s ∧ o.r=r s ∧ o.e=ell s+r s ∧ o.q=q s ∧
      o.rho=rho s ∧ o.W0=W0 s ∧ o.W=W s := by
  obtain ⟨s,⟨hvisit,hpred⟩,rfl⟩ := ho
  exact ⟨s,hvisit,hpred,rfl,rfl,rfl,rfl,rfl,rfl,full_embedding_dimension s,
    rfl,rfl,rfl,rfl⟩

theorem output_is_in_target (p : Core.Parameters) (o : OutputRecord)
    (ho : o∈primaryRecords p) : Core.InTarget p o.state ∧ o.W0<0 := by
  obtain ⟨s,⟨_,hpred⟩,rfl⟩ := ho
  exact hpred

/-- No arithmetic sign is assumed: the decreasing measure is stated for each
actual append. Its list-maximum proof remains in the target module. -/
def measure (s : PrefixState) : ℕ := c s-1-b s

end Partials.WilfFinite.Prefix
