import Partials.WilfFinite.ForestChecker

/-! Noncircular finite producer existence and local reconstruction kernels.
There is no universal target-coverage field in the certificate grammar. The
fixed-conductor PRIMARY path/pruning adapter is stated separately below.
All declarations are blind source and UNCOMPILED. -/
namespace Partials.WilfFinite.Forest
open Partials.WilfFinite.Core
open Partials.Interface

theorem forest_of_nodes (p : Parameters) (labels : List Label) :
    (∀ l ∈ labels, ∃ events outputs, NodeCertificate p l events outputs) →
    ∃ events outputs, ForestCertificate p labels events outputs := by
  induction labels with
  | nil => intro h; exact ⟨[],[],.nil⟩
  | cons l labels ih =>
    intro h
    obtain ⟨es,os,hn⟩ := h l (by simp)
    obtain ⟨tail,more,hf⟩ := ih (fun b hb => h b (by simp [hb]))
    exact ⟨es++tail,os++more,.cons hn hf⟩

/-- A finite abstract certificate exists independently of every W sign.
It is obtained from exact local entries and all required constructed children,
by induction on c-1-max(G), rather than an asserted universal coverage flag. -/
theorem finite_node_certificate_exists (p : Parameters) (l : Label) :
    ∃ events outputs, NodeCertificate p l events outputs := by
  have build : ∀ n : ℕ, ∀ l : Label, rank l = n →
      ∃ events outputs, NodeCertificate p l events outputs := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro l hl
      have hk : ∀ b ∈ requiredChildren p l,
          ∃ events outputs, NodeCertificate p b events outputs := by
        intro b hb
        exact ih (rank b) (by simpa [hl] using child_rank_decreases p l b hb) b rfl
      obtain ⟨body,outs,hbody⟩ := forest_of_nodes p (requiredChildren p l) hk
      exact ⟨.enter (exactEntry p l)::(body++[.exit]),
        (expectedOutput p l).toList++outs,
        .node (exactEntry_matches p l) hbody⟩
  exact build (rank l) l rfl

theorem finite_root_forest_exists (p : Parameters) :
    ∃ events outputs, ForestCertificate p (rootLabels p) events outputs :=
  forest_of_nodes p (rootLabels p) (fun l _ => finite_node_certificate_exists p l)

def abstractHeader (p : Parameters) : Header :=
  ⟨p.C,p.u,p.v,"fixed-c-ordered-left-dfs-v1",
    "actual-conductor-complete-left-sorted-v1","signed-exact-unique-zero-v1",
    "balanced-enter-exit-length-prefixed-v1","noncanonical-rank-output-product-tail-gaps-v1",
    "abstract-local-producer-v1","abstract-local-checker-v1","frozen-general-certificate-v1",
    (ordinaryConductors p).map (fun c => (c,ordinaryFields c))⟩

theorem abstractHeader_matches (p : Parameters) : HeaderMatches p (abstractHeader p) := by
  simp [HeaderMatches,abstractHeader]

theorem accepted_forest_exists (p : Parameters) :
    ∃ h events outputs, Accepted p h events outputs := by
  obtain ⟨events,outputs,hf⟩ := finite_root_forest_exists p
  exact ⟨abstractHeader p,events,outputs,abstractHeader_matches p,hf⟩

theorem positive_summand_test (l : Label) (h : CanonicalLabel l) (x : ℕ) :
    (∃ y : ℕ, 0 < y ∧ y < x ∧ Member l y ∧ Member l (x-y)) ↔
    IsDecomposable (semigroup (canonicalState l h)) x := by
  constructor
  · rintro ⟨y,hy,hyx,hyS,hrem⟩
    exact ⟨y,x-y,hy,by omega,
      (independent_membership l h y).2 hyS,
      (independent_membership l h (x-y)).2 hrem,by omega⟩
  · rintro ⟨a,b,ha,hb,haS,hbS,heq⟩
    have hrem : x-a = b := by omega
    exact ⟨a,ha,by omega,(independent_membership l h a).1 haS,
      by rw [hrem]; exact (independent_membership l h b).1 hbS⟩

theorem independent_primitive_test (l : Label) (h : CanonicalLabel l) (x : ℕ) :
    Primitive l x ↔ IsPrimitive (semigroup (canonicalState l h)) x := by
  rw [Primitive, IsPrimitive, ← independent_membership l h x,
    ← positive_summand_test l h x]
  tauto

def MultiplicityCorrect (l : Label) (h : CanonicalLabel l) : Prop :=
  IsMultiplicity (semigroup (canonicalState l h)) l.m

noncomputable def reconstructedData (l : Label) (h : CanonicalLabel l)
    (hm : MultiplicityCorrect l h) : Partials.WilfStructural.Foundation.Data :=
  ⟨semigroup (canonicalState l h),l.c,l.m,actual_conductor _,hm,by have hc := h.1; omega⟩

theorem all_primitive_test (l : Label) (h : CanonicalLabel l)
    (hm : MultiplicityCorrect l h) (x : ℕ) :
    x ∈ rebuiltPrimitives l ↔ IsPrimitive (semigroup (canonicalState l h)) x := by
  classical
  simp only [rebuiltPrimitives,Finset.mem_filter,Finset.mem_range]
  rw [independent_primitive_test l h]
  exact ⟨And.right,fun hx =>
    ⟨Partials.WilfStructural.Foundation.primitive_cutoff (reconstructedData l h hm) hx,hx⟩⟩

theorem output_reconstructs_target (p : Parameters) (l : Label)
    (hc : 2 ≤ l.c) (hC : l.c ≤ p.C) (hout : NeedsOutput p l) :
    ∃ a : CanonicalState, key a = (exactOutput l).identity ∧ InTarget p a := by
  let a := canonicalState l ⟨hc,hout.1⟩
  refine ⟨a,rfl,?_⟩
  exact ⟨hC,hout.2.2.1,hout.2.1⟩

theorem expected_output_exact (p : Parameters) (l : Label) (o : Output)
    (h : expectedOutput p l = some o) : NeedsOutput p l ∧ o = exactOutput l := by
  classical
  unfold expectedOutput at h
  split_ifs at h with hp
  exact ⟨hp,(Option.some.inj h).symm⟩

inductive Reachable (p : Parameters) : Label → Prop
  | root {l : Label} : l ∈ rootLabels p → Reachable p l
  | child {l b : Label} : Reachable p l → b ∈ requiredChildren p l → Reachable p b

def GroundRecord (p : Parameters) (o : Output) : Prop :=
  ∃ l, Reachable p l ∧ NeedsOutput p l ∧ o = exactOutput l

theorem forest_node_lookup (p : Parameters) (labels : List Label)
    (events : List Event) (outputs : List Output)
    (hc : ForestCertificate p labels events outputs) (l : Label) (hl : l ∈ labels) :
    ∃ es os, NodeCertificate p l es os ∧ ∀ o ∈ os, o ∈ outputs := by
  induction labels generalizing events outputs with
  | nil => simp at hl
  | cons first labels ih =>
    cases hc with
    | cons hn hf =>
      rcases List.mem_cons.mp hl with hfirst | htail
      · subst l
        exact ⟨_,_,hn,fun o ho => List.mem_append_left _ ho⟩
      · obtain ⟨es,os,hs,hsub⟩ := ih _ _ hf htail
        exact ⟨es,os,hs,fun o ho => List.mem_append_right _ (hsub o ho)⟩

theorem reachable_node_lookup (p : Parameters) (events : List Event)
    (outputs : List Output) (hc : ForestCertificate p (rootLabels p) events outputs)
    (l : Label) (hl : Reachable p l) :
    ∃ es os, NodeCertificate p l es os ∧ ∀ o ∈ os, o ∈ outputs := by
  induction hl with
  | root hroot => exact forest_node_lookup p _ _ _ hc _ hroot
  | @child parent child hparent hchild ih =>
    obtain ⟨es,os,hn,hsub⟩ := ih
    cases hn with
    | node hm hk =>
      obtain ⟨childEs,childOs,hcn,hcsub⟩ := forest_node_lookup p _ _ _ hk child hchild
      exact ⟨childEs,childOs,hcn,fun o ho =>
        hsub o (List.mem_append_right _ (hcsub o ho))⟩

theorem required_output_in_node (p : Parameters) (l : Label)
    (events : List Event) (outputs : List Output)
    (hc : NodeCertificate p l events outputs) (hneed : NeedsOutput p l) :
    exactOutput l ∈ outputs := by
  classical
  cases hc with
  | @node l entry body outs hm hk =>
    have he : expectedOutput p l = some (exactOutput l) := by simp [expectedOutput,hneed]
    have hout : exactOutput l ∈ entry.output.toList := by
      rw [hm.2.2,he]
      simp
    exact List.mem_append_left _ hout

/-- Every reachable local output is present in any closed local forest.
This is proved from exact child indexing, before the PRIMARY target adapter. -/
theorem ground_record_present (p : Parameters) (events : List Event)
    (outputs : List Output) (hc : ForestCertificate p (rootLabels p) events outputs)
    (o : Output) (ho : GroundRecord p o) : o ∈ outputs := by
  obtain ⟨l,hl,hneed,rfl⟩ := ho
  obtain ⟨es,os,hn,hsub⟩ := reachable_node_lookup p events outputs hc l hl
  exact hsub _ (required_output_in_node p l es os hn hneed)

/-- The converse is an induction on total retained event length. Both the
child body and the following forest are smaller after stripping ENTER/EXIT.
No universal canonical target coverage is assumed in this induction. -/
theorem local_forest_outputs_origin (p : Parameters) : ∀ labels events outputs,
    ForestCertificate p labels events outputs →
    (∀ l ∈ labels, Reachable p l) → ∀ o ∈ outputs, GroundRecord p o := by
  have sound : ∀ n : ℕ, ∀ labels events outputs, events.length=n →
      ForestCertificate p labels events outputs →
      (∀ l ∈ labels, Reachable p l) → ∀ o ∈ outputs, GroundRecord p o := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro labels events outputs hn hc hr o ho
      cases hc with
      | nil => simp at ho
      | @cons l ls nodeEvents rest nodeOut more hnode hrest =>
        have hl : Reachable p l := hr l (by simp)
        cases hnode with
        | @node l entry body childOut hm hk =>
          rcases List.mem_append.mp ho with hnodeOut | hmore
          · rcases List.mem_append.mp hnodeOut with hhere | hchild
            · have he : expectedOutput p l = some o := by
                rw [← hm.2.2]
                simpa using hhere
              obtain ⟨hneed,heq⟩ := expected_output_exact p l o he
              exact ⟨l,hl,hneed,heq⟩
            · have hsmall : body.length < n := by
                simp only [List.length_append,List.length_cons,List.length_singleton] at hn
                omega
              exact ih body.length hsmall (requiredChildren p l) body childOut rfl hk
                (fun b hb => .child hl hb) o hchild
          · have hsmall : rest.length < n := by
              simp only [List.length_append,List.length_cons,List.length_singleton] at hn
              omega
            exact ih rest.length hsmall ls rest more rfl hrest
              (fun b hb => hr b (by simp [hb])) o hmore
  intro labels events outputs hc hr o ho
  exact sound events.length labels events outputs rfl hc hr o ho

theorem local_grammar_output_exact (p : Parameters) (h : Header)
    (events : List Event) (outputs : List Output) (ha : Accepted p h events outputs)
    (o : Output) : o ∈ outputs ↔ GroundRecord p o := by
  constructor
  · exact local_forest_outputs_origin p _ _ _ ha.2
      (fun l hl => .root hl) o
  · exact ground_record_present p events outputs ha.2 o

def Verified (p : Parameters) (h : Header) (events : List Event)
    (outputs : List Output) : Prop :=
  Accepted p h events outputs ∧ ∀ o ∈ outputs, 0 ≤ o.fields.W

/-- Negative witness validation is independent of forest closure, counts and
resource outcomes. Its adapter requires actual primitive/multiplicity agreement.
One such record suffices; malformed or omitted records provide no witness. -/
def NegativeWitness (p : Parameters) : Prop :=
  ∃ (l : Label) (hc : CanonicalLabel l), l.c ≤ p.C ∧
    p.u ≤ (reconstruct l).k ∧ (reconstruct l).k ≤ p.v ∧
    PrimitiveListCorrect l ∧ MultiplicityCorrect l hc ∧ (reconstruct l).W < 0

inductive Result
  | verified
  | counterexample
  | unresolved
  deriving DecidableEq

def OutcomeSound (p : Parameters) (h : Header) (events : List Event)
    (outputs : List Output) : Result → Prop
  | .verified => Verified p h events outputs
  | .counterexample => NegativeWitness p
  | .unresolved => True

theorem unresolved_has_no_witness_premise (p : Parameters) (h : Header)
    (events : List Event) (outputs : List Output) :
    OutcomeSound p h events outputs .unresolved := True.intro

/-- Only canonical-key uniqueness remains here after the concrete local output
equivalence above. It additionally needs primitive-list/multiplicity agreement;
different generator labels must not be conflated merely by aggregate counts. -/
def LocalGrammarOutputTarget : Prop := ∀ p h events outputs,
  Accepted p h events outputs →
    (outputs.map Output.identity).Nodup

/-- Mathematical adapter to the fixed-c PRIMARY model. It must be proved using
primitive reconstruction, unique ordered paths, and the exact product/tail
lemmas. It cannot be filled by assuming the desired target coverage. -/
def PrimaryModelAdapter (actualW0 : CanonicalState → ℤ) : Prop :=
  ∀ p o, GroundRecord p o ↔
    ∃ a : CanonicalState, InTarget p a ∧ actualW0 a < 0 ∧
      o.identity = key a ∧
      ∃ (l : Label) (hc : CanonicalLabel l),
        MultiplicityCorrect l hc ∧ PrimitiveListCorrect l ∧
        o = exactOutput l ∧ key a = (l.c,rebuiltLeft l)

end Partials.WilfFinite.Forest
