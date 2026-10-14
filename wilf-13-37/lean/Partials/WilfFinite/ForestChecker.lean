import Partials.WilfFinite.ForestModel

/-! Local proof-relevant certificate grammar and an independent stack relation.
Acceptance tests no universal target-coverage proposition. All node exits,
including inert gap children, must appear in the grammar. UNCOMPILED R10. -/
namespace Partials.WilfFinite.Forest
open Partials.WilfFinite.Core

def ordinaryConductors (p : Parameters) : List ℕ :=
  (List.range (p.C+1)).filter (fun c => 2 ≤ c)

def rootLabels (p : Parameters) : List Label :=
  (ordinaryConductors p).flatMap (fun c =>
    ((List.range c).filter (fun m => 2 ≤ m)).map (fun m => ⟨c,m,[m]⟩))

def ordinaryFields (c : ℕ) : Fields :=
  ⟨{0},[],c,c,1,0,c,c,1,0,0,0⟩

theorem ordinary_wilf_accounting (c : ℕ) :
    (ordinaryFields c).W0=0 ∧ (ordinaryFields c).W=0 := ⟨rfl,rfl⟩

structure Header where
  C : ℕ
  u : ℕ
  v : ℕ
  algorithmRevision : String
  stateRepresentation : String
  integerRepresentation : String
  grammarRevision : String
  gateRevision : String
  producerRevision : String
  checkerRevision : String
  specificationRevision : String
  ordinary : List (ℕ × Fields)

def HeaderMatches (p : Parameters) (h : Header) : Prop :=
  h.C = p.C ∧ h.u = p.u ∧ h.v = p.v ∧
  h.algorithmRevision = "fixed-c-ordered-left-dfs-v1" ∧
  h.stateRepresentation = "actual-conductor-complete-left-sorted-v1" ∧
  h.integerRepresentation = "signed-exact-unique-zero-v1" ∧
  h.grammarRevision = "balanced-enter-exit-length-prefixed-v1" ∧
  h.gateRevision = "noncanonical-rank-output-product-tail-gaps-v1" ∧
  h.producerRevision ≠ "" ∧ h.checkerRevision ≠ "" ∧
  h.specificationRevision ≠ "" ∧
  h.ordinary = (ordinaryConductors p).map (fun c => (c,ordinaryFields c))

structure SourceBindings where
  producer : String
  checker : String
  specification : String

/-- Concrete admission compares all source identities with the selected bundle;
nonempty self-reported strings in an abstract header do not prove provenance. -/
def SourceBound (expected : SourceBindings) (h : Header) : Prop :=
  h.producerRevision=expected.producer ∧ h.checkerRevision=expected.checker ∧
    h.specificationRevision=expected.specification

structure Entry where
  label : Label
  reason : Reason
  output : Option Output
  deriving DecidableEq

def LocalMatches (p : Parameters) (l : Label) (e : Entry) : Prop :=
  e.label = l ∧ e.reason = expectedReason p l ∧ e.output = expectedOutput p l

noncomputable def exactEntry (p : Parameters) (l : Label) : Entry :=
  ⟨l,expectedReason p l,expectedOutput p l⟩

theorem exactEntry_matches (p : Parameters) (l : Label) :
    LocalMatches p l (exactEntry p l) := ⟨rfl,rfl,rfl⟩

inductive Event
  | enter (entry : Entry)
  | exit
  deriving DecidableEq

mutual
  /-- A locally checked complete subtree. The entry is compared field by field;
  the child forest is indexed by the derived exact ordered list. -/
  inductive NodeCertificate (p : Parameters) : Label → List Event → List Output → Prop
    | node {l : Label} {entry : Entry} {body : List Event} {outs : List Output}
      (entryMatches : LocalMatches p l entry)
      (children : ForestCertificate p (requiredChildren p l) body outs) :
      NodeCertificate p l (.enter entry :: (body ++ [.exit]))
        (entry.output.toList ++ outs)

  inductive ForestCertificate (p : Parameters) :
      List Label → List Event → List Output → Prop
    | nil : ForestCertificate p [] [] []
    | cons {l : Label} {ls : List Label} {body rest : List Event}
      {out more : List Output}
      (node : NodeCertificate p l body out)
      (following : ForestCertificate p ls rest more) :
      ForestCertificate p (l::ls) (body++rest) (out++more)
end

def Accepted (p : Parameters) (h : Header) (events : List Event)
    (outputs : List Output) : Prop :=
  HeaderMatches p h ∧ ForestCertificate p (rootLabels p) events outputs

def BoundAccepted (expected : SourceBindings) (p : Parameters) (h : Header)
    (events : List Event) (outputs : List Output) : Prop :=
  SourceBound expected h ∧ Accepted p h events outputs

/-- Arbitrary root sharding: flattening need only permute the complete root
list, but every individual assigned list preserves the required root order.
Permutation retains multiplicity, so a repeated or omitted pair cannot pass. -/
def ShardPartition (p : Parameters) (assigned : List (List Label)) : Prop :=
  assigned.flatten.Perm (rootLabels p) ∧
    ∀ roots ∈ assigned, roots.Sublist (rootLabels p)

inductive CheckedShards (p : Parameters) :
    List (List Label) → List (List Event × List Output) → Prop
  | nil : CheckedShards p [] []
  | cons {roots : List Label} {assigned : List (List Label)}
      {events : List Event} {outputs : List Output}
      {following : List (List Event × List Output)}
      (here : ForestCertificate p roots events outputs)
      (rest : CheckedShards p assigned following) :
      CheckedShards p (roots::assigned) ((events,outputs)::following)

def ShardsAccepted (p : Parameters) (h : Header) (assigned : List (List Label))
    (shards : List (List Event × List Output)) : Prop :=
  HeaderMatches p h ∧ ShardPartition p assigned ∧ CheckedShards p assigned shards

theorem shard_partition_root_present (p : Parameters) (assigned : List (List Label))
    (h : ShardPartition p assigned) (l : Label) (hl : l ∈ rootLabels p) :
    ∃ roots ∈ assigned, l ∈ roots := by
  have hflat : l ∈ assigned.flatten := h.1.mem_iff.mpr hl
  simpa using hflat

def isEnter : Event → Bool
  | .enter _ => true
  | .exit => false

/-- Counts describe retained constructed records only. An omitted tail subtree
has no node to count. Counts never enter Accepted as premises. -/
def constructedCount (events : List Event) : ℕ := (events.filter isEnter).length
def outputCount (outputs : List Output) : ℕ := outputs.length

structure Frame where
  label : Label
  fields : Fields
  pending : List Label

noncomputable def frame (p : Parameters) (l : Label) : Frame :=
  ⟨l,reconstruct l,requiredChildren p l⟩

structure ParserState where
  roots : List Label
  stack : List Frame
  outputs : List Output
  constructed : ℕ

def parserStart (p : Parameters) : ParserState := ⟨rootLabels p,[],[],0⟩
def ParserDone (s : ParserState) : Prop := s.roots = [] ∧ s.stack = []

inductive ParserStep (p : Parameters) : ParserState → Event → ParserState → Prop
  | root {l : Label} {ls : List Label} {e : Entry} {out : List Output} {n : ℕ}
      (h : LocalMatches p l e) :
      ParserStep p ⟨l::ls,[],out,n⟩ (.enter e)
        ⟨ls,[frame p l],out++e.output.toList,n+1⟩
  | child {l : Label} {ls roots : List Label} {parent : Label} {f : Fields}
      {rest : List Frame} {e : Entry} {out : List Output} {n : ℕ}
      (h : LocalMatches p l e) :
      ParserStep p ⟨roots,⟨parent,f,l::ls⟩::rest,out,n⟩ (.enter e)
        ⟨roots,frame p l::⟨parent,f,ls⟩::rest,out++e.output.toList,n+1⟩
  | exit {roots : List Label} {l : Label} {f : Fields} {rest : List Frame}
      {out : List Output} {n : ℕ} :
      ParserStep p ⟨roots,⟨l,f,[]⟩::rest,out,n⟩ .exit ⟨roots,rest,out,n⟩

inductive Parses (p : Parameters) : ParserState → List Event → ParserState → Prop
  | nil (s : ParserState) : Parses p s [] s
  | cons {s t u : ParserState} {e : Event} {events : List Event}
      (step : ParserStep p s e t) (rest : Parses p t events u) :
      Parses p s (e::events) u

theorem parser_exit_pending_empty (p : Parameters) (s t : ParserState)
    (h : ParserStep p s .exit t) :
    ∃ roots l f rest out n,
      s = ⟨roots,⟨l,f,[]⟩::rest,out,n⟩ ∧ t = ⟨roots,rest,out,n⟩ := by
  cases h with
  | exit => exact ⟨_,_,_,_,_,_,rfl,rfl⟩

theorem parser_exit_unmatched_impossible (p : Parameters)
    (roots : List Label) (out : List Output) (n : ℕ) (t : ParserState) :
    ¬ ParserStep p ⟨roots,[],out,n⟩ .exit t := by
  intro h
  cases h

/-- After the final root closes, every extra token is rejected. -/
theorem parser_no_postlude (p : Parameters) (out : List Output) (n : ℕ)
    (e : Event) (t : ParserState) :
    ¬ ParserStep p ⟨[],[],out,n⟩ e t := by
  intro h
  cases h

/-- Mandatory source correspondence target: the stack parser must recognize
exactly this finite local grammar, preserving all parent frames and outputs.
No supplied parser result or completion flag inhabits this proposition. -/
def ParserGrammarCorrespondence : Prop := ∀ p events outputs,
  ForestCertificate p (rootLabels p) events outputs ↔
    ∃ done, Parses p (parserStart p) events done ∧ ParserDone done ∧
      done.outputs = outputs ∧ done.constructed = constructedCount events

/-- An actual byte decoder must establish these identities and reject nonunique
zero/sign encodings, incomplete length prefixes and malformed/trailing bits. -/
def ByteDecoderCorrespondence (Bytes : Type*)
    (expected : SourceBindings)
    (decode : Bytes → Option (Header × List Event))
    (check : Bytes → Bool) : Prop :=
  ∀ bytes, check bytes = true ↔
    ∃ p h events outputs, decode bytes = some (h,events) ∧
      BoundAccepted expected p h events outputs

end Partials.WilfFinite.Forest
