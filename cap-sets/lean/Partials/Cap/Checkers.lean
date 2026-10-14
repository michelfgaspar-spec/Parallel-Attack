import Partials.Cap.Enumeration

/-!
R5 BLIND SOURCE / UNCOMPILED. Source correspondence: main.tex:365-380,
484-524 and supplement.tex:198-274; verification/verify.py functions
valid_vertices, verify_graph, verify_family and verify_direct_roots.

Every Boolean below ranges over explicit finite sets/lists. Its SOUNDNESS
is conditional on an equality to true. No such equality is asserted for
the delivered data. Stored flags, rank counts, hashes and metadata are inputs,
not proof. A separate mathematical interpretation is needed even after a
syntactic or recomputation check. The shared checkFinite_sound API is reused.
-/
namespace Partials.Cap.Certificate

open Partials.Cap

instance independent_decidable {α : Type*} [DecidableEq α]
    (G : Hypergraph α) (s : Finset α) : Decidable (Independent G s) := by
  unfold Independent
  infer_instance

structure NaturalTripleRow where
  i : ℕ
  j : ℕ
  k : ℕ
  discriminant : ℕ
  forbidden : Bool
  deriving DecidableEq, Repr

def tripleVertices (r : NaturalTripleRow) : Finset ℕ := {r.i, r.j, r.k}
def tripleUniverse (n : ℕ) : Finset (Finset ℕ) := (Finset.range n).powersetCard 3

def RowShape (n q : ℕ) (r : NaturalTripleRow) : Prop :=
  r.i < r.j ∧ r.j < r.k ∧ r.k < n ∧ r.discriminant < q

instance rowShape_decidable (n q : ℕ) (r : NaturalTripleRow) : Decidable (RowShape n q r) := by
  unfold RowShape
  infer_instance

def graphFromRows (rows : List NaturalTripleRow) : Hypergraph ℕ :=
  ((rows.filter (fun r => r.forbidden)).map tripleVertices).toFinset

/-- Coverage and absence of duplicate triples are checked, not inferred from
the list length. The counts themselves are independent finite equalities. -/
def GraphRowsAccepted (rows : List NaturalTripleRow) (n q edges nonedges zeros : ℕ) : Prop :=
  (∀ r ∈ rows, RowShape n q r) ∧
  (rows.map tripleVertices).Nodup ∧
  (rows.map tripleVertices).toFinset = tripleUniverse n ∧
  (graphFromRows rows).card = edges ∧
  (rows.filter (fun r => !r.forbidden)).length = nonedges ∧
  (rows.filter (fun r => decide (r.discriminant = 0))).length = zeros

instance graphRowsAccepted_decidable (rows : List NaturalTripleRow) (n q edges nonedges zeros : ℕ) :
    Decidable (GraphRowsAccepted rows n q edges nonedges zeros) := by
  unfold GraphRowsAccepted
  infer_instance

def checkGraphRows (rows : List NaturalTripleRow) (n q edges nonedges zeros : ℕ) : Bool :=
  decide (GraphRowsAccepted rows n q edges nonedges zeros)

theorem checkGraphRows_sound (rows : List NaturalTripleRow) (n q edges nonedges zeros : ℕ)
    (h : checkGraphRows rows n q edges nonedges zeros = true) :
    GraphRowsAccepted rows n q edges nonedges zeros := by
  simpa [checkGraphRows] using h

def RowCodeConsistent (discriminantCode : ℕ → ℕ → ℕ → ℕ)
    (squareCode : ℕ → Bool) (r : NaturalTripleRow) : Prop :=
  r.discriminant = discriminantCode r.i r.j r.k ∧
  r.forbidden = squareCode r.discriminant

instance rowCodeConsistent_decidable (discriminantCode : ℕ → ℕ → ℕ → ℕ)
    (squareCode : ℕ → Bool) (r : NaturalTripleRow) :
    Decidable (RowCodeConsistent discriminantCode squareCode r) := by
  unfold RowCodeConsistent
  infer_instance

/-- This checks agreement with the supplied arithmetic functions. It does
not certify that those functions implement the manuscript quotient field. -/
def checkRowCodes (rows : List NaturalTripleRow)
    (discriminantCode : ℕ → ℕ → ℕ → ℕ) (squareCode : ℕ → Bool) : Bool :=
  Partials.checkFinite rows.toFinset (RowCodeConsistent discriminantCode squareCode)

theorem checkRowCodes_sound (rows : List NaturalTripleRow)
    (discriminantCode : ℕ → ℕ → ℕ → ℕ) (squareCode : ℕ → Bool)
    (h : checkRowCodes rows discriminantCode squareCode = true) :
    ∀ r ∈ rows, RowCodeConsistent discriminantCode squareCode r := by
  have hc := Partials.checkFinite_sound rows.toFinset
    (RowCodeConsistent discriminantCode squareCode) h
  intro r hr
  exact hc r (List.mem_toFinset.mpr hr)

/-- Independently specified interpretation duty: recomputed code-square
status means the target edge predicate, not merely a stored Boolean flag. -/
def CodeEdgeMeaningDuty (rows : List NaturalTripleRow)
    (discriminantCode : ℕ → ℕ → ℕ → ℕ) (squareCode : ℕ → Bool)
    (TargetEdge : Finset ℕ → Prop) : Prop :=
  ∀ r ∈ rows,
    squareCode (discriminantCode r.i r.j r.k) = true ↔ TargetEdge (tripleVertices r)

theorem row_flags_mean_edges (rows : List NaturalTripleRow)
    (discriminantCode : ℕ → ℕ → ℕ → ℕ) (squareCode : ℕ → Bool)
    (TargetEdge : Finset ℕ → Prop)
    (hc : checkRowCodes rows discriminantCode squareCode = true)
    (hm : CodeEdgeMeaningDuty rows discriminantCode squareCode TargetEdge) :
    ∀ r ∈ rows, r.forbidden = true ↔ TargetEdge (tripleVertices r) := by
  intro r hr
  have hrow := checkRowCodes_sound rows discriminantCode squareCode hc r hr
  rw [hrow.2, hrow.1]
  exact hm r hr

theorem graphFromRows_mem_iff (rows : List NaturalTripleRow) (e : Finset ℕ) :
    e ∈ graphFromRows rows ↔
      ∃ r ∈ rows, r.forbidden = true ∧ tripleVertices r = e := by
  constructor
  · intro he
    obtain ⟨r, hr, hre⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    obtain ⟨hrrows, hrtrue⟩ := List.mem_filter.mp hr
    exact ⟨r, hrrows, hrtrue, hre⟩
  · rintro ⟨r, hr, hflag, hre⟩
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨r, List.mem_filter.mpr ⟨hr, hflag⟩, hre⟩

/-- Exact graph refinement needs BOTH every-triple coverage and mathematical
flag meaning. Hash agreement, counts or a partial row check cannot supply it. -/
theorem graph_rows_refine_target (rows : List NaturalTripleRow)
    (n q edges nonedges zeros : ℕ) (TargetEdge : Finset ℕ → Prop)
    (hc : GraphRowsAccepted rows n q edges nonedges zeros)
    (hm : ∀ r ∈ rows, r.forbidden = true ↔ TargetEdge (tripleVertices r))
    (e : Finset ℕ) :
    e ∈ graphFromRows rows ↔ e ∈ tripleUniverse n ∧ TargetEdge e := by
  rcases hc with ⟨hshape, hnodup, hcoverage, hcount, hnonedges, hzeros⟩
  constructor
  · intro he
    obtain ⟨r, hr, hflag, hre⟩ := (graphFromRows_mem_iff rows e).mp he
    constructor
    · rw [← hcoverage]
      exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, hr, hre⟩)
    · simpa [hre] using (hm r hr).mp hflag
  · rintro ⟨he, htarget⟩
    have he' : e ∈ (rows.map tripleVertices).toFinset := by
      simpa [hcoverage] using he
    obtain ⟨r, hr, hre⟩ := List.mem_map.mp (List.mem_toFinset.mp he')
    apply (graphFromRows_mem_iff rows e).mpr
    exact ⟨r, hr, (hm r hr).mpr (by simpa [hre] using htarget), hre⟩

def OrderedNaturalRow (n : ℕ) (xs : List ℕ) : Prop :=
  xs.Pairwise (fun x y => x < y) ∧ ∀ x ∈ xs, x < n

instance orderedNaturalRow_decidable (n : ℕ) (xs : List ℕ) : Decidable (OrderedNaturalRow n xs) := by
  unfold OrderedNaturalRow
  infer_instance

def familyFromLists (rows : List (List ℕ)) : Finset (Finset ℕ) :=
  (rows.map List.toFinset).toFinset

/-- Raw list checks retain order, duplicate-row and collapsed-set issues that
would disappear on conversion to a Finset. Mathematical validity is separate. -/
def RawFamilyAccepted (n : ℕ) (rows : List (List ℕ)) : Prop :=
  rows.Nodup ∧ (rows.map List.toFinset).Nodup ∧
    ∀ xs ∈ rows, OrderedNaturalRow n xs ∧ xs ≠ [] ∧ 0 ∈ xs

instance rawFamilyAccepted_decidable (n : ℕ) (rows : List (List ℕ)) :
    Decidable (RawFamilyAccepted n rows) := by
  unfold RawFamilyAccepted
  infer_instance

def checkRawFamily (n : ℕ) (rows : List (List ℕ)) : Bool :=
  decide (RawFamilyAccepted n rows)

theorem checkRawFamily_sound (n : ℕ) (rows : List (List ℕ))
    (h : checkRawFamily n rows = true) : RawFamilyAccepted n rows := by
  simpa [checkRawFamily] using h

theorem familyFromLists_member (rows : List (List ℕ)) (xs : List ℕ) (h : xs ∈ rows) :
    xs.toFinset ∈ familyFromLists rows := by
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨xs, h, rfl⟩)

theorem familyFromLists_card (rows : List (List ℕ))
    (h : (rows.map List.toFinset).Nodup) :
    (familyFromLists rows).card = rows.length := by
  simpa [familyFromLists] using List.toFinset_card_of_nodup h

/-- A finite-domain implementation of the exact larger-vertex rule. -/
def FiniteIncreasingClosed (G : Hypergraph ℕ)
    (family : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ s ∈ family, ∀ v ∈ Finset.range n,
    (∀ x ∈ s, x < v) → Independent G (insert v s) → insert v s ∈ family

instance finiteIncreasingClosed_decidable (G : Hypergraph ℕ)
    (family : Finset (Finset ℕ)) (n : ℕ) : Decidable (FiniteIncreasingClosed G family n) := by
  unfold FiniteIncreasingClosed
  infer_instance

theorem finiteIncreasingClosed_iff (G : Hypergraph ℕ)
    (family : Finset (Finset ℕ)) (n : ℕ) :
    FiniteIncreasingClosed G family n ↔ IncreasingExtensionClosed G family n := by
  constructor
  · intro h s hs v hv
    exact h s hs v (Finset.mem_range.mpr hv)
  · intro h s hs v hv
    exact h s hs v (Finset.mem_range.mp hv)

def rankCount (family : Finset (Finset ℕ)) (k : ℕ) : ℕ :=
  (family.filter (fun s => s.card = k)).card

/-- Pairs are retained, so checks belonging to different parents are counted
separately even when they use the same next vertex. All largest rows are tested. -/
def extensionObligations (family : Finset (Finset ℕ)) (n : ℕ) :
    Finset (Finset ℕ × ℕ) :=
  (family ×ˢ Finset.range n).filter (fun p => ∀ x ∈ p.1, x < p.2)

def compatibleExtensions (G : Hypergraph ℕ)
    (family : Finset (Finset ℕ)) (n : ℕ) : Finset (Finset ℕ × ℕ) :=
  (extensionObligations family n).filter (fun p => Independent G (insert p.2 p.1))

/-- Summary checks remain distinct from the premises needed for completeness.
No row size is used to skip its extension obligations. -/
def FamilyAccepted (G : Hypergraph ℕ) (family : Finset (Finset ℕ))
    (n total upper : ℕ) (expectedRank : ℕ → ℕ) (witness : Finset ℕ)
    (expectedExtensions expectedCompatible : ℕ) : Prop :=
  (∀ s ∈ family, 0 ∈ s ∧ Independent G s ∧ ∀ x ∈ s, x < n) ∧
  ({0} : Finset ℕ) ∈ family ∧
  FiniteIncreasingClosed G family n ∧
  (∀ s ∈ family, s.card ≤ upper) ∧
  family.card = total ∧
  (∀ k ∈ Finset.range (upper + 1), rankCount family k = expectedRank k) ∧
  witness ∈ family ∧
  witness.card = upper ∧
  (extensionObligations family n).card = expectedExtensions ∧
  (compatibleExtensions G family n).card = expectedCompatible

instance familyAccepted_decidable (G : Hypergraph ℕ) (family : Finset (Finset ℕ))
    (n total upper : ℕ) (expectedRank : ℕ → ℕ) (witness : Finset ℕ)
    (expectedExtensions expectedCompatible : ℕ) :
    Decidable (FamilyAccepted G family n total upper expectedRank witness expectedExtensions expectedCompatible) := by
  unfold FamilyAccepted
  infer_instance

def checkFamily (G : Hypergraph ℕ) (family : Finset (Finset ℕ))
    (n total upper : ℕ) (expectedRank : ℕ → ℕ) (witness : Finset ℕ)
    (expectedExtensions expectedCompatible : ℕ) : Bool :=
  decide (FamilyAccepted G family n total upper expectedRank witness
    expectedExtensions expectedCompatible)

theorem checkFamily_sound (G : Hypergraph ℕ) (family : Finset (Finset ℕ))
    (n total upper : ℕ) (expectedRank : ℕ → ℕ) (witness : Finset ℕ)
    (expectedExtensions expectedCompatible : ℕ)
    (h : checkFamily G family n total upper expectedRank witness
      expectedExtensions expectedCompatible = true) :
    FamilyAccepted G family n total upper expectedRank witness
      expectedExtensions expectedCompatible := by
  simpa [checkFamily] using h

theorem accepted_family_complete (G : Hypergraph ℕ) (family : Finset (Finset ℕ))
    (n total upper : ℕ) (expectedRank : ℕ → ℕ) (witness : Finset ℕ)
    (expectedExtensions expectedCompatible : ℕ)
    (h : FamilyAccepted G family n total upper expectedRank witness
      expectedExtensions expectedCompatible) (s : Finset ℕ) :
    s ∈ family ↔ 0 ∈ s ∧ Independent G s ∧ ∀ x ∈ s, x < n := by
  exact increasing_extension_certificate_iff G family n h.2.1 h.1
    ((finiteIncreasingClosed_iff G family n).mp h.2.2.1) s

theorem accepted_family_rooted_upper (G : Hypergraph ℕ) (family : Finset (Finset ℕ))
    (n total upper : ℕ) (expectedRank : ℕ → ℕ) (witness : Finset ℕ)
    (expectedExtensions expectedCompatible : ℕ)
    (h : FamilyAccepted G family n total upper expectedRank witness
      expectedExtensions expectedCompatible) (s : Finset ℕ)
    (hroot : 0 ∈ s) (hind : Independent G s) (hb : ∀ x ∈ s, x < n) :
    s.card ≤ upper := by
  have hmem := (accepted_family_complete G family n total upper expectedRank witness
    expectedExtensions expectedCompatible h s).mpr ⟨hroot, hind, hb⟩
  exact h.2.2.2.1 s hmem

theorem accepted_family_witness (G : Hypergraph ℕ) (family : Finset (Finset ℕ))
    (n total upper : ℕ) (expectedRank : ℕ → ℕ) (witness : Finset ℕ)
    (expectedExtensions expectedCompatible : ℕ)
    (h : FamilyAccepted G family n total upper expectedRank witness
      expectedExtensions expectedCompatible) :
    0 ∈ witness ∧ Independent G witness ∧
      (∀ x ∈ witness, x < n) ∧ witness.card = upper := by
  rcases h with ⟨hvalid, hbase, hclosed, hupper, htotal, hranks,
    hwitness, hwcard, hextensions, hcompatible⟩
  have hw := hvalid witness hwitness
  exact ⟨hw.1, hw.2.1, hw.2.2, hwcard⟩

/-- The separately stored all_normalized_maximizers list must equal the
cardinality filter of the complete family; a length-40 report is insufficient. -/
def MaximumListAccepted (family : Finset (Finset ℕ)) (upper : ℕ)
    (rows : List (List ℕ)) : Prop :=
  (rows.map List.toFinset).Nodup ∧
    familyFromLists rows = family.filter (fun s => s.card = upper)

instance maximumListAccepted_decidable (family : Finset (Finset ℕ)) (upper : ℕ)
    (rows : List (List ℕ)) : Decidable (MaximumListAccepted family upper rows) := by
  unfold MaximumListAccepted
  infer_instance

def checkMaximumList (family : Finset (Finset ℕ)) (upper : ℕ)
    (rows : List (List ℕ)) : Bool := decide (MaximumListAccepted family upper rows)

theorem checkMaximumList_sound (family : Finset (Finset ℕ)) (upper : ℕ)
    (rows : List (List ℕ)) (h : checkMaximumList family upper rows = true) :
    MaximumListAccepted family upper rows := by
  simpa [checkMaximumList] using h

theorem accepted_maximum_list_mem_iff (family : Finset (Finset ℕ)) (upper : ℕ)
    (rows : List (List ℕ)) (h : MaximumListAccepted family upper rows) (s : Finset ℕ) :
    s ∈ familyFromLists rows ↔ s ∈ family ∧ s.card = upper := by
  rw [h.2]
  exact Finset.mem_filter

def ResidueFamilyAccepted (G : Hypergraph Vertex)
    (family : Finset (Finset Vertex)) : Prop :=
  ({0} : Finset Vertex) ∈ family ∧
  (∀ s ∈ family, (0 : Vertex) ∈ s ∧ Independent G s) ∧
  ∀ s ∈ family, ∀ v ∈ (Finset.univ : Finset Vertex),
    (∀ x ∈ s, x.val < v.val) → Independent G (insert v s) → insert v s ∈ family

instance residueFamilyAccepted_decidable (G : Hypergraph Vertex)
    (family : Finset (Finset Vertex)) : Decidable (ResidueFamilyAccepted G family) := by
  unfold ResidueFamilyAccepted
  infer_instance

def checkRootedResidueFamily (G : Hypergraph Vertex)
    (family : Finset (Finset Vertex)) : Bool :=
  decide (ResidueFamilyAccepted G family)

theorem checkRootedResidueFamily_sound (G : Hypergraph Vertex)
    (family : Finset (Finset Vertex))
    (h : checkRootedResidueFamily G family = true) : RootedCertificate G family := by
  have ha : ResidueFamilyAccepted G family := by
    simpa [checkRootedResidueFamily] using h
  refine ⟨ha.1, ha.2.1, ?_⟩
  intro s hs v hgreater hind
  exact ha.2.2 s hs v (Finset.mem_univ v) hgreater hind

section DirectRoots
variable {K : Type*} [Field K] [CharP K 3] [Fintype K] [DecidableEq K]

/-- Exact one-order-per-multiset checks; interpretation as ALL point triples
still requires coefficient distinctness, reordering and normalization. -/
def DirectRootRows (m : ℕ) (coefficients : Fin m → K) : Prop :=
  ∀ i ∈ (Finset.univ : Finset (Fin m)),
    ∀ j ∈ (Finset.univ : Finset (Fin m)),
    ∀ k ∈ (Finset.univ : Finset (Fin m)), i.val ≤ j.val → j.val ≤ k.val →
      ∀ t ∈ (Finset.univ : Finset K), ratioAdmissible t →
        (quadratic (coefficients i) (coefficients j) (coefficients k) t = 0 ↔
          i = j ∧ j = k ∧ t = 1)

instance directRootRows_decidable (m : ℕ) (coefficients : Fin m → K) :
    Decidable (DirectRootRows m coefficients) := by
  unfold DirectRootRows ratioAdmissible
  infer_instance

def normalizedWitnessCheck (m : ℕ) (coefficients : Fin m → K) : Bool :=
  decide (DirectRootRows m coefficients)

theorem normalizedWitnessCheck_sound (m : ℕ) (coefficients : Fin m → K)
    (h : normalizedWitnessCheck m coefficients = true) : DirectRootRows m coefficients := by
  simpa [normalizedWitnessCheck] using h

theorem normalizedWitnessCheck_ordered_result (m : ℕ) (coefficients : Fin m → K)
    (h : normalizedWitnessCheck m coefficients = true)
    (i j k : Fin m) (hij : i.val ≤ j.val) (hjk : j.val ≤ k.val)
    (t : K) (ht : ratioAdmissible t) :
    quadratic (coefficients i) (coefficients j) (coefficients k) t = 0 ↔
      i = j ∧ j = k ∧ t = 1 := by
  exact normalizedWitnessCheck_sound m coefficients h i (Finset.mem_univ i)
    j (Finset.mem_univ j) k (Finset.mem_univ k) hij hjk t (Finset.mem_univ t) ht

end DirectRoots

end Partials.Cap.Certificate
