import Partials.Cap.Checkers

/-!
R5 BLIND SOURCE / UNCOMPILED. Alternate upper-certificate correspondence:
supplement.tex:109-196, including its 24 displayed representatives; exact
recurrence text at 127-134 and verification/verify.py:verify_link.

Deletion, transport of an internal edge, exclusion of rooted six-sets and
passage from arbitrary larger sets to six-subsets have proof bodies. The
actual 24-orbit coverage, every displayed edge, and all enumeration counts
are separate finite duties; no table or verifier was executed here.
-/
namespace Partials.Cap.Certificate

open Partials.Cap

section Link
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The root is excluded from the link vertices. Link edges are exactly the
two-sets whose union with the root is a forbidden hyperedge. -/
def linkAt (G : Hypergraph α) (root : α) : Hypergraph α :=
  (Finset.univ : Finset (Finset α)).filter
    (fun e => e.card = 2 ∧ root ∉ e ∧ insert root e ∈ G)

theorem linkAt_edge_iff (G : Hypergraph α) (root : α) (e : Finset α) :
    e ∈ linkAt G root ↔ e.card = 2 ∧ root ∉ e ∧ insert root e ∈ G := by
  simp [linkAt]

theorem erase_root_link_independent (G : Hypergraph α) (root : α)
    (s : Finset α) (hroot : root ∈ s) (hind : Independent G s) :
    Independent (linkAt G root) (s.erase root) := by
  intro e he hes
  obtain ⟨hcard, hnotroot, hedge⟩ := (linkAt_edge_iff G root e).mp he
  apply hind (insert root e) hedge
  intro x hx
  rcases Finset.mem_insert.mp hx with hxr | hxe
  · simpa [hxr] using hroot
  · exact (Finset.mem_erase.mp (hes hxe)).2

structure ObstructionRow (α : Type*) where
  representative : Finset α
  forbiddenEdge : Finset α

/-- A separately checkable table duty. Containment and edge status are both
required; a recorded triple or claimed orbit size is insufficient. -/
def RepresentativeEdgeDuty (G : Hypergraph α)
    (rows : List (ObstructionRow α)) : Prop :=
  ∀ r ∈ rows, r.forbiddenEdge ∈ G ∧ r.forbiddenEdge ⊆ r.representative

def EdgeTransportDuty {ι : Type*} (G : Hypergraph α) (action : ι → α → α) : Prop :=
  ∀ i : ι, ∀ e ∈ G, e.image (action i) ∈ G

/-- This finite-domain coverage duty quantifies over EVERY independent link
five-set, not only listed examples. For H41, indices are Fin8 multipliers,
the root is 0 and there are 24 literal rows. No second vertex is pinned. -/
def LinkFiveOrbitCoverageDuty {ι : Type*} (G : Hypergraph α) (root : α)
    (rows : List (ObstructionRow α)) (action : ι → α → α) : Prop :=
  ∀ s : Finset α, root ∉ s → Independent (linkAt G root) s → s.card = 5 →
    ∃ r ∈ rows, ∃ i : ι, s = r.representative.image (action i)

theorem orbit_contains_forbidden_edge {ι : Type*} (G : Hypergraph α)
    (rows : List (ObstructionRow α)) (action : ι → α → α)
    (hrows : RepresentativeEdgeDuty G rows) (htransport : EdgeTransportDuty G action)
    (r : ObstructionRow α) (hr : r ∈ rows) (i : ι) :
    ∃ e ∈ G, e ⊆ r.representative.image (action i) := by
  refine ⟨r.forbiddenEdge.image (action i), htransport i _ (hrows r hr).1, ?_⟩
  intro x hx
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨v, (hrows r hr).2 hv, rfl⟩

theorem covered_link_five_not_hypergraph_independent {ι : Type*}
    (G : Hypergraph α) (root : α) (rows : List (ObstructionRow α))
    (action : ι → α → α)
    (hrows : RepresentativeEdgeDuty G rows) (htransport : EdgeTransportDuty G action)
    (hcover : LinkFiveOrbitCoverageDuty G root rows action)
    (s : Finset α) (hroot : root ∉ s) (hlink : Independent (linkAt G root) s)
    (hcard : s.card = 5) : ¬ Independent G s := by
  intro hind
  obtain ⟨r, hr, i, hs⟩ := hcover s hroot hlink hcard
  obtain ⟨e, he, hes⟩ := orbit_contains_forbidden_edge G rows action hrows htransport r hr i
  exact hind e he (by simpa [hs] using hes)

theorem rooted_six_impossible_from_link {ι : Type*}
    (G : Hypergraph α) (root : α) (rows : List (ObstructionRow α))
    (action : ι → α → α)
    (hrows : RepresentativeEdgeDuty G rows) (htransport : EdgeTransportDuty G action)
    (hcover : LinkFiveOrbitCoverageDuty G root rows action)
    (s : Finset α) (hroot : root ∈ s) (hcard : s.card = 6)
    (hind : Independent G s) : False := by
  have hlink : Independent (linkAt G root) (s.erase root) :=
    erase_root_link_independent G root s hroot hind
  have hcard' : (s.erase root).card = 5 := by
    rw [Finset.card_erase_of_mem hroot, hcard]
  have hnotroot : root ∉ s.erase root := by simp
  have hsub : s.erase root ⊆ s := by
    intro x hx
    exact (Finset.mem_erase.mp hx).2
  exact covered_link_five_not_hypergraph_independent G root rows action
    hrows htransport hcover (s.erase root) hnotroot hlink hcard'
    (independent_of_subset G hsub hind)

/-- Named normalization premise, independently supplied by vertex translation
invariance. This contains no numerical upper-bound conclusion. -/
def RootingDuty (G : Hypergraph α) (root : α) : Prop :=
  ∀ s : Finset α, Independent G s → s.Nonempty →
    ∃ t : Finset α, Independent G t ∧ root ∈ t ∧ t.card = s.card

/-- Larger sets are handled through an actual independent six-subset. -/
theorem card_le_five_from_link {ι : Type*}
    (G : Hypergraph α) (root : α) (rows : List (ObstructionRow α))
    (action : ι → α → α)
    (hrows : RepresentativeEdgeDuty G rows) (htransport : EdgeTransportDuty G action)
    (hcover : LinkFiveOrbitCoverageDuty G root rows action)
    (hrooting : RootingDuty G root)
    (s : Finset α) (hind : Independent G s) : s.card ≤ 5 := by
  by_contra hbad
  have hsix : 6 ≤ s.card := by omega
  obtain ⟨u, hus, hucard⟩ := Finset.exists_subset_card_eq (s := s) (n := 6) hsix
  have huind : Independent G u := independent_of_subset G hus hind
  have hune : u.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨t, htind, htroot, htcard⟩ := hrooting u huind hune
  have htsix : t.card = 6 := by omega
  exact rooted_six_impossible_from_link G root rows action
    hrows htransport hcover t htroot htsix htind

end Link

theorem rooting_from_translation_invariance (G : Hypergraph Vertex)
    (htranslation : ∀ a : Vertex, ∀ s : Finset Vertex,
      Independent G s → Independent G (s.image (fun x => x + a))) :
    RootingDuty G (0 : Vertex) := by
  intro s hind hne
  obtain ⟨v, hv⟩ := hne
  refine ⟨s.image (fun x => x + (-v)), htranslation (-v) s hind, ?_, ?_⟩
  · exact Finset.mem_image.mpr ⟨v, hv, by simp⟩
  · apply Finset.card_image_iff.mpr
    intro a ha b hb hab
    exact add_right_cancel hab

/-! The next lemmas formalize the recurrence's increasing-set argument. Its
computed output distribution is not assumed or executed. -/

def LowerIncreasingClosed (G : Hypergraph ℕ) (family : Finset (Finset ℕ))
    (lo n : ℕ) : Prop :=
  ∀ s ∈ family, ∀ v : ℕ, lo ≤ v → v < n →
    (∀ x ∈ s, x < v) → Independent G (insert v s) → insert v s ∈ family

/-- Empty-root version of the increasing induction for the link domain
`1 ≤ v < 41`. It covers every independent set, including the empty set. -/
theorem empty_independent_mem_of_ordered_extensions (G : Hypergraph ℕ)
    (family : Finset (Finset ℕ)) (lo n : ℕ)
    (hbase : (∅ : Finset ℕ) ∈ family)
    (hstep : LowerIncreasingClosed G family lo n)
    (s : Finset ℕ) (hind : Independent G s)
    (hbound : ∀ x ∈ s, lo ≤ x ∧ x < n) : s ∈ family := by
  have aux : ∀ m : ℕ, m ≤ n → ∀ t : Finset ℕ, Independent G t →
      (∀ x ∈ t, lo ≤ x ∧ x < m) → t ∈ family := by
    intro m
    induction m with
    | zero =>
        intro hm t ht hb
        have hempty : t = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          have hbad := (hb x hx).2
          omega
        simpa [hempty] using hbase
    | succ m ih =>
        intro hm t ht hb
        by_cases hmem : m ∈ t
        · have hsub : t.erase m ⊆ t := by
            intro x hx
            exact (Finset.mem_erase.mp hx).2
          have hbound' : ∀ x ∈ t.erase m, lo ≤ x ∧ x < m := by
            intro x hx
            have hxne := (Finset.mem_erase.mp hx).1
            have hxb := hb x (Finset.mem_erase.mp hx).2
            exact ⟨hxb.1, by omega⟩
          have hprev : t.erase m ∈ family :=
            ih (by omega) (t.erase m) (independent_of_subset G hsub ht) hbound'
          have hgreater : ∀ x ∈ t.erase m, x < m := fun x hx => (hbound' x hx).2
          have hcurrent : Independent G (insert m (t.erase m)) := by
            simpa only [Finset.insert_erase hmem] using ht
          have hnext := hstep (t.erase m) hprev m (hb m hmem).1
            (by omega) hgreater hcurrent
          simpa only [Finset.insert_erase hmem] using hnext
        · have hbound' : ∀ x ∈ t, lo ≤ x ∧ x < m := by
            intro x hx
            have hxb := hb x hx
            have hxne : x ≠ m := by
              intro heq
              subst x
              exact hmem hx
            exact ⟨hxb.1, by omega⟩
          exact ih (by omega) t ht hbound'
  exact aux n (le_refl n) s hind hbound

theorem link_enumeration_certificate_iff (G : Hypergraph ℕ)
    (family : Finset (Finset ℕ)) (lo n : ℕ)
    (hbase : (∅ : Finset ℕ) ∈ family)
    (hvalid : ∀ s ∈ family, Independent G s ∧ ∀ x ∈ s, lo ≤ x ∧ x < n)
    (hstep : LowerIncreasingClosed G family lo n) (s : Finset ℕ) :
    s ∈ family ↔ Independent G s ∧ ∀ x ∈ s, lo ≤ x ∧ x < n := by
  constructor
  · exact hvalid s
  · intro hs
    exact empty_independent_mem_of_ordered_extensions G family lo n hbase hstep s hs.1 hs.2

def PairwiseNonadjacent (Adj : ℕ → ℕ → Prop) (s : Finset ℕ) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ¬ Adj x y

theorem nonadjacent_insert (Adj : ℕ → ℕ → Prop)
    (hsymm : ∀ x y, Adj x y → Adj y x)
    (s : Finset ℕ) (v : ℕ) (hs : PairwiseNonadjacent Adj s)
    (hv : ∀ x ∈ s, ¬ Adj x v) : PairwiseNonadjacent Adj (insert v s) := by
  intro x hx y hy hxy
  rcases Finset.mem_insert.mp hx with hxv | hxs
  · subst x
    rcases Finset.mem_insert.mp hy with hyv | hys
    · exact False.elim (hxy hyv.symm)
    · intro hbad
      exact hv y hys (hsymm v y hbad)
  · rcases Finset.mem_insert.mp hy with hyv | hys
    · subst y
      exact hv x hxs
    · exact hs x hxs y hys hxy

def CandidateInvariant (Adj : ℕ → ℕ → Prop)
    (chosen : Finset ℕ) (remaining : List ℕ) : Prop :=
  remaining.Pairwise (fun x y => x < y) ∧
    ∀ v ∈ remaining, ∀ x ∈ chosen, x < v ∧ ¬ Adj x v

def retainedCandidates (Adj : ℕ → ℕ → Prop) [DecidableRel Adj]
    (v : ℕ) (remaining : List ℕ) : List ℕ :=
  remaining.filter (fun u => decide (v < u ∧ ¬ Adj v u))

theorem pairwise_lt_filter (xs : List ℕ) (p : ℕ → Bool)
    (h : xs.Pairwise (fun x y => x < y)) :
    (xs.filter p).Pairwise (fun x y => x < y) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp h
      cases hp : p x with
      | false => simpa [hp] using ih htail
      | true =>
          have hnew : (x :: xs.filter p).Pairwise (fun x y => x < y) := by
            apply List.pairwise_cons.mpr
            refine ⟨?_, ih htail⟩
            intro y hy
            exact hhead y (List.mem_filter.mp hy).1
          simpa [hp] using hnew

/-- Filtering later nonneighbors preserves compatibility with ALL chosen
vertices, exactly the invariant needed by the stated recursive visit. -/
theorem retained_candidate_invariant (Adj : ℕ → ℕ → Prop) [DecidableRel Adj]
    (chosen : Finset ℕ) (remaining : List ℕ) (v : ℕ)
    (h : CandidateInvariant Adj chosen remaining) :
    CandidateInvariant Adj (insert v chosen) (retainedCandidates Adj v remaining) := by
  constructor
  · exact pairwise_lt_filter remaining _ h.1
  · intro u hu x hx
    obtain ⟨huold, hukeep⟩ := List.mem_filter.mp hu
    have hnew : v < u ∧ ¬ Adj v u := of_decide_eq_true hukeep
    rcases Finset.mem_insert.mp hx with hxv | hxold
    · simpa [hxv] using hnew
    · exact h.2 u huold x hxold

theorem selected_candidate_keeps_independence (Adj : ℕ → ℕ → Prop)
    (hsymm : ∀ x y, Adj x y → Adj y x)
    (chosen : Finset ℕ) (remaining : List ℕ) (v : ℕ)
    (h : CandidateInvariant Adj chosen remaining)
    (hv : v ∈ remaining) (hchosen : PairwiseNonadjacent Adj chosen) :
    PairwiseNonadjacent Adj (insert v chosen) := by
  exact nonadjacent_insert Adj hsymm chosen v hchosen
    (fun x hx => (h.2 v hv x hx).2)

/-- A set has at most one strictly increasing branch sequence. This avoids
claiming uniqueness merely from distinctness of the recorded examples. -/
theorem increasing_list_unique (xs ys : List ℕ)
    (hxs : xs.Pairwise (fun x y => x < y))
    (hys : ys.Pairwise (fun x y => x < y)) (hsets : xs.toFinset = ys.toFinset) :
    xs = ys := by
  induction xs generalizing ys with
  | nil =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          have hy : y ∈ ([] : List ℕ).toFinset := by
            rw [hsets]
            simp
          simpa using hy
  | cons x xs ih =>
      cases ys with
      | nil =>
          have hx : x ∈ ([] : List ℕ).toFinset := by
            rw [← hsets]
            simp
          simpa using hx
      | cons y ys =>
          obtain ⟨hxhead, hxtail⟩ := List.pairwise_cons.mp hxs
          obtain ⟨hyhead, hytail⟩ := List.pairwise_cons.mp hys
          have hxy : x = y := by
            by_contra hne
            have hxmem : x ∈ y :: ys := by
              apply List.mem_toFinset.mp
              rw [← hsets]
              simp
            have hymem : y ∈ x :: xs := by
              apply List.mem_toFinset.mp
              rw [hsets]
              simp
            have hxys : x ∈ ys := (List.mem_cons.mp hxmem).resolve_left hne
            have hyxs : y ∈ xs := (List.mem_cons.mp hymem).resolve_left (Ne.symm hne)
            have hlt := hxhead y hyxs
            have hgt := hyhead x hxys
            omega
          subst y
          have hxnotxs : x ∉ xs := by
            intro hx
            have hbad := hxhead x hx
            omega
          have hxnotys : x ∉ ys := by
            intro hx
            have hbad := hyhead x hx
            omega
          have htailsets : xs.toFinset = ys.toFinset := by
            have he := congrArg (fun s : Finset ℕ => s.erase x) hsets
            simpa [hxnotxs, hxnotys] using he
          have htail := ih ys hxtail hytail htailsets
          simpa [htail]

/-- Concrete enumeration output, output counts, 24-row coverage and the
Python-call/source-recurrence correspondence still require finite admission.
This named duty does not claim those checks have happened. -/
def LinkEnumerationCountDuty (G : Hypergraph ℕ) (family : Finset (Finset ℕ)) : Prop :=
  (∀ s ∈ family, Independent G s ∧ ∀ x ∈ s, 1 ≤ x ∧ x < 41) ∧
  (∅ : Finset ℕ) ∈ family ∧ LowerIncreasingClosed G family 1 41 ∧
  family.card = 2361 ∧
  rankCount family 0 = 1 ∧ rankCount family 1 = 40 ∧ rankCount family 2 = 360 ∧
  rankCount family 3 = 960 ∧ rankCount family 4 = 808 ∧ rankCount family 5 = 192 ∧
  (∀ s ∈ family, s.card ≤ 5)

theorem admitted_link_enumeration_complete (G : Hypergraph ℕ)
    (family : Finset (Finset ℕ)) (h : LinkEnumerationCountDuty G family) (s : Finset ℕ) :
    s ∈ family ↔ Independent G s ∧ ∀ x ∈ s, 1 ≤ x ∧ x < 41 := by
  exact link_enumeration_certificate_iff G family 1 41 h.2.1 h.1 h.2.2.1 s

/-- Finite single-vertex maximality is sufficient for inclusion maximality
because independent sets are closed under subsets. -/
def OneVertexMaximal (G : Hypergraph ℕ) (domain s : Finset ℕ) : Prop :=
  Independent G s ∧ s ⊆ domain ∧
    ∀ v ∈ domain, v ∉ s → ¬ Independent G (insert v s)

instance oneVertexMaximal_decidable (G : Hypergraph ℕ) (domain s : Finset ℕ) :
    Decidable (OneVertexMaximal G domain s) := by
  unfold OneVertexMaximal
  infer_instance

theorem oneVertexMaximal_no_strict_independent_superset (G : Hypergraph ℕ)
    (domain s : Finset ℕ) (h : OneVertexMaximal G domain s)
    (t : Finset ℕ) (hst : s ⊆ t) (htd : t ⊆ domain) (ht : Independent G t) : t = s := by
  apply Finset.Subset.antisymm
  · intro v hvt
    by_contra hvs
    have hins : insert v s ⊆ t := by
      intro x hx
      rcases Finset.mem_insert.mp hx with hxv | hxs
      · simpa [hxv] using hvt
      · exact hst hxs
    exact h.2.2 v (htd hvt) hvs (independent_of_subset G hins ht)
  · exact hst

def maximalRows (G : Hypergraph ℕ) (domain : Finset ℕ)
    (family : Finset (Finset ℕ)) : Finset (Finset ℕ) :=
  family.filter (OneVertexMaximal G domain)

/-- Additional retained statistics from supplement.tex:120-124. They are
not used as substitutes for recurrence completeness or obstruction coverage. -/
def LinkMaximalCountDuty (G : Hypergraph ℕ) (family : Finset (Finset ℕ)) : Prop :=
  let domain := (Finset.range 41).erase 0
  let maximal := maximalRows G domain family
  maximal.card = 360 ∧ rankCount maximal 3 = 24 ∧ rankCount maximal 4 = 144 ∧
    rankCount maximal 5 = 192 ∧ ∀ s ∈ maximal, s.card = 3 ∨ s.card = 4 ∨ s.card = 5

def ZeroLinkEdgeCountDuty (G : Hypergraph Vertex) : Prop :=
  (linkAt G (0 : Vertex)).card = 420

def EveryVertexDegreeDuty (G : Hypergraph Vertex) : Prop :=
  ∀ v : Vertex, (linkAt G v).card = 420

/-- Full orbit statistics are stronger than the coverage needed by the upper
implication. This unproved target also exposes disjointness and size eight. -/
def LinkOrbitStatisticsDuty (G : Hypergraph Vertex)
    (rows : List (ObstructionRow Vertex)) (action : Fin 8 → Vertex → Vertex) : Prop :=
  rows.length = 24 ∧
  (∀ r ∈ rows, r.representative.card = 5 ∧ (0 : Vertex) ∉ r.representative ∧
    Independent (linkAt G (0 : Vertex)) r.representative ∧
    ((Finset.univ : Finset (Fin 8)).image
      (fun i => r.representative.image (action i))).card = 8) ∧
  (∀ r ∈ rows, ∀ s ∈ rows, r ≠ s →
    Disjoint ((Finset.univ : Finset (Fin 8)).image (fun i => r.representative.image (action i)))
      ((Finset.univ : Finset (Fin 8)).image (fun i => s.representative.image (action i)))) ∧
  LinkFiveOrbitCoverageDuty G (0 : Vertex) rows action

end Partials.Cap.Certificate
