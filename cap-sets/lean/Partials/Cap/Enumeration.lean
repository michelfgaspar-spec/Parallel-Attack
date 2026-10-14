import Partials.Cap.Model

/-!
R5 BLIND SOURCE / UNCOMPILED. The natural-number induction is adapted from
the retained R1 `historical-drafts/FiniteCertificate.lean` (SHA-256
29973aa7ee12ed8f3bf72ff884b09a96adbaeb93d630f1eba55f16fa6ef2a22e).
The exact rule is Main Lemma `lem:closure`, main.tex:343-362: an added vertex
is BELOW n and ABOVE EVERY vertex already present. No all-extension premise,
stored maximum, hash or search result substitutes for this rule.

The residue bridge uses ordinary ZMod41 representatives only to order sets;
it does not identify natural-number arithmetic with finite-field arithmetic.
All declarations, including library names and tactics, await kernel checking.
-/
namespace Partials.Cap.Certificate

open Partials.Cap

variable {α : Type*} [DecidableEq α]

theorem independent_of_subset (G : Hypergraph α) {s t : Finset α}
    (hst : s ⊆ t) (ht : Independent G t) : Independent G s := by
  intro e he hes
  exact ht e he (Finset.Subset.trans hes hst)

/-- The source-matched bounded increasing rule, not arbitrary insertion. -/
def IncreasingExtensionClosed (G : Hypergraph ℕ)
    (family : Finset (Finset ℕ)) (n : ℕ) : Prop :=
  ∀ s ∈ family, ∀ v : ℕ, v < n →
    (∀ x ∈ s, x < v) → Independent G (insert v s) →
    insert v s ∈ family

/-- Completeness is proved by induction on the ambient upper bound. -/
theorem rooted_independent_mem_of_increasing_extensions
    (G : Hypergraph ℕ) (family : Finset (Finset ℕ)) (n : ℕ)
    (hbase : ({0} : Finset ℕ) ∈ family)
    (hstep : IncreasingExtensionClosed G family n)
    (s : Finset ℕ) (hroot : 0 ∈ s) (hind : Independent G s)
    (hvertices : ∀ x ∈ s, x < n) : s ∈ family := by
  have aux : ∀ m : ℕ, m ≤ n → ∀ t : Finset ℕ,
      0 ∈ t → Independent G t → (∀ x ∈ t, x < m) → t ∈ family := by
    intro m
    induction m with
    | zero =>
        intro _ t ht _ hbound
        have hbad : 0 < 0 := hbound 0 ht
        omega
    | succ m ih =>
        intro hm t ht hindt hbound
        by_cases hmzero : m = 0
        · subst m
          have hsingle : t = {0} := by
            ext x
            constructor
            · intro hx
              have hlt : x < 1 := hbound x hx
              have hxzero : x = 0 := by omega
              simpa [hxzero]
            · intro hx
              have hxzero : x = 0 := by simpa using hx
              simpa [hxzero] using ht
          simpa [hsingle] using hbase
        · by_cases hmem : m ∈ t
          · have hroot' : 0 ∈ t.erase m := by
              apply Finset.mem_erase.mpr
              constructor
              · omega
              · exact ht
            have hsub : t.erase m ⊆ t := by
              intro x hx
              exact (Finset.mem_erase.mp hx).2
            have hind' : Independent G (t.erase m) :=
              independent_of_subset G hsub hindt
            have hbelow : ∀ x ∈ t.erase m, x < m := by
              intro x hx
              have hne : x ≠ m := (Finset.mem_erase.mp hx).1
              have hlt : x < m + 1 := hbound x (Finset.mem_erase.mp hx).2
              omega
            have hprevious : t.erase m ∈ family :=
              ih (by omega) (t.erase m) hroot' hind' hbelow
            have hcurrent : Independent G (insert m (t.erase m)) := by
              simpa only [Finset.insert_erase hmem] using hindt
            have hnext := hstep (t.erase m) hprevious m (by omega)
              hbelow hcurrent
            simpa only [Finset.insert_erase hmem] using hnext
          · have hbelow : ∀ x ∈ t, x < m := by
              intro x hx
              have hlt : x < m + 1 := hbound x hx
              have hne : x ≠ m := by
                intro heq
                subst x
                exact hmem hx
              omega
            exact ih (by omega) t ht hindt hbelow
  exact aux n (le_refl n) s hroot hind hvertices

/-- Reverse inclusion is a separate validity hypothesis, not inferred from
extension closure. This is precisely the conclusion of Main Lemma 4.1. -/
theorem increasing_extension_certificate_iff
    (G : Hypergraph ℕ) (family : Finset (Finset ℕ)) (n : ℕ)
    (hbase : ({0} : Finset ℕ) ∈ family)
    (hvalid : ∀ s ∈ family,
      0 ∈ s ∧ Independent G s ∧ ∀ x ∈ s, x < n)
    (hstep : IncreasingExtensionClosed G family n)
    (s : Finset ℕ) :
    s ∈ family ↔ 0 ∈ s ∧ Independent G s ∧ ∀ x ∈ s, x < n := by
  constructor
  · exact hvalid s
  · intro hs
    exact rooted_independent_mem_of_increasing_extensions
      G family n hbase hstep s hs.1 hs.2.1 hs.2.2

def naturalVertices (s : Finset Vertex) : Finset ℕ := s.image ZMod.val
def naturalGraph (G : Hypergraph Vertex) : Hypergraph ℕ := G.image naturalVertices
def naturalFamily (family : Finset (Finset Vertex)) : Finset (Finset ℕ) :=
  family.image naturalVertices

theorem vertex_value_injective : Function.Injective (ZMod.val : Vertex → ℕ) := by
  intro a b hab
  have ha : (a.val : Vertex) = a := ZMod.natCast_zmod_val a
  have hb : (b.val : Vertex) = b := ZMod.natCast_zmod_val b
  calc
    a = (a.val : Vertex) := ha.symm
    _ = (b.val : Vertex) := congrArg (fun n : ℕ => (n : Vertex)) hab
    _ = b := hb

theorem vertex_value_lt (a : Vertex) : a.val < 41 := ZMod.val_lt a

theorem natural_value_of_bounded {v : ℕ} (hv : v < 41) :
    (v : Vertex).val = v := by
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt hv]

theorem naturalVertices_subset_iff {s t : Finset Vertex} :
    naturalVertices s ⊆ naturalVertices t ↔ s ⊆ t := by
  constructor
  · intro h v hv
    have hval := h (Finset.mem_image.mpr ⟨v, hv, rfl⟩)
    obtain ⟨w, hw, hweq⟩ := Finset.mem_image.mp hval
    have hwv : w = v := vertex_value_injective hweq
    simpa [hwv] using hw
  · intro h x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_image.mpr ⟨v, h hv, rfl⟩

theorem naturalVertices_injective : Function.Injective naturalVertices := by
  intro s t hst
  apply Finset.Subset.antisymm
  · exact naturalVertices_subset_iff.mp (by rw [hst])
  · exact naturalVertices_subset_iff.mp (by rw [hst])

theorem naturalVertices_card (s : Finset Vertex) :
    (naturalVertices s).card = s.card := by
  exact Finset.card_image_iff.mpr (fun a _ b _ hab => vertex_value_injective hab)

theorem naturalVertices_bounded (s : Finset Vertex) :
    ∀ x ∈ naturalVertices s, x < 41 := by
  intro x hx
  obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hx
  exact vertex_value_lt v

theorem naturalVertices_zero_mem (s : Finset Vertex) :
    0 ∈ naturalVertices s ↔ (0 : Vertex) ∈ s := by
  constructor
  · intro h
    obtain ⟨v, hv, hzero⟩ := Finset.mem_image.mp h
    have hvzero : v = 0 := vertex_value_injective (by simpa using hzero)
    simpa [hvzero] using hv
  · intro h
    exact Finset.mem_image.mpr ⟨0, h, by simp⟩

theorem naturalFamily_mem_iff (family : Finset (Finset Vertex))
    (s : Finset Vertex) : naturalVertices s ∈ naturalFamily family ↔ s ∈ family := by
  constructor
  · intro h
    obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp h
    simpa [naturalVertices_injective hts] using ht
  · intro h
    exact Finset.mem_image.mpr ⟨s, h, rfl⟩

/-- Relabeling preserves the forbidden-edge/subset relation in both directions. -/
theorem naturalIndependent_iff (G : Hypergraph Vertex) (s : Finset Vertex) :
    Independent (naturalGraph G) (naturalVertices s) ↔ Independent G s := by
  constructor
  · intro h e he hes
    apply h (naturalVertices e) (Finset.mem_image.mpr ⟨e, he, rfl⟩)
    exact naturalVertices_subset_iff.mpr hes
  · intro h e he hes
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact h f hf (naturalVertices_subset_iff.mp hes)

def ResidueIncreasingExtensionClosed (G : Hypergraph Vertex)
    (family : Finset (Finset Vertex)) : Prop :=
  ∀ s ∈ family, ∀ v : Vertex, (∀ x ∈ s, x.val < v.val) →
    Independent G (insert v s) → insert v s ∈ family

/-- A primitive finite certificate interface. It asserts row validity and
closure; it contains no maximum, classification or conclusion field. -/
structure RootedCertificate (G : Hypergraph Vertex)
    (family : Finset (Finset Vertex)) : Prop where
  root : ({0} : Finset Vertex) ∈ family
  valid : ∀ s ∈ family, (0 : Vertex) ∈ s ∧ Independent G s
  increasing : ResidueIncreasingExtensionClosed G family

theorem residue_increasing_to_natural (G : Hypergraph Vertex)
    (family : Finset (Finset Vertex))
    (hstep : ResidueIncreasingExtensionClosed G family) :
    IncreasingExtensionClosed (naturalGraph G) (naturalFamily family) 41 := by
  intro s hs v hv hgreater hind
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  have hvval : (v : Vertex).val = v := natural_value_of_bounded hv
  have hins : naturalVertices (insert (v : Vertex) t) =
      insert v (naturalVertices t) := by
    simp [naturalVertices, hvval]
  have hgreater' : ∀ x ∈ t, x.val < (v : Vertex).val := by
    intro x hx
    rw [hvval]
    exact hgreater x.val (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have hind' : Independent G (insert (v : Vertex) t) :=
    (naturalIndependent_iff G _).mp (by simpa [hins] using hind)
  have hmem := hstep t ht (v : Vertex) hgreater' hind'
  rw [← hins]
  exact (naturalFamily_mem_iff family _).mpr hmem

/-- Meaningful ZMod41 completeness, not a theorem over the wrong ambient type. -/
theorem residue_certificate_iff (G : Hypergraph Vertex)
    (family : Finset (Finset Vertex)) (hc : RootedCertificate G family)
    (s : Finset Vertex) :
    s ∈ family ↔ (0 : Vertex) ∈ s ∧ Independent G s := by
  have hbase : ({0} : Finset ℕ) ∈ naturalFamily family := by
    simpa [naturalVertices] using
      (naturalFamily_mem_iff family ({0} : Finset Vertex)).mpr hc.root
  have hvalid : ∀ t ∈ naturalFamily family,
      0 ∈ t ∧ Independent (naturalGraph G) t ∧ ∀ x ∈ t, x < 41 := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact ⟨(naturalVertices_zero_mem u).mpr (hc.valid u hu).1,
      (naturalIndependent_iff G u).mpr (hc.valid u hu).2,
      naturalVertices_bounded u⟩
  have hcriterion := increasing_extension_certificate_iff
    (naturalGraph G) (naturalFamily family) 41 hbase hvalid
    (residue_increasing_to_natural G family hc.increasing) (naturalVertices s)
  constructor
  · exact hc.valid s
  · intro hs
    apply (naturalFamily_mem_iff family s).mp
    apply hcriterion.mpr
    exact ⟨(naturalVertices_zero_mem s).mpr hs.1,
      (naturalIndependent_iff G s).mpr hs.2, naturalVertices_bounded s⟩

/-- Natural labels may be cast only with a separate bound check: casting
unbounded JSON integers modulo 41 would silently identify different vertices. -/
def decodeResidueVertices (s : Finset ℕ) : Finset Vertex :=
  s.image (fun n : ℕ => (n : Vertex))

def decodeResidueFamily (family : Finset (Finset ℕ)) : Finset (Finset Vertex) :=
  family.image decodeResidueVertices

theorem naturalVertices_decodeResidueVertices (s : Finset ℕ)
    (hbound : ∀ n ∈ s, n < 41) :
    naturalVertices (decodeResidueVertices s) = s := by
  ext n
  constructor
  · intro hn
    obtain ⟨v, hv, hvn⟩ := Finset.mem_image.mp hn
    obtain ⟨m, hm, hmv⟩ := Finset.mem_image.mp hv
    have hval : v.val = m := by
      rw [← hmv]
      exact natural_value_of_bounded (hbound m hm)
    have hmn : m = n := hval.symm.trans hvn
    simpa [hmn] using hm
  · intro hn
    exact Finset.mem_image.mpr ⟨(n : Vertex),
      Finset.mem_image.mpr ⟨n, hn, rfl⟩, natural_value_of_bounded (hbound n hn)⟩

theorem decodeResidueVertices_naturalVertices (s : Finset Vertex) :
    decodeResidueVertices (naturalVertices s) = s := by
  ext v
  constructor
  · intro hv
    obtain ⟨n, hn, hnv⟩ := Finset.mem_image.mp hv
    obtain ⟨w, hw, hwn⟩ := Finset.mem_image.mp hn
    have hwv : w = v := by
      calc
        w = (w.val : Vertex) := (ZMod.natCast_zmod_val w).symm
        _ = (n : Vertex) := congrArg (fun m : ℕ => (m : Vertex)) hwn
        _ = v := hnv
    simpa [hwv] using hw
  · intro hv
    exact Finset.mem_image.mpr ⟨v.val,
      Finset.mem_image.mpr ⟨v, hv, rfl⟩, ZMod.natCast_zmod_val v⟩

theorem naturalFamily_decodeResidueFamily (family : Finset (Finset ℕ))
    (hbound : ∀ s ∈ family, ∀ n ∈ s, n < 41) :
    naturalFamily (decodeResidueFamily family) = family := by
  ext s
  constructor
  · intro hs
    obtain ⟨t, ht, hts⟩ := Finset.mem_image.mp hs
    obtain ⟨u, hu, hut⟩ := Finset.mem_image.mp ht
    have hus : u = s := by
      calc
        u = naturalVertices (decodeResidueVertices u) :=
          (naturalVertices_decodeResidueVertices u (hbound u hu)).symm
        _ = naturalVertices t := congrArg naturalVertices hut
        _ = s := hts
    simpa [hus] using hu
  · intro hs
    refine Finset.mem_image.mpr ⟨decodeResidueVertices s, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨s, hs, rfl⟩
    · exact naturalVertices_decodeResidueVertices s (hbound s hs)

/-- A direct data-adapter bridge. Equality of the actual relabeled graph to
the supplied natural graph is an explicit independent field/table obligation.
The finite certificate then transports to the concrete residue universe. -/
theorem natural_certificate_to_residue_iff (G : Hypergraph Vertex)
    (natG : Hypergraph ℕ) (family : Finset (Finset ℕ))
    (hgraph : naturalGraph G = natG)
    (hbase : ({0} : Finset ℕ) ∈ family)
    (hvalid : ∀ s ∈ family, 0 ∈ s ∧ Independent natG s ∧ ∀ n ∈ s, n < 41)
    (hstep : IncreasingExtensionClosed natG family 41) (s : Finset Vertex) :
    s ∈ decodeResidueFamily family ↔ (0 : Vertex) ∈ s ∧ Independent G s := by
  have hfamily : naturalFamily (decodeResidueFamily family) = family :=
    naturalFamily_decodeResidueFamily family (fun t ht => (hvalid t ht).2.2)
  have hcriterion := increasing_extension_certificate_iff natG family 41
    hbase hvalid hstep (naturalVertices s)
  constructor
  · intro hs
    have hmem : naturalVertices s ∈ family := by
      rw [← hfamily]
      exact (naturalFamily_mem_iff _ s).mpr hs
    have h := hcriterion.mp hmem
    refine ⟨(naturalVertices_zero_mem s).mp h.1, ?_⟩
    apply (naturalIndependent_iff G s).mp
    simpa [hgraph] using h.2.1
  · intro hs
    apply (naturalFamily_mem_iff _ s).mp
    rw [hfamily]
    apply hcriterion.mpr
    refine ⟨(naturalVertices_zero_mem s).mpr hs.1, ?_, naturalVertices_bounded s⟩
    simpa [hgraph] using (naturalIndependent_iff G s).mpr hs.2

end Partials.Cap.Certificate
