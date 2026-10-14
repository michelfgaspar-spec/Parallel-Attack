import Partials.UnitDistance.Network

/-! Blind source for main.tex lines 895–947 and supplement lines 231–272.
Not compiled or replayed. Packing partitions occurrence names, and imposes
no disjointness on the physical vertex sets of distinct packed blocks. -/
namespace Partials.UnitDistance

def DirectedPairEligible (a b : GadgetOccurrence) : Prop :=
  a.direction = b.direction ∧ b.anchor = a.anchor + 2 * occurrenceUnit a

structure OccurrenceIdentityDuty {I : Type*} (occurrences : I → GadgetOccurrence) : Prop where
  unique_anchor_direction : Function.Injective
    (fun i ↦ ((occurrences i).anchor, (occurrences i).direction))

theorem directed_successor_unique {I : Type*} (occurrences : I → GadgetOccurrence)
    (h : OccurrenceIdentityDuty occurrences) (a b c : I)
    (hab : DirectedPairEligible (occurrences a) (occurrences b))
    (hac : DirectedPairEligible (occurrences a) (occurrences c)) : b = c := by
  apply h.unique_anchor_direction
  apply Prod.ext
  · exact hab.2.trans hac.2.symm
  · exact hab.1.symm.trans hac.1

theorem directed_predecessor_unique {I : Type*} (occurrences : I → GadgetOccurrence)
    (h : OccurrenceIdentityDuty occurrences) (a b c : I)
    (hac : DirectedPairEligible (occurrences a) (occurrences c))
    (hbc : DirectedPairEligible (occurrences b) (occurrences c)) : a = b := by
  have hdir : (occurrences a).direction = (occurrences b).direction :=
    hac.1.trans hbc.1.symm
  have hunit : occurrenceUnit (occurrences a) = occurrenceUnit (occurrences b) := by
    simp only [occurrenceUnit, hdir]
  have hanchor : (occurrences a).anchor = (occurrences b).anchor := by
    have he : (occurrences a).anchor + 2 * occurrenceUnit (occurrences a) =
        (occurrences b).anchor + 2 * occurrenceUnit (occurrences a) := by
      simpa only [← hunit] using hac.2.symm.trans hbc.2
    exact add_right_cancel he
  exact h.unique_anchor_direction (Prod.ext hanchor hdir)

theorem directed_chain_endpoint (u : ℂ) (anchor : ℕ → ℂ)
    (hstep : ∀ n, anchor (n + 1) = anchor n + 2 * u) (n : ℕ) :
    anchor n = anchor 0 + (n : ℂ) * (2 * u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [hstep, ih, Nat.cast_add, Nat.cast_one]
    ring

theorem directed_chain_no_positive_cycle (u : ℂ) (hu : u ≠ 0)
    (anchor : ℕ → ℂ) (hstep : ∀ n, anchor (n + 1) = anchor n + 2 * u)
    (n : ℕ) (hn : 0 < n) : anchor n ≠ anchor 0 := by
  intro hcycle
  have hsum := directed_chain_endpoint u anchor hstep n
  have hzero : (n : ℂ) * (2 * u) = 0 := by
    have he : anchor 0 + (n : ℂ) * (2 * u) = anchor 0 + 0 := by
      simpa only [add_zero] using hsum.symm.trans hcycle
    exact add_left_cancel he
  have hncast : (n : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have htwou : 2 * u = 0 := (mul_eq_zero.mp hzero).resolve_left hncast
  exact hu ((mul_eq_zero.mp htwou).resolve_left (by norm_num))

/-- Abstract occurrence matching. Its disjointness is about indices in a
path of m occurrences. No coordinate/vertex-set disjointness is a premise. -/
structure OccurrenceMatching (m : ℕ) where
  size : ℕ
  endpoints : Fin size → Fin m × Fin m
  no_self : ∀ k, (endpoints k).1 ≠ (endpoints k).2
  disjoint_pairs : ∀ k l, k ≠ l →
    (endpoints k).1 ≠ (endpoints l).1 ∧
    (endpoints k).1 ≠ (endpoints l).2 ∧
    (endpoints k).2 ≠ (endpoints l).1 ∧
    (endpoints k).2 ≠ (endpoints l).2

def matchingEndpointMap {m : ℕ} (M : OccurrenceMatching m)
    (p : Fin M.size × Fin 2) : Fin m :=
  if p.2.val = 0 then (M.endpoints p.1).1 else (M.endpoints p.1).2

theorem matching_endpoint_injective {m : ℕ} (M : OccurrenceMatching m) :
    Function.Injective (matchingEndpointMap M) := by
  intro p q hpq
  rcases p with ⟨k, s⟩
  rcases q with ⟨l, t⟩
  have hkl : k = l := by
    by_contra hne
    obtain ⟨h00, h01, h10, h11⟩ := M.disjoint_pairs k l hne
    fin_cases s <;> fin_cases t <;> simp_all [matchingEndpointMap]
  subst l
  have hst : s = t := by
    have hdistinct := M.no_self k
    fin_cases s <;> fin_cases t <;> simp_all [matchingEndpointMap]
  subst t
  rfl

theorem matching_size_at_most_half {m : ℕ} (M : OccurrenceMatching m) :
    M.size ≤ m / 2 := by
  have h := Fintype.card_le_of_injective (matchingEndpointMap M)
    (matching_endpoint_injective M)
  have htwice : M.size * 2 ≤ m := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using h
  omega

def alternatingPathMatching (m : ℕ) : OccurrenceMatching m where
  size := m / 2
  endpoints := fun k ↦
    (⟨2 * k.val, by have hk := k.isLt; omega⟩,
      ⟨2 * k.val + 1, by have hk := k.isLt; omega⟩)
  no_self := by
    intro k h
    have hv := congrArg Fin.val h
    simp only [Prod.fst, Prod.snd, Fin.val_mk] at hv
    omega
  disjoint_pairs := by
    intro k l hkl
    have hval : k.val ≠ l.val := by
      intro he
      exact hkl (Fin.ext he)
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intro he <;>
      have hv := congrArg Fin.val he <;>
      simp only [Prod.fst, Prod.snd, Fin.val_mk] at hv <;> omega

theorem alternating_pairs_are_path_adjacent (m : ℕ) (k : Fin (m / 2)) :
    ((alternatingPathMatching m).endpoints k).1.val + 1 =
      ((alternatingPathMatching m).endpoints k).2.val := rfl

theorem alternating_path_matching_maximum (m : ℕ) (M : OccurrenceMatching m) :
    M.size ≤ (alternatingPathMatching m).size :=
  matching_size_at_most_half M

/-- Applying the abstract maximum to the actual eligibility graph requires
the complete path-component adapter, not merely a retained total P. All
listed component occurrences must be distinct and cover the frozen stream. -/
structure DirectedPathComponentDuty {I : Type*}
    (occurrences : I → GadgetOccurrence) where
  components : Type
  length : components → ℕ
  occurrenceAt : (c : components) → Fin (length c) → I
  covers_once : Function.Bijective
    (fun p : (Σ c : components, Fin (length c)) ↦ occurrenceAt p.1 p.2)
  adjacency_exact : ∀ c d (k : Fin (length c)) (l : Fin (length d)),
    DirectedPairEligible (occurrences (occurrenceAt c k))
      (occurrences (occurrenceAt d l)) ↔
      ∃ h : c = d, k.val + 1 = l.val

structure OccurrencePairPacking {I : Type*} (occurrences : I → GadgetOccurrence) where
  pairs : Finset (I × I)
  eligible : ∀ p ∈ pairs, DirectedPairEligible (occurrences p.1) (occurrences p.2)
  no_self : ∀ p ∈ pairs, p.1 ≠ p.2
  disjoint_occurrences : ∀ p ∈ pairs, ∀ q ∈ pairs, p ≠ q →
    p.1 ≠ q.1 ∧ p.1 ≠ q.2 ∧ p.2 ≠ q.1 ∧ p.2 ≠ q.2

/- Uniform local pair savings require the same indexed direction and exact
anchor placement from DirectedPairEligible. Shared residues, reversed
equality implications, or consecutive stream positions are insufficient.
After a true path decomposition, alternatingPathMatching gives floor(m/2)
disjoint adjacent occurrence pairs per component; separate physical blocks
may overlap, and a union bound remains valid. The fixed P=1460199 and every
local geometry/count, graph partition and stream digest are consumer duties;
none was inferred or replayed in this file. -/
end Partials.UnitDistance
