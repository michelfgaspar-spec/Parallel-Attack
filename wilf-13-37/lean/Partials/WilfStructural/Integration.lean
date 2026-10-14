import Partials.WilfStructural.FoundationTargets
import Partials.WilfStructural.ShadowTargets
import Partials.WilfStructural.PackingTargets

/-! Root integration source, uncompiled. This connects the three actual authors'
models without assuming a Wilf conclusion or treating selected formal monomials
as all possible numerical factorizations. Cardinal partitions and exact candidate
enumeration remain independently specified duties. -/
namespace Partials.WilfStructural.Integration

theorem left_primitive_membership (d : Foundation.Data) {x : ℕ}
    (hx : x ∈ Foundation.B d) : x ∈ d.S.carrier ∧ d.m ≤ x := by
  classical
  have ht := (Finset.mem_filter.mp hx).1
  have ha := (Finset.mem_filter.mp ht).1
  have hp := ((Finset.mem_filter.mp ht).2).1
  have hs := ((Foundation.mem_A d x).1 ha).1
  exact ⟨hs, d.multiplicity.2.2 x hp hs⟩

theorem packing_value_eq {s : ℕ} (b : Fin s → ℕ)
    (u : Shadow.Monomial s) :
    Packing.value (fun i => (b i : ℤ)) u = (Shadow.value b u : ℤ) := by
  simp [Packing.value, Shadow.value, Nat.cast_sum, Nat.cast_mul]

/-- The actual global selection on the foundational semigroup gives the
numeric injection used by the packing graph, across every selected degree. -/
theorem selected_integer_values_injective {s : ℕ} (d : Foundation.Data)
    (b : Fin s → ℕ) (hb : ∀ i, b i ∈ Foundation.B d)
    (hdepth : d.c ≤ Foundation.depth d * d.m) :
    Set.InjOn (Packing.value (fun i => (b i : ℤ)))
      (↑(Shadow.selectedFinset d.S b d.m (Foundation.depth d)) :
        Set (Shadow.Monomial s)) := by
  have hs := Shadow.global_apery_selection d.S b d.m d.c (Foundation.depth d)
    d.multiplicity.1 d.conductor hdepth
    (fun i => (left_primitive_membership d (hb i)).1)
    (fun i => (left_primitive_membership d (hb i)).2)
  intro u hu v hv he
  apply hs.2.1 hu hv
  have hn : (Shadow.value b u : ℤ) = (Shadow.value b v : ℤ) := by
    simpa only [packing_value_eq] using he
  exact_mod_cast hn

/-- This consumes a subset of ONE global selection and one joint graph.
It still owes the independent top partition, candidate completeness and
interval membership; it does not assume the matching inequality itself. -/
theorem selected_top_integer_cap {s : ℕ} (d : Foundation.Data)
    (b : Fin s → ℕ) (hb : ∀ i, b i ∈ Foundation.B d)
    (hdepth : d.c ≤ Foundation.depth d * d.m)
    (actual candidates : Finset (Shadow.Monomial s))
    (interval : Shadow.Monomial s → Finset ℤ)
    (hselected : actual ⊆ Shadow.selectedFinset d.S b d.m (Foundation.depth d))
    (hcandidates : actual ⊆ candidates)
    (hinterval : ∀ u ∈ actual, Packing.value (fun i => (b i : ℤ)) u ∈ interval u)
    (hpartition : Foundation.delta d = Foundation.K d + actual.card) :
    Foundation.delta d ≤ Foundation.K d +
      Packing.matchingCapacity (Packing.intervalGraph candidates interval) := by
  apply Packing.joint_integer_cap actual candidates interval
    (Packing.value (fun i => (b i : ℤ))) hcandidates
    (fun _ hu _ hv he => selected_integer_values_injective d b hb hdepth
      (hselected hu) (hselected hv) he) hinterval
    (Foundation.delta d) (Foundation.K d) hpartition

end Partials.WilfStructural.Integration
