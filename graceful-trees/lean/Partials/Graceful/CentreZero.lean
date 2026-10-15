import Partials.Graceful.Geometry
import Partials.Graceful.Assembly

namespace Partials.Graceful

/-- The established all-positive graceful labeling now has zero at the unique
graph-theoretic centre, as asserted in the manuscript. -/
theorem main_center_zero (u v : ℕ) (hu : 0 < u) (hv : 0 < v) :
    (simpleGraph u v).diam = 6 ∧
      ∃ f : Vertex u v → Fin (q u v + 1),
        RootZeroGraceful u v f ∧
          ∀ x, x ∈ (simpleGraph u v).center ↔ f x = 0 := by
  obtain ⟨f, hf⟩ := main_root_zero u v hu hv
  refine ⟨diameter_six u v, f, hf, ?_⟩
  intro x
  rw [center_eq_root, Set.mem_singleton_iff]
  constructor
  · rintro rfl
    exact hf.2.1
  · intro hx
    exact hf.1.1 (hx.trans hf.2.1.symm)

end Partials.Graceful
