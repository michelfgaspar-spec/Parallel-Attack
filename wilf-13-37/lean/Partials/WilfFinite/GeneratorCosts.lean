import Partials.WilfFinite.SparseCosts

/-! R10 blind source. No Dijkstra run, gcd computation or tuple evaluation.
The residue-table obligations are mathematical conditions, not success flags. -/
namespace Partials.WilfFinite.Application
open Partials.Interface
open Partials.WilfStructural.Foundation
open scoped BigOperators

inductive Generated (A : Finset ℕ) : ℕ → Prop
  | zero : Generated A 0
  | add {a x : ℕ} : a ∈ A → Generated A x → Generated A (a+x)

theorem generated_add {A : Finset ℕ} {x y : ℕ}
    (hx : Generated A x) (hy : Generated A y) : Generated A (x+y) := by
  induction hx with
  | zero => simpa using hy
  | @add a x ha hx ih => simpa [Nat.add_assoc] using Generated.add ha ih

theorem generated_multiple {A : Finset ℕ} {m : ℕ} (hm : m ∈ A) (k : ℕ) :
    Generated A (k*m) := by
  induction k with
  | zero => simpa using Generated.zero (A := A)
  | succ k ih => simpa [Nat.succ_mul,Nat.add_comm] using Generated.add hm ih

structure GeneratorPresentation where
  A : Finset ℕ
  positive : ∀ a ∈ A, 0 < a
  nonempty : A.Nonempty
  S : NumericalSemigroup
  exact_carrier : ∀ x, x ∈ S.carrier ↔ Generated A x

/-- Every primitive of a finitely generated positive monoid is an input
generator. Minimality and absence of repeated input entries are unnecessary. -/
theorem primitive_occurs_in_input (P : GeneratorPresentation) {x : ℕ}
    (hp : IsPrimitive P.S x) : x ∈ P.A := by
  have hg := (P.exact_carrier x).1 hp.1
  have hpos := hp.2.1
  induction hg with
  | zero => exact False.elim (by omega)
  | @add a y ha hy ih =>
    by_cases hy0 : y=0
    · simpa [hy0] using ha
    · exact False.elim (hp.2.2 ⟨a,y,P.positive a ha,by omega,
        (P.exact_carrier a).2 (by simpa using Generated.add ha Generated.zero),
        (P.exact_carrier y).2 hy,rfl⟩)

/-- Least semigroup value in each residue. Reachability/gcd-one and exact
Dijkstra construction must supply this structure independently. -/
structure LeastResidueTable (A : Finset ℕ) (m : ℕ) where
  m_pos : 0 < m
  m_input : m ∈ A
  w : ℕ → ℕ
  represented : ∀ z < m, Generated A (w z)
  residue : ∀ z < m, w z % m=z
  least : ∀ x, Generated A x → w (x%m) ≤ x

theorem equal_residue_progression (x w m : ℕ) (hm : 0 < m)
    (horder : w ≤ x) (hres : x%m=w%m) :
    ∃ k : ℕ, x=w+k*m := by
  have hx := Nat.mod_add_div x m
  have hw := Nat.mod_add_div w m
  have hq : w/m ≤ x/m := by
    by_contra h
    have hh : x/m+1 ≤ w/m := by omega
    have hh' := Nat.mul_le_mul_left m hh
    nlinarith
  refine ⟨x/m-w/m,?_⟩
  have hcancel : x/m-w/m+w/m=x/m := Nat.sub_add_cancel hq
  nlinarith

theorem least_residue_membership {A : Finset ℕ} {m : ℕ}
    (T : LeastResidueTable A m) (x : ℕ) :
    Generated A x ↔ T.w (x%m) ≤ x := by
  constructor
  · exact T.least x
  · intro horder
    have hz : x%m < m := Nat.mod_lt x T.m_pos
    obtain ⟨k,hx⟩ := equal_residue_progression x (T.w (x%m)) m T.m_pos
      horder (T.residue (x%m) hz).symm
    rw [hx]
    exact generated_add (T.represented (x%m) hz) (generated_multiple T.m_input k)

/-- A shortest path with a repeated vertex can lose its positive cycle.
This local inequality underlies the simple-path bound (m-1)*a_max. -/
theorem positive_cycle_removal (prefixCost cycle suffix : ℕ) (hc : 0 < cycle) :
    prefixCost+suffix < prefixCost+cycle+suffix := by omega

/-- Finalized-set cut lemma for Dijkstra, including ties. A putative shorter
path supplies an edge whose tentative label is no larger than its distance. -/
theorem dijkstra_cut_contradiction (chosen shorter tentative : ℕ)
    (hshort : shorter < chosen) (hrelax : tentative ≤ shorter)
    (hminimum : chosen ≤ tentative) : False := by omega

def GeneratorReachabilityTarget (A : Finset ℕ) (m : ℕ) : Prop :=
  0 < m → (∀ a ∈ A, 0 < a) → m ∈ A →
  (∃ coeff : ℕ → ℤ, (∑ a ∈ A, coeff a*(a : ℤ))+(m : ℤ)=1) →
  ∀ z < m, ∃ x, Generated A x ∧ x%m=z

/-- Formula and finite minimal-generator test, still awaiting the full
path/table construction and gap-count proofs. The gcd-zero/non-one cases
must be rejected or explicitly scaled; they are not numerical semigroups. -/
def GeneratorExtractionTarget (P : GeneratorPresentation) (m : ℕ)
    (T : LeastResidueTable P.A m) (c g : ℕ) : Prop :=
  IsMultiplicity P.S m ∧ 2 ≤ m ∧ c=(Finset.range m).sup T.w-m+1 ∧
  g=∑ z ∈ Finset.range m, (T.w z-z)/m ∧
  ∀ a ∈ P.A, IsDecomposable P.S a ↔
    ∃ b ∈ P.A, b<a ∧ T.w ((a-b)%m) ≤ a-b

theorem generated_positive_head {A : Finset ℕ} {x : ℕ}
    (hx : Generated A x) (hpos : 0 < x) :
    ∃ a y, a ∈ A ∧ Generated A y ∧ x=a+y := by
  cases hx with
  | zero => omega
  | @add a y ha hy => exact ⟨a,y,ha,hy,rfl⟩

theorem generator_decomposable_test (P : GeneratorPresentation) (m : ℕ)
    (T : LeastResidueTable P.A m) (a : ℕ) :
    IsDecomposable P.S a ↔
      ∃ b ∈ P.A, b<a ∧ T.w ((a-b)%m) ≤ a-b := by
  constructor
  · rintro ⟨x,y,hxp,hyp,hxS,hyS,ha⟩
    obtain ⟨b,z,hb,hz,hxb⟩ := generated_positive_head ((P.exact_carrier x).1 hxS) hxp
    have hbpos := P.positive b hb
    have hab : a-b=z+y := by omega
    refine ⟨b,hb,by omega,?_⟩
    apply (least_residue_membership T (a-b)).1
    rw [hab]
    exact generated_add hz ((P.exact_carrier y).1 hyS)
  · rintro ⟨b,hb,hba,hleast⟩
    have hrem := (least_residue_membership T (a-b)).2 hleast
    have hbS : b ∈ P.S.carrier :=
      (P.exact_carrier b).2 (by simpa using Generated.add hb Generated.zero)
    exact ⟨b,a-b,P.positive b hb,by omega,hbS,
      (P.exact_carrier (a-b)).2 hrem,by omega⟩

def generatorTimeScale (I d m aWidth logm logd Z : ℕ) : ℕ :=
  I+d*aWidth^3+(d*m*logm+d*logd)*aWidth+(d^2+m)*aWidth^2+Z
def generatorResidentScale (I d m B : ℕ) : ℕ := I+(m+d)*B
def denseGeneratorOutputScale (c B : ℕ) : ℕ := c*B^2
def sparseGeneratorOutputScale (m n logm B : ℕ) : ℕ := (m+n)*logm*B

theorem generator_charging (I d m B logm logd Z A read gcd heap tests output : ℕ)
    (hr : read ≤ A*I) (hg : gcd ≤ A*(d*B^3))
    (hh : heap ≤ A*((d*m*logm+d*logd)*B))
    (ht : tests ≤ A*((d^2+m)*B^2)) (ho : output ≤ A*Z) :
    read+gcd+heap+tests+output ≤ A*generatorTimeScale I d m B logm logd Z := by
  unfold generatorTimeScale
  nlinarith

/-- m=1 is handled before positive-conductor extraction. -/
theorem generator_one_spans (A : Finset ℕ) (h : 1 ∈ A) (x : ℕ) :
    Generated A x := by simpa using generated_multiple h x

def GeneratorGcdPolicy : Prop :=
  ∀ A : Finset ℕ, ∀ g : ℕ,
    (∀ a ∈ A, g ∣ a) → (1 < g) →
    ∀ x, Generated A x → g ∣ x

theorem generated_divisibility (A : Finset ℕ) (g : ℕ)
    (h : ∀ a ∈ A, g ∣ a) {x : ℕ} (hx : Generated A x) : g ∣ x := by
  induction hx with
  | zero => exact dvd_zero g
  | @add a y ha hy ih => exact dvd_add (h a ha) ih

end Partials.WilfFinite.Application
