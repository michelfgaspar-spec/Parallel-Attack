import Partials.WilfFinite.PrefixTransition

/-! Exact signed arithmetic supporting pruning. No current W0>=0 test is an
exit. Full tree bridges are uninhabited targets below, not axioms. -/
namespace Partials.WilfFinite.Prefix

theorem product_arithmetic (c k ell q r k' ell' : ℕ)
    (hk : k+1≤k') (he : ell+1≤ell') (hprod : c≤(k+1)*(ell+1)) :
    0≤(k' : ℤ)*ell'+(q : ℤ)*r-c := by
  have hmul : (k+1)*(ell+1)≤k'*ell' := Nat.mul_le_mul hk he
  have hbase : (c : ℤ)≤(k' : ℤ)*ell' := by exact_mod_cast le_trans hprod hmul
  have hqr : (0 : ℤ)≤(q : ℤ)*r := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  omega

theorem large_tail_arithmetic (c k ell q r k' r' : ℕ)
    (hk : k+1≤k') (hr : r≤r'+1) (hq : q≤k) :
    ((k' : ℤ)*(ell+1)+(q : ℤ)*r'-c)-
      ((k : ℤ)*ell+(q : ℤ)*r-c) ≥ (k : ℤ)+ell+1-q ∧
    (k : ℤ)+ell+1-q ≥ ell+1 ∧ (0 : ℤ)<(k : ℤ)+ell+1-q := by
  have hkZ : (k : ℤ)+1≤k' := by exact_mod_cast hk
  have hrZ : (r : ℤ)≤(r' : ℤ)+1 := by exact_mod_cast hr
  have hqZ : (q : ℤ)≤k := by exact_mod_cast hq
  have hprodK := mul_nonneg (show 0≤(k' : ℤ)-k-1 by omega)
    (show (0 : ℤ)≤(ell : ℤ)+1 by omega)
  have hprodR := mul_nonneg (show (0 : ℤ)≤q from Nat.cast_nonneg _)
    (show 0≤(r' : ℤ)-r+1 by omega)
  constructor
  · nlinarith
  · constructor <;> omega

theorem suffix_first_child_nonnegative (w delta w' : ℤ)
    (hinc : delta≤w'-w) (hguard : 0≤w+delta) : 0≤w' := by omega

theorem suffix_later_nonnegative (w w' : ℤ) (hw : 0≤w)
    (hstrict : w<w') : 0≤w' := by omega

theorem equality_at_tail_excludes_second (c m gamma a x : ℕ)
    (ha : c+m≤a+gamma) (hx : x<c+m) : ¬a+gamma≤x := by omega

theorem two_new_generators_excluded (c m gamma a x : ℕ)
    (ha : c+m≤a+gamma) (hag : gamma<a) (hx : x<c+m) : ¬a+a≤x := by omega

/-- Two values in one half-open interval of length m cannot be distinct
members of a single arithmetic progression. Coefficients are mathematical
integers; the residue argument therefore also covers equality at the gate. -/
theorem threshold_progression_unique (c m a x y j k : ℤ)
    (hm : 0<m) (hx : c≤x ∧ x<c+m) (hy : c≤y ∧ y<c+m)
    (hex : x=a+j*m) (hey : y=a+k*m) : x=y := by
  by_cases hjk : j=k
  · subst k
    omega
  · by_cases hjlt : j<k
    · have hp := mul_nonneg (show 0≤k-j-1 by omega) (show 0≤m by omega)
      nlinarith
    · have hp := mul_nonneg (show 0≤j-k-1 by omega) (show 0≤m by omega)
      nlinarith

theorem rank_upper_arithmetic (k v k' : ℕ) (hkv : v<k) (hmono : k≤k') :
    ¬k'≤v := by omega

theorem rank_upper_descendants (s t : PrefixState) (p : Core.Parameters)
    (hpath : Descendant s t) (hbad : p.v<k s) : ¬Core.InTarget p t.canonical := by
  intro htarget
  have hbound := htarget.2.2
  change k t≤p.v at hbound
  exact rank_upper_arithmetic _ _ _ hbad (descendant_k_mono hpath) hbound

/-- Raw newly decomposable threshold values, expressed without a desired
right-count conclusion. Proving this residue-form target is the precise
remaining combinatorial Lean duty for the large-tail theorem. -/
def NewlyDecomposable (c : ℕ) (G : List ℕ) (a x : ℕ) : Prop :=
  Decomposable c (G++[a]) x ∧ ¬Decomposable c G x

def LargeTailResidueTarget : Prop := ∀ (s : PrefixState) (gamma a x : ℕ),
  s.G[1]?=some gamma → b s<a → a<c s → a∉Core.left s.canonical →
  c s+s.m≤a+gamma → c s≤x → x<c s+s.m →
  NewlyDecomposable (c s) s.G a x → ∃ j : ℕ, 1≤j ∧ x=a+j*s.m

def ProductDescendantsTarget : Prop := ∀ s t : PrefixState,
  ProperDescendant s t → c s≤(k s+1)*(ell s+1) → 0≤W0 t

def LargeTailChildTarget : Prop := ∀ (s t : PrefixState) (a gamma : ℕ),
  Child s t a → s.G[1]?=some gamma → c s+s.m≤a+gamma →
  r s≤r t+1 ∧ Delta s≤W0 t-W0 s ∧ (ell s : ℤ)+1≤Delta s

def LargeTailSuffixTarget : Prop := ∀ (s t z : PrefixState) (a gamma : ℕ),
  Child s t a → Descendant t z → s.G[1]?=some gamma →
  c s+s.m≤a+gamma → 0≤W0 s+Delta s → 0≤W0 z

def UpperCardinalityTarget : Prop := ∀ (s t : PrefixState) (p : Core.Parameters),
  Descendant s t → p.v<k s → ¬Core.InTarget p t.canonical

theorem upper_cardinality : UpperCardinalityTarget := by
  intro s t p hpath hbad
  exact rank_upper_descendants s t p hpath hbad

theorem product_descendants : ProductDescendantsTarget := by
  intro s t hproper hprod
  obtain ⟨z,a,hchild,hpath⟩ := hproper
  have hkchild := child_k_growth s z a hchild
  have hkpath := descendant_k_mono hpath
  have hechild := child_ell_growth s z a hchild
  have hepath := descendant_ell_mono hpath
  have hc := (descendant_conductor_fixed hpath).trans hchild.1
  unfold W0
  rw [hc]
  exact product_arithmetic (c s) (k s) (ell s) (q t) (r t) (k t) (ell t)
    (by omega) (by omega) hprod

end Partials.WilfFinite.Prefix
