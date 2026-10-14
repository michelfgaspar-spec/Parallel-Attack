import Partials.Cap.Classification

/-! Blind R5 source for main.tex mixed-pair lemma and two-coset theorem,
and supplement.tex §2. Scaling and class/cardinality transfer are proved
from the actual cap definition. Mixed-pair character and normalized-root
bridges are explicitly uninstantiated; no two-coset maximum is an input. -/
namespace Partials.Cap

noncomputable section
section Field
variable {K : Type*} [Field K] [CharP K 3] [DecidableEq K]

def scalePoint (u : K) (p : Point K) : Point K := (p.1, u * p.2)
def scaleCoefficients (u : K) (S : Finset K) : Finset K := S.image (fun a => u * a)

theorem scalePoint_zero (u : K) : scalePoint u 0 = 0 := by simp [scalePoint]

theorem scalePoint_add (u : K) (p q : Point K) :
    scalePoint u (p + q) = scalePoint u p + scalePoint u q := by
  apply Prod.ext
  · rfl
  · simp [scalePoint, mul_add]

theorem scalePoint_injective {u : K} (hu : u ≠ 0) : Function.Injective (scalePoint u) := by
  intro p q hpq
  have hf := congrArg (fun r : Point K => r.1) hpq
  have hs := congrArg (fun r : Point K => r.2) hpq
  apply Prod.ext
  · exact hf
  · exact mul_left_cancel₀ hu hs

theorem scalePoint_inverse {u : K} (hu : u ≠ 0) (p : Point K) :
    scalePoint u⁻¹ (scalePoint u p) = p := by
  apply Prod.ext
  · rfl
  · simp [scalePoint, hu, ← mul_assoc]

theorem cap_image_additive_iff (U : Set (Point K)) (f : Point K → Point K)
    (hfi : Function.Injective f) (hf0 : f 0 = 0)
    (hfa : ∀ p q, f (p + q) = f p + f q) : Cap (f '' U) ↔ Cap U := by
  constructor
  · intro hc a ha b hb c hcU hab hac hbc hsum
    apply hc (f a) ⟨a, ha, rfl⟩ (f b) ⟨b, hb, rfl⟩ (f c) ⟨c, hcU, rfl⟩
      (fun h => hab (hfi h)) (fun h => hac (hfi h)) (fun h => hbc (hfi h))
    calc
      f a + f b + f c = f (a + b + c) := by rw [hfa, hfa]
      _ = 0 := by rw [hsum, hf0]
  · intro hc a ha b hb c hcU hab hac hbc hsum
    obtain ⟨a₀, ha₀, rfl⟩ := ha
    obtain ⟨b₀, hb₀, rfl⟩ := hb
    obtain ⟨c₀, hc₀, rfl⟩ := hcU
    apply hc a₀ ha₀ b₀ hb₀ c₀ hc₀
      (fun h => hab (congrArg f h)) (fun h => hac (congrArg f h))
      (fun h => hbc (congrArg f h))
    apply hfi
    simpa [hfa, hf0] using hsum

theorem parabola_scaling (u a x : K) :
    scalePoint u (parabolaPoint a x) = parabolaPoint (u * a) x := by
  apply Prod.ext
  · rfl
  · simp [scalePoint, parabolaPoint, mul_assoc]

theorem P_scaling (u : K) (S : Finset K) :
    P (scaleCoefficients u S) = scalePoint u '' P S := by
  ext p
  constructor
  · rintro ⟨b, hb, x, hx, rfl⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    refine ⟨parabolaPoint a x, ⟨a, ha, x, hx, rfl⟩, ?_⟩
    exact parabola_scaling u a x
  · rintro ⟨p, ⟨a, ha, x, hx, rfl⟩, rfl⟩
    refine ⟨u * a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, x, hx, ?_⟩
    exact parabola_scaling u a x

theorem cap_scaling_iff {u : K} (hu : u ≠ 0) (S : Finset K) :
    Cap (P (scaleCoefficients u S)) ↔ Cap (P S) := by
  rw [P_scaling]
  exact cap_image_additive_iff _ _ (scalePoint_injective hu) (scalePoint_zero u) (scalePoint_add u)

theorem scaleCoefficients_card {u : K} (hu : u ≠ 0) (S : Finset K) :
    (scaleCoefficients u S).card = S.card :=
  Finset.card_image_of_injective S (fun _ _ h => mul_left_cancel₀ hu h)

theorem scaleCoefficients_injective {u : K} (hu : u ≠ 0) :
    Function.Injective (scaleCoefficients u) :=
  finset_image_injective (fun _ _ h => mul_left_cancel₀ hu h)

theorem scaleCoefficients_inverse {u : K} (hu : u ≠ 0) (S : Finset K) :
    scaleCoefficients u⁻¹ (scaleCoefficients u S) = S := by
  simp [scaleCoefficients, Finset.image_image, hu, ← mul_assoc]

theorem scaleCoefficients_inverse_right {u : K} (hu : u ≠ 0) (S : Finset K) :
    scaleCoefficients u (scaleCoefficients u⁻¹ S) = S := by
  simp [scaleCoefficients, Finset.image_image, hu, ← mul_assoc]

theorem P_mono {S T : Finset K} (h : S ⊆ T) : P S ⊆ P T := by
  rintro p ⟨a, ha, hp⟩
  exact ⟨a, h ha, hp⟩

theorem cap_mono {U V : Set (Point K)} (h : U ⊆ V) (hc : Cap V) : Cap U := by
  intro a ha b hb c hcU hab hac hbc
  exact hc a (h ha) b (h hb) c (h hcU) hab hac hbc

theorem repeated_delta_left (a b : K) : delta a a b = a * (b - a) := by
  have hthree : (3 : K) = 0 := CharP.cast_eq_zero K 3
  unfold delta
  linear_combination -a * b * hthree

theorem repeated_delta_right (a b : K) : delta a b b = b * (a - b) := by
  have hthree : (3 : K) = 0 := CharP.cast_eq_zero K 3
  unfold delta
  linear_combination -a * b * hthree

theorem repeated_delta_ratio {a b : K} (ha : a ≠ 0) (hab : a ≠ b) :
    (delta a b b) / (delta a a b) = -(b / a) := by
  rw [repeated_delta_left, repeated_delta_right]
  have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  field_simp [ha, hba]
  ring

/-- Primitive quadratic-character dichotomy for the specified finite field.
It is not valid for arbitrary characteristic-three fields without extra
information. All its numerical/algebraic discharge remains open. -/
def SquareIndexTwoDuty (K : Type*) [Field K] [CharP K 3] : Prop :=
  ∀ d₁ d₂ : K, d₁ ≠ 0 → d₂ ≠ 0 → ¬ Square (d₂ / d₁) →
    Square d₁ ∨ Square d₂

structure OppositeCharacterDuty (z : K) : Prop where
  primitive_nonzero : primitive z ≠ 0
  domain_nonzero : NonzeroCoefficients (domainD z)
  cosets_disjoint : Disjoint (H41 z) (oppositeCoset z)
  ratio_negative_nonsquare : ∀ a ∈ H41 z, ∀ b ∈ oppositeCoset z,
    ¬ Square (-(b / a))

/-- Explicit unfinished interpretation of a repeated-label square root.
Its discharge is the normalized equation, admissible endpoints and distinct
point argument. This is a pair-level bridge, not a maximum or classification
premise. Nonantipodality of D must be established in that discharge. -/
def RepeatedSquareObstructionDuty (z : K) : Prop :=
  ∀ a b : K, a ∈ domainD z → b ∈ domainD z → a ≠ b →
    (Square (delta a a b) ∨ Square (delta a b b)) → ¬ Cap (P ({a, b} : Finset K))

def MixedPairBridge (z : K) : Prop :=
  ∀ a ∈ H41 z, ∀ b ∈ oppositeCoset z, ¬ Cap (P ({a, b} : Finset K))

theorem mixed_pair_bridge_from_character {z : K} (hc : OppositeCharacterDuty z)
    (hs : SquareIndexTwoDuty K) (hn : RepeatedSquareObstructionDuty z) : MixedPairBridge z := by
  intro a ha b hb
  have haD : a ∈ domainD z := Or.inl ha
  have hbD : b ∈ domainD z := Or.inr hb
  have han : a ≠ 0 := hc.domain_nonzero a haD
  have hbn : b ≠ 0 := hc.domain_nonzero b hbD
  have hab : a ≠ b := by
    intro h
    exact Set.disjoint_left.mp hc.cosets_disjoint ha (h.symm ▸ hb)
  have hd₁ : delta a a b ≠ 0 := by
    rw [repeated_delta_left]
    exact mul_ne_zero han (sub_ne_zero.mpr hab.symm)
  have hd₂ : delta a b b ≠ 0 := by
    rw [repeated_delta_right]
    exact mul_ne_zero hbn (sub_ne_zero.mpr hab)
  have hratio : ¬ Square ((delta a b b) / (delta a a b)) := by
    rw [repeated_delta_ratio han hab]
    exact hc.ratio_negative_nonsquare a ha b hb
  exact hn a b haD hbD hab (hs _ _ hd₁ hd₂ hratio)

theorem cap_in_D_one_coset {z : K} (hm : MixedPairBridge z) (S : Finset K)
    (hD : (↑S : Set K) ⊆ domainD z) (hcap : Cap (P S)) :
    (↑S : Set K) ⊆ H41 z ∨ (↑S : Set K) ⊆ oppositeCoset z := by
  by_cases hH : (↑S : Set K) ⊆ H41 z
  · exact Or.inl hH
  · right
    have hex : ∃ b ∈ S, b ∉ H41 z := by
      by_contra h
      push_neg at h
      exact hH (fun b hb => h b hb)
    obtain ⟨b, hb, hbH⟩ := hex
    have hbG : b ∈ oppositeCoset z := (hD hb).resolve_left hbH
    intro a ha
    rcases hD ha with haH | haG
    · have hpair : Cap (P ({a, b} : Finset K)) := by
        apply cap_mono (P_mono ?_) hcap
        intro c hc
        simp only [Finset.mem_insert, Finset.mem_singleton] at hc
        rcases hc with rfl | rfl
        · exact ha
        · exact hb
      exact False.elim (hm a haH b hbG hpair)
    · exact haG

theorem scaled_H_subset_coset {z : K} (S : Finset K) (hS : (↑S : Set K) ⊆ H41 z) :
    (↑(scaleCoefficients (primitive z) S) : Set K) ⊆ oppositeCoset z := by
  intro b hb
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  exact ⟨a, hS ha, rfl⟩

theorem unscaled_coset_subset_H {z : K} (hg : primitive z ≠ 0) (S : Finset K)
    (hS : (↑S : Set K) ⊆ oppositeCoset z) :
    (↑(scaleCoefficients (primitive z)⁻¹ S) : Set K) ⊆ H41 z := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨c, hc, rfl⟩ := hS hb
  simpa [hg, ← mul_assoc] using hc

theorem maximum_five_two_cosets {z : K} (hg : primitive z ≠ 0)
    (hm : MixedPairBridge z) (hH : MaximumFive (H41 z)) : MaximumFive (domainD z) := by
  constructor
  · intro S hS
    rcases cap_in_D_one_coset hm S hS.1 hS.2 with hsH | hsG
    · exact hH.1 S ⟨hsH, hS.2⟩
    · let T := scaleCoefficients (primitive z)⁻¹ S
      have hT : CapCoefficientSet (H41 z) T :=
        ⟨unscaled_coset_subset_H hg S hsG, (cap_scaling_iff (inv_ne_zero hg) S).2 hS.2⟩
      have hc := hH.1 T hT
      simpa [T, scaleCoefficients_card (inv_ne_zero hg)] using hc
  · obtain ⟨S, hS, hc⟩ := hH.2
    refine ⟨S, ⟨?_, hS.2⟩, hc⟩
    intro a ha
    exact Or.inl (hS.1 ha)

theorem maximizers_two_cosets {z : K} (hg : primitive z ≠ 0) (hm : MixedPairBridge z) :
    Maximizers (domainD z) = Maximizers (H41 z) ∪
      scaleCoefficients (primitive z) '' Maximizers (H41 z) := by
  ext S
  constructor
  · rintro ⟨hS, hc⟩
    rcases cap_in_D_one_coset hm S hS.1 hS.2 with hsH | hsG
    · exact Or.inl ⟨⟨hsH, hS.2⟩, hc⟩
    · right
      refine ⟨scaleCoefficients (primitive z)⁻¹ S, ⟨⟨unscaled_coset_subset_H hg S hsG,
        (cap_scaling_iff (inv_ne_zero hg) S).2 hS.2⟩, ?_⟩, ?_⟩
      · rw [scaleCoefficients_card (inv_ne_zero hg), hc]
      · exact scaleCoefficients_inverse_right hg S
  · rintro (hH | ⟨T, hT, rfl⟩)
    · refine ⟨⟨?_, hH.1.2⟩, hH.2⟩
      intro a ha
      exact Or.inl (hH.1.1 ha)
    · refine ⟨⟨?_, (cap_scaling_iff hg T).2 hT.1.2⟩, ?_⟩
      · intro a ha
        exact Or.inr (scaled_H_subset_coset T hT.1.1 ha)
      · rw [scaleCoefficients_card hg, hT.2]

theorem maximizing_classes_disjoint {z : K} (hg : primitive z ≠ 0)
    (hdis : Disjoint (H41 z) (oppositeCoset z)) :
    Disjoint (Maximizers (H41 z))
      (scaleCoefficients (primitive z) '' Maximizers (H41 z)) := by
  apply Set.disjoint_left.mpr
  intro S hS hSG
  obtain ⟨T, hT, hTS⟩ := hSG
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hS.2]; omega)
  obtain ⟨a, ha⟩ := hSne
  have haH := hS.1.1 ha
  have haG : a ∈ oppositeCoset z := by
    rw [← hTS] at ha
    exact scaled_H_subset_coset T hT.1.1 ha
  exact Set.disjoint_left.mp hdis haH haG

def coefficientTwoClassFamily (z : K) (F : Finset (Finset K)) : Finset (Finset K) :=
  F ∪ F.image (scaleCoefficients (primitive z))

theorem two_class_family_card {z : K} (hg : primitive z ≠ 0)
    (hdis : Disjoint (H41 z) (oppositeCoset z)) (F : Finset (Finset K))
    (hF : ∀ S ∈ F, S ∈ Maximizers (H41 z)) (hc : F.card = 328) :
    (coefficientTwoClassFamily z F).card = 656 := by
  have hclasses := maximizing_classes_disjoint hg hdis
  have hfdis : Disjoint F (F.image (scaleCoefficients (primitive z))) := by
    apply Finset.disjoint_left.mpr
    intro S hS hSI
    obtain ⟨T, hT, hTS⟩ := Finset.mem_image.mp hSI
    exact Set.disjoint_left.mp hclasses (hF S hS) ⟨T, hF T hT, hTS⟩
  rw [coefficientTwoClassFamily, Finset.card_union_of_disjoint hfdis,
    Finset.card_image_of_injective F (scaleCoefficients_injective hg), hc]

theorem two_class_family_exhausts {z : K} (hg : primitive z ≠ 0)
    (hm : MixedPairBridge z) (F : Finset (Finset K))
    (hF : (↑F : Set (Finset K)) = Maximizers (H41 z)) :
    (↑(coefficientTwoClassFamily z F) : Set (Finset K)) = Maximizers (domainD z) := by
  rw [maximizers_two_cosets hg hm, coefficientTwoClassFamily]
  simp [hF]

/-- Exact theorem-level transfer: the H classification, once derived from
its certificate and action, supplies a finite family F. No D maximum,
D count or D classification is an input. -/
theorem two_coset_classification_transfer {z : K} (hg : primitive z ≠ 0)
    (hm : MixedPairBridge z) (hdis : Disjoint (H41 z) (oppositeCoset z))
    (hmaxH : MaximumFive (H41 z)) (F : Finset (Finset K))
    (hF : (↑F : Set (Finset K)) = Maximizers (H41 z)) (hc : F.card = 328) :
    MaximumFive (domainD z) ∧
      (↑(coefficientTwoClassFamily z F) : Set (Finset K)) = Maximizers (domainD z) ∧
      (coefficientTwoClassFamily z F).card = 656 := by
  refine ⟨maximum_five_two_cosets hg hm hmaxH,
    two_class_family_exhausts hg hm F hF, two_class_family_card hg hdis F ?_ hc⟩
  intro S hS
  rw [← hF]
  exact hS

end Field
end
end Partials.Cap
