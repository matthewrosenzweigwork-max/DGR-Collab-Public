import DGRHS.Decoupling.FiniteCubeBanachMixedDegreeSmallBall
import DGRHS.Decoupling.FiniteCubeCharacterMask

/-!
Records-only, uncompiled finite selector expansion for one fixed ordered
injective tuple. The all-false slot subset is the all-copy-pattern constant
term. Every nonempty subset maps to a Walsh mask whose degree is exactly its
cardinality. This is not the all-pattern swap-invariance identity and makes
no probability claim.
-/
noncomputable section
open DGRHS.Decoupling.FiniteCube

namespace DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion

abbrev OrderedTuple (n k : ℕ) := SourceOrderedTuple n k

def selectedLabel {n k : ℕ} (σ : Cube n) (ell : Cube k)
    (t : OrderedTuple n k) (q : Fin k) : Bool :=
  if σ (t.1 q) then ell q else !(ell q)

def slotEta {k : ℕ} (ell j : Cube k) (q : Fin k) : ℝ :=
  if j q = ell q then 1 else -1

def selectorSubsetMask {n k : ℕ} (t : OrderedTuple n k) (a : Cube k) : Cube n :=
  sourceSupportMask ((boolMaskSupport a).image t.1)

def selectorSubsetWeight {k : ℕ} (ell j a : Cube k) : ℝ :=
  ∏ q : Fin k, if a q then slotEta ell j q else 1

lemma selector_factor_eq_two_or_zero
    {n k : ℕ} (σ : Cube n) (ell j : Cube k)
    (t : OrderedTuple n k) (q : Fin k) :
    1 + slotEta ell j q * DGRHS.Decoupling.rademacherSign (σ (t.1 q)) =
      if j q = selectedLabel σ ell t q then 2 else 0 := by
  cases hs : σ (t.1 q) <;> cases he : ell q <;> cases hj : j q <;>
    simp [slotEta, selectedLabel, DGRHS.Decoupling.rademacherSign,
      hs, he, hj] <;> norm_num

lemma selector_product_expand
    {n k : ℕ} (σ : Cube n) (ell j : Cube k) (t : OrderedTuple n k) :
    (∏ q : Fin k,
      (1 + slotEta ell j q * DGRHS.Decoupling.rademacherSign (σ (t.1 q)))) =
      ∑ a : Cube k, ∏ q : Fin k,
        if a q then slotEta ell j q * DGRHS.Decoupling.rademacherSign (σ (t.1 q))
        else 1 := by
  classical
  calc
    _ = ∏ q : Fin k,
        ∑ b : Bool,
          if b then slotEta ell j q * DGRHS.Decoupling.rademacherSign (σ (t.1 q))
          else 1 := by
        apply Finset.prod_congr rfl
        intro q hq
        rw [Fintype.sum_bool]
        simp <;> ring
    _ = ∑ a : Cube k, ∏ q : Fin k,
          if a q then slotEta ell j q * DGRHS.Decoupling.rademacherSign (σ (t.1 q))
          else 1 := Fintype.prod_sum _

lemma selector_subset_monomial_eq_weight_mul_walsh
    {n k : ℕ} (σ : Cube n) (ell j a : Cube k)
    (t : OrderedTuple n k) :
    (∏ q : Fin k,
      if a q then slotEta ell j q * DGRHS.Decoupling.rademacherSign (σ (t.1 q))
      else 1) =
      selectorSubsetWeight ell j a * cubeWalsh n (selectorSubsetMask t a) σ := by
  classical
  have hsplit :
      (∏ q : Fin k,
        if a q then slotEta ell j q * DGRHS.Decoupling.rademacherSign (σ (t.1 q))
        else 1) =
      (∏ q : Fin k, if a q then slotEta ell j q else 1) *
        (∏ q : Fin k, if a q then DGRHS.Decoupling.rademacherSign (σ (t.1 q))
          else 1) := by
    calc
      _ = ∏ q : Fin k,
          (if a q then slotEta ell j q else 1) *
            (if a q then DGRHS.Decoupling.rademacherSign (σ (t.1 q)) else 1) := by
          apply Finset.prod_congr rfl
          intro q hq
          by_cases ha : a q <;> simp [ha]
      _ = _ := Finset.prod_mul_distrib
  have hsign :
      (∏ q : Fin k, if a q then DGRHS.Decoupling.rademacherSign (σ (t.1 q))
        else 1) =
      DGRHS.Decoupling.rademacherCharacter ((boolMaskSupport a).image t.1) σ := by
    classical
    unfold DGRHS.Decoupling.rademacherCharacter
    rw [Finset.prod_image (fun q hq r hr hqr => t.2 hqr)]
    simp [boolMaskSupport, Finset.prod_filter]
  calc
    _ = (∏ q : Fin k, if a q then slotEta ell j q else 1) *
          (∏ q : Fin k, if a q then DGRHS.Decoupling.rademacherSign (σ (t.1 q))
            else 1) := hsplit
    _ = selectorSubsetWeight ell j a *
          DGRHS.Decoupling.rademacherCharacter ((boolMaskSupport a).image t.1) σ := by
        rw [selectorSubsetWeight, hsign]
    _ = selectorSubsetWeight ell j a * cubeWalsh n (selectorSubsetMask t a) σ := by
        rw [selectorSubsetMask, cubeWalsh_sourceSupportMask]

theorem fixed_tuple_all_pattern_walsh_expansion
    {n k : ℕ} {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (σ : Cube n) (ell : Cube k) (t : OrderedTuple n k)
    (F : Cube k → E) :
    (2 : ℝ)^k • F (fun q => selectedLabel σ ell t q) =
      ∑ j : Cube k, ∑ a : Cube k,
        (selectorSubsetWeight ell j a *
          cubeWalsh n (selectorSubsetMask t a) σ) • F j := by
  classical
  have hselected :
      (2 : ℝ)^k • F (fun q => selectedLabel σ ell t q) =
        ∑ j : Cube k,
          (∏ q : Fin k,
            (1 + slotEta ell j q *
              DGRHS.Decoupling.rademacherSign (σ (t.1 q)))) • F j := by
    simp_rw [selector_factor_eq_two_or_zero]
    let j₀ : Cube k := fun q => selectedLabel σ ell t q
    rw [Finset.sum_eq_single j₀]
    · have hprod :
          (∏ q : Fin k,
            if j₀ q = selectedLabel σ ell t q then (2 : ℝ) else 0) =
          ∏ _q : Fin k, (2 : ℝ) := by
        apply Finset.prod_congr rfl
        intro q hq
        simp [j₀]
      have hpow : (∏ _q : Fin k, (2 : ℝ)) = (2 : ℝ)^k := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [hprod, hpow]
    · intro j hj hne
      have hdiff : ∃ q : Fin k, j q ≠ j₀ q := by
        by_contra h
        apply hne
        funext q
        by_contra hq
        exact (h ⟨q, hq⟩).elim
      obtain ⟨q, hq⟩ := hdiff
      have hfactor :
          (if j q = selectedLabel σ ell t q then (2 : ℝ) else 0) = 0 := by
        simp [j₀, hq]
      have hprod :
          (∏ q : Fin k,
            if j q = selectedLabel σ ell t q then (2 : ℝ) else 0) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ q) hfactor
      simp [hprod]
    · simp
  calc
    _ = ∑ j : Cube k,
          (∏ q : Fin k,
            (1 + slotEta ell j q *
              DGRHS.Decoupling.rademacherSign (σ (t.1 q)))) • F j := hselected
    _ = ∑ j : Cube k, ∑ a : Cube k,
          (∏ q : Fin k,
            if a q then slotEta ell j q *
              DGRHS.Decoupling.rademacherSign (σ (t.1 q)) else 1) • F j := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [selector_product_expand]
        rw [Finset.sum_smul]
    _ = ∑ j : Cube k, ∑ a : Cube k,
          (selectorSubsetWeight ell j a *
            cubeWalsh n (selectorSubsetMask t a) σ) • F j := by
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro a ha
        rw [selector_subset_monomial_eq_weight_mul_walsh]

theorem empty_subset_is_all_pattern_constant
    {n k : ℕ} {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (σ : Cube n) (ell : Cube k) (t : OrderedTuple n k)
    (F : Cube k → E) :
    ∑ j : Cube k,
      (selectorSubsetWeight ell j (fun _ => false) *
        cubeWalsh n (selectorSubsetMask t (fun _ => false)) σ) • F j =
      ∑ j : Cube k, F j := by
  classical
  have hmask : selectorSubsetMask t (fun _ : Fin k => false) =
      sourceSupportMask (∅ : Finset (Fin n)) := by
    unfold selectorSubsetMask
    have hsupport : boolMaskSupport (fun _ : Fin k => false) = ∅ := by
      ext q
      simp [boolMaskSupport]
    rw [hsupport, Finset.image_empty]
  have hchar :
      cubeWalsh n (selectorSubsetMask t (fun _ : Fin k => false)) σ = 1 := by
    rw [hmask, cubeWalsh_sourceSupportMask]
    simp [DGRHS.Decoupling.rademacherCharacter]
  simp [selectorSubsetWeight, hchar]

theorem selector_subset_mask_degree
    {n k : ℕ} (t : OrderedTuple n k) (a : Cube k) :
    cubeWalshDegree n (selectorSubsetMask t a) = (boolMaskSupport a).card := by
  rw [selectorSubsetMask, cubeWalshDegree_sourceSupportMask,
    Finset.card_image_of_injective _ t.2]

theorem selector_subset_degree_bounds
    {n k : ℕ} (t : OrderedTuple n k) (a : Cube k)
    (ha : a ≠ fun _ => false) :
    1 ≤ cubeWalshDegree n (selectorSubsetMask t a) ∧
      cubeWalshDegree n (selectorSubsetMask t a) ≤ k := by
  have hsome : ∃ q : Fin k, a q = true := by
    by_contra hnone
    apply ha
    funext q
    cases hq : a q with
    | false => rfl
    | true => exact False.elim (hnone ⟨q, hq⟩)
  rcases hsome with ⟨q, hq⟩
  have hcard_pos : 0 < (boolMaskSupport a).card :=
    Finset.card_pos.mpr ⟨q, by simp [boolMaskSupport, hq]⟩
  rw [selector_subset_mask_degree]
  constructor
  · exact Nat.succ_le_iff.mpr hcard_pos
  · exact le_trans (Finset.card_le_univ _) (by simp)

end DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion

#print DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.fixed_tuple_all_pattern_walsh_expansion
#print DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.empty_subset_is_all_pattern_constant
#print DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selector_subset_degree_bounds

#print axioms DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.fixed_tuple_all_pattern_walsh_expansion
#print axioms DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.empty_subset_is_all_pattern_constant
#print axioms DGRHS.Decoupling.Prop33.FixedTupleSelectorExpansion.selector_subset_degree_bounds
