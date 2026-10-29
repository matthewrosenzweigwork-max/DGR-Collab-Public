import DGRHS.Attractive.CanonicalArrayIntegrals
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Attractive
variable {Ω : Type*} [MeasurableSpace Ω] {n m : ℕ}

/-- A whole word is admissible precisely when every selected cross-copy edge
has distinct sample indices. Positions of repeated labels are unrestricted. -/
def maskedArrayProduct (h : Ω × Ω → ℝ) (i j : Fin m → Fin n)
    (z : (Fin n → Ω) × (Fin n → Ω)) : ℝ :=
  if ∀ l, i l ≠ j l then arrayProduct h i j z else 0

lemma maskedArrayProduct_eq_prod (h : Ω × Ω → ℝ) (i j : Fin m → Fin n)
    (z : (Fin n → Ω) × (Fin n → Ω)) :
    maskedArrayProduct h i j z =
      ∏ l : Fin m, if i l ≠ j l then h (z.1 (i l),z.2 (j l)) else 0 := by
  classical
  by_cases ha : ∀ l, i l ≠ j l
  · simp only [maskedArrayProduct,if_pos ha,arrayProduct]
    apply Finset.prod_congr rfl
    intro l hl
    exact (if_pos (ha l)).symm
  · obtain ⟨l,hl⟩ := not_forall.mp ha
    simp only [maskedArrayProduct,if_neg ha]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ l) (if_neg hl)

/-- Native finite product-of-sums expansion; no improper-integral convention
is used in this algebraic identity. -/
lemma offDiagonalSum_pow_array_expansion (h : Ω × Ω → ℝ)
    (z : (Fin n → Ω) × (Fin n → Ω)) (m : ℕ) :
    (DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (z.1 i,z.2 j)))^m =
      ∑ i : Fin m → Fin n, ∑ j : Fin m → Fin n, maskedArrayProduct h i j z := by
  classical
  unfold DGRHS.Decoupling.offDiagonalSum
  calc
    _ = ∏ _l : Fin m, ∑ a : Fin n, ∑ b : Fin n,
        if a ≠ b then h (z.1 a,z.2 b) else 0 := by simp
    _ = ∑ i : Fin m → Fin n, ∏ l : Fin m, ∑ b : Fin n,
        if i l ≠ b then h (z.1 (i l),z.2 b) else 0 := Fintype.prod_sum _
    _ = _ := by
      simp_rw [Fintype.prod_sum,← maskedArrayProduct_eq_prod]

lemma maskedArrayProduct_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (i j : Fin m → Fin n) :
    Integrable (maskedArrayProduct h i j)
      ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ))) := by
  classical
  by_cases ha : ∀ l, i l ≠ j l
  · have he : maskedArrayProduct h i j = arrayProduct h i j := by
      funext z
      exact if_pos ha
    rw [he]
    exact arrayProduct_integrable μ h hh C hC i j
  · have he : maskedArrayProduct h i j = fun _ ↦ (0 : ℝ) := by
      funext z
      exact if_neg ha
    rw [he]
    exact integrable_const (0 : ℝ)

lemma offDiagonalSum_pow_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (n m : ℕ) :
    Integrable (fun z : (Fin n → Ω) × (Fin n → Ω) ↦
      (DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (z.1 i,z.2 j)))^m)
      ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ))) := by
  simp_rw [offDiagonalSum_pow_array_expansion]
  exact integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
    maskedArrayProduct_integrable μ h hh C hC i j

lemma offDiagonalSum_pow_integral (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (n m : ℕ) :
    (∫ z : (Fin n → Ω) × (Fin n → Ω),
      (DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (z.1 i,z.2 j)))^m
        ∂((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ)))) =
      ∑ i : Fin m → Fin n, ∑ j : Fin m → Fin n,
        ∫ z, maskedArrayProduct h i j z
          ∂((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ))) := by
  simp_rw [offDiagonalSum_pow_array_expansion]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum _ fun j _ ↦ maskedArrayProduct_integrable μ h hh C hC i j
  · intro i hi
    exact integrable_finsetSum _ fun j _ ↦ maskedArrayProduct_integrable μ h hh C hC i j

def arraySurvivingWords (m n : ℕ) : Finset (Fin m → Fin n) :=
  Finset.univ.filter (fun i ↦ ∀ a, multiplicity i a ≠ 1)

lemma maskedArrayProduct_singleton (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (hs : ∀ x y, h (x,y) = h (y,x))
    (hc : ∀ᵐ y ∂μ, ∫ x, h (x,y) ∂μ = 0) (i j : Fin m → Fin n)
    (ha : (∃ a, multiplicity i a = 1) ∨ ∃ a, multiplicity j a = 1) :
    (∫ z, maskedArrayProduct h i j z
      ∂((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ)))) = 0 := by
  classical
  by_cases had : ∀ l, i l ≠ j l
  · simp only [maskedArrayProduct,if_pos had]
    rcases ha with ⟨a,ha⟩ | ⟨a,ha⟩
    · exact canonical_array_singleton_left μ h hh C hC hc i j a ha
    · exact canonical_array_singleton_right μ h hh C hC hs hc i j a ha
  · simp [maskedArrayProduct,had]

lemma maskedArrayProduct_abs_integral_le (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (i j : Fin m → Fin n) :
    |∫ z, maskedArrayProduct h i j z
      ∂((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ)))| ≤
      C^m * ∏ a : Fin n, ((multiplicity i a).factorial : ℝ) := by
  classical
  by_cases ha : ∀ l, i l ≠ j l
  · simpa only [maskedArrayProduct,if_pos ha] using canonical_array_integral_abs_le μ h hh C hC i j
  · simp only [maskedArrayProduct,if_neg ha,integral_zero,abs_zero]
    exact mul_nonneg (pow_nonneg hC.nonneg _) (Finset.prod_nonneg fun a _ ↦ Nat.cast_nonneg _)

/-- The source singleton deletion is a finite equality of proper integrals. -/
lemma offDiagonalSum_pow_integral_surviving (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (hs : ∀ x y, h (x,y) = h (y,x))
    (hc : ∀ᵐ y ∂μ, ∫ x, h (x,y) ∂μ = 0) (n m : ℕ) :
    (∫ z : (Fin n → Ω) × (Fin n → Ω),
      (DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (z.1 i,z.2 j)))^m
        ∂((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ)))) =
      ∑ i ∈ arraySurvivingWords m n, ∑ j ∈ arraySurvivingWords m n,
        ∫ z, maskedArrayProduct h i j z
          ∂((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ))) := by
  classical
  rw [offDiagonalSum_pow_integral μ h hh C hC]
  simp only [arraySurvivingWords,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases his : ∀ a, multiplicity i a ≠ 1
  · simp only [if_pos his]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjs : ∀ a, multiplicity j a ≠ 1
    · simp only [if_pos hjs]
    · simp only [if_neg hjs]
      exact maskedArrayProduct_singleton μ h hh C hC hs hc i j
        (Or.inr (by simpa only [not_forall,not_not] using hjs))
  · simp only [if_neg his]
    apply Finset.sum_eq_zero
    intro j hj
    exact maskedArrayProduct_singleton μ h hh C hC hs hc i j
      (Or.inl (by simpa only [not_forall,not_not] using his))

/-- Exact analytic input to the coordinator's numerical count. The full surviving
word count dominates the off-diagonal restriction without imposing a new premise. -/
theorem canonical_decoupled_even_moment_le_surviving (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (hs : ∀ x y, h (x,y) = h (y,x))
    (hc : ∀ᵐ y ∂μ, ∫ x, h (x,y) ∂μ = 0) (n k : ℕ) :
    (∫ z : (Fin n → Ω) × (Fin n → Ω),
      |DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (z.1 i,z.2 j))|^(2*k)
        ∂((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ)))) ≤
      C^(2*k) * ∑ i ∈ arraySurvivingWords (2*k) n, ∑ _j ∈ arraySurvivingWords (2*k) n,
        ∏ a : Fin n, ((multiplicity i a).factorial : ℝ) := by
  classical
  have he (x : ℝ) : |x|^(2*k) = x^(2*k) := by rw [pow_mul,pow_mul,sq_abs]
  simp_rw [he]
  rw [offDiagonalSum_pow_integral_surviving μ h hh C hC hs hc]
  calc
    _ ≤ ∑ i ∈ arraySurvivingWords (2*k) n, ∑ j ∈ arraySurvivingWords (2*k) n,
        C^(2*k) * ∏ a : Fin n, ((multiplicity i a).factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact (le_abs_self _).trans (maskedArrayProduct_abs_integral_le μ h hh C hC i j)
    _ = _ := by simp_rw [← Finset.mul_sum]

#check @DGRHS.Attractive.canonical_decoupled_even_moment_le_surviving
#print axioms DGRHS.Attractive.canonical_decoupled_even_moment_le_surviving
#check @DGRHS.Attractive.offDiagonalSum_pow_integrable
#check @DGRHS.Attractive.offDiagonalSum_pow_integral
#print axioms DGRHS.Attractive.offDiagonalSum_pow_integrable
#print axioms DGRHS.Attractive.offDiagonalSum_pow_integral
end DGRHS.Attractive
