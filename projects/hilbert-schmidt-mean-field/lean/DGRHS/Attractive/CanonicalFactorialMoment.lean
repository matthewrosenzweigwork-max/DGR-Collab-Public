import DGRHS.Attractive.CanonicalArrayMoment
import DGRHS.Attractive.CountingBounds

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Attractive
variable {Ω : Type*} [MeasurableSpace Ω]

/-- An explicit universal constant; the original source asserts existence. -/
def attractiveMomentConstant : ℝ := 8 * Real.exp 2

lemma attractiveMomentConstant_pos : 0 < attractiveMomentConstant := by
  unfold attractiveMomentConstant
  positivity

lemma arraySurvivingWords_eq_noSingletonWords (n m : ℕ) :
    arraySurvivingWords m n = noSingletonWords (α := Fin n) m := by
  classical
  ext i
  simp only [arraySurvivingWords,noSingletonWords,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [wordMultiplicity_apply,multiplicity]

lemma surviving_factorial_sum_bound (n k : ℕ) (hk : 1 ≤ k) :
    (∑ i ∈ arraySurvivingWords (2*k) n, ∑ _j ∈ arraySurvivingWords (2*k) n,
      ∏ a : Fin n, ((multiplicity i a).factorial : ℝ)) ≤
      ((2*k).factorial : ℝ) * (4*Real.exp 3)^k * (n : ℝ)^(2*k) := by
  simpa only [arraySurvivingWords_eq_noSingletonWords,wordMultiplicity_apply,multiplicity,
    Nat.cast_sum,Nat.cast_prod] using surviving_pair_factorial_bound n k hk

lemma attractive_moment_coefficient_le (C : ℝ) (hC : 0 ≤ C) (k : ℕ) :
    (4*C)^(2*k) * (4*Real.exp 3)^k ≤ (attractiveMomentConstant*C)^(2*k) := by
  have he : Real.exp 4 = (Real.exp 2)^2 := by
    rw [pow_two,← Real.exp_add]
    norm_num
  have hb : (4*C)^2 * (4*Real.exp 3) ≤ (attractiveMomentConstant*C)^2 := by
    calc
      _ = 64*C^2*Real.exp 3 := by ring
      _ ≤ 64*C^2*Real.exp 4 :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num)) (by positivity)
      _ = _ := by rw [he]; unfold attractiveMomentConstant; ring
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (4*C)^2 * (4*Real.exp 3)) hb k
  simpa only [mul_pow,← pow_mul] using hp

/-- Full actual source Step2 bound, with the numerical count proved upstream. -/
theorem canonical_coupled_even_factorial_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (hs : ∀ x y, h (x,y) = h (y,x))
    (hc : ∀ᵐ y ∂μ, ∫ x, h (x,y) ∂μ = 0) (n k : ℕ) (hk : 1 ≤ k) :
    (∫ x : Fin n → Ω,
      |DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (x i,x j))|^(2*k)
        ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤
      (attractiveMomentConstant*C)^(2*k) * (n : ℝ)^(2*k) * ((2*k).factorial : ℝ) := by
  have hC0 : 0 ≤ C := hC.nonneg
  have hsCount := surviving_factorial_sum_bound n k hk
  calc
    _ ≤ (4*C)^(2*k) * ∑ i ∈ arraySurvivingWords (2*k) n,
        ∑ _j ∈ arraySurvivingWords (2*k) n, ∏ a : Fin n, ((multiplicity i a).factorial : ℝ) :=
      canonical_coupled_even_moment_le_surviving μ h hh C hC hs hc n k hk
    _ ≤ (4*C)^(2*k) * (((2*k).factorial : ℝ)*(4*Real.exp 3)^k*(n : ℝ)^(2*k)) :=
      mul_le_mul_of_nonneg_left hsCount (by positivity)
    _ = ((4*C)^(2*k)*(4*Real.exp 3)^k) * ((n : ℝ)^(2*k)*((2*k).factorial : ℝ)) := by ring
    _ ≤ (attractiveMomentConstant*C)^(2*k) * ((n : ℝ)^(2*k)*((2*k).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right (attractive_moment_coefficient_le C hC.nonneg k) (by positivity)
    _ = _ := by ring

/-- This normalization is exactly the exponent in source Z_{N,2β}: -S_N/N.
At n=0 the real division is totalized to zero, and no positive-N claim is hidden. -/
def attractiveNormalizedStatistic (n : ℕ) (h : Ω × Ω → ℝ) (x : Fin n → Ω) : ℝ :=
  -DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (x i,x j)) / (n : ℝ)

lemma attractiveNormalizedStatistic_even_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (n k : ℕ) :
    Integrable (fun x : Fin n → Ω ↦ |attractiveNormalizedStatistic n h x|^(2*k))
      (Measure.pi (fun _ : Fin n ↦ μ)) := by
  cases k with
  | zero => simp
  | succ k =>
    simpa only [attractiveNormalizedStatistic,abs_div,abs_neg,div_pow] using
      (canonical_coupled_abs_power_integrable μ h hh C hC n (2*(k+1)) (by omega)).div_const
        (|(n : ℝ)|^(2*(k+1)))

theorem attractiveNormalizedStatistic_even_factorial_moment (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (hs : ∀ x y, h (x,y) = h (y,x))
    (hc : ∀ᵐ y ∂μ, ∫ x, h (x,y) ∂μ = 0) (n k : ℕ) :
    (∫ x : Fin n → Ω, |attractiveNormalizedStatistic n h x|^(2*k)
      ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤
      (attractiveMomentConstant*C)^(2*k) * ((2*k).factorial : ℝ) := by
  have hC0 : 0 ≤ C := hC.nonneg
  have hK0 : 0 ≤ attractiveMomentConstant := attractiveMomentConstant_pos.le
  by_cases hk : k = 0
  · subst k
    simp
  · have hk1 : 1 ≤ k := by omega
    by_cases hn : n = 0
    · subst n
      simp only [attractiveNormalizedStatistic,Nat.cast_zero,div_zero,abs_zero]
      simp only [zero_pow (by omega : 2*k ≠ 0),integral_zero]
      positivity
    · have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
      have hnP : 0 < (n : ℝ)^(2*k) := pow_pos hnR _
      simp only [attractiveNormalizedStatistic,abs_div,abs_neg,abs_of_nonneg hnR.le,div_pow,integral_div]
      apply (div_le_iff₀ hnP).mpr
      have hb := canonical_coupled_even_factorial_moment μ h hh C hC hs hc n k hk1
      simpa only [mul_assoc,mul_comm,mul_left_comm] using hb

#check @DGRHS.Attractive.canonical_coupled_even_factorial_moment
#check @DGRHS.Attractive.attractiveNormalizedStatistic_even_integrable
#check @DGRHS.Attractive.attractiveNormalizedStatistic_even_factorial_moment
#print axioms DGRHS.Attractive.canonical_coupled_even_factorial_moment
#print axioms DGRHS.Attractive.attractiveNormalizedStatistic_even_integrable
#print axioms DGRHS.Attractive.attractiveNormalizedStatistic_even_factorial_moment
end DGRHS.Attractive
