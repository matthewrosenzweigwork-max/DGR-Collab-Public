import DGRHS.Attractive.CanonicalArraySamples
import DGRHS.Attractive.CanonicalArrayExpansion

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace DGRHS.Attractive
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Actual distinct-index product laws supply proper coupled high moments. -/
lemma canonical_coupled_abs_power_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (n p : ℕ) (hp : 1 ≤ p) :
    Integrable (fun x : Fin n → Ω ↦
      |DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (x i,x j))|^p)
      (Measure.pi (fun _ : Fin n ↦ μ)) := by
  have hLp : MemLp (fun x : Fin n → Ω ↦
      DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (x i,x j))) (p : ℝ≥0∞)
      (Measure.pi (fun _ : Fin n ↦ μ)) := by
    unfold DGRHS.Decoupling.offDiagonalSum
    apply memLp_finsetSum
    intro i hi
    apply memLp_finsetSum
    intro j hj
    by_cases hij : i ≠ j
    · simp_rw [if_pos hij]
      exact DGRHS.Decoupling.memLp_coupled_term μ h (p : ℝ≥0∞)
        (joint_memLp μ h hh C hC p hp) i j hij
    · simp_rw [if_neg hij]
      simp
  simpa only [Real.norm_eq_abs] using hLp.integrable_norm_pow'

/-- The decoupled power expansion proves proper absolute moments, including
the zeroth moment, before any numerical count is substituted. -/
lemma canonical_decoupled_abs_power_integrable (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (n p : ℕ) :
    Integrable (fun z : (Fin n → Ω) × (Fin n → Ω) ↦
      |DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (z.1 i,z.2 j))|^p)
      ((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ))) := by
  simpa only [Real.norm_eq_abs,abs_pow] using
    (offDiagonalSum_pow_integrable μ h hh C hC n p).norm

/-- The source2533--2567 analytic endpoint: actual factor-four decoupling,
actual finite expansion and singleton cancellation, followed by the actual
row factorial product estimate. No numerical count or moment bound is assumed. -/
theorem canonical_coupled_even_moment_le_surviving (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (hs : ∀ x y, h (x,y) = h (y,x))
    (hc : ∀ᵐ y ∂μ, ∫ x, h (x,y) ∂μ = 0) (n k : ℕ) (hk : 1 ≤ k) :
    (∫ x : Fin n → Ω,
      |DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (x i,x j))|^(2*k)
        ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤
      (4*C)^(2*k) * ∑ i ∈ arraySurvivingWords (2*k) n, ∑ _j ∈ arraySurvivingWords (2*k) n,
        ∏ a : Fin n, ((multiplicity i a).factorial : ℝ) := by
  calc
    _ ≤ 4^(2*k) * ∫ z : (Fin n → Ω) × (Fin n → Ω),
        |DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (z.1 i,z.2 j))|^(2*k)
          ∂((Measure.pi (fun _ : Fin n ↦ μ)).prod (Measure.pi (fun _ : Fin n ↦ μ))) :=
      row_factorial_even_decoupling μ h hh C hC hs hc n k hk
    _ ≤ 4^(2*k) * (C^(2*k) * ∑ i ∈ arraySurvivingWords (2*k) n,
        ∑ _j ∈ arraySurvivingWords (2*k) n, ∏ a : Fin n, ((multiplicity i a).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left (canonical_decoupled_even_moment_le_surviving μ h hh C hC hs hc n k)
        (by positivity)
    _ = _ := by rw [mul_pow,mul_assoc]

#check @DGRHS.Attractive.rowFactorialMoments_of_proper_bound
#check @DGRHS.Attractive.rowFactorialMoments_of_lintegral
#check @DGRHS.Attractive.canonical_coupled_abs_power_integrable
#check @DGRHS.Attractive.canonical_decoupled_abs_power_integrable
#check @DGRHS.Attractive.canonical_coupled_even_moment_le_surviving
#print axioms DGRHS.Attractive.canonical_coupled_abs_power_integrable
#print axioms DGRHS.Attractive.canonical_decoupled_abs_power_integrable
#print axioms DGRHS.Attractive.canonical_coupled_even_moment_le_surviving
#print axioms DGRHS.Attractive.abs_prod_le_mean_powers
#print axioms DGRHS.Attractive.symmetric_row_moments
#print axioms DGRHS.Attractive.arrayProduct_section_factorization
#print axioms DGRHS.Attractive.arraysEquiv_preserving
#print axioms DGRHS.Attractive.offDiagonalSum_pow_array_expansion
#print axioms DGRHS.Attractive.offDiagonalSum_pow_integral_surviving
end DGRHS.Attractive
