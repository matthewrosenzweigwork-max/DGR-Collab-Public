/- Supporting adaptation from Apache-2.0 StatLean/Stat-Lean86b3823f77fc2b0f5a9923f85b588a4f8a65f94c,
StatLean/MultipleTesting/ForMathlib/GaussianMoments.lean, original SHA73294400a3e27bbbde978e55bb77f08f591a552c00691c8b4414a3bd2a247e7b.
MODIFIED: narrow sixth-moment recursion from the checked fourth-moment proof.
Attribution/license retained in imported closure; this new draft is not yet Lean checked. -/
import DGRHS.Gaussian.Imported.GaussianMoments
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace DGRHS.Gaussian
private lemma integrable_pow_stdGaussian (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k) (gaussianReal 0 1) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hk0
  · subst hk0; simp
  have h : Integrable (fun x : ℝ => ‖id x‖ ^ k) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal' (μ := 0) (v := 1) (k : ℝ≥0∞)
      (ENNReal.natCast_ne_top k)).integrable_norm_pow hk0.ne'
  refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp [id, Real.norm_eq_abs]

/-- Integrability over Lebesgue measure of `x ↦ xᵏ · exp(−x²/2)`, obtained from
`integrable_pow_stdGaussian` by unfolding the standard-Gaussian density. -/
private lemma integrable_pow_mul_exp_half (k : ℕ) :
    Integrable (fun x : ℝ => x ^ k * Real.exp (-x ^ 2 / 2)) := by
  have hN := integrable_pow_stdGaussian k
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
      integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
        (ae_of_all _ (fun _ => gaussianPDF_lt_top))] at hN
  simp only [toReal_gaussianPDF, smul_eq_mul] at hN
  have hconv : (fun x : ℝ => x ^ k * Real.exp (-x ^ 2 / 2))
      = fun x => Real.sqrt (2 * Real.pi) * (gaussianPDFReal 0 1 x * x ^ k) := by
    funext x
    have hpdf : gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
      rw [gaussianPDFReal]; simp only [NNReal.coe_one, mul_one, sub_zero]
    have hs : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
    rw [hpdf,
      show Real.sqrt (2 * Real.pi) * ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * x ^ k)
        = (Real.sqrt (2 * Real.pi) * (Real.sqrt (2 * Real.pi))⁻¹) * (Real.exp (-x ^ 2 / 2) * x ^ k)
        from by ring,
      mul_inv_cancel₀ hs, one_mul]
    exact mul_comm _ _
  rw [hconv]
  exact hN.const_mul _

private lemma integral_pow_six_mul_exp_half :
    ∫ x : ℝ, x ^ 6 * Real.exp (-x ^ 2 / 2)
      = 5 * ∫ x : ℝ, x ^ 4 * Real.exp (-x ^ 2 / 2) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun y => y ^ 5 * Real.exp (-y ^ 2 / 2))
      (5 * (x ^ 4 * Real.exp (-x ^ 2 / 2)) - x ^ 6 * Real.exp (-x ^ 2 / 2)) x := by
    intro x
    have h1 : HasDerivAt (fun y : ℝ => y ^ 5) (5 * x ^ 4) x := by
      simpa using hasDerivAt_pow 5 x
    have hu : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-x) x := by
      have h : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-(2 * x) / 2) x := by
        simpa using ((hasDerivAt_pow 2 x).neg).div_const 2
      rwa [show -(2 * x) / 2 = -x from by ring] at h
    have h2 : HasDerivAt (fun y : ℝ => Real.exp (-y ^ 2 / 2))
        (Real.exp (-x ^ 2 / 2) * (-x)) x := by
      simpa using hu.exp
    convert h1.mul h2 using 1
    ring
  have hf : Integrable (fun x : ℝ => x ^ 5 * Real.exp (-x ^ 2 / 2)) :=
    integrable_pow_mul_exp_half 5
  have hf2 : Integrable (fun x : ℝ => x ^ 4 * Real.exp (-x ^ 2 / 2)) :=
    integrable_pow_mul_exp_half 4
  have hf4 : Integrable (fun x : ℝ => x ^ 6 * Real.exp (-x ^ 2 / 2)) :=
    integrable_pow_mul_exp_half 6
  have hf' : Integrable (fun x : ℝ =>
      5 * (x ^ 4 * Real.exp (-x ^ 2 / 2)) - x ^ 6 * Real.exp (-x ^ 2 / 2)) :=
    (hf2.const_mul 5).sub hf4
  have hzero := integral_eq_zero_of_hasDerivAt_of_integrable hderiv hf' hf
  rw [integral_sub (hf2.const_mul 5) hf4, integral_const_mul] at hzero
  linarith

private lemma integral_pow_six_eq_five_mul_four :
    ∫ x, x ^ 6 ∂(gaussianReal 0 1) = 5 * ∫ x, x ^ 4 ∂(gaussianReal 0 1) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0),
      integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul]
  have hpt : ∀ (k : ℕ) (x : ℝ), gaussianPDFReal 0 1 x * x ^ k
      = (Real.sqrt (2 * Real.pi))⁻¹ * (x ^ k * Real.exp (-x ^ 2 / 2)) := by
    intro k x
    have hpdf : gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) := by
      rw [gaussianPDFReal]; simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [hpdf]; ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_const_mul, integral_pow_six_mul_exp_half]
  ring


theorem integral_pow_six_stdGaussian : ∫ x, x ^ 6 ∂(gaussianReal 0 1) = 15 := by
  rw [integral_pow_six_eq_five_mul_four, StatLean.MultipleTesting.integral_pow_four_stdGaussian]
  norm_num

lemma map_stdGaussian_mul (c : ℝ) :
    (gaussianReal 0 1).map (fun x ↦ c * x) = gaussianReal 0 (Real.toNNReal (c^2)) := by
  have h := gaussianReal_map_const_mul (μ := 0) (v := 1) c
  simp only [mul_zero, mul_one] at h
  rw [h]
  congr 1
  ext
  simp [Real.toNNReal_of_nonneg (sq_nonneg c)]


lemma integral_pow_six_gaussianReal_sq (c : ℝ) :
    (∫ x, x ^ 6 ∂(gaussianReal 0 (Real.toNNReal (c^2)))) = 15 * c ^ 6 := by
  rw [← map_stdGaussian_mul c, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_pow_six_stdGaussian]
  ring

lemma integral_pow_four_gaussianReal_sq (c : ℝ) :
    (∫ x, x ^ 4 ∂(gaussianReal 0 (Real.toNNReal (c^2)))) = 3 * c ^ 4 := by
  rw [← map_stdGaussian_mul c, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul, StatLean.MultipleTesting.integral_pow_four_stdGaussian]
  ring

lemma integral_cube_gaussianReal_sq (c : ℝ) :
    (∫ x, x ^ 3 ∂(gaussianReal 0 (Real.toNNReal (c^2)))) = 0 := by
  rw [← map_stdGaussian_mul c, integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul, StatLean.MultipleTesting.integral_cube_stdGaussian, mul_zero]

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.integral_pow_six_stdGaussian
#check DGRHS.Gaussian.integral_pow_six_stdGaussian

#print axioms DGRHS.Gaussian.integral_pow_six_gaussianReal_sq
#print axioms DGRHS.Gaussian.integral_pow_four_gaussianReal_sq
#print axioms DGRHS.Gaussian.integral_cube_gaussianReal_sq
