import LeanResearch.PeriodicAttractiveLogGas.HerbstEntropy
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Prod

/-! The Gaussian moment and Tonelli calculation in source lines 2921--2933.
The linear exponential bound is an explicit intermediate input; its source
crossing-probability specialization is supplied by the component argument. -/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.GaussianSquareMoment

/-- Exponential tilting of the standard Gaussian square gives twice the
variance-four Gaussian density, with the exact source exponent 3/8. -/
theorem square_density (x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp ((3 / 8 : ℝ) * x ^ 2) =
      2 * gaussianPDFReal 0 4 x := by
  have hs : Real.sqrt (2 * Real.pi * 4) = 2 * Real.sqrt (2 * Real.pi) := by
    rw [show 2 * Real.pi * 4 = 4 * (2 * Real.pi) by ring,
      Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [gaussianPDFReal, NNReal.coe_one, NNReal.coe_ofNat, sub_zero, mul_one]
  rw [mul_assoc, ← Real.exp_add, hs]
  have he : -(x ^ 2) / 2 + (3 / 8 : ℝ) * x ^ 2 = -(x ^ 2) / (2 * 4) := by ring
  rw [he, mul_inv_rev]
  ring

theorem integrable_standard_square :
    Integrable (fun x : ℝ => Real.exp ((3 / 8 : ℝ) * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (one_ne_zero : (1 : ℝ≥0) ≠ 0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (Eventually.of_forall fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF, smul_eq_mul, square_density]
  exact (integrable_gaussianPDFReal 0 4).const_mul 2

/-- The literal finite Gaussian integral in the manuscript is exactly two. -/
theorem integral_standard_square :
    (∫ x : ℝ, Real.exp ((3 / 8 : ℝ) * x ^ 2) ∂gaussianReal 0 1) = 2 := by
  rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)]
  simp only [smul_eq_mul, square_density, integral_const_mul,
    integral_gaussianPDFReal_eq_one 0 (by norm_num : (4 : ℝ≥0) ≠ 0), mul_one]

/-- The scalar Gaussian moment identity used before interchanging the
nonnegative integrals. -/
theorem gaussian_linearization {s : ℝ} (hs : 0 ≤ s) (z : ℝ) :
    (∫ x : ℝ, Real.exp (Real.sqrt (2 * s) * x * z) ∂gaussianReal 0 1) =
      Real.exp (s * z ^ 2) := by
  have h := congrFun (mgf_fun_id_gaussianReal (μ := 0) (v := 1))
    (Real.sqrt (2 * s) * z)
  simp only [mgf, zero_mul, NNReal.coe_one, one_mul, zero_add] at h
  calc
    _ = ∫ x : ℝ, Real.exp ((Real.sqrt (2 * s) * z) * x) ∂gaussianReal 0 1 := by
      congr 1
      funext x
      congr 1
      ring
    _ = _ := h
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 2 * s)]
      congr 1
      ring

/-- The exact Young inequality and source scale give a finite Gaussian
dominator, retaining the stated constants. -/
theorem source_gaussian_domination {N c₁ c₂ : ℝ} (hN : 0 < N) (hc₂ : 0 < c₂) (x : ℝ) :
    let s := N / (16 * c₂)
    Real.exp ((|Real.sqrt (2 * s) * x| * c₁ + c₂ * (Real.sqrt (2 * s) * x) ^ 2) / N) ≤
      Real.exp (2 * s * c₁ ^ 2 / N ^ 2) * Real.exp ((3 / 8 : ℝ) * x ^ 2) := by
  let s := N / (16 * c₂)
  have hs : 0 ≤ 2 * s := by dsimp [s]; positivity
  have he : 2 * s * c₂ / N = (1 / 8 : ℝ) := by
    dsimp [s]
    field_simp
    ring
  have ha : (Real.sqrt (2 * s) * c₁ / N) ^ 2 = 2 * s * c₁ ^ 2 / N ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hs]
  have hy : Real.sqrt (2 * s) * |x| * c₁ / N ≤ x ^ 2 / 4 + 2 * s * c₁ ^ 2 / N ^ 2 := by
    rw [← ha]
    calc
      _ = |x| * (Real.sqrt (2 * s) * c₁ / N) := by ring
      _ ≤ _ := by
        generalize Real.sqrt (2 * s) * c₁ / N = y
        nlinarith [sq_nonneg (|x| / 2 - y), sq_abs x]
  change Real.exp _ ≤ _
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  calc
    _ = Real.sqrt (2 * s) * |x| * c₁ / N + (2 * s * c₂ / N) * x ^ 2 := by
      rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hs]
      ring
    _ ≤ (x ^ 2 / 4 + 2 * s * c₁ ^ 2 / N ^ 2) + (1 / 8 : ℝ) * x ^ 2 := by
      rw [he]
      linarith only [hy]
    _ = _ := by ring

/-- The supplied Gaussian calculation from a linear exponential estimate.
Integrability of the square exponential and of the joint Gaussian integrand
is derived, rather than assumed. The finite-product criterion is Tonelli
applied to its nonnegative norm; Fubini then identifies the real integrals. -/
theorem square_exponential_of_linear {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {F : Ω → ℝ} {M N c₁ c₂ : ℝ}
    (hF : Measurable F) (hb : ∀ᵐ x ∂μ, |F x| ≤ M)
    (hN : 1 ≤ N) (hc₂ : 0 < c₂)
    (hlinear : ∀ r : ℝ, (∫ x, Real.exp (r * F x) ∂μ) ≤
      Real.exp ((|r| * c₁ + c₂ * r ^ 2) / N)) :
    Integrable (fun x => Real.exp (N * F x ^ 2 / (16 * c₂))) μ ∧
      (∫ x, Real.exp (N * F x ^ 2 / (16 * c₂)) ∂μ) ≤
        2 * Real.exp (c₁ ^ 2 / (8 * c₂)) := by
  let s := N / (16 * c₂)
  let a := Real.sqrt (2 * s)
  let B := Real.exp (2 * s * c₁ ^ 2 / N ^ 2)
  let H : ℝ × Ω → ℝ := fun z => Real.exp (a * z.1 * F z.2)
  have hN0 : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hs : 0 ≤ s := by dsimp [s]; positivity
  have hm : Measurable H := ((measurable_fst.const_mul a).mul (hF.comp measurable_snd)).exp
  have hhi (r : ℝ) : Integrable (fun x => H (r, x)) μ :=
    HerbstEntropy.integrable_exp_mul hF.aemeasurable hb (a * r)
  have hbound (r : ℝ) : (∫ x, H (r, x) ∂μ) ≤ B * Real.exp ((3 / 8 : ℝ) * r ^ 2) :=
    (hlinear (a * r)).trans (source_gaussian_domination hN0 hc₂ r)
  have hout : Integrable (fun r => ∫ x, H (r, x) ∂μ) (gaussianReal 0 1) :=
    (integrable_standard_square.const_mul B).mono'
      hm.stronglyMeasurable.integral_prod_right'.aestronglyMeasurable
      (Eventually.of_forall fun r => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => (Real.exp_pos _).le)]
        exact hbound r)
  have hjoint : Integrable H ((gaussianReal 0 1).prod μ) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall hhi, ?_⟩
    simpa only [H, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hout
  have hsq : Integrable (fun x => Real.exp (s * F x ^ 2)) μ :=
    HerbstEntropy.integrable_continuous_comp hF.aemeasurable hb
      (Real.continuous_exp.comp (continuous_const.mul (continuous_id.pow 2)))
  have heq : (fun x => Real.exp (N * F x ^ 2 / (16 * c₂))) =
      fun x => Real.exp (s * F x ^ 2) := by
    funext x
    congr 1
    dsimp [s]
    ring
  rw [heq]
  refine ⟨hsq, ?_⟩
  have hbexp : B ≤ Real.exp (c₁ ^ 2 / (8 * c₂)) := by
    apply Real.exp_le_exp.mpr
    have hid : 2 * s * c₁ ^ 2 / N ^ 2 = (c₁ ^ 2 / (8 * c₂)) / N := by
      dsimp [s]
      field_simp
      ring
    rw [hid]
    exact div_le_self (by positivity) hN
  calc
    (∫ x, Real.exp (s * F x ^ 2) ∂μ) = ∫ x, ∫ r, H (r, x) ∂gaussianReal 0 1 ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => (gaussian_linearization hs (F x)).symm
    _ = ∫ r, ∫ x, H (r, x) ∂μ ∂gaussianReal 0 1 :=
      (integral_integral_swap hjoint).symm
    _ ≤ ∫ r, B * Real.exp ((3 / 8 : ℝ) * r ^ 2) ∂gaussianReal 0 1 :=
      integral_mono_ae hout (integrable_standard_square.const_mul B) (Eventually.of_forall hbound)
    _ = B * 2 := by rw [integral_const_mul, integral_standard_square]
    _ ≤ _ := by nlinarith only [hbexp]

end PeriodicAttractiveLogGas.GaussianSquareMoment
