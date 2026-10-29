import DGPS.Examples.AttractiveXYTilt
import DGPS.Equilibrium.GaussianRate
import DGPS.Analysis.WeightedRateComparison
import DGPS.Structural.AmplitudePoincare
import DGPS.FiniteN.Tools.PositiveRate
import DGPS.Circle.BesselConcavity

/-!
# EX024: tilted centered Hessian and local Gaussian bound

At the tilted law `q_t` of the attractive XY model (`t = κ g(t) + h`) the centered interaction kernel
is `-κ[(cos-g)⊗(cos-g)+sin⊗sin]`; the density Hessian has eigenvalues `1-κ g'(t)`, `h/t` and `1`, so
`H ≥ (h/t) Id`; the inverse-Hessian (Gaussian) rate is at least `a₀ (h/t) e^{-2t}`
`≥ a₀ h/(h+κ) e^{-2(h+κ)}` with `a₀ = 4π²`.

New file (the nominal module `DGPS.Examples.AttractiveXYTilt` already holds EX023).
-/

open MeasureTheory UnitAddTorus DGPS.Circle.AngularNormalization
open scoped ENNReal NNReal BoundedContinuousFunction

namespace DGPS.Examples.AttractiveXYTiltEX024

open DGPS DGPS.Models DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYCritical
open DGPS.Examples.AttractiveXYTilt
open DGPS.Circle.BesselMoments DGPS.Circle.BesselConcavity DGPS.Circle.BesselMonotonicity

theorem xyFrozen_measure_EX024 (t : ℝ) :
    (xyFrozen t 0).measure = (xyLaw_EX023 t : Measure (Torus 1)) := by
  rfl

theorem haar_poincareRate_EX024 :
    ENNReal.ofReal (4 * Real.pi ^ 2) ≤
      poincareRate (⟨haar 1, inferInstance⟩ : ProbabilityMeasure (Torus 1)) := by
  refine (le_poincareRate_iff_forall _ _).2 ?_
  intro f hf
  have hw : IsWeakGradient f.fn f.grad :=
    ⟨f.isWeak.memLp, f.isWeak.memLp_grad, f.isWeak.ibp⟩
  have hP := DGPS.FiniteN.PositiveRate.torus_poincare hw
  have hvar : ProbabilityTheory.variance f.fn (haar 1) =
      weightedVariance (⟨haar 1, inferInstance⟩ : ProbabilityMeasure (Torus 1)) f.fn := by
    exact (ProbabilityTheory.variance_eq_integral
      f.isWeak.memLp.aestronglyMeasurable.aemeasurable).trans rfl
  have hgi : Integrable (fun x => ‖f.grad x‖ ^ 2) (haar 1) :=
    f.isWeak.memLp_grad.norm.integrable_sq
  have hE : dirichletEnergy (⟨haar 1, inferInstance⟩ : ProbabilityMeasure (Torus 1)) f =
      ENNReal.ofReal (∫ x, ‖f.grad x‖ ^ 2 ∂haar 1) := by
    unfold dirichletEnergy
    rw [ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall fun x => sq_nonneg _)]
    simp only [ProbabilityMeasure.coe_mk]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hE, ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by rw [← hvar]; exact hP)

theorem poincare_xyLaw_EX024 {t : ℝ} (ht : 0 ≤ t) :
    ENNReal.ofReal (Real.exp (-(2 * t))) * ENNReal.ofReal (4 * Real.pi ^ 2) ≤
      poincareRate (xyLaw_EX023 t) := by
  have hosc : ∀ᵐ x ∂haar 1, ∀ᵐ y ∂haar 1,
      Real.log ((xyFrozen t 0).density x / (DGPS.Structural.unitReference 1).density x) -
        Real.log ((xyFrozen t 0).density y / (DGPS.Structural.unitReference 1).density y)
          ≤ 2 * t :=
    Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall fun y => by
      have h1 := log_xyFrozen_density t 0 x
      have h2 := log_xyFrozen_density t 0 y
      have hx := (abs_le.1 (abs_xyMode_re_le x)).2
      have hy := (abs_le.1 (abs_xyMode_re_le y)).1
      show Real.log ((xyFrozen t 0).density x / 1) - Real.log ((xyFrozen t 0).density y / 1) ≤ _
      rw [div_one, div_one, h1, h2]
      simp only [xyTrig]
      nlinarith
  have key := (DGPS.Examples.ordinary_lsi_bounded_density_comparison (DGPS.Structural.unitReference 1)
    (xyFrozen t 0) (2 * t) hosc).2.1.1
  have hU : (⟨(DGPS.Structural.unitReference 1).measure,
      (DGPS.Structural.unitReference 1).isProbabilityMeasure⟩ : ProbabilityMeasure (Torus 1)) =
      ⟨haar 1, inferInstance⟩ := Subtype.ext (DGPS.Structural.unitReference_measure 1)
  rw [hU] at key
  have hQ : (⟨(xyFrozen t 0).measure, (xyFrozen t 0).isProbabilityMeasure⟩ :
      ProbabilityMeasure (Torus 1)) = xyLaw_EX023 t := Subtype.ext (xyFrozen_measure_EX024 t)
  rw [hQ] at key
  exact (mul_le_mul' le_rfl haar_poincareRate_EX024).trans key


theorem integrable_cont_EX024 (μ : ProbabilityMeasure (Torus 1)) {φ : Torus 1 → ℝ}
    (hφ : Continuous φ) : Integrable φ (μ : Measure (Torus 1)) :=
  hφ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem law_cos_sq_EX024 {t : ℝ} (ht : t ≠ 0) :
    ∫ x, ((xyMode x).re) ^ 2 ∂(xyLaw_EX023 t : Measure (Torus 1)) =
      1 - besselRatio t / t := by
  rw [law_integral_EX023]
  simp_rw [xyMode_re_eq_angCos_xyc]
  rw [integral_comp_angEquiv (fun θ => Real.exp (t * angCos θ) / besselI 0 t * angCos θ ^ 2)]
  have e := besselI2Moment_eq t
  unfold besselI2Moment at e
  have hE := (besselI_zero_pos t).ne'
  have : ∀ θ : AngCircle, Real.exp (t * angCos θ) / besselI 0 t * angCos θ ^ 2 =
      (besselI 0 t)⁻¹ * (angCos θ * Real.exp (t * angCos θ) * angCos θ) := by
    intro θ; field_simp
  simp_rw [this]
  rw [integral_const_mul, e, ratio_div_eq t ht]
  field_simp

theorem law_odd_EX024 (t : ℝ) (G : ℝ → ℝ) :
    ∫ x, G (xyMode x).re * (xyMode x).im ∂(xyLaw_EX023 t : Measure (Torus 1)) = 0 := by
  have : (haar 1).IsNegInvariant := Pi.isNegInvariant_volume
  rw [law_integral_EX023]
  have hi := integral_neg_eq_self (fun x : Torus 1 =>
    Real.exp (t * (xyMode x).re) / besselI 0 t * (G (xyMode x).re * (xyMode x).im)) (haar 1)
  simp only [mode_neg_EX023, Complex.conj_re, Complex.conj_im, mul_neg, integral_neg] at hi
  linarith

theorem im_sq_EX024 (x : Torus 1) : (xyMode x).im ^ 2 = 1 - (xyMode x).re ^ 2 := by
  have h := xyMode_norm x
  have h2 : (xyMode x).re * (xyMode x).re + (xyMode x).im * (xyMode x).im = 1 := by
    have := Complex.sq_norm (xyMode x)
    rw [h, Complex.normSq_apply] at this
    linarith
  nlinarith

section Moments

variable (t : ℝ)

theorem m_c_EX024 : ∫ x, (xyMode x).re ∂(xyLaw_EX023 t : Measure (Torus 1)) = besselRatio t :=
  law_cos_EX023 t

theorem m_s_EX024 : ∫ x, (xyMode x).im ∂(xyLaw_EX023 t : Measure (Torus 1)) = 0 :=
  law_sin_EX023 t

theorem m_cs_EX024 : ∫ x, (xyMode x).re * (xyMode x).im ∂(xyLaw_EX023 t : Measure (Torus 1)) = 0 :=
  law_odd_EX024 t (fun r => r)

theorem m_ss_EX024 (ht : t ≠ 0) :
    ∫ x, (xyMode x).im ^ 2 ∂(xyLaw_EX023 t : Measure (Torus 1)) = besselRatio t / t := by
  simp_rw [im_sq_EX024]
  have hi : Integrable (fun x => (xyMode x).re ^ 2) (xyLaw_EX023 t : Measure (Torus 1)) :=
    integrable_cont_EX024 _ ((Complex.continuous_re.comp continuous_xyMode).pow 2)
  rw [integral_sub (integrable_const _) hi, law_cos_sq_EX024 ht]
  simp

end Moments


theorem interactionConvolution_EX024 (κ h t : ℝ) (x : Torus 1) :
    interactionConvolution (attractiveXY κ h) (xyLaw_EX023 t) x =
      κ * (1 - besselRatio t * (xyMode x).re) := by
  unfold interactionConvolution
  have hW : ∀ z : Torus 1, (attractiveXY κ h).W x z =
      κ - (κ * (xyMode x).re) * (xyMode z).re - (κ * (xyMode x).im) * (xyMode z).im := by
    intro z; rw [attractiveXY_W, xyMode_re_sub]; ring
  simp_rw [hW]
  have hc : Integrable (fun z : Torus 1 => (xyMode z).re) (xyLaw_EX023 t : Measure (Torus 1)) :=
    integrable_cont_EX024 _ (Complex.continuous_re.comp continuous_xyMode)
  have hs : Integrable (fun z : Torus 1 => (xyMode z).im) (xyLaw_EX023 t : Measure (Torus 1)) :=
    integrable_cont_EX024 _ (Complex.continuous_im.comp continuous_xyMode)
  have i1 : Integrable (fun z : Torus 1 => κ - κ * (xyMode x).re * (xyMode z).re)
      (xyLaw_EX023 t : Measure (Torus 1)) := (integrable_const _).sub (hc.const_mul _)
  have i2 : Integrable (fun z : Torus 1 => κ * (xyMode x).im * (xyMode z).im)
      (xyLaw_EX023 t : Measure (Torus 1)) := hs.const_mul _
  have i3 : Integrable (fun z : Torus 1 => κ * (xyMode x).re * (xyMode z).re)
      (xyLaw_EX023 t : Measure (Torus 1)) := hc.const_mul _
  rw [integral_sub i1 i2, integral_sub (integrable_const _) i3, integral_const_mul,
    integral_const_mul, m_c_EX024, m_s_EX024]
  simp only [integral_const, smul_eq_mul, probReal_univ, one_mul, mul_zero, sub_zero]
  ring

theorem meanInteraction_EX024 (κ h t : ℝ) :
    meanInteraction (attractiveXY κ h) (xyLaw_EX023 t) = κ * (1 - besselRatio t ^ 2) := by
  rw [← integral_interactionConvolution]
  simp_rw [interactionConvolution_EX024]
  have hc : Integrable (fun z : Torus 1 => (xyMode z).re) (xyLaw_EX023 t : Measure (Torus 1)) :=
    integrable_cont_EX024 _ (Complex.continuous_re.comp continuous_xyMode)
  have i3 : Integrable (fun z : Torus 1 => besselRatio t * (xyMode z).re)
      (xyLaw_EX023 t : Measure (Torus 1)) := hc.const_mul _
  rw [integral_const_mul, integral_sub (integrable_const _) i3, integral_const_mul,
    m_c_EX024]
  simp only [integral_const, smul_eq_mul, probReal_univ, one_mul]
  ring

theorem centeredKernel_EX024 (κ h t : ℝ) (x y : Torus 1) :
    centeredKernel (attractiveXY κ h) (xyLaw_EX023 t) x y =
      -κ * (((xyMode x).re - besselRatio t) * ((xyMode y).re - besselRatio t) +
        (xyMode x).im * (xyMode y).im) := by
  unfold centeredKernel
  rw [interactionConvolution_EX024, interactionConvolution_EX024, meanInteraction_EX024,
    attractiveXY_W, xyMode_re_sub]
  ring

theorem bessel_EX024 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u v f : E)
    {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (huu : inner ℝ u u = σ) (hvv : inner ℝ v v = τ)
    (huv : inner ℝ u v = 0) :
    inner ℝ f u ^ 2 / σ + inner ℝ f v ^ 2 / τ ≤ ‖f‖ ^ 2 := by
  have hvu : inner ℝ v u = 0 := by rw [real_inner_comm]; exact huv
  have hfu : inner ℝ u f = inner ℝ f u := real_inner_comm _ _
  have hfv : inner ℝ v f = inner ℝ f v := real_inner_comm _ _
  have h := real_inner_self_nonneg (x := f - (inner ℝ f u / σ) • u - (inner ℝ f v / τ) • v)
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, huu, hvv, huv,
    hvu, hfu, hfv, real_inner_self_eq_norm_sq, RCLike.conj_to_real] at h
  have e1 : inner ℝ f u / σ * inner ℝ f u = inner ℝ f u ^ 2 / σ := by ring
  have e2 : inner ℝ f v / τ * inner ℝ f v = inner ℝ f v ^ 2 / τ := by ring
  have e3 : inner ℝ f u / σ * (inner ℝ f u / σ) * σ = inner ℝ f u ^ 2 / σ := by
    field_simp
  have e4 : inner ℝ f v / τ * (inner ℝ f v / τ) * τ = inner ℝ f v ^ 2 / τ := by
    field_simp
  nlinarith [e1, e2, e3, e4]

noncomputable def uBCF_EX024 (t : ℝ) : Torus 1 →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x => (xyMode x).re - besselRatio t,
    (Complex.continuous_re.comp continuous_xyMode).sub continuous_const⟩

noncomputable def vBCF_EX024 : Torus 1 →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun x => (xyMode x).im,
    Complex.continuous_im.comp continuous_xyMode⟩

theorem uBCF_apply_EX024 (t : ℝ) (x : Torus 1) : uBCF_EX024 t x = (xyMode x).re - besselRatio t :=
  rfl

theorem vBCF_apply_EX024 (x : Torus 1) : vBCF_EX024 x = (xyMode x).im := rfl

noncomputable def uLp_EX024 (t : ℝ) : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1)) :=
  BoundedContinuousFunction.toLp 2 (xyLaw_EX023 t : Measure (Torus 1)) ℝ (uBCF_EX024 t)

noncomputable def vLp_EX024 (t : ℝ) : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1)) :=
  BoundedContinuousFunction.toLp 2 (xyLaw_EX023 t : Measure (Torus 1)) ℝ vBCF_EX024

theorem uLp_ae_EX024 (t : ℝ) :
    (uLp_EX024 t : Torus 1 → ℝ) =ᵐ[(xyLaw_EX023 t : Measure (Torus 1))]
      fun x => (xyMode x).re - besselRatio t :=
  BoundedContinuousFunction.coeFn_toLp 2 (xyLaw_EX023 t : Measure (Torus 1)) ℝ (uBCF_EX024 t)

theorem vLp_ae_EX024 (t : ℝ) :
    (vLp_EX024 t : Torus 1 → ℝ) =ᵐ[(xyLaw_EX023 t : Measure (Torus 1))]
      fun x => (xyMode x).im :=
  BoundedContinuousFunction.coeFn_toLp 2 (xyLaw_EX023 t : Measure (Torus 1)) ℝ vBCF_EX024

theorem inner_toLp_EX024 (μ : ProbabilityMeasure (Torus 1)) (φ : Torus 1 →ᵇ ℝ)
    (f : Lp ℝ 2 (μ : Measure (Torus 1))) :
    inner ℝ (BoundedContinuousFunction.toLp 2 (μ : Measure (Torus 1)) ℝ φ) f =
      ∫ x, φ x * f x ∂(μ : Measure (Torus 1)) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 (μ : Measure (Torus 1)) ℝ φ] with y hy
  rw [hy]; simp [mul_comm]

theorem inner_u_EX024 (t : ℝ) (f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) :
    inner ℝ (uLp_EX024 t) f =
      ∫ x, ((xyMode x).re - besselRatio t) * f x ∂(xyLaw_EX023 t : Measure (Torus 1)) :=
  inner_toLp_EX024 _ _ f

theorem inner_v_EX024 (t : ℝ) (f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) :
    inner ℝ (vLp_EX024 t) f =
      ∫ x, (xyMode x).im * f x ∂(xyLaw_EX023 t : Measure (Torus 1)) :=
  inner_toLp_EX024 _ _ f

theorem integrable_cont_mul_lp_EX024 (μ : ProbabilityMeasure (Torus 1)) {φ : Torus 1 → ℝ}
    (hφ : Continuous φ) (f : Lp ℝ 2 (μ : Measure (Torus 1))) :
    Integrable (fun y => φ y * f y) (μ : Measure (Torus 1)) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hφ.continuousOn
  exact (integrable_lp μ f).bdd_mul (c := C) hφ.aestronglyMeasurable
    (ae_of_all _ fun y => by simpa using hC y (Set.mem_univ _))

theorem kernelOp_EX024 (κ h t : ℝ) (F : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) :
    kernelOp (attractiveXY κ h) (xyLaw_EX023 t) F =
      (-κ * inner ℝ (uLp_EX024 t) F) • uLp_EX024 t +
        (-κ * inner ℝ (vLp_EX024 t) F) • vLp_EX024 t := by
  refine Lp.ext ?_
  have hcu : Continuous fun x : Torus 1 => (xyMode x).re - besselRatio t :=
    (Complex.continuous_re.comp continuous_xyMode).sub continuous_const
  have hcv : Continuous fun x : Torus 1 => (xyMode x).im := Complex.continuous_im.comp continuous_xyMode
  filter_upwards [kernelOp_ae (attractiveXY κ h) (xyLaw_EX023 t) F,
    Lp.coeFn_add ((-κ * inner ℝ (uLp_EX024 t) F) • uLp_EX024 t)
      ((-κ * inner ℝ (vLp_EX024 t) F) • vLp_EX024 t),
    Lp.coeFn_smul (-κ * inner ℝ (uLp_EX024 t) F) (uLp_EX024 t),
    Lp.coeFn_smul (-κ * inner ℝ (vLp_EX024 t) F) (vLp_EX024 t),
    uLp_ae_EX024 t, vLp_ae_EX024 t] with x h1 h2 h3 h4 hu hv
  rw [h1, h2, Pi.add_apply, h3, h4, Pi.smul_apply, Pi.smul_apply, hu, hv, smul_eq_mul, smul_eq_mul]
  unfold kernelTransform
  simp_rw [centeredKernel_EX024]
  have e : ∀ y : Torus 1, -κ * (((xyMode x).re - besselRatio t) * ((xyMode y).re - besselRatio t) +
      (xyMode x).im * (xyMode y).im) * F y =
      (-κ * ((xyMode x).re - besselRatio t)) * (((xyMode y).re - besselRatio t) * F y) +
        (-κ * (xyMode x).im) * ((xyMode y).im * F y) := fun y => by ring
  simp_rw [e]
  rw [integral_add ((integrable_cont_mul_lp_EX024 _ hcu F).const_mul _)
    ((integrable_cont_mul_lp_EX024 _ hcv F).const_mul _), integral_const_mul, integral_const_mul,
    inner_u_EX024, inner_v_EX024]
  ring

theorem ratioDeriv_eq_EX024 {t : ℝ} (ht : t ≠ 0) :
    ratioDeriv t = 1 - besselRatio t / t - besselRatio t ^ 2 := by
  rw [ratio_div_eq t ht]; rfl

theorem inner_toLp_toLp_EX024 (μ : ProbabilityMeasure (Torus 1)) (φ ψ : Torus 1 →ᵇ ℝ) :
    inner ℝ (BoundedContinuousFunction.toLp 2 (μ : Measure (Torus 1)) ℝ φ)
      (BoundedContinuousFunction.toLp 2 (μ : Measure (Torus 1)) ℝ ψ) =
      ∫ x, φ x * ψ x ∂(μ : Measure (Torus 1)) := by
  rw [inner_toLp_EX024]
  refine integral_congr_ae ?_
  filter_upwards [BoundedContinuousFunction.coeFn_toLp 2 (μ : Measure (Torus 1)) ℝ ψ] with y hy
  rw [hy]

theorem hc_EX024 : Continuous fun x : Torus 1 => (xyMode x).re :=
  Complex.continuous_re.comp continuous_xyMode

theorem hs_EX024 : Continuous fun x : Torus 1 => (xyMode x).im :=
  Complex.continuous_im.comp continuous_xyMode

theorem inner_uu_EX024 {t : ℝ} (ht : t ≠ 0) :
    inner ℝ (uLp_EX024 t) (uLp_EX024 t) = ratioDeriv t := by
  unfold uLp_EX024
  rw [inner_toLp_toLp_EX024]
  simp only [uBCF_apply_EX024]
  have e : ∀ x : Torus 1, ((xyMode x).re - besselRatio t) * ((xyMode x).re - besselRatio t) =
      (xyMode x).re ^ 2 - (2 * besselRatio t) * (xyMode x).re + besselRatio t ^ 2 :=
    fun x => by ring
  simp_rw [e]
  have i1 : Integrable (fun x : Torus 1 => (xyMode x).re ^ 2) (xyLaw_EX023 t : Measure (Torus 1)) :=
    integrable_cont_EX024 _ (hc_EX024.pow 2)
  have i2 : Integrable (fun x : Torus 1 => (2 * besselRatio t) * (xyMode x).re)
      (xyLaw_EX023 t : Measure (Torus 1)) :=
    (integrable_cont_EX024 _ hc_EX024).const_mul _
  have i12 : Integrable (fun x : Torus 1 => (xyMode x).re ^ 2 - (2 * besselRatio t) * (xyMode x).re)
      (xyLaw_EX023 t : Measure (Torus 1)) := i1.sub i2
  rw [integral_add i12 (integrable_const _), integral_sub i1 i2, integral_const_mul,
    law_cos_sq_EX024 ht, m_c_EX024, ratioDeriv_eq_EX024 ht]
  simp only [integral_const, smul_eq_mul, probReal_univ, one_mul]
  ring

theorem inner_vv_EX024 {t : ℝ} (ht : t ≠ 0) :
    inner ℝ (vLp_EX024 t) (vLp_EX024 t) = besselRatio t / t := by
  unfold vLp_EX024
  rw [inner_toLp_toLp_EX024]
  simp only [vBCF_apply_EX024]
  have e : ∀ x : Torus 1, (xyMode x).im * (xyMode x).im = (xyMode x).im ^ 2 := fun x => by ring
  simp_rw [e]
  exact m_ss_EX024 t ht

theorem inner_uv_EX024 (t : ℝ) : inner ℝ (uLp_EX024 t) (vLp_EX024 t) = 0 := by
  unfold uLp_EX024 vLp_EX024
  rw [inner_toLp_toLp_EX024]
  simp only [uBCF_apply_EX024, vBCF_apply_EX024]
  have e : ∀ x : Torus 1, ((xyMode x).re - besselRatio t) * (xyMode x).im =
      (xyMode x).re * (xyMode x).im - besselRatio t * (xyMode x).im := fun x => by ring
  simp_rw [e]
  have i1 : Integrable (fun x : Torus 1 => (xyMode x).re * (xyMode x).im)
      (xyLaw_EX023 t : Measure (Torus 1)) :=
    integrable_cont_EX024 _ (hc_EX024.mul hs_EX024)
  have i2 : Integrable (fun x : Torus 1 => besselRatio t * (xyMode x).im)
      (xyLaw_EX023 t : Measure (Torus 1)) :=
    (integrable_cont_EX024 _ hs_EX024).const_mul _
  rw [integral_sub i1 i2, integral_const_mul, m_cs_EX024, m_s_EX024]
  simp

theorem uLp_centered_EX024 (t : ℝ) : ∫ x, (uLp_EX024 t) x ∂(xyLaw_EX023 t : Measure (Torus 1)) = 0 := by
  rw [integral_congr_ae (uLp_ae_EX024 t)]
  rw [integral_sub (integrable_cont_EX024 _ hc_EX024) (integrable_const _), m_c_EX024]
  simp

theorem vLp_centered_EX024 (t : ℝ) : ∫ x, (vLp_EX024 t) x ∂(xyLaw_EX023 t : Measure (Torus 1)) = 0 := by
  rw [integral_congr_ae (vLp_ae_EX024 t)]
  exact m_s_EX024 t

theorem coe_hessian_EX024 (κ h t : ℝ) (f : centeredL2 (xyLaw_EX023 t)) :
    ((densityHessian (attractiveXY κ h) (xyLaw_EX023 t) f : centeredL2 (xyLaw_EX023 t)) :
      Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) =
      (f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) +
        kernelOp (attractiveXY κ h) (xyLaw_EX023 t) f := rfl

theorem quad_form_EX024 (κ h t : ℝ) (f : centeredL2 (xyLaw_EX023 t)) :
    inner ℝ f (densityHessian (attractiveXY κ h) (xyLaw_EX023 t) f) =
      ‖f‖ ^ 2 - κ * (inner ℝ (f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) (uLp_EX024 t) ^ 2 +
        inner ℝ (f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) (vLp_EX024 t) ^ 2) := by
  have hi : inner ℝ f (densityHessian (attractiveXY κ h) (xyLaw_EX023 t) f) =
      inner ℝ (f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1)))
        ((densityHessian (attractiveXY κ h) (xyLaw_EX023 t) f : centeredL2 (xyLaw_EX023 t)) :
          Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) := rfl
  have hn : ‖(f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1)))‖ = ‖f‖ := rfl
  rw [hi, coe_hessian_EX024, kernelOp_EX024, inner_add_right, inner_add_right,
    inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq, hn,
    real_inner_comm (uLp_EX024 t), real_inner_comm (vLp_EX024 t)]
  ring

theorem hessian_lower_EX024 {κ h t : ℝ} (hκ : 0 ≤ κ) (ht : 0 < t)
    (heq : t = κ * besselRatio t + h) (f : centeredL2 (xyLaw_EX023 t)) :
    h / t * ‖f‖ ^ 2 ≤ inner ℝ f (densityHessian (attractiveXY κ h) (xyLaw_EX023 t) f) := by
  rw [quad_form_EX024]
  have hσ := ratioDeriv_pos t ht
  have hlt := ratioDeriv_lt_div t ht
  have hτ : 0 < besselRatio t / t := hσ.trans hlt
  have hb := bessel_EX024 (uLp_EX024 t) (vLp_EX024 t) (f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1)))
    hσ hτ (inner_uu_EX024 ht.ne') (inner_vv_EX024 ht.ne') (inner_uv_EX024 t)
  have hn : ‖(f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1)))‖ = ‖f‖ := rfl
  rw [hn] at hb
  set a := inner ℝ (f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) (uLp_EX024 t)
  set b := inner ℝ (f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) (vLp_EX024 t)
  have h1 : a ^ 2 / (besselRatio t / t) ≤ a ^ 2 / ratioDeriv t :=
    div_le_div_of_nonneg_left (sq_nonneg a) hσ hlt.le
  have h2 : (a ^ 2 + b ^ 2) / (besselRatio t / t) ≤ ‖f‖ ^ 2 := by
    rw [add_div]; linarith
  rw [div_le_iff₀ hτ] at h2
  have h3 : κ * (besselRatio t / t) = 1 - h / t := by
    field_simp; linarith
  nlinarith [mul_le_mul_of_nonneg_left h2 hκ, sq_nonneg ‖f‖]

noncomputable def uC_EX024 (t : ℝ) : centeredL2 (xyLaw_EX023 t) :=
  ⟨uLp_EX024 t, uLp_centered_EX024 t⟩

noncomputable def vC_EX024 (t : ℝ) : centeredL2 (xyLaw_EX023 t) :=
  ⟨vLp_EX024 t, vLp_centered_EX024 t⟩

theorem hessian_u_EX024 (κ h t : ℝ) (ht : t ≠ 0) :
    densityHessian (attractiveXY κ h) (xyLaw_EX023 t) (uC_EX024 t) =
      (1 - κ * ratioDeriv t) • uC_EX024 t := by
  apply Subtype.ext
  rw [coe_hessian_EX024]
  show (uLp_EX024 t) + _ = (1 - κ * ratioDeriv t) • uLp_EX024 t
  rw [show ((uC_EX024 t : centeredL2 (xyLaw_EX023 t)) : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) =
    uLp_EX024 t from rfl, kernelOp_EX024, inner_uu_EX024 ht, real_inner_comm, inner_uv_EX024]
  module

theorem hessian_v_EX024 (κ h t : ℝ) (ht : t ≠ 0) :
    densityHessian (attractiveXY κ h) (xyLaw_EX023 t) (vC_EX024 t) =
      (1 - κ * (besselRatio t / t)) • vC_EX024 t := by
  apply Subtype.ext
  rw [coe_hessian_EX024]
  show (vLp_EX024 t) + _ = (1 - κ * (besselRatio t / t)) • vLp_EX024 t
  rw [show ((vC_EX024 t : centeredL2 (xyLaw_EX023 t)) : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) =
    vLp_EX024 t from rfl, kernelOp_EX024, inner_vv_EX024 ht, inner_uv_EX024]
  module

theorem hessian_orth_EX024 (κ h t : ℝ) (f : centeredL2 (xyLaw_EX023 t))
    (h1 : inner ℝ f (uC_EX024 t) = 0) (h2 : inner ℝ f (vC_EX024 t) = 0) :
    densityHessian (attractiveXY κ h) (xyLaw_EX023 t) f = f := by
  apply Subtype.ext
  rw [coe_hessian_EX024, kernelOp_EX024]
  have e1 : inner ℝ (uLp_EX024 t) (f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) = 0 := by
    rw [real_inner_comm]; exact h1
  have e2 : inner ℝ (vLp_EX024 t) (f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) = 0 := by
    rw [real_inner_comm]; exact h2
  rw [e1, e2]
  simp

theorem inverse_bound_EX024 {κ h t : ℝ} (hκ : 0 ≤ κ) (hh : 0 < h) (ht : 0 < t)
    (heq : t = κ * besselRatio t + h)
    (hH : IsCoerciveDensityHessian (attractiveXY κ h) (xyLaw_EX023 t))
    (f : centeredL2 (xyLaw_EX023 t)) :
    inner ℝ f (densityCovariance (attractiveXY κ h) (xyLaw_EX023 t) hH f) ≤ t / h * ‖f‖ ^ 2 := by
  set w := densityCovariance (attractiveXY κ h) (xyLaw_EX023 t) hH f with hw
  have hwf : densityHessian (attractiveXY κ h) (xyLaw_EX023 t) w = f :=
    densityHessian_densityCovariance _ _ hH f
  have low := hessian_lower_EX024 hκ ht heq w
  rw [hwf] at low
  have cs : inner ℝ w f ≤ ‖w‖ * ‖f‖ := real_inner_le_norm w f
  rw [real_inner_comm] at low cs
  have hk : 0 < h / t := div_pos hh ht
  have hkn : h / t * ‖w‖ ≤ ‖f‖ := by
    rcases (norm_nonneg w).eq_or_lt with h0 | hn
    · rw [← h0]; simp
    · by_contra hcon
      have hcon := not_le.1 hcon
      nlinarith [mul_lt_mul_of_pos_left hcon hn]
  have hn : ‖w‖ ≤ t / h * ‖f‖ := by
    have : ‖w‖ = t / h * (h / t * ‖w‖) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left hkn (div_pos ht hh).le
  calc inner ℝ f w ≤ ‖w‖ * ‖f‖ := cs
    _ ≤ t / h * ‖f‖ * ‖f‖ := mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ = t / h * ‖f‖ ^ 2 := by ring

theorem weightedVariance_eq_EX024 {μ : ProbabilityMeasure (Torus 1)} (f : WeakH1Test μ)
    (hf : ∫ x, f.fn x ∂(μ : Measure (Torus 1)) = 0) :
    weightedVariance μ f.fn = ‖f.toCentered μ hf‖ ^ 2 := by
  unfold weightedVariance
  rw [hf, ← real_inner_self_eq_norm_sq]
  have hi : inner ℝ (f.toCentered μ hf) (f.toCentered μ hf) =
      inner ℝ (f.isWeak.memLp.toLp f.fn) (f.isWeak.memLp.toLp f.fn) := rfl
  rw [hi, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [f.isWeak.memLp.coeFn_toLp] with y hy
  rw [hy]
  simp [sq]

theorem gaussian_lower_EX024 {κ h t : ℝ} (hκ : 0 ≤ κ) (hh : 0 < h) (ht : 0 < t)
    (heq : t = κ * besselRatio t + h)
    (hH : IsCoerciveDensityHessian (attractiveXY κ h) (xyLaw_EX023 t)) :
    ENNReal.ofReal (4 * Real.pi ^ 2 * (h / t) * Real.exp (-(2 * t))) ≤
      gaussianRate (attractiveXY κ h) (xyLaw_EX023 t) hH := by
  rw [le_gaussianRate_iff_forall]
  intro f hf
  have hV := weightedVariance_eq_EX024 f hf.1
  have hne := toCentered_ne_zero (xyLaw_EX023 t) hf
  have hVpos : 0 < weightedVariance (xyLaw_EX023 t) f.fn := by
    rw [hV]; exact pow_pos (norm_pos_iff.2 hne) 2
  have hP := (le_poincareRate_iff_forall _ _).1 (poincare_xyLaw_EX024 ht.le) f hVpos
  have hD : gaussianDenominator (attractiveXY κ h) (xyLaw_EX023 t) hH f hf.1 ≤
      t / h * weightedVariance (xyLaw_EX023 t) f.fn := by
    rw [hV]
    exact inverse_bound_EX024 hκ hh ht heq hH _
  have hA : 0 ≤ 4 * Real.pi ^ 2 * (h / t) * Real.exp (-(2 * t)) := by positivity
  have hc : 0 ≤ Real.exp (-(2 * t)) * (4 * Real.pi ^ 2) := by positivity
  rw [← ENNReal.ofReal_mul hA]
  refine le_trans ?_ hP
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul hc]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := mul_le_mul_of_nonneg_left hD hA
  have h2 : 4 * Real.pi ^ 2 * (h / t) * Real.exp (-(2 * t)) *
      (t / h * weightedVariance (xyLaw_EX023 t) f.fn) =
      Real.exp (-(2 * t)) * (4 * Real.pi ^ 2) * weightedVariance (xyLaw_EX023 t) f.fn := by
    field_simp
  linarith

theorem local_numeric_EX024 {κ h t : ℝ} (hκ : 0 ≤ κ) (hh : 0 < h) (ht : 0 < t)
    (heq : t = κ * besselRatio t + h) :
    4 * Real.pi ^ 2 * (h / (h + κ)) * Real.exp (-(2 * (h + κ))) ≤
      4 * Real.pi ^ 2 * (h / t) * Real.exp (-(2 * t)) := by
  have hg := besselRatio_lt_one t
  have htle : t ≤ h + κ := by nlinarith
  have h1 : h / (h + κ) ≤ h / t := div_le_div_of_nonneg_left hh.le ht htle
  have h2 : Real.exp (-(2 * (h + κ))) ≤ Real.exp (-(2 * t)) :=
    Real.exp_le_exp.2 (by linarith)
  have h0 : 0 ≤ h / (h + κ) := by positivity
  have hpi : 0 ≤ 4 * Real.pi ^ 2 := by positivity
  exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hpi) h2 (Real.exp_pos _).le (by positivity)

end DGPS.Examples.AttractiveXYTiltEX024

namespace DGPS.Examples

open MeasureTheory UnitAddTorus
open DGPS DGPS.Models DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYTilt
open DGPS.Examples.AttractiveXYTiltEX024
open DGPS.Circle.BesselMoments DGPS.Circle.BesselConcavity

/-- EX024: at the tilted law `q_t` of the attractive XY model (`t = κ g(t) + h`, `κ ≥ 0`, `h > 0`),
the centered interaction kernel is `-κ[(cos-g)⊗(cos-g)+sin⊗sin]`, the density Hessian has the
eigenvalues `1-κ g'(t)` (on `cos-g`), `h/t` (on `sin`) and `1` on the orthogonal complement, so
`H ≥ (h/t) Id` (hence coercive), `H⁻¹ ≤ (t/h) Id`, and the Gaussian Hessian rate (the inverse-Hessian
local Rayleigh value) is at least `a₀ (h/t) e^{-2t} ≥ a₀ h/(h+κ) e^{-2(h+κ)}` with `a₀ = 4π²`. -/
theorem tilted_centered_hessian_and_local_gaussian_bound {κ h t : ℝ}
    (hκ : 0 ≤ κ) (hh : 0 < h) (ht : 0 < t) (heq : t = κ * besselRatio t + h) :
    (∀ x y : Torus 1, centeredKernel (attractiveXY κ h) (xyLaw_EX023 t) x y =
        -κ * (((xyMode x).re - besselRatio t) * ((xyMode y).re - besselRatio t) +
          (xyMode x).im * (xyMode y).im)) ∧
    (∃ e₁ e₂ : centeredL2 (xyLaw_EX023 t),
      ((e₁ : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) : Torus 1 → ℝ)
        =ᵐ[(xyLaw_EX023 t : Measure (Torus 1))] (fun x => (xyMode x).re - besselRatio t) ∧
      ((e₂ : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) : Torus 1 → ℝ)
        =ᵐ[(xyLaw_EX023 t : Measure (Torus 1))] (fun x => (xyMode x).im) ∧
      inner ℝ e₁ e₂ = 0 ∧
      ‖e₁‖ ^ 2 = deriv besselRatio t ∧ ‖e₂‖ ^ 2 = besselRatio t / t ∧
      deriv besselRatio t < besselRatio t / t ∧
      densityHessian (attractiveXY κ h) (xyLaw_EX023 t) e₁ = (1 - κ * deriv besselRatio t) • e₁ ∧
      densityHessian (attractiveXY κ h) (xyLaw_EX023 t) e₂ = (h / t) • e₂ ∧
      (∀ f : centeredL2 (xyLaw_EX023 t), inner ℝ f e₁ = 0 → inner ℝ f e₂ = 0 →
        densityHessian (attractiveXY κ h) (xyLaw_EX023 t) f = f)) ∧
    (∀ f : centeredL2 (xyLaw_EX023 t),
      h / t * ‖f‖ ^ 2 ≤ inner ℝ f (densityHessian (attractiveXY κ h) (xyLaw_EX023 t) f)) ∧
    IsCoerciveDensityHessian (attractiveXY κ h) (xyLaw_EX023 t) ∧
    ENNReal.ofReal (4 * Real.pi ^ 2 * Real.exp (-(2 * t))) ≤ poincareRate (xyLaw_EX023 t) ∧
    (∀ hH : IsCoerciveDensityHessian (attractiveXY κ h) (xyLaw_EX023 t),
      (∀ f : centeredL2 (xyLaw_EX023 t),
        inner ℝ f (densityCovariance (attractiveXY κ h) (xyLaw_EX023 t) hH f) ≤ t / h * ‖f‖ ^ 2) ∧
      ENNReal.ofReal (4 * Real.pi ^ 2 * (h / t) * Real.exp (-(2 * t))) ≤
        gaussianRate (attractiveXY κ h) (xyLaw_EX023 t) hH ∧
      ENNReal.ofReal (4 * Real.pi ^ 2 * (h / (h + κ)) * Real.exp (-(2 * (h + κ)))) ≤
        gaussianRate (attractiveXY κ h) (xyLaw_EX023 t) hH) ∧
    4 * Real.pi ^ 2 * (h / (h + κ)) * Real.exp (-(2 * (h + κ))) ≤
      4 * Real.pi ^ 2 * (h / t) * Real.exp (-(2 * t)) := by
  have ht0 : t ≠ 0 := ht.ne'
  have hlow := hessian_lower_EX024 hκ ht heq
  have hcoer : IsCoerciveDensityHessian (attractiveXY κ h) (xyLaw_EX023 t) :=
    ⟨h / t, div_pos hh ht, hlow⟩
  have hnum := local_numeric_EX024 hκ hh ht heq
  refine ⟨centeredKernel_EX024 κ h t, ⟨uC_EX024 t, vC_EX024 t, uLp_ae_EX024 t, vLp_ae_EX024 t,
    inner_uv_EX024 t, ?_, ?_, ?_, ?_, ?_, ?_⟩, hlow, hcoer, ?_, fun hH => ?_, hnum⟩
  · rw [deriv_ratio, ← real_inner_self_eq_norm_sq]
    exact inner_uu_EX024 ht0
  · rw [← real_inner_self_eq_norm_sq]
    exact inner_vv_EX024 ht0
  · rw [deriv_ratio]; exact ratioDeriv_lt_div t ht
  · rw [deriv_ratio]; exact hessian_u_EX024 κ h t ht0
  · rw [hessian_v_EX024 κ h t ht0]
    have : 1 - κ * (besselRatio t / t) = h / t := by field_simp; linarith
    rw [this]
  · intro f h1 h2
    exact hessian_orth_EX024 κ h t f h1 h2
  · have := poincare_xyLaw_EX024 ht.le
    rwa [← ENNReal.ofReal_mul (Real.exp_pos _).le, mul_comm] at this
  · have hg := gaussian_lower_EX024 hκ hh ht heq hH
    refine ⟨inverse_bound_EX024 hκ hh ht heq hH, hg, ?_⟩
    exact le_trans (ENNReal.ofReal_le_ofReal hnum) hg

/-- EX024, with the positive root `t_h` of `t = κ g(t) + h` supplied by EX023: the positive root exists
and is unique, the density Hessian at `q_{t_h}` is coercive, and the Gaussian Hessian rate is at least
`a₀ h/(h+κ) e^{-2(h+κ)}`. -/
theorem tilted_local_gaussian_bound_at_root {κ h : ℝ} (hκ : 0 ≤ κ) (hh : 0 < h) :
    ∃ t : ℝ, 0 < t ∧ t = κ * besselRatio t + h ∧
      (∀ u : ℝ, 0 < u → u = κ * besselRatio u + h → u = t) ∧
      ∃ hH : IsCoerciveDensityHessian (attractiveXY κ h) (xyLaw_EX023 t),
        ENNReal.ofReal (4 * Real.pi ^ 2 * (h / (h + κ)) * Real.exp (-(2 * (h + κ)))) ≤
          gaussianRate (attractiveXY κ h) (xyLaw_EX023 t) hH := by
  obtain ⟨t, ⟨ht, he⟩, hu⟩ := positive_root_unique_EX023 hκ hh
  obtain ⟨-, -, -, hcoer, -, hG, -⟩ := tilted_centered_hessian_and_local_gaussian_bound hκ hh ht he
  exact ⟨t, ht, he, fun u hu0 hue => hu u ⟨hu0, hue⟩, hcoer, (hG hcoer).2.2⟩

end DGPS.Examples
