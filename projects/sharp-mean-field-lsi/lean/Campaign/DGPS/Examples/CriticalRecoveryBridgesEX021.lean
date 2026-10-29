import DGPS.Examples.CriticalRecoveryAsymptoticsEX021
import DGPS.Examples.CriticalHessianKernelEX021
import DGPS.Analysis.CircleMoments
import DGPS.FiniteN.Tools.GroundState

/-!
# Canonical density bridges for critical recovery (EX021)

This file identifies the actual positive von Mises law and its free-energy gap with DEF010's
absolute-density and scalar-gap interfaces.
-/

open MeasureTheory
open scoped ENNReal NNReal
open DGPS.Examples.AttractiveXY
open DGPS.Examples.CriticalRecoveryAsymptoticsEX021
open DGPS.Circle.BesselMoments

namespace DGPS.Examples.CriticalRecoveryBridgesEX021

/-- The positive square root of the normalized von Mises density. -/
noncomputable def vonMisesRootEX021 (t : ℝ) (x : DGPS.Torus 1) : ℝ :=
  (Real.sqrt (besselI 0 t))⁻¹ * Real.exp ((t / 2) * (xyMode x).re)

theorem vonMisesRoot_smoothEX021 (t : ℝ) :
    DGPS.IsSmoothPeriodic (vonMisesRootEX021 t) := by
  have hc : DGPS.IsSmoothPeriodic (fun x : DGPS.Torus 1 => (xyMode x).re) :=
    DGPS.Examples.AttractiveXY.isSmoothPeriodic_re_xyMode
  have harg : DGPS.IsSmoothPeriodic (fun x : DGPS.Torus 1 => (t / 2) * (xyMode x).re) := by
    unfold DGPS.IsSmoothPeriodic at *
    exact contDiff_const.mul hc
  have hexp : DGPS.IsSmoothPeriodic (fun x : DGPS.Torus 1 =>
      Real.exp ((t / 2) * (xyMode x).re)) := by
    unfold DGPS.IsSmoothPeriodic at *
    exact Real.contDiff_exp.comp harg
  unfold vonMisesRootEX021
  exact (show DGPS.IsSmoothPeriodic (fun x => (Real.sqrt (besselI 0 t))⁻¹ *
      Real.exp ((t / 2) * (xyMode x).re)) from by
    unfold DGPS.IsSmoothPeriodic at *
    exact contDiff_const.mul hexp)

theorem vonMisesRoot_sqEX021 (t : ℝ) (x : DGPS.Torus 1) :
    vonMisesRootEX021 t x ^ 2 = vonMisesTorusDensityEX021 t x := by
  rw [vonMisesRootEX021, vonMisesTorusDensity_exp_EX021,
    mul_pow, inv_pow, Real.sq_sqrt (besselI_zero_pos t).le, ← Real.exp_nat_mul]
  ring_nf

/-- The actual von Mises trial law as an admissible square-root density. -/
noncomputable def vonMisesAbsoluteDensityEX021 (t : ℝ) : DGPS.AbsoluteDensity 1 where
  sqrt := vonMisesRootEX021 t
  sqrt_mem := ⟨_, (vonMisesRoot_smoothEX021 t).isWeakGradient⟩
  sqrt_nonneg := Filter.Eventually.of_forall fun x => by
    unfold vonMisesRootEX021
    positivity
  mass_one := by
    rw [integral_congr_ae (Filter.Eventually.of_forall (vonMisesRoot_sqEX021 t))]
    exact vonMisesTorusDensity_mass_EX021 t

theorem vonMisesProbability_eq_densityMeasureEX021 (t : ℝ) :
    (vonMisesProbabilityEX021 t : Measure (DGPS.Torus 1)) =
      (DGPS.densityMeasure (vonMisesAbsoluteDensityEX021 t) : Measure (DGPS.Torus 1)) := by
  apply Measure.ext
  intro s hs
  rw [DGPS.densityMeasure_coe]
  have hden : (fun x : DGPS.Torus 1 =>
      ENNReal.ofReal ((vonMisesAbsoluteDensityEX021 t).sqrt x ^ 2)) =ᵐ[DGPS.haar 1]
      (fun x => ENNReal.ofReal (vonMisesTorusDensityEX021 t x)) := by
    filter_upwards with x
    show ENNReal.ofReal (vonMisesRootEX021 t x ^ 2) = _
    rw [vonMisesRoot_sqEX021]
  simp only [vonMisesProbabilityEX021, vonMisesMeasureEX021]
  rw [MeasureTheory.withDensity_congr_ae hden]
  rfl

theorem vonMisesProbability_eq_densityProbabilityEX021 (t : ℝ) :
    vonMisesProbabilityEX021 t = DGPS.densityMeasure (vonMisesAbsoluteDensityEX021 t) := by
  apply ProbabilityMeasure.toMeasure_injective
  exact vonMisesProbability_eq_densityMeasureEX021 t

theorem vonMisesEntropy_nonnegEX021 (t : ℝ) : 0 ≤ vonMisesEntropyEX021 t := by
  have hq : Continuous (vonMisesTorusDensityEX021 t) :=
    vonMisesTorusDensity_continuous_EX021 t
  have hqI : Integrable (vonMisesTorusDensityEX021 t) (DGPS.haar 1) :=
    hq.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc : Continuous (fun x : DGPS.Torus 1 => (xyMode x).re) :=
    Complex.continuous_re.comp continuous_xyMode
  have hlog : Integrable
      (fun x => vonMisesTorusDensityEX021 t x * Real.log (vonMisesTorusDensityEX021 t x))
      (DGPS.haar 1) := by
    have hp := vonMisesTorus_logDensity_EX021 t
    rw [show (fun x => vonMisesTorusDensityEX021 t x * Real.log
        (vonMisesTorusDensityEX021 t x)) =
        fun x => vonMisesTorusDensityEX021 t x *
          (t * (xyMode x).re - Real.log (besselI 0 t)) by
      funext x; rw [vonMisesTorus_logDensity_EX021]]
    have hcont : Continuous (fun x => vonMisesTorusDensityEX021 t x *
        (t * (xyMode x).re - Real.log (besselI 0 t))) :=
      hq.mul ((continuous_const.mul hc).sub continuous_const)
    exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hK : Integrable
      (fun x => vonMisesTorusDensityEX021 t x *
          Real.log (vonMisesTorusDensityEX021 t x) - vonMisesTorusDensityEX021 t x + 1)
      (DGPS.haar 1) := (hlog.sub hqI).add (integrable_const 1)
  have hnonneg : 0 ≤ᵐ[DGPS.haar 1]
      (fun x => vonMisesTorusDensityEX021 t x *
        Real.log (vonMisesTorusDensityEX021 t x) - vonMisesTorusDensityEX021 t x + 1) := by
    filter_upwards with x
    exact DGPS.self_mul_log_sub_add_one_nonneg (vonMisesTorusDensity_pos_EX021 t x).le
  have heq : vonMisesEntropyEX021 t =
      ∫ x, vonMisesTorusDensityEX021 t x *
        Real.log (vonMisesTorusDensityEX021 t x) - vonMisesTorusDensityEX021 t x + 1
        ∂DGPS.haar 1 := by
    have h1 : ∫ x, (vonMisesTorusDensityEX021 t x *
          Real.log (vonMisesTorusDensityEX021 t x) - vonMisesTorusDensityEX021 t x + 1)
          ∂DGPS.haar 1 =
        ∫ x, (vonMisesTorusDensityEX021 t x *
          Real.log (vonMisesTorusDensityEX021 t x) - vonMisesTorusDensityEX021 t x)
          ∂DGPS.haar 1 + ∫ _x, (1 : ℝ) ∂DGPS.haar 1 :=
      integral_add (hlog.sub hqI) (integrable_const 1)
    have h2 : ∫ x, (vonMisesTorusDensityEX021 t x *
          Real.log (vonMisesTorusDensityEX021 t x) - vonMisesTorusDensityEX021 t x)
          ∂DGPS.haar 1 =
        ∫ x, vonMisesTorusDensityEX021 t x *
          Real.log (vonMisesTorusDensityEX021 t x) ∂DGPS.haar 1 -
        ∫ x, vonMisesTorusDensityEX021 t x ∂DGPS.haar 1 := integral_sub hlog hqI
    rw [h1, h2, vonMisesTorusDensity_mass_EX021]
    simp [vonMisesEntropyEX021]
  rw [heq]
  exact integral_nonneg_of_ae hnonneg

theorem densityFreeEnergy_vonMises_formulaEX021 (t : ℝ) :
    DGPS.densityFreeEnergy (DGPS.Models.attractiveXY 2 0)
      (vonMisesAbsoluteDensityEX021 t) =
        vonMisesEntropyEX021 t + 1 - besselRatio t ^ 2 := by
  apply EReal.coe_injective
  rw [DGPS.coe_densityFreeEnergy, ← vonMisesProbability_eq_densityProbabilityEX021 t,
    freeEnergy_vonMises_formula_EX021]
  have hnonneg := vonMisesEntropy_nonnegEX021 t
  rw [EReal.coe_ennreal_ofReal, max_eq_left hnonneg, ← EReal.coe_add]
  congr 1
  ring

theorem actualVonMisesGap_eq_scalarGapEX021 (t : ℝ) :
    actualVonMisesGapEX021 t =
      ((DGPS.scalarGap (DGPS.Models.attractiveXY 2 0)
        (vonMisesAbsoluteDensityEX021 t) : ℝ≥0) : ℝ) := by
  rw [DGPS.coe_scalarGap, densityFreeEnergy_vonMises_formulaEX021]
  have hmin := DGPS.Examples.strict_entropy_fourier_inequality_at_criticality
  have hminReal : DGPS.freeEnergyMinimumReal (DGPS.Models.attractiveXY 2 0) = 1 :=
    hmin.2.2.2.2.2.1
  rw [hminReal, actualVonMisesGapEX021, vonMisesEntropy_formula_EX021]
  ring


/-- A real first-harmonic combination, represented in the actual Haar `L²` space. -/
noncomputable def firstHarmonicCombinationEX021 (a b : ℝ) : Lp ℝ 2 (DGPS.haar 1) :=
  BoundedContinuousFunction.toLp 2 (DGPS.haar 1) ℝ
    (BoundedContinuousFunction.mkOfCompact
      ⟨fun x => a * (xyMode x).re + b * (xyMode x).im,
        (continuous_const.mul (Complex.continuous_re.comp continuous_xyMode)).add
          (continuous_const.mul (Complex.continuous_im.comp continuous_xyMode))⟩)

theorem firstHarmonicCombination_ae_reprEX021 (a b : ℝ) :
    firstHarmonicCombinationEX021 a b =ᵐ[DGPS.haar 1]
      (fun x => a * (xyMode x).re + b * (xyMode x).im) := by
  unfold firstHarmonicCombinationEX021
  exact BoundedContinuousFunction.coeFn_toLp 2 (DGPS.haar 1) ℝ _

theorem firstHarmonicPart_combinationEX021 (a b : ℝ) :
    DGPS.Examples.CriticalHessianKernelEX021.firstHarmonicPartEX021
      (firstHarmonicCombinationEX021 a b) = firstHarmonicCombinationEX021 a b := by
  have hc : Continuous (fun x : DGPS.Torus 1 => (xyMode x).re) :=
    Complex.continuous_re.comp continuous_xyMode
  have hs : Continuous (fun x : DGPS.Torus 1 => (xyMode x).im) :=
    Complex.continuous_im.comp continuous_xyMode
  have hcomb : Continuous (fun x : DGPS.Torus 1 => a * (xyMode x).re +
      b * (xyMode x).im) := (continuous_const.mul hc).add (continuous_const.mul hs)
  have hciBase : Integrable (fun x : DGPS.Torus 1 => (xyMode x).re *
      (a * (xyMode x).re + b * (xyMode x).im)) (DGPS.haar 1) :=
    (hc.mul hcomb).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hsiBase : Integrable (fun x : DGPS.Torus 1 => (xyMode x).im *
      (a * (xyMode x).re + b * (xyMode x).im)) (DGPS.haar 1) :=
    (hs.mul hcomb).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hci : Integrable (fun x : DGPS.Torus 1 => (xyMode x).re *
      (firstHarmonicCombinationEX021 a b) x) (DGPS.haar 1) :=
    hciBase.congr (by
      filter_upwards [firstHarmonicCombination_ae_reprEX021 a b] with x hx
      rw [hx])
  have hsi : Integrable (fun x : DGPS.Torus 1 => (xyMode x).im *
      (firstHarmonicCombinationEX021 a b) x) (DGPS.haar 1) :=
    hsiBase.congr (by
      filter_upwards [firstHarmonicCombination_ae_reprEX021 a b] with x hx
      rw [hx])
  have hcos : ∫ x, (xyMode x).re * (firstHarmonicCombinationEX021 a b) x
      ∂DGPS.haar 1 = a / 2 := by
    calc
      ∫ x, (xyMode x).re * (firstHarmonicCombinationEX021 a b) x ∂DGPS.haar 1 =
          ∫ x, (xyMode x).re * (a * (xyMode x).re + b * (xyMode x).im) ∂DGPS.haar 1 := by
            apply integral_congr_ae
            filter_upwards [firstHarmonicCombination_ae_reprEX021 a b] with x hx
            rw [hx]
      _ = ∫ x, a * (xyMode x).re ^ 2 +
          b * ((xyMode x).re * (xyMode x).im) ∂DGPS.haar 1 := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = a / 2 := by
        rw [integral_add]
        · rw [integral_const_mul, integral_const_mul,
            DGPS.Examples.CriticalHessianKernelEX021.integral_xyMode_re_sq_EX021,
            DGPS.Examples.CriticalHessianKernelEX021.integral_re_im_product_zero_EX021]
          ring
        · exact (continuous_const.mul (hc.pow 2)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        · exact (continuous_const.mul (hc.mul hs)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
  have himre : ∫ x, (xyMode x).im * (xyMode x).re ∂DGPS.haar 1 = 0 := by
    calc
      ∫ x, (xyMode x).im * (xyMode x).re ∂DGPS.haar 1 =
          ∫ x, (xyMode x).re * (xyMode x).im ∂DGPS.haar 1 := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = 0 := DGPS.Examples.CriticalHessianKernelEX021.integral_re_im_product_zero_EX021
  have hsin : ∫ x, (xyMode x).im * (firstHarmonicCombinationEX021 a b) x
      ∂DGPS.haar 1 = b / 2 := by
    calc
      ∫ x, (xyMode x).im * (firstHarmonicCombinationEX021 a b) x ∂DGPS.haar 1 =
          ∫ x, (xyMode x).im * (a * (xyMode x).re + b * (xyMode x).im) ∂DGPS.haar 1 := by
            apply integral_congr_ae
            filter_upwards [firstHarmonicCombination_ae_reprEX021 a b] with x hx
            rw [hx]
      _ = ∫ x, a * ((xyMode x).im * (xyMode x).re) +
          b * (xyMode x).im ^ 2 ∂DGPS.haar 1 := by
        apply integral_congr_ae
        filter_upwards with x
        ring
      _ = b / 2 := by
        rw [integral_add]
        · rw [integral_const_mul, integral_const_mul, himre,
            DGPS.Examples.CriticalHessianKernelEX021.integral_xyMode_im_sq_EX021]
          ring
        · exact (continuous_const.mul (hs.mul hc)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        · exact (continuous_const.mul (hs.pow 2)).integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
  have hpart := DGPS.Examples.CriticalHessianKernelEX021.firstHarmonicPart_ae_reprEX021
    (firstHarmonicCombinationEX021 a b)
  have hcomb := firstHarmonicCombination_ae_reprEX021 a b
  apply Lp.ext
  filter_upwards [hpart, hcomb] with x hp hc'
  rw [hp, hc', hcos, hsin]
  ring

theorem exact_hessian_kernel_spanEX021 :
    ∀ f : DGPS.centeredL2 (DGPS.haarProbability 1),
      DGPS.densityHessian (DGPS.Models.attractiveXY 2 0)
          (DGPS.haarProbability 1) f = 0 ↔
        ∃ a b : ℝ, f.1 = firstHarmonicCombinationEX021 a b := by
  intro f
  constructor
  · intro hf
    have hproj := (DGPS.Examples.CriticalHessianKernelEX021.exact_hessian_kernel_projection_EX021 f).mp hf
    refine ⟨2 * ∫ x, (xyMode x).re * f.1 x ∂DGPS.haar 1,
      2 * ∫ x, (xyMode x).im * f.1 x ∂DGPS.haar 1, ?_⟩
    refine hproj.trans ?_
    have hpart := DGPS.Examples.CriticalHessianKernelEX021.firstHarmonicPart_ae_reprEX021
      f.1
    have hcomb := firstHarmonicCombination_ae_reprEX021
      (2 * ∫ x, (xyMode x).re * f.1 x ∂DGPS.haar 1)
      (2 * ∫ x, (xyMode x).im * f.1 x ∂DGPS.haar 1)
    apply Lp.ext
    filter_upwards [hpart, hcomb] with x hp hc'
    rw [hp, hc']
    ring_nf
    rfl
  · rintro ⟨a, b, h⟩
    apply (DGPS.Examples.CriticalHessianKernelEX021.exact_hessian_kernel_projection_EX021 f).mpr
    rw [h, firstHarmonicPart_combinationEX021]


/-- Classical derivative of the positive square root, with the physical `2π` scale. -/
theorem vonMisesRoot_coordPartialEX021 (t : ℝ) (x : DGPS.Torus 1) :
    DGPS.coordPartial 0 (vonMisesRootEX021 t) x =
      (t / 2) * vonMisesRootEX021 t x *
        DGPS.coordPartial 0 (fun y => (xyMode y).re) x := by
  have hc : DGPS.IsSmoothPeriodic (fun y : DGPS.Torus 1 => (xyMode y).re) :=
    DGPS.Examples.AttractiveXY.isSmoothPeriodic_re_xyMode
  have hx : DifferentiableAt ℝ ((fun y => (xyMode y).re) ∘ DGPS.torusLift)
      (SharpLSI.secT x) := (hc.differentiable (by simp)) _
  have e : DGPS.coordPartial 0 (vonMisesRootEX021 t) x =
      DGPS.coordPartial 0 (fun y : DGPS.Torus 1 => (Real.sqrt (besselI 0 t))⁻¹ *
        Real.exp ((t / 2) * (xyMode y).re)) x := rfl
  rw [e, DGPS.Lipschitz.WeightedGenerator.coordPartial_exp_comp
      ((Real.sqrt (besselI 0 t))⁻¹) (t / 2) 0 x hx]
  unfold vonMisesRootEX021
  ring

/-- The canonical Hessian kernel is exactly the real span of cosine and sine in Haar `L²`. -/
noncomputable def vonMisesDriftEX021 : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY 2 0) :=
  DGPS.Models.attractiveXYDrift 2 0

theorem vonMises_score_difference_vecEX021 (t : ℝ) :
    vonMisesScoreDifferenceEX021 t =
      fun x => -2 * Real.pi * (t - 2 * besselRatio t) * (xyMode x).im := by
  funext x
  exact vonMisesScoreDifference_formula_EX021 t x

theorem vonMises_scalarDissipation_bridgeEX021 (t : ℝ) :
    DGPS.scalarDissipation (DGPS.Models.attractiveXY 2 0) vonMisesDriftEX021
      (vonMisesAbsoluteDensityEX021 t) = ENNReal.ofReal (actualVonMisesDissipationEX021 t) := by
  let ρ := vonMisesAbsoluteDensityEX021 t
  let P := xyFrozen (2 * besselRatio t) 0
  have hLaw := vonMisesProbability_eq_densityMeasureEX021 t
  have hMomP : xyZ1 (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) = besselRatio t ∧
      xyZ2 (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) = 0 := by
    have hm := vonMisesProbability_firstMomentsEX021 t
    rw [hLaw] at hm
    exact hm
  have hP : xyFrozenLaw 2 0 (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) = P := by
    unfold xyFrozenLaw P
    rw [hMomP.1, hMomP.2]
    simp
  have hrootW := DGPS.isWeakGradient_weakGradient ρ.sqrt_mem
  have hrootGrad : DGPS.weakGradient ρ.sqrt ρ.sqrt_mem =ᵐ[DGPS.haar 1]
      DGPS.smoothGrad (vonMisesRootEX021 t) :=
    hrootW.ae_eq (vonMisesRoot_smoothEX021 t).isWeakGradient
  have hlog := DGPS.Examples.AttractiveXY.weakGradient_log_xyFrozen
    (2 * besselRatio t) 0
  have hscore :
      (fun x => (2 : ℝ) • DGPS.weakGradient ρ.sqrt ρ.sqrt_mem x -
        ρ.sqrt x • DGPS.weakGradient (fun x => Real.log (P.density x))
          (P.memH1_log (DGPS.Examples.AttractiveXY.xyFrozen_hasPositiveLipschitzDensity
            (2 * besselRatio t) 0)) x) =ᵐ[DGPS.haar 1]
      (fun x => (WithLp.toLp 2 (fun _ : Fin 1 => vonMisesRootEX021 t x *
        vonMisesScoreDifferenceEX021 t x) : DGPS.Tangent 1)) := by
    filter_upwards [hrootGrad, hlog] with x hx hr
    ext j
    obtain rfl : j = 0 := Subsingleton.elim _ _
    simp only [PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply]
    rw [hx, hr, DGPS.smoothGrad_apply, DGPS.smoothGrad_apply,
      vonMisesRoot_coordPartialEX021,
      DGPS.Examples.AttractiveXY.coordPartial_re_xyMode,
      DGPS.Examples.AttractiveXY.coordPartial_xyTrig,
      vonMisesScoreDifference_formula_EX021]
    have hρ : ρ.sqrt x = vonMisesRootEX021 t x := rfl
    rw [hρ]
    unfold xyTrig
    ring
  have hcont : Continuous (fun x : DGPS.Torus 1 =>
      vonMisesScoreDifferenceEX021 t x ^ 2 * vonMisesTorusDensityEX021 t x) := by
    rw [vonMises_score_difference_vecEX021 t]
    exact (continuous_const.mul (Complex.continuous_im.comp continuous_xyMode)).pow 2 |>.mul
      (vonMisesTorusDensity_continuous_EX021 t)
  have hI : Integrable (fun x : DGPS.Torus 1 =>
      vonMisesScoreDifferenceEX021 t x ^ 2 * vonMisesTorusDensityEX021 t x) (DGPS.haar 1) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnn : 0 ≤ᵐ[DGPS.haar 1]
      (fun x => vonMisesScoreDifferenceEX021 t x ^ 2 * vonMisesTorusDensityEX021 t x) :=
    Filter.Eventually.of_forall fun x => mul_nonneg (sq_nonneg _) (vonMisesTorusDensity_pos_EX021 t x).le
  rw [DGPS.Examples.AttractiveXY.scalarDissipation_attractiveXY 2 0
    vonMisesDriftEX021 ρ, hP]
  rw [DGPS.positiveReference_absolute_identity P
    (DGPS.Examples.AttractiveXY.xyFrozen_hasPositiveLipschitzDensity _ _) ρ]
  have hscoreENN :
      (fun x => ‖(2 : ℝ) • DGPS.weakGradient ρ.sqrt ρ.sqrt_mem x -
          ρ.sqrt x • DGPS.weakGradient (fun x => Real.log (P.density x))
            (P.memH1_log (DGPS.Examples.AttractiveXY.xyFrozen_hasPositiveLipschitzDensity
              (2 * besselRatio t) 0)) x‖ₑ ^ 2) =ᵐ[DGPS.haar 1]
        (fun x => ENNReal.ofReal
          (vonMisesScoreDifferenceEX021 t x ^ 2 * vonMisesTorusDensityEX021 t x)) := by
    filter_upwards [hscore] with x hx
    rw [hx, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), tangent_norm_sq]
    simp only [Finset.univ_unique, Fin.default_eq_zero,
      Finset.sum_singleton]
    congr 1
    rw [mul_pow, vonMisesRoot_sqEX021]
    ring
  rw [lintegral_congr_ae hscoreENN,
    ← ofReal_integral_eq_lintegral_ofReal hI hnn]
  unfold actualVonMisesDissipationEX021
  rfl


/-- The scalar rate quotient transports an ordinary real quotient through ENNReal. -/
theorem ofReal_div_two_mul_EX021 {G : ℝ≥0} {I : ℝ} {D : ℝ≥0∞}
    (hD : D = ENNReal.ofReal I) {H : ℝ}
    (hH : (G : ℝ) = H) (hHpos : 0 < H) :
    D / (2 * (G : ℝ≥0∞)) = ENNReal.ofReal (I / (2 * H)) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), hD,
    ENNReal.ofReal_mul (by norm_num), ← hH, ENNReal.ofReal_coe_nnreal]
  simp

theorem vonMises_scalarGap_jetEX021 (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 100) :
    |((DGPS.scalarGap (DGPS.Models.attractiveXY 2 0)
        (vonMisesAbsoluteDensityEX021 t) : ℝ≥0) : ℝ) - t ^ 4 / 64| ≤
      5 * t ^ 6 := by
  rw [← actualVonMisesGap_eq_scalarGapEX021 t,
    actualVonMisesGap_eq_EX021]
  exact vonMisesGap_jet_EX021 t ht0 (by linarith [ht1])

theorem vonMises_scalarGap_posEX021 (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 100) :
    0 < DGPS.scalarGap (DGPS.Models.attractiveXY 2 0)
      (vonMisesAbsoluteDensityEX021 t) := by
  rw [← NNReal.coe_pos, ← actualVonMisesGap_eq_scalarGapEX021 t,
    actualVonMisesGap_eq_EX021]
  exact (vonMisesQuotient_jet_EX021 t ht0 ht1).1

theorem actualVonMisesDissipation_nonnegEX021 (t : ℝ) :
    0 ≤ actualVonMisesDissipationEX021 t := by
  have hnn : 0 ≤ᵐ[DGPS.haar 1]
      (fun x => vonMisesScoreDifferenceEX021 t x ^ 2 *
        vonMisesTorusDensityEX021 t x) :=
    Filter.Eventually.of_forall fun x =>
      mul_nonneg (sq_nonneg _) (vonMisesTorusDensity_pos_EX021 t x).le
  unfold actualVonMisesDissipationEX021
  exact integral_nonneg_of_ae hnn

theorem vonMises_scalarDissipation_real_jetEX021
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 100) :
    |ENNReal.toReal (DGPS.scalarDissipation
        (DGPS.Models.attractiveXY 2 0) vonMisesDriftEX021
        (vonMisesAbsoluteDensityEX021 t)) -
      (4 * Real.pi ^ 2) * t ^ 6 / 128| ≤
        3 * (4 * Real.pi ^ 2) * t ^ 8 := by
  rw [vonMises_scalarDissipation_bridgeEX021,
    ENNReal.toReal_ofReal (actualVonMisesDissipation_nonnegEX021 t),
    actualVonMisesDissipation_formula_EX021 t ht0]
  exact vonMisesDissipation_jet_EX021 t ht0 (by linarith [ht1])

theorem vonMises_scalarQuotient_bridgeEX021
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 100) :
    DGPS.scalarQuotient (DGPS.Models.attractiveXY 2 0) vonMisesDriftEX021
        (vonMisesAbsoluteDensityEX021 t) =
      ENNReal.ofReal (vonMisesQuotientEX021 t) := by
  have hgap : 0 < actualVonMisesGapEX021 t := by
    rw [actualVonMisesGap_eq_EX021]
    exact (vonMisesQuotient_jet_EX021 t ht0 ht1).1
  have hH :
      ((DGPS.scalarGap (DGPS.Models.attractiveXY 2 0)
        (vonMisesAbsoluteDensityEX021 t) : ℝ≥0) : ℝ) =
        actualVonMisesGapEX021 t :=
    (actualVonMisesGap_eq_scalarGapEX021 t).symm
  unfold DGPS.scalarQuotient
  rw [ofReal_div_two_mul_EX021
    (vonMises_scalarDissipation_bridgeEX021 t) hH hgap,
    ← actualVonMisesQuotient_eq_EX021 t ht0]
  rfl

theorem vonMises_scalarQuotient_real_jetEX021
    (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 100) :
    |ENNReal.toReal (DGPS.scalarQuotient (DGPS.Models.attractiveXY 2 0)
        vonMisesDriftEX021 (vonMisesAbsoluteDensityEX021 t)) -
      (4 * Real.pi ^ 2) * t ^ 2 / 4| ≤
        400 * (4 * Real.pi ^ 2) * t ^ 4 := by
  have hjet := vonMisesQuotient_jet_EX021 t ht0 ht1
  have hDnn := actualVonMisesDissipation_nonnegEX021 t
  have hDraw : 0 ≤ vonMisesDissipationEX021 t := by
    rw [← actualVonMisesDissipation_formula_EX021 t ht0]
    exact hDnn
  have hqnn : 0 ≤ vonMisesQuotientEX021 t := by
    unfold vonMisesQuotientEX021
    exact div_nonneg hDraw (le_of_lt (mul_pos (by norm_num) hjet.1))
  rw [vonMises_scalarQuotient_bridgeEX021 t ht0 ht1,
    ENNReal.toReal_ofReal hqnn]
  exact hjet.2

end DGPS.Examples.CriticalRecoveryBridgesEX021
