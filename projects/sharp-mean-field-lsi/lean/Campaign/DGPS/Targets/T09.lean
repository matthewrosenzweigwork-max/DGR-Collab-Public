import DGPS.Examples.CriticalZeroRatesEX022
import DGPS.Examples.AttractiveXYStationaryEX020
import DGPS.Examples.CriticalRecoveryBridgesEX021
import DGPS.Examples.AttractiveXYTiltRemoteEX025
import DGPS.Examples.AttractiveXYTiltEX024
import DGPS.Examples.AttractiveXYFoldUpperEX028
import DGPS.Examples.AttractiveXYFoldEX027
import DGPS.Examples.AttractiveXYSmallRateEX029
import DGPS.Circle.BesselConcavity
import DGPS.Analysis.RateTopology
import DGPS.Equilibrium.GaussianRate

/-!
# T09: attractive first-harmonic three-regime family

Assembles the critical `(2, 0)` regime, the remote `(4, 1/2)` saddle regime and the positive fold
continuation `(4, h_c + ε)` of the attractive XY family into `three_regimes`.

Design notes: `xyG_T09 = besselRatio`; `vonMisesReference_T09 t = xyLaw_EX023 t`;
`IsEquilibrium_T09 A ν` is `freeEnergy A ν = freeEnergyMinimum A`; the distributional-stationarity
predicate is `IsCircleDistributionalStationary`; the kernel is stated as a submodule equality in
`centeredL2`; `xyCriticalField_T09` is `4 g(s*) - s*` for the unique positive root `s*` of `g' = 1/4`.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS.Examples.AttractiveXY

open DGPS DGPS.Models DGPS.Circle.BesselMoments DGPS.Examples.AttractiveXYTilt
open DGPS.Examples.ThreeSpeciesCircle (IsCircleDistributionalStationary)

/-- `g = I₀'/I₀`. -/
noncomputable abbrev xyG_T09 : ℝ → ℝ := besselRatio

noncomputable abbrev vonMisesReference_T09 (t : ℝ) : ProbabilityMeasure (Torus 1) := xyLaw_EX023 t

def IsEquilibrium_T09 (A : InteractionData 1) (ν : ProbabilityMeasure (Torus 1)) : Prop :=
  freeEnergy A ν = freeEnergyMinimum A

def IsDistributionalStationary_T09 (A : InteractionData 1) (ν : ProbabilityMeasure (Torus 1)) :
    Prop := IsCircleDistributionalStationary A ν

def NoPositiveGapScalarAttainment_T09 (A : InteractionData 1) (b : AbsoluteDrift A) : Prop :=
  ¬ ∃ ρ : AbsoluteDensity 1, 0 < scalarGap A ρ ∧ scalarQuotient A b ρ = scalarRate A b

def NoPositiveGapSpeciesAttainment_T09 (A : InteractionData 1) (b : AbsoluteDrift A) : Prop :=
  ¬ ∃ F : SpeciesFamily 1, 0 < speciesGap A F ∧ speciesQuotient A b F = speciesRate A b

def SmoothPositiveDensity_T09 (ρ : AbsoluteDensity 1) : Prop :=
  ∃ φ : Torus 1 → ℝ, IsSmoothPeriodic φ ∧ (∀ x, 0 < φ x) ∧ ρ.density =ᵐ[haar 1] φ

def IsSaddleDensity_T09 (A : InteractionData 1) (ρ : AbsoluteDensity 1) : Prop :=
  ∃ f g : centeredL2 (densityMeasure ρ),
    (∃ φ : Torus 1 → ℝ, IsSmoothPeriodic φ ∧
      ((f : Lp ℝ 2 (densityMeasure ρ : Measure (Torus 1))) : Torus 1 → ℝ)
        =ᵐ[(densityMeasure ρ : Measure (Torus 1))] φ) ∧
    (∃ φ : Torus 1 → ℝ, IsSmoothPeriodic φ ∧
      ((g : Lp ℝ 2 (densityMeasure ρ : Measure (Torus 1))) : Torus 1 → ℝ)
        =ᵐ[(densityMeasure ρ : Measure (Torus 1))] φ) ∧
    inner ℝ f (densityHessian A (densityMeasure ρ) f) < 0 ∧
    0 < inner ℝ g (densityHessian A (densityMeasure ρ) g)


theorem fold_exists_unique_T09 : ∃! s : ℝ, 0 < s ∧ deriv besselRatio s = 1 / 4 :=
  DGPS.Examples.strict_bessel_concavity_and_fold_parameter.2.2.1

/-- The unique positive root `s*` of `g'(s) = 1/4`. -/
noncomputable def foldRoot_T09 : ℝ := Classical.choose fold_exists_unique_T09

theorem foldRoot_spec_T09 : (0 < foldRoot_T09 ∧ deriv besselRatio foldRoot_T09 = 1 / 4) ∧
    ∀ u : ℝ, (0 < u ∧ deriv besselRatio u = 1 / 4) → u = foldRoot_T09 :=
  Classical.choose_spec fold_exists_unique_T09

/-- The critical field `h_c = 4 g(s*) - s*`. -/
noncomputable def xyCriticalField_T09 : ℝ := 4 * besselRatio foldRoot_T09 - foldRoot_T09

open DGPS.Examples.AttractiveXYCritical DGPS.Examples.CriticalRecoveryBridgesEX021 in
theorem fh_centered_T09 (a b : ℝ) :
    ∫ x, (firstHarmonicCombinationEX021 a b) x ∂(haar 1) = 0 := by
  have hre : ∫ y, (xyMode y).re ∂(haar 1) = 0 := by
    show xyZ1 (haar 1) = 0
    rw [← re_integral_xyMode_xyc, integral_xyMode_haar_xyc]; rfl
  have him : ∫ y, (xyMode y).im ∂(haar 1) = 0 := by
    show xyZ2 (haar 1) = 0
    rw [← im_integral_xyMode_xyc, integral_xyMode_haar_xyc]; rfl
  rw [integral_congr_ae (firstHarmonicCombination_ae_reprEX021 a b)]
  rw [integral_add (by
      exact (continuous_const.mul (Complex.continuous_re.comp continuous_xyMode)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    (by
      exact (continuous_const.mul (Complex.continuous_im.comp continuous_xyMode)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)),
    integral_const_mul, integral_const_mul, hre, him]
  ring

open DGPS.Examples.CriticalRecoveryBridgesEX021 in
/-- The first cosine mode `cos 2πx`, as an element of the centered `L²(Haar)`. -/
noncomputable def cosElt_T09 : centeredL2 (haarProbability 1) :=
  ⟨firstHarmonicCombinationEX021 1 0, fh_centered_T09 1 0⟩

open DGPS.Examples.CriticalRecoveryBridgesEX021 in
/-- The first sine mode `sin 2πx`, as an element of the centered `L²(Haar)`. -/
noncomputable def sinElt_T09 : centeredL2 (haarProbability 1) :=
  ⟨firstHarmonicCombinationEX021 0 1, fh_centered_T09 0 1⟩

open DGPS.Examples.CriticalRecoveryBridgesEX021 in
theorem smul_add_fh_T09 (a b : ℝ) :
    a • firstHarmonicCombinationEX021 1 0 + b • firstHarmonicCombinationEX021 0 1 =
      firstHarmonicCombinationEX021 a b := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_add (a • firstHarmonicCombinationEX021 1 0)
      (b • firstHarmonicCombinationEX021 0 1),
    Lp.coeFn_smul a (firstHarmonicCombinationEX021 1 0),
    Lp.coeFn_smul b (firstHarmonicCombinationEX021 0 1),
    firstHarmonicCombination_ae_reprEX021 1 0, firstHarmonicCombination_ae_reprEX021 0 1,
    firstHarmonicCombination_ae_reprEX021 a b] with x h1 h2 h3 h4 h5 h6
  rw [h1, h6]
  simp only [Pi.add_apply, h2, h3, Pi.smul_apply, h4, h5, smul_eq_mul]
  ring

open DGPS.Examples.CriticalRecoveryBridgesEX021 in
theorem hessian_kernel_T09 :
    LinearMap.ker (densityHessian (attractiveXY 2 0) (haarProbability 1)).toLinearMap =
      Submodule.span ℝ {cosElt_T09, sinElt_T09} := by
  ext f
  rw [LinearMap.mem_ker, Submodule.mem_span_pair]
  show densityHessian (attractiveXY 2 0) (haarProbability 1) f = 0 ↔ _
  rw [exact_hessian_kernel_spanEX021 f]
  constructor
  · rintro ⟨a, b, h⟩
    refine ⟨a, b, ?_⟩
    apply Subtype.ext
    show a • firstHarmonicCombinationEX021 1 0 + b • firstHarmonicCombinationEX021 0 1 = f.1
    rw [smul_add_fh_T09, h]
  · rintro ⟨a, b, h⟩
    refine ⟨a, b, ?_⟩
    rw [← h]
    exact smul_add_fh_T09 a b

theorem part1_T09 :
    (∀ ν, IsEquilibrium_T09 (attractiveXY 2 0) ν ↔ ν = haarProbability 1) ∧
    (∀ ν, IsDistributionalStationary_T09 (attractiveXY 2 0) ν ↔ ν = haarProbability 1) ∧
    scalarRate (attractiveXY 2 0) (attractiveXYDrift 2 0) = 0 ∧
    speciesRate (attractiveXY 2 0) (attractiveXYDrift 2 0) = 0 ∧
    NoPositiveGapScalarAttainment_T09 (attractiveXY 2 0) (attractiveXYDrift 2 0) ∧
    NoPositiveGapSpeciesAttainment_T09 (attractiveXY 2 0) (attractiveXYDrift 2 0) ∧
    LinearMap.ker (densityHessian (attractiveXY 2 0) (haarProbability 1)).toLinearMap =
      Submodule.span ℝ {cosElt_T09, sinElt_T09} := by
  obtain ⟨hr1, hr2, hn1, hn2⟩ := DGPS.Examples.critical_zero_rates_and_nonattainment
  have hE := DGPS.Examples.strict_entropy_fourier_inequality_at_criticality
  refine ⟨fun ν => ⟨hE.2.2.2.2.2.2 ν, ?_⟩, fun ν => (DGPS.Examples.critical_stationary_uniqueness_iff_EX020.1 ν),
    hr1, hr2, ?_, ?_, hessian_kernel_T09⟩
  · rintro rfl
    exact (hE.2.2.1.trans hE.2.2.2.2.1.symm)
  · rintro ⟨ρ, hg, hq⟩
    exact hn1 ⟨ρ, hg, hq.trans hr1⟩
  · rintro ⟨F, hg, hq⟩
    exact hn2 ⟨F, hg, hq.trans hr2⟩

open scoped BoundedContinuousFunction

open DGPS.Examples.AttractiveXYTiltEX024 in
theorem openPos_law_T09 (t : ℝ) : (xyLaw_EX023 t : Measure (Torus 1)).IsOpenPosMeasure := by
  refine ⟨fun U hUo hne => ?_⟩
  have hcont : Continuous fun x : Torus 1 => Real.exp (t * (xyMode x).re) / besselI 0 t :=
    (Real.continuous_exp.comp (continuous_const.mul hc_EX024)).div_const _
  have hq : ∀ x : Torus 1, 0 < Real.exp (t * (xyMode x).re) / besselI 0 t := fun x =>
    div_pos (Real.exp_pos _) (besselI_zero_pos t)
  have hm : AEMeasurable (fun x : Torus 1 =>
      ENNReal.ofReal (Real.exp (t * (xyMode x).re) / besselI 0 t)) (haar 1) :=
    (ENNReal.measurable_ofReal.comp hcont.measurable).aemeasurable
  rw [law_density_EX023, Ne, withDensity_apply_eq_zero' hm]
  have : {x | ENNReal.ofReal (Real.exp (t * (xyMode x).re) / besselI 0 t) ≠ 0} ∩ U = U := by
    ext x; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, and_iff_right_iff_imp]
    intro _; simpa using hq x
  rw [this]
  exact hUo.measure_ne_zero _ hne

/-- Gram-Schmidt coefficient making `sin · (2 cos - a)` orthogonal to `sin` in `L²(q_t)`. -/
noncomputable def aCoef_T09 (t : ℝ) : ℝ :=
  2 * (∫ x, (xyMode x).re * (xyMode x).im ^ 2 ∂(xyLaw_EX023 t : Measure (Torus 1))) /
    (besselRatio t / t)

noncomputable def phiFun_T09 (t : ℝ) (x : Torus 1) : ℝ :=
  (xyMode x).im * (2 * (xyMode x).re - aCoef_T09 t)

open DGPS.Examples.AttractiveXYTiltEX024 in
theorem phi_cont_T09 (t : ℝ) : Continuous (phiFun_T09 t) :=
  hs_EX024.mul ((continuous_const.mul hc_EX024).sub continuous_const)

theorem phi_smooth_T09 (t : ℝ) : IsSmoothPeriodic (phiFun_T09 t) := by
  have hre := isSmoothPeriodic_re_xyMode
  have him := isSmoothPeriodic_im_xyMode
  unfold IsSmoothPeriodic at hre him ⊢
  exact him.mul ((contDiff_const.mul hre).sub contDiff_const)

noncomputable def phiBCF_T09 (t : ℝ) : Torus 1 →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨phiFun_T09 t, phi_cont_T09 t⟩

theorem phiBCF_apply_T09 (t : ℝ) (x : Torus 1) : phiBCF_T09 t x = phiFun_T09 t x := rfl

noncomputable def phiLp_T09 (t : ℝ) : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1)) :=
  BoundedContinuousFunction.toLp 2 (xyLaw_EX023 t : Measure (Torus 1)) ℝ (phiBCF_T09 t)

theorem phiLp_ae_T09 (t : ℝ) :
    (phiLp_T09 t : Torus 1 → ℝ) =ᵐ[(xyLaw_EX023 t : Measure (Torus 1))] phiFun_T09 t :=
  BoundedContinuousFunction.coeFn_toLp 2 (xyLaw_EX023 t : Measure (Torus 1)) ℝ (phiBCF_T09 t)

open DGPS.Examples.AttractiveXYTiltEX024 in
theorem phiLp_centered_T09 (t : ℝ) :
    ∫ x, (phiLp_T09 t) x ∂(xyLaw_EX023 t : Measure (Torus 1)) = 0 := by
  rw [integral_congr_ae (phiLp_ae_T09 t)]
  have := law_odd_EX024 t (fun r => 2 * r - aCoef_T09 t)
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [phiFun_T09]; ring

open DGPS.Examples.AttractiveXYTiltEX024 in
theorem inner_phi_u_T09 (t : ℝ) : inner ℝ (phiLp_T09 t) (uLp_EX024 t) = 0 := by
  unfold phiLp_T09 uLp_EX024
  rw [inner_toLp_toLp_EX024]
  have := law_odd_EX024 t (fun r => (2 * r - aCoef_T09 t) * (r - besselRatio t))
  rw [← this]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [phiBCF_apply_T09, uBCF_apply_EX024, phiFun_T09]; ring

open DGPS.Examples.AttractiveXYTiltEX024 in
theorem inner_phi_v_T09 {t : ℝ} (ht : t ≠ 0) (hpos : 0 < besselRatio t / t) :
    inner ℝ (phiLp_T09 t) (vLp_EX024 t) = 0 := by
  unfold phiLp_T09 vLp_EX024
  rw [inner_toLp_toLp_EX024]
  have e : ∀ x : Torus 1, phiBCF_T09 t x * vBCF_EX024 x =
      2 * ((xyMode x).re * (xyMode x).im ^ 2) - aCoef_T09 t * (xyMode x).im ^ 2 := by
    intro x; simp only [phiBCF_apply_T09, vBCF_apply_EX024, phiFun_T09]; ring
  simp_rw [e]
  have i1 : Integrable (fun x : Torus 1 => 2 * ((xyMode x).re * (xyMode x).im ^ 2))
      (xyLaw_EX023 t : Measure (Torus 1)) :=
    (integrable_cont_EX024 _ (hc_EX024.mul (hs_EX024.pow 2))).const_mul _
  have i2 : Integrable (fun x : Torus 1 => aCoef_T09 t * (xyMode x).im ^ 2)
      (xyLaw_EX023 t : Measure (Torus 1)) :=
    (integrable_cont_EX024 _ (hs_EX024.pow 2)).const_mul _
  rw [integral_sub i1 i2, integral_const_mul, integral_const_mul, m_ss_EX024 t ht]
  unfold aCoef_T09
  rw [div_mul_cancel₀ _ hpos.ne']
  ring

open DGPS.Examples.AttractiveXYTiltEX024 in
theorem phi_ne_zero_T09 (t : ℝ) : ∃ x, phiFun_T09 t x ≠ 0 := by
  by_cases ha : aCoef_T09 t = 0
  · refine ⟨torusLift (fun _ => 1 / 6), ?_⟩
    have e1 : 2 * Real.pi * (1 / 6 : ℝ) = Real.pi / 3 := by ring
    simp only [phiFun_T09, xyMode_re_lift, xyMode_im_lift, ha, e1, Real.cos_pi_div_three,
      Real.sin_pi_div_three]
    have : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
    positivity
  · refine ⟨torusLift (fun _ => 1 / 4), ?_⟩
    have e1 : 2 * Real.pi * (1 / 4 : ℝ) = Real.pi / 2 := by ring
    simp only [phiFun_T09, xyMode_re_lift, xyMode_im_lift, e1, Real.cos_pi_div_two,
      Real.sin_pi_div_two]
    simpa using ha

open DGPS.Examples.AttractiveXYTiltEX024 in
theorem inner_phi_phi_pos_T09 (t : ℝ) : 0 < inner ℝ (phiLp_T09 t) (phiLp_T09 t) := by
  have := openPos_law_T09 t
  unfold phiLp_T09
  rw [inner_toLp_toLp_EX024]
  obtain ⟨x0, hx0⟩ := phi_ne_zero_T09 t
  have hc : Continuous fun x => phiBCF_T09 t x * phiBCF_T09 t x :=
    (phi_cont_T09 t).mul (phi_cont_T09 t)
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := x0)
    (HasCompactSupport.of_compactSpace _) (fun x => mul_self_nonneg _) ?_
  simpa [phiBCF_apply_T09] using hx0

open DGPS.Examples.AttractiveXYTiltEX024 in
theorem saddle_law_T09 (κ h t : ℝ) (ht : t ≠ 0) (hpos : 0 < besselRatio t / t)
    (hneg : 1 - κ * (besselRatio t / t) < 0) :
    ∃ f g : centeredL2 (xyLaw_EX023 t),
      (∃ φ : Torus 1 → ℝ, IsSmoothPeriodic φ ∧
        ((f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) : Torus 1 → ℝ)
          =ᵐ[(xyLaw_EX023 t : Measure (Torus 1))] φ) ∧
      (∃ φ : Torus 1 → ℝ, IsSmoothPeriodic φ ∧
        ((g : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) : Torus 1 → ℝ)
          =ᵐ[(xyLaw_EX023 t : Measure (Torus 1))] φ) ∧
      inner ℝ f (densityHessian (attractiveXY κ h) (xyLaw_EX023 t) f) < 0 ∧
      0 < inner ℝ g (densityHessian (attractiveXY κ h) (xyLaw_EX023 t) g) := by
  let G : centeredL2 (xyLaw_EX023 t) := ⟨phiLp_T09 t, phiLp_centered_T09 t⟩
  refine ⟨vC_EX024 t, G, ⟨fun x => (xyMode x).im, isSmoothPeriodic_im_xyMode, vLp_ae_EX024 t⟩,
    ⟨phiFun_T09 t, phi_smooth_T09 t, phiLp_ae_T09 t⟩, ?_, ?_⟩
  · rw [hessian_v_EX024 κ h t ht]
    show inner ℝ (vLp_EX024 t) ((1 - κ * (besselRatio t / t)) • vLp_EX024 t) < 0
    rw [real_inner_smul_right, inner_vv_EX024 ht]
    exact mul_neg_of_neg_of_pos hneg hpos
  · have h1 : inner ℝ G (uC_EX024 t) = 0 := inner_phi_u_T09 t
    have h2 : inner ℝ G (vC_EX024 t) = 0 := inner_phi_v_T09 ht hpos
    rw [hessian_orth_EX024 κ h t G h1 h2]
    exact inner_phi_phi_pos_T09 t

theorem saddle_of_law_T09 (A : InteractionData 1) (ρ : AbsoluteDensity 1) (t : ℝ)
    (hρ : densityMeasure ρ = xyLaw_EX023 t)
    (H : ∃ f g : centeredL2 (xyLaw_EX023 t),
      (∃ φ : Torus 1 → ℝ, IsSmoothPeriodic φ ∧
        ((f : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) : Torus 1 → ℝ)
          =ᵐ[(xyLaw_EX023 t : Measure (Torus 1))] φ) ∧
      (∃ φ : Torus 1 → ℝ, IsSmoothPeriodic φ ∧
        ((g : Lp ℝ 2 (xyLaw_EX023 t : Measure (Torus 1))) : Torus 1 → ℝ)
          =ᵐ[(xyLaw_EX023 t : Measure (Torus 1))] φ) ∧
      inner ℝ f (densityHessian A (xyLaw_EX023 t) f) < 0 ∧
      0 < inner ℝ g (densityHessian A (xyLaw_EX023 t) g)) :
    IsSaddleDensity_T09 A ρ := by
  have key : ∀ μ : ProbabilityMeasure (Torus 1), μ = xyLaw_EX023 t →
      ∃ f g : centeredL2 μ,
        (∃ φ : Torus 1 → ℝ, IsSmoothPeriodic φ ∧
          ((f : Lp ℝ 2 (μ : Measure (Torus 1))) : Torus 1 → ℝ) =ᵐ[(μ : Measure (Torus 1))] φ) ∧
        (∃ φ : Torus 1 → ℝ, IsSmoothPeriodic φ ∧
          ((g : Lp ℝ 2 (μ : Measure (Torus 1))) : Torus 1 → ℝ) =ᵐ[(μ : Measure (Torus 1))] φ) ∧
        inner ℝ f (densityHessian A μ f) < 0 ∧ 0 < inner ℝ g (densityHessian A μ g) := by
    rintro μ rfl
    exact H
  exact key _ hρ

open DGPS.Examples.CriticalRecoveryBridgesEX021 in
theorem remote_saddle_T09 {s : ℝ} (hs0 : 0 < s) (hs : 4 * besselRatio s - s = 1 / 2) :
    IsSaddleDensity_T09 (attractiveXY 4 (1 / 2)) (vonMisesAbsoluteDensityEX021 (-s)) := by
  refine saddle_of_law_T09 _ _ (-s)
    (DGPS.Examples.AttractiveXYTiltRemoteEX025.densityMeasure_eq_EX025 (-s)) ?_
  have hg : 0 < besselRatio s := DGPS.Circle.BesselMonotonicity.besselRatio_pos s hs0
  have e : besselRatio (-s) / (-s) = besselRatio s / s := by
    rw [besselRatio_neg, neg_div_neg_eq]
  have hpos : 0 < besselRatio (-s) / (-s) := by rw [e]; positivity
  refine saddle_law_T09 4 (1 / 2) (-s) (by linarith) hpos ?_
  rw [e]
  have : 4 * besselRatio s / s = 1 + 1 / (2 * s) := by
    field_simp; linarith
  have h2 : 4 * (besselRatio s / s) = 4 * besselRatio s / s := by ring
  rw [h2, this]
  have : 0 < 1 / (2 * s) := by positivity
  linarith

open DGPS.Examples.AttractiveXYTiltRemoteEX025 DGPS.Examples.CriticalRecoveryBridgesEX021 in
theorem part2_T09 :
    ∃ t : ℝ, 0 < t ∧ t = 4 * xyG_T09 t + 1 / 2 ∧
      (∀ u : ℝ, 0 < u → u = 4 * xyG_T09 u + 1 / 2 → u = t) ∧
      (∀ ν : ProbabilityMeasure (Torus 1),
        IsEquilibrium_T09 (attractiveXY 4 (1 / 2)) ν ↔ ν = vonMisesReference_T09 t) ∧
      ∃ hH : IsCoerciveDensityHessian (attractiveXY 4 (1 / 2)) (vonMisesReference_T09 t),
        ENNReal.ofReal (DGPS.a0 * Real.exp (-9) / 9) ≤
          gaussianRate (attractiveXY 4 (1 / 2)) (vonMisesReference_T09 t) hH ∧
        scalarRate (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2)) = 0 ∧
        speciesRate (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2)) = 0 ∧
        ∃ ρ : AbsoluteDensity 1, SmoothPositiveDensity_T09 ρ ∧
          IsDistributionalStationary_T09 (attractiveXY 4 (1 / 2)) (densityMeasure ρ) ∧
          0 < scalarGap (attractiveXY 4 (1 / 2)) ρ ∧
          scalarDissipation (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2)) ρ = 0 ∧
          IsSaddleDensity_T09 (attractiveXY 4 (1 / 2)) ρ := by
  obtain ⟨t, ht, he, -, hmin, -, -, hlow, hG⟩ := equilibrium_EX025
  have hH : IsCoerciveDensityHessian (attractiveXY 4 (1 / 2)) (vonMisesReference_T09 t) :=
    ⟨1 / 9, by norm_num, fun f => hlow f⟩
  obtain ⟨s, hs0, hs⟩ := exists_positive_remote_root_EX025
  refine ⟨t, ht, he, fun u hu heu => ?_, hmin, hH, ?_, scalarRate_zero_EX025,
    speciesRate_zero_EX025, vonMisesAbsoluteDensityEX021 (-s),
    ⟨_, vonMises_density_smooth_EX025 (-s), vonMises_density_pos_EX025 (-s),
      Filter.EventuallyEq.refl _ _⟩, ?_, remote_gap_pos_EX025 hs0,
    remote_dissipation_zero_EX025 hs, remote_saddle_T09 hs0 hs⟩
  · exact positive_root_atMostOne_EX023 (κ := 4) (h := 1 / 2) (by norm_num) (by norm_num) hu ht heu he
  · have e : DGPS.a0 * Real.exp (-9) / 9 = 4 * Real.pi ^ 2 * Real.exp (-9) / 9 := rfl
    rw [e]
    exact hG hH
  · rw [densityMeasure_eq_EX025 (-s)]
    exact root_stationary_EX023 (κ := 4) (h := 1 / 2) (remote_root_iff_EX025.mpr hs)

theorem part3_T09 :
    ∃ s : ℝ, 0 < s ∧ deriv xyG_T09 s = 1 / 4 ∧
      (∀ u : ℝ, 0 < u → deriv xyG_T09 u = 1 / 4 → u = s) ∧
      1 / 2 < 4 * xyG_T09 s - s ∧
      ∃ c C cG CG : ℝ, 0 < c ∧ 0 < C ∧ 0 < cG ∧ 0 < CG ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∃ μ : ProbabilityMeasure (Torus 1),
            (∀ ν : ProbabilityMeasure (Torus 1),
              IsDistributionalStationary_T09 (attractiveXY 4 (4 * xyG_T09 s - s + ε)) ν ↔ ν = μ) ∧
            (∀ ν : ProbabilityMeasure (Torus 1),
              IsEquilibrium_T09 (attractiveXY 4 (4 * xyG_T09 s - s + ε)) ν ↔ ν = μ) ∧
            ∃ hH : IsCoerciveDensityHessian (attractiveXY 4 (4 * xyG_T09 s - s + ε)) μ,
              ENNReal.ofReal (c * DGPS.a0 * ε ^ 2) ≤
                speciesRate (attractiveXY 4 (4 * xyG_T09 s - s + ε))
                  (attractiveXYDrift 4 (4 * xyG_T09 s - s + ε)) ∧
              speciesRate (attractiveXY 4 (4 * xyG_T09 s - s + ε))
                  (attractiveXYDrift 4 (4 * xyG_T09 s - s + ε)) ≤
                scalarRate (attractiveXY 4 (4 * xyG_T09 s - s + ε))
                  (attractiveXYDrift 4 (4 * xyG_T09 s - s + ε)) ∧
              scalarRate (attractiveXY 4 (4 * xyG_T09 s - s + ε))
                  (attractiveXYDrift 4 (4 * xyG_T09 s - s + ε)) ≤
                ENNReal.ofReal (C * DGPS.a0 * ε ^ 2) ∧
              ENNReal.ofReal (cG * DGPS.a0) ≤
                gaussianRate (attractiveXY 4 (4 * xyG_T09 s - s + ε)) μ hH ∧
              gaussianRate (attractiveXY 4 (4 * xyG_T09 s - s + ε)) μ hH ≤
                ENNReal.ofReal (CG * DGPS.a0) := by
  obtain ⟨⟨hs0, hd⟩, huniq⟩ := foldRoot_spec_T09
  have hmax := DGPS.Examples.strict_bessel_concavity_and_fold_parameter.2.2.2 _ hs0 hd
  have hhc : xyCriticalField_T09 = 4 * besselRatio foldRoot_T09 - foldRoot_T09 := rfl
  obtain ⟨hc0, cG, CG, hcGdef, hcG, hCG, hall⟩ :=
    fold_upper_bound_and_gaussian_comparability hs0 hd hhc
  obtain ⟨-, hlow⟩ := all_species_fold_lower_bound hs0 hd hhc
  refine ⟨foldRoot_T09, hs0, hd, fun u hu hdu => huniq u ⟨hu, hdu⟩, hmax.2, 
    Real.exp (-(2 * (xyCriticalField_T09 + 5))) /
      (1 + 20 * (max 8 (max (16 / xyCriticalField_T09)
        ((2 + Real.sqrt 2) * (xyCriticalField_T09 + 5) / xyCriticalField_T09))) ^ 2),
    1 / (4 * xyCriticalField_T09 * foldRoot_T09), cG, CG, by positivity, by positivity, hcG, hCG, ?_⟩
  intro ε hε0 hε1
  obtain ⟨-, hroot, -, -, hup, hgauss⟩ := hall ε hε0 hε1
  have hh : 0 < xyCriticalField_T09 + ε := by linarith
  obtain ⟨hstat, -, t0, ht0, he0, hu0, -, -, -, hmin, -⟩ :=
    DGPS.Examples.tilted_stationary_scalar_root_and_global_minimizer (κ := 4)
      (h := xyCriticalField_T09 + ε) (by norm_num) hh
  obtain ⟨hH, hbd⟩ := hgauss t0 ht0 he0
  refine ⟨xyLaw_EX023 t0, ?_, hmin, hH, ?_, speciesRate_le_scalarRate _ _, ?_, (hbd hH).1, (hbd hH).2⟩
  · intro ν
    rw [show IsDistributionalStationary_T09 (attractiveXY 4 (4 * xyG_T09 foldRoot_T09 - foldRoot_T09 + ε)) ν ↔
        IsCircleDistributionalStationary (attractiveXY 4 (xyCriticalField_T09 + ε)) ν from Iff.rfl,
      hstat ν]
    constructor
    · rintro ⟨t, ht, he, rfl⟩
      rcases lt_trichotomy t 0 with hneg | hzero | hpos
      · exfalso
        have hu : 0 < -t := by linarith
        have h1 : 4 * besselRatio (-t) - (-t) = xyCriticalField_T09 + ε := by
          rw [DGPS.Circle.BesselMoments.besselRatio_neg]
          have : t = 4 * besselRatio t + (xyCriticalField_T09 + ε) := he
          linarith
        have h2 : 4 * besselRatio (-t) - (-t) ≤ 4 * besselRatio foldRoot_T09 - foldRoot_T09 := by
          by_cases hts : -t = foldRoot_T09
          · rw [hts]
          · exact (hmax.1 _ hu.le hts).le
        linarith
      · exact absurd hzero ht
      · rw [hu0 t hpos he]
    · rintro rfl
      exact ⟨t0, ht0.ne', he0, rfl⟩
  · have h := (hlow ε hε0 hε1).2.2.2 (attractiveXYDrift 4 (xyCriticalField_T09 + ε))
    refine le_trans (le_of_eq ?_) h
    congr 1
    ring
  · have h := hup (attractiveXYDrift 4 (xyCriticalField_T09 + ε))
    refine le_trans h (le_of_eq ?_)
    congr 1
    ring

theorem part4_T09 :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      speciesRate (attractiveXY 4 (xyCriticalField_T09 + ε))
          (attractiveXYDrift 4 (xyCriticalField_T09 + ε)) =
        scalarRate (attractiveXY 4 (xyCriticalField_T09 + ε))
          (attractiveXYDrift 4 (xyCriticalField_T09 + ε)) := by
  obtain ⟨⟨hs0, hd⟩, -⟩ := foldRoot_spec_T09
  have hhc : xyCriticalField_T09 = 4 * besselRatio foldRoot_T09 - foldRoot_T09 := rfl
  obtain ⟨ε0, h0, h1, c1, c2, c3, c4, -, -, -, -, hall⟩ :=
    small_rate_equality_along_the_positive_fold_side hs0 hd hhc
  refine ⟨ε0, h0, h1, fun ε hε hlt => ?_⟩
  have h := ((hall ε hε (by linarith)).2.1 (lipschitzData_attractiveXY 4 (xyCriticalField_T09 + ε))).2.2 hlt
  rw [DGPS.Analysis.RateTopology.speciesRate_eq_of_providers (attractiveXYDrift 4 (xyCriticalField_T09 + ε))
      (lipschitz_absoluteDrift _ (lipschitzData_attractiveXY 4 (xyCriticalField_T09 + ε))),
    DGPS.Analysis.RateTopology.scalarRate_eq_of_providers (attractiveXYDrift 4 (xyCriticalField_T09 + ε))
      (lipschitz_absoluteDrift _ (lipschitzData_attractiveXY 4 (xyCriticalField_T09 + ε)))]
  exact h

/-- The three regimes of the attractive first-harmonic XY family. -/
theorem three_regimes :
    ((∀ ν, IsEquilibrium_T09 (attractiveXY 2 0) ν ↔ ν = haarProbability 1) ∧
    (∀ ν, IsDistributionalStationary_T09 (attractiveXY 2 0) ν ↔ ν = haarProbability 1) ∧
    scalarRate (attractiveXY 2 0) (attractiveXYDrift 2 0) = 0 ∧
    speciesRate (attractiveXY 2 0) (attractiveXYDrift 2 0) = 0 ∧
    NoPositiveGapScalarAttainment_T09 (attractiveXY 2 0) (attractiveXYDrift 2 0) ∧
    NoPositiveGapSpeciesAttainment_T09 (attractiveXY 2 0) (attractiveXYDrift 2 0) ∧
    LinearMap.ker (densityHessian (attractiveXY 2 0) (haarProbability 1)).toLinearMap =
      Submodule.span ℝ {cosElt_T09, sinElt_T09}) ∧
    (∃ t : ℝ, 0 < t ∧ t = 4 * xyG_T09 t + 1 / 2 ∧
      (∀ u : ℝ, 0 < u → u = 4 * xyG_T09 u + 1 / 2 → u = t) ∧
      (∀ ν : ProbabilityMeasure (Torus 1),
        IsEquilibrium_T09 (attractiveXY 4 (1 / 2)) ν ↔ ν = vonMisesReference_T09 t) ∧
      ∃ hH : IsCoerciveDensityHessian (attractiveXY 4 (1 / 2)) (vonMisesReference_T09 t),
        ENNReal.ofReal (DGPS.a0 * Real.exp (-9) / 9) ≤
          gaussianRate (attractiveXY 4 (1 / 2)) (vonMisesReference_T09 t) hH ∧
        scalarRate (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2)) = 0 ∧
        speciesRate (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2)) = 0 ∧
        ∃ ρ : AbsoluteDensity 1, SmoothPositiveDensity_T09 ρ ∧
          IsDistributionalStationary_T09 (attractiveXY 4 (1 / 2)) (densityMeasure ρ) ∧
          0 < scalarGap (attractiveXY 4 (1 / 2)) ρ ∧
          scalarDissipation (attractiveXY 4 (1 / 2)) (attractiveXYDrift 4 (1 / 2)) ρ = 0 ∧
          IsSaddleDensity_T09 (attractiveXY 4 (1 / 2)) ρ) ∧
    (∃ s : ℝ, 0 < s ∧ deriv xyG_T09 s = 1 / 4 ∧
      (∀ u : ℝ, 0 < u → deriv xyG_T09 u = 1 / 4 → u = s) ∧
      1 / 2 < 4 * xyG_T09 s - s ∧
      ∃ c C cG CG : ℝ, 0 < c ∧ 0 < C ∧ 0 < cG ∧ 0 < CG ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
          ∃ μ : ProbabilityMeasure (Torus 1),
            (∀ ν : ProbabilityMeasure (Torus 1),
              IsDistributionalStationary_T09 (attractiveXY 4 (4 * xyG_T09 s - s + ε)) ν ↔ ν = μ) ∧
            (∀ ν : ProbabilityMeasure (Torus 1),
              IsEquilibrium_T09 (attractiveXY 4 (4 * xyG_T09 s - s + ε)) ν ↔ ν = μ) ∧
            ∃ hH : IsCoerciveDensityHessian (attractiveXY 4 (4 * xyG_T09 s - s + ε)) μ,
              ENNReal.ofReal (c * DGPS.a0 * ε ^ 2) ≤
                speciesRate (attractiveXY 4 (4 * xyG_T09 s - s + ε))
                  (attractiveXYDrift 4 (4 * xyG_T09 s - s + ε)) ∧
              speciesRate (attractiveXY 4 (4 * xyG_T09 s - s + ε))
                  (attractiveXYDrift 4 (4 * xyG_T09 s - s + ε)) ≤
                scalarRate (attractiveXY 4 (4 * xyG_T09 s - s + ε))
                  (attractiveXYDrift 4 (4 * xyG_T09 s - s + ε)) ∧
              scalarRate (attractiveXY 4 (4 * xyG_T09 s - s + ε))
                  (attractiveXYDrift 4 (4 * xyG_T09 s - s + ε)) ≤
                ENNReal.ofReal (C * DGPS.a0 * ε ^ 2) ∧
              ENNReal.ofReal (cG * DGPS.a0) ≤
                gaussianRate (attractiveXY 4 (4 * xyG_T09 s - s + ε)) μ hH ∧
              gaussianRate (attractiveXY 4 (4 * xyG_T09 s - s + ε)) μ hH ≤
                ENNReal.ofReal (CG * DGPS.a0)) ∧
    (∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ 1 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      speciesRate (attractiveXY 4 (xyCriticalField_T09 + ε))
          (attractiveXYDrift 4 (xyCriticalField_T09 + ε)) =
        scalarRate (attractiveXY 4 (xyCriticalField_T09 + ε))
          (attractiveXYDrift 4 (xyCriticalField_T09 + ε))) := 
  ⟨part1_T09, part2_T09, part3_T09, part4_T09⟩
end DGPS.Examples.AttractiveXY
