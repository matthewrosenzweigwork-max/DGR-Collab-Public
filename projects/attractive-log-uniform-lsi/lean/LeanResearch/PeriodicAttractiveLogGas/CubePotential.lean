import LeanResearch.PeriodicAttractiveLogGas.EuclideanCubeWeight
import LeanResearch.Imported.TauCetiAppendix.Analysis.Sobolev.Poincare.Potential
import LeanResearch.Imported.TauCetiAppendix.MeasureTheory.Integral.NormRpow

/-! Convex-domain segment averaging on the actual closed cube, as used
in source Lemma fixed-weighted-PI. The lower-integral argument below adapts
the attributed Apache-2.0 Tau Ceti proof of Gilbarg--Trudinger Lemma 7.16
at the public commit recorded in research/runs; only the closed-domain
and globally C1 formulation changes. No potential estimate is assumed. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Module
open scoped ENNReal NNReal BigOperators Topology
namespace PeriodicAttractiveLogGas.CubePotential
open PhysicalCubes ImportedTauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- The integrated segment inequality also holds on a closed convex
set when the observable is genuinely C1 on the whole ambient space. -/
theorem integrated_oscillation {S : Set E} (hS : MeasurableSet S) (hc : Convex ℝ S)
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) {x : E} (hx : x ∈ S)
    {D : ℝ} (hD : S ⊆ closedBall x D) :
    (∫⁻ y in S, ‖u x - u y‖ₑ ∂μ) ≤
      ENNReal.ofReal (D ^ finrank ℝ E / finrank ℝ E) *
        ∫⁻ y in S, ‖fderiv ℝ u y‖ₑ * ‖x - y‖ₑ ^ (1 - (finrank ℝ E : ℝ)) ∂μ := by
  classical
  let g : E → ℝ≥0∞ := S.indicator (fun y => ‖fderiv ℝ u y‖ₑ)
  have hg : Measurable g := (measurable_fderiv ℝ u).enorm.indicator hS
  have hfc : Continuous (fderiv ℝ u) := hu.continuous_fderiv (by norm_num)
  have hseg (y : E) (hy : y ∈ S) :
      ‖u x - u y‖ₑ ≤ (∫⁻ t in Ioc (0 : ℝ) 1, g (x + t • (y - x))) * ‖x - y‖ₑ := by
    have hmem (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : x + t • (y - x) ∈ S :=
      (hc.starConvex hx).add_smul_sub_mem hy ht.1 ht.2
    have hh := enorm_sub_le_lintegral_enorm_fderiv_apply (u := u) x (y - x)
      (fun _ _ => hu.differentiable (by norm_num) _) (by
        exact ((hfc.comp (by fun_prop)).clm_apply continuous_const).continuousOn)
    rw [add_sub_cancel, enorm_sub_rev] at hh
    rw [← lintegral_mul_const' _ _ enorm_ne_top, setLIntegral_congr Ioc_ae_eq_Icc]
    apply hh.trans
    apply setLIntegral_mono' measurableSet_Icc
    intro t ht
    simp only [g, indicator_of_mem (hmem t ht), enorm_sub_rev x y]
    exact ContinuousLinearMap.le_opENorm _ _
  calc
    _ ≤ ∫⁻ y in S, (∫⁻ t in Ioc (0 : ℝ) 1, g (x + t • (y - x))) * ‖x - y‖ₑ ∂μ :=
      setLIntegral_mono' hS hseg
    _ ≤ ∫⁻ y in closedBall x D,
        (∫⁻ t in Ioc (0 : ℝ) 1, g (x + t • (y - x))) * ‖x - y‖ₑ ∂μ :=
      lintegral_mono_set hD
    _ ≤ _ := setLIntegral_closedBall_lintegral_segment_le hg x D
    _ = _ := by
      rw [← lintegral_indicator hS]
      simp only [g, indicator_mul_left]

/-- The source pointwise potential estimate, including all boundary
points of the closed convex averaging set. -/
theorem mean_oscillation {S : Set E} (hS : IsCompact S) (hc : Convex ℝ S)
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) {x : E} (hx : x ∈ S)
    {D : ℝ} (hD : S ⊆ closedBall x D) (hS₀ : μ S ≠ 0) :
    ‖u x - ⨍ y in S, u y ∂μ‖ₑ ≤
      ENNReal.ofReal (D ^ finrank ℝ E / finrank ℝ E) / μ S *
        ∫⁻ y in S, ‖fderiv ℝ u y‖ₑ * ‖x - y‖ₑ ^ (1 - (finrank ℝ E : ℝ)) ∂μ := by
  have hS_top : μ S ≠ ∞ := hS.measure_lt_top.ne
  have hu_int : IntegrableOn u S μ := hu.continuous.continuousOn.integrableOn_compact hS
  have hdiff : IntegrableOn (fun y => u x - u y) S μ :=
    (integrableOn_const (C := u x) hS_top).sub hu_int
  have hmean : u x - ⨍ y in S, u y ∂μ = ⨍ y in S, (u x - u y) ∂μ := by
    rw [setAverage_fun_sub (integrableOn_const (C := u x) hS_top) hu_int,
      setAverage_const hS₀ hS_top]
  have hcore := integrated_oscillation (μ := μ) hS.measurableSet hc hu hx hD
  rw [ENNReal.div_eq_inv_mul, mul_assoc]
  calc
    _ = ‖(μ.real S)⁻¹ • ∫ y in S, u x - u y ∂μ‖ₑ := by rw [hmean, setAverage_eq]
    _ ≤ (μ S)⁻¹ * ∫⁻ y in S, ‖u x - u y‖ₑ ∂μ := by
      rw [enorm_smul]
      gcongr
      · rw [Real.enorm_of_nonneg (inv_nonneg.mpr measureReal_nonneg),
          ENNReal.ofReal_inv_of_pos (by rw [measureReal_def]; exact ENNReal.toReal_pos hS₀ hS_top),
          ofReal_measureReal hS_top]
      · exact enorm_integral_le_lintegral_enorm _
    _ ≤ _ := by gcongr

end PeriodicAttractiveLogGas.CubePotential
