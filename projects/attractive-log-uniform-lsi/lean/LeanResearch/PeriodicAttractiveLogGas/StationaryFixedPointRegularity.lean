import LeanResearch.PeriodicAttractiveLogGas.OccupationNearContraction
import LeanResearch.PeriodicAttractiveLogGas.GreenTorusIntegration
import LeanResearch.PeriodicAttractiveLogGas.Periodization
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! The regularity passage in the supplied source Corollary `cor:fixedpoint`.
The potential below is the existing actual Green convolution. The input is
the literal original-Green probability fixed-point equation, not a regularity
or differential-equation certificate. Checking and source correspondence are
recorded in `research/reviews/stationary-fixed-point-regularity-development.md`.
-/

noncomputable section
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal BigOperators ContDiff Convolution

namespace PeriodicAttractiveLogGas.StationaryFixedPointRegularity

open OccupationNearContraction

def normalizer (β : ℝ) (f : Torus → ℝ) : ℝ :=
  ∫ x, Real.exp (β * densityPotential f x) ∂torusMeasure

def representative (β : ℝ) (f : Torus → ℝ) (x : Torus) : ℝ :=
  Real.exp (β * densityPotential f x) / normalizer β f

def potentialBound (f : Torus → ℝ) : ℝ :=
  lpNorm f 4 torusMeasure *
    lpNorm regularGreenRepresentative GreenConditionalInfluence.conjugateExponent torusMeasure

theorem potentialBound_nonneg (f : Torus → ℝ) : 0 ≤ potentialBound f :=
  mul_nonneg lpNorm_nonneg lpNorm_nonneg

theorem scaled_potential_bound {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure)
    (β : ℝ) (x : Torus) : |β * densityPotential f x| ≤ |β| * potentialBound f := by
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (densityPotential_bound hf x) (abs_nonneg β)

theorem exponential_integrable {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure)
    (β : ℝ) : Integrable (fun x ↦ Real.exp (β * densityPotential f x)) torusMeasure :=
  integrable_continuous_torus torusMeasure
    (Real.continuous_exp.comp (continuous_const.mul (continuous_densityPotential hf)))

theorem normalizer_bounds {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure) (β : ℝ) :
    Real.exp (-(|β| * potentialBound f)) ≤ normalizer β f ∧
      normalizer β f ≤ Real.exp (|β| * potentialBound f) := by
  have hb (x : Torus) := abs_le.mp (scaled_potential_bound hf β x)
  constructor
  · have hh := integral_mono (integrable_const (Real.exp (-(|β| * potentialBound f))))
      (exponential_integrable hf β) (fun x ↦ Real.exp_le_exp.mpr (hb x).1)
    simpa only [integral_const, probReal_univ, one_smul, normalizer] using hh
  · have hh := integral_mono (exponential_integrable hf β)
      (integrable_const (Real.exp (|β| * potentialBound f)))
      (fun x ↦ Real.exp_le_exp.mpr (hb x).2)
    simpa only [integral_const, probReal_univ, one_smul, normalizer] using hh

theorem normalizer_pos {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure) (β : ℝ) :
    0 < normalizer β f := (Real.exp_pos _).trans_le (normalizer_bounds hf β).1

theorem continuous_representative {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure) (β : ℝ) :
    Continuous (representative β f) :=
  (Real.continuous_exp.comp (continuous_const.mul (continuous_densityPotential hf))).div_const _

theorem representative_pos {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure)
    (β : ℝ) (x : Torus) : 0 < representative β f x :=
  div_pos (Real.exp_pos _) (normalizer_pos hf β)

theorem representative_bounds {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure)
    (β : ℝ) (x : Torus) :
    Real.exp (-(|β| * potentialBound f)) / normalizer β f ≤ representative β f x ∧
      representative β f x ≤ Real.exp (|β| * potentialBound f) / normalizer β f := by
  have hb := abs_le.mp (scaled_potential_bound hf β x)
  exact ⟨div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hb.1) (normalizer_pos hf β).le,
    div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hb.2) (normalizer_pos hf β).le⟩

theorem representative_mass {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure) (β : ℝ) :
    (∫ x, representative β f x ∂torusMeasure) = 1 := by
  simp only [representative, integral_div]
  change normalizer β f / normalizer β f = 1
  exact div_self (normalizer_pos hf β).ne'

theorem original_fixedPoint_ae {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure) (β : ℝ)
    (hfix : f =ᵐ[torusMeasure] fun x ↦
      Real.exp (β * ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure) /
        (∫ z, Real.exp (β * ∫ y, greenRealRepresentative (z - y) * f y ∂torusMeasure)
          ∂torusMeasure)) :
    f =ᵐ[torusMeasure] representative β f := by
  change f =ᵐ[torusMeasure] fun x ↦
    Real.exp (β * densityPotential f x) / normalizer β f
  simp only [normalizer, densityPotential_eq_original hf]
  exact hfix

theorem representative_potential {f : Torus → ℝ} (β : ℝ)
    (hfix : f =ᵐ[torusMeasure] representative β f) :
    densityPotential (representative β f) = densityPotential f :=
  densityPotential_congr_ae hfix.symm

theorem green_translate_test (φ : SmoothPair 1) (y : Torus) :
    (∫ x, regularGreenRepresentative (x - y) * (-φ.laplacian.torusValue x)
      ∂torusMeasure) =
      (2 * Real.pi) * (φ.torusValue y - ∫ x, φ.torusValue x ∂torusMeasure) := by
  have hh := regularGreenRepresentative_weak_laplacian
    (φ.translateSub (singleConfiguration y))
  have hl (z : Torus) : (φ.translateSub (singleConfiguration y)).laplacian.torusValue z =
      φ.laplacian.torusValue (y - z) :=
    φ.translateSub_laplacian_value (singleConfiguration y) (singleConfiguration z)
  simp only [hl, SmoothPair.translateSub_torusValue, sub_zero,
    integral_sub_left_eq_self φ.torusValue torusMeasure y] at hh
  calc
    _ = ∫ z, regularGreenRepresentative ((y - z) - y) *
        (-φ.laplacian.torusValue (y - z)) ∂torusMeasure :=
      (integral_sub_left_eq_self
        (fun x ↦ regularGreenRepresentative (x - y) * (-φ.laplacian.torusValue x))
          torusMeasure y).symm
    _ = ∫ z, regularGreenRepresentative z * (-φ.laplacian.torusValue (y - z))
        ∂torusMeasure := by
      apply integral_congr_ae
      filter_upwards with z
      rw [show (y - z) - y = -z by abel, regularGreenRepresentative_even]
    _ = _ := hh

/-- The actual weak Poisson identity, with its original factor `2*pi`.
The test's Laplacian is the ordinary two-coordinate periodic Laplacian. -/
theorem potential_weak_poisson {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure)
    (hmass : (∫ x, f x ∂torusMeasure) = 1) (φ : SmoothPair 1) :
    (∫ x, densityPotential f x * (-φ.laplacian.torusValue x) ∂torusMeasure) =
      (2 * Real.pi) * (∫ x, (f x - 1) * φ.torusValue x ∂torusMeasure) := by
  have hfi : Integrable f torusMeasure := hf.integrable (by norm_num)
  have hj : Integrable (fun p : Torus × Torus ↦ f p.2 * regularGreenRepresentative (p.1 - p.2))
      (torusMeasure.prod torusMeasure) :=
    hfi.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) regularGreenRepresentative_integrable
  have hw : Integrable (fun p : Torus × Torus ↦
      (f p.2 * regularGreenRepresentative (p.1 - p.2)) * (-φ.laplacian.torusValue p.1))
      (torusMeasure.prod torusMeasure) :=
    hj.mul_bdd ((φ.laplacian.torusValue.continuous.neg.comp continuous_fst).aestronglyMeasurable)
      (Eventually.of_forall fun p ↦ by simpa only [norm_neg] using
        φ.laplacian.torusValue.norm_coe_le_norm p.1)
  have hφ := integrable_continuous_torus torusMeasure φ.torusValue.continuous
  have hfφ : Integrable (fun x ↦ f x * φ.torusValue x) torusMeasure :=
    hfi.mul_bdd φ.torusValue.continuous.aestronglyMeasurable
      (Eventually.of_forall φ.torusValue.norm_coe_le_norm)
  calc
    _ = ∫ x, ∫ y, (f y * regularGreenRepresentative (x - y)) *
        (-φ.laplacian.torusValue x) ∂torusMeasure ∂torusMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ (integral_mul_const _ _).symm
    _ = ∫ y, ∫ x, (f y * regularGreenRepresentative (x - y)) *
        (-φ.laplacian.torusValue x) ∂torusMeasure ∂torusMeasure := integral_integral_swap hw
    _ = ∫ y, f y * ((2 * Real.pi) *
        (φ.torusValue y - ∫ x, φ.torusValue x ∂torusMeasure)) ∂torusMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [mul_assoc, integral_const_mul, green_translate_test]
    _ = (2 * Real.pi) * ((∫ y, f y * φ.torusValue y ∂torusMeasure) -
        (∫ y, f y * (∫ x, φ.torusValue x ∂torusMeasure) ∂torusMeasure)) := by
      simp_rw [show ∀ y, f y * ((2 * Real.pi) *
          (φ.torusValue y - ∫ x, φ.torusValue x ∂torusMeasure)) =
        (2 * Real.pi) * (f y * φ.torusValue y -
          f y * (∫ x, φ.torusValue x ∂torusMeasure)) by intro y; ring]
      rw [integral_const_mul, integral_sub hfφ (hfi.mul_const _)]
    _ = (2 * Real.pi) * ((∫ y, f y * φ.torusValue y ∂torusMeasure) -
        ∫ x, φ.torusValue x ∂torusMeasure) := by rw [integral_mul_const, hmass, one_mul]
    _ = _ := by
      congr 1
      simp only [sub_mul, one_mul]
      exact (integral_sub hfφ hφ).symm

section ConvolutionSmoothness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A bounded continuous density multiplies the actual integrable kernel. -/
theorem integrable_density_smul (f : C(Torus, ℝ)) {g : Torus → E}
    (hg : Integrable g torusMeasure) (x : Torus) :
    Integrable (fun y ↦ f (x - y) • g y) torusMeasure := by
  have hc : Continuous (fun y : Torus ↦ f (x - y)) := by fun_prop
  apply (hg.norm.const_mul ‖f‖).mono' (hc.aestronglyMeasurable.smul hg.aestronglyMeasurable)
  filter_upwards with y
  change ‖f (x - y) • g y‖ ≤ ‖f‖ * ‖g y‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (norm_nonneg _)

theorem fundamentalBox_norm_le_two {y : PlanarSpace}
    (hy : y ∈ euclideanFundamentalBox 0) : ‖y‖ ≤ 2 := by
  have h0 : 0 < y 0 ∧ y 0 ≤ 1 := by simpa only [PiLp.zero_apply, zero_add, mem_Ioc] using hy 0 (mem_univ _)
  have h1 : 0 < y 1 ∧ y 1 ≤ 1 := by simpa only [PiLp.zero_apply, zero_add, mem_Ioc] using hy 1 (mem_univ _)
  have hn := EuclideanSpace.real_norm_sq_eq y
  simp only [Fin.sum_univ_two] at hn
  nlinarith [norm_nonneg y]

/-- An integrable torus kernel preserves every finite smoothness order of
the other factor. The proof uses the true Haar fundamental box and local
agreement with a compactly supported Euclidean convolution. -/
theorem contDiff_integral_density_smul [CompleteSpace E] (n : ℕ) (f : C(Torus, ℝ))
    (hf : ContDiff ℝ n (fun x : PlanarSpace ↦ f (torusQuotient x)))
    {g : Torus → E} (hg : Integrable g torusMeasure) :
    ContDiff ℝ n (fun x : PlanarSpace ↦
      ∫ y, f (torusQuotient x - y) • g y ∂torusMeasure) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  let B : Set PlanarSpace := euclideanFundamentalBox 0
  let K : PlanarSpace → E := B.indicator (fun y ↦ g (torusQuotient y))
  have hB : MeasurableSet B := measurableSet_euclideanFundamentalBox _
  have hK : Integrable K volume := (integrable_indicator_iff hB).mpr
    ((measurePreserving_torusQuotient_box 0).integrable_comp_of_integrable hg)
  let χ : ContDiffBump x := ⟨3, 4, by norm_num, by norm_num⟩
  let H : PlanarSpace → ℝ := fun y ↦ χ y * f (torusQuotient y)
  have hH : ContDiff ℝ n H := χ.contDiff.mul hf
  have hHc : HasCompactSupport H := χ.hasCompactSupport.mul_right
  let L : E →L[ℝ] ℝ →L[ℝ] E := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have hs := hHc.contDiff_convolution_right L hK.locallyIntegrable hH
  apply hs.contDiffAt.congr_of_eventuallyEq
  filter_upwards [ball_mem_nhds x (by norm_num : (0 : ℝ) < 1)] with z hz
  symm
  change (∫ y, H (z - y) • K y ∂volume) =
    ∫ y, f (torusQuotient z - y) • g y ∂torusMeasure
  have he : (fun y ↦ H (z - y) • K y) =
      B.indicator (fun y ↦ f (torusQuotient z - torusQuotient y) • g (torusQuotient y)) := by
    funext y
    by_cases hy : y ∈ B
    · have hclose : z - y ∈ closedBall x 3 := by
        rw [mem_closedBall, dist_eq_norm]
        have hzy : ‖z - y - x‖ ≤ ‖z - x‖ + ‖y‖ := by
          rw [show z - y - x = (z - x) - y by abel]
          exact norm_sub_le _ _
        have hz' : ‖z - x‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hz
        have hy' := fundamentalBox_norm_le_two hy
        linarith
      have hχ : χ (z - y) = 1 := χ.one_of_mem_closedBall hclose
      simp only [H, K, indicator_of_mem hy, hχ, one_mul, torusQuotient_sub]
    · simp only [K, indicator_of_notMem hy, smul_zero]
  rw [he, integral_indicator hB]
  exact TorusPatchDensity.integral_comp_ae (measurePreserving_torusQuotient_box 0)
    (integrable_density_smul f hg (torusQuotient z)).aestronglyMeasurable

theorem norm_integral_density_smul_sub_le [CompleteSpace E] (f : C(Torus, ℝ)) {g h : Torus → E}
    (hg : Integrable g torusMeasure) (hh : Integrable h torusMeasure) (x : Torus) :
    ‖(∫ y, f (x - y) • g y ∂torusMeasure) -
      (∫ y, f (x - y) • h y ∂torusMeasure)‖ ≤
        ‖f‖ * ∫ y, ‖g y - h y‖ ∂torusMeasure := by
  have hi := integrable_density_smul f (hg.sub hh) x
  calc
    _ = ‖∫ y, f (x - y) • (g y - h y) ∂torusMeasure‖ := by
      simp only [smul_sub]
      rw [integral_sub (integrable_density_smul f hg x) (integrable_density_smul f hh x)]
    _ ≤ ∫ y, ‖f (x - y) • (g y - h y)‖ ∂torusMeasure := norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖f‖ * ‖g y - h y‖ ∂torusMeasure := by
      apply integral_mono hi.norm ((hg.sub hh).norm.const_mul ‖f‖)
      intro y
      change ‖f (x - y) • (g y - h y)‖ ≤ ‖f‖ * ‖g y - h y‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (f.norm_coe_le_norm _) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem integral_density_smul_swap (f : C(Torus, ℝ)) (g : Torus → E) (x : Torus) :
    (∫ y, f y • g (x - y) ∂torusMeasure) =
      ∫ y, f (x - y) • g y ∂torusMeasure := by
  have hh := integral_sub_left_eq_self (fun y ↦ f y • g (x - y)) torusMeasure x
  simpa only [sub_sub_cancel] using hh.symm

end ConvolutionSmoothness

theorem integrable_greenDifferential : Integrable greenDifferential torusMeasure := by
  apply integrable_greenGradient.norm.mono' measurable_greenDifferential.aestronglyMeasurable
  exact Eventually.of_forall fun z ↦ (norm_greenGradient z).symm.le

theorem integrable_regularizedDifferential (ε : ℝ) (hε : 0 < ε) (hs : ε ≤ 1 / 16) :
    Integrable (regularizedGreenDifferential ε hε) torusMeasure := by
  let A : C(Torus, PlanarSpace →L[ℝ] ℝ) :=
    ⟨regularizedGreenDifferential ε hε, continuous_regularizedGreenDifferential ε hε hs⟩
  exact (integrable_const ‖A‖).mono' A.continuous.aestronglyMeasurable
    (Eventually.of_forall A.norm_coe_le_norm)

/-- Real L1 convergence of the genuine regularized differentials. The
singular Hessian is never used as an integrable majorant. -/
theorem tendsto_integral_differential_error
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hs : ∀ n, ε n ≤ 1 / 16)
    (ht : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z, ‖regularizedGreenDifferential (ε n) (hε n) z -
      greenDifferential z‖ ∂torusMeasure) atTop (𝓝 0) := by
  let M : Torus → ℝ := fun z ↦ regularizedGradientConstant / torusEuclideanNorm z +
    ‖greenGradient z‖
  have hM : Integrable M torusMeasure := by
    simpa only [M, div_eq_mul_inv, Pi.add_apply] using!
      (integrable_torusEuclideanNorm_inv.const_mul regularizedGradientConstant).add
        integrable_greenGradient.norm
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun z ↦ ‖regularizedGreenDifferential (ε n) (hε n) z - greenDifferential z‖)
      torusMeasure :=
    ((continuous_regularizedGreenDifferential (ε n) (hε n) (hs n)).aestronglyMeasurable.sub
      measurable_greenDifferential.aestronglyMeasurable).norm
  have hb (n : ℕ) : ∀ᵐ z ∂torusMeasure,
      ‖‖regularizedGreenDifferential (ε n) (hε n) z - greenDifferential z‖‖ ≤ M z := by
    filter_upwards [torusMeasure.ae_ne (0 : Torus)] with z hz
    rw [norm_norm]
    apply (norm_sub_le _ _).trans
    rw [← norm_regularizedGreenGradient, ← norm_greenGradient]
    exact add_le_add (regularizedGradientConstant_bound (ε n) (hε n) (hs n) hz) le_rfl
  have hp : ∀ᵐ z ∂torusMeasure, Tendsto
      (fun n ↦ ‖regularizedGreenDifferential (ε n) (hε n) z - greenDifferential z‖)
      atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [torusMeasure.ae_ne (0 : Torus)] with z hz
    have he := eventually_regularizedGreenDifferential_eq hε hs ht hz
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    simp only [hn, sub_self, norm_zero]
  simpa only [integral_zero] using
    tendsto_integral_of_dominated_convergence M hm hM hb hp

def potentialDifferential (f : C(Torus, ℝ)) (x : Torus) : PlanarSpace →L[ℝ] ℝ :=
  ∫ y, f (x - y) • greenDifferential y ∂torusMeasure

theorem tendstoUniformly_regularizedPotential_differential (f : C(Torus, ℝ))
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hs : ∀ n, ε n ≤ 1 / 16)
    (ht : Tendsto ε atTop (𝓝 0)) :
    TendstoUniformly
      (fun n (x : PlanarSpace) ↦ ∫ y, f y •
        regularizedGreenDifferential (ε n) (hε n) (torusQuotient x - y) ∂torusMeasure)
      (fun x ↦ potentialDifferential f (torusQuotient x)) atTop := by
  have he := (tendsto_integral_differential_error ε hε hs ht).const_mul ‖f‖
  simp only [mul_zero] at he
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  filter_upwards [he.eventually (gt_mem_nhds hδ)] with n hn
  intro x
  rw [dist_eq_norm, norm_sub_rev]
  change ‖(∫ y, f y • regularizedGreenDifferential (ε n) (hε n)
    (torusQuotient x - y) ∂torusMeasure) -
      (∫ y, f (torusQuotient x - y) • greenDifferential y ∂torusMeasure)‖ < δ
  rw [integral_density_smul_swap]
  exact (norm_integral_density_smul_sub_le f
    (integrable_regularizedDifferential (ε n) (hε n) (hs n))
      integrable_greenDifferential (torusQuotient x)).trans_lt hn

/-- The genuine first derivative of the potential of a continuous density,
proved by uniform convergence of the actual regularized derivatives. -/
theorem hasFDerivAt_densityPotential (f : C(Torus, ℝ)) (x : PlanarSpace) :
    HasFDerivAt (fun w : PlanarSpace ↦ densityPotential f (torusQuotient w))
      (potentialDifferential f (torusQuotient x)) x := by
  let ε : ℕ → ℝ := fun n ↦ (1 / 16 : ℝ) * (1 / ((n : ℝ) + 1))
  have hε (n : ℕ) : 0 < ε n := by dsimp only [ε]; positivity
  have hs (n : ℕ) : ε n ≤ 1 / 16 := by
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
      (le_add_of_nonneg_left (Nat.cast_nonneg n))
    dsimp only [ε]
    nlinarith
  have ht : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 16 : ℝ)
  have hf : MemLp f 4 torusMeasure := ContinuousMap.memLp (μ := torusMeasure) ℝ f
  exact hasFDerivAt_of_tendstoUniformly
    (tendstoUniformly_regularizedPotential_differential f ε hε hs ht)
    (fun n w ↦ OccupationNearContraction.hasFDerivAt_regularizedPotential hf (ε n) (hε n) (hs n) w)
    (fun w ↦ tendsto_regularizedPotential hf ε hε hs ht (torusQuotient w)) x

/-- Each finite order follows from the preceding order of the actual
exponential density and the integrable first Green differential. -/
theorem contDiff_densityPotential_of_fixedPoint {f : Torus → ℝ}
    (hf : MemLp f 4 torusMeasure) (β : ℝ)
    (hfix : f =ᵐ[torusMeasure] representative β f) :
    ContDiff ℝ ∞ (fun x : PlanarSpace ↦ densityPotential f (torusQuotient x)) := by
  let F : C(Torus, ℝ) := ⟨representative β f, continuous_representative hf β⟩
  have hp : densityPotential F = densityPotential f := representative_potential β hfix
  have hd (x : PlanarSpace) :
      HasFDerivAt (fun w : PlanarSpace ↦ densityPotential f (torusQuotient w))
        (potentialDifferential F (torusQuotient x)) x := by
    have hh := hasFDerivAt_densityPotential F x
    rw [hp] at hh
    exact hh
  have hfd : fderiv ℝ (fun w : PlanarSpace ↦ densityPotential f (torusQuotient w)) =
      fun x ↦ potentialDifferential F (torusQuotient x) := funext fun x ↦ (hd x).fderiv
  apply contDiff_infty.mpr
  intro n
  induction n with
  | zero =>
    exact contDiff_zero.mpr
      ((continuous_densityPotential hf).comp isOpenQuotientMap_torusQuotient.continuous)
  | succ n ih =>
    have hF : ContDiff ℝ n (fun x : PlanarSpace ↦ F (torusQuotient x)) := by
      change ContDiff ℝ n (fun x : PlanarSpace ↦
        Real.exp (β * densityPotential f (torusQuotient x)) / normalizer β f)
      exact (Real.contDiff_exp.comp (contDiff_const.mul ih)).div_const _
    have hD := contDiff_integral_density_smul n F hF integrable_greenDifferential
    have hsucc : ContDiff ℝ ((n : ℕ∞ω) + 1)
        (fun w : PlanarSpace ↦ densityPotential f (torusQuotient w)) := by
      apply contDiff_succ_iff_fderiv.mpr
      refine ⟨fun x ↦ (hd x).differentiableAt, ?_, ?_⟩
      · simp
      · rw [hfd]
        exact hD
    simpa only [Nat.cast_add, Nat.cast_one] using hsucc

theorem contDiff_representative_of_fixedPoint {f : Torus → ℝ}
    (hf : MemLp f 4 torusMeasure) (β : ℝ)
    (hfix : f =ᵐ[torusMeasure] representative β f) :
    ContDiff ℝ ∞ (fun x : PlanarSpace ↦ representative β f (torusQuotient x)) := by
  exact (Real.contDiff_exp.comp
    (contDiff_const.mul (contDiff_densityPotential_of_fixedPoint hf β hfix))).div_const _

theorem torus_negativeLaplacian_selfAdjoint (f g : SmoothPair 1) :
    (∫ x, f.torusValue x * (-g.laplacian.torusValue x) ∂torusMeasure) =
      ∫ x, (-f.laplacian.torusValue x) * g.torusValue x ∂torusMeasure := by
  have hh := f.integral_laplacian_selfAdjoint g
  rw [integral_reference_one_eq_torus _ (by unfold singleConfiguration; fun_prop),
    integral_reference_one_eq_torus _ (by unfold singleConfiguration; fun_prop)] at hh
  change (∫ x, g.torusValue x * f.laplacian.torusValue x ∂torusMeasure) =
    ∫ x, f.torusValue x * g.laplacian.torusValue x ∂torusMeasure at hh
  simp only [mul_neg, neg_mul, integral_neg, mul_comm (f.laplacian.torusValue _) (g.torusValue _)]
  exact congrArg Neg.neg hh.symm

theorem contDiff_torusValue_lift (P : SmoothPair 1) :
    ContDiff ℝ ∞ (fun x : PlanarSpace ↦ P.torusValue (torusQuotient x)) := by
  have hh : ContDiff ℝ ∞
      ((fun y : Gradient 1 ↦ P.value (configurationQuotient 1 y)) ∘
        singleParticleCoordinatesL) := P.smooth.comp singleParticleCoordinatesL.contDiff
  simpa only [Function.comp_def, singleParticleCoordinatesL_apply,
    configurationQuotient_singleParticleCoordinates, SmoothPair.torusValue,
    ContinuousMap.coe_mk] using! hh

theorem poisson_pointwise_of_smooth_weak (P : SmoothPair 1) (H : C(Torus, ℝ))
    (hH : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ H (torusQuotient x)))
    (hweak : ∀ φ : SmoothPair 1,
      (∫ x, P.torusValue x * (-φ.laplacian.torusValue x) ∂torusMeasure) =
        ∫ x, H x * φ.torusValue x ∂torusMeasure) :
    ∀ x, -P.laplacian.torusValue x = H x := by
  let r : C(Torus, ℝ) :=
    ⟨fun x ↦ -P.laplacian.torusValue x - H x,
      P.laplacian.torusValue.continuous.neg.sub H.continuous⟩
  have hPL : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ P.laplacian.torusValue (torusQuotient x)) :=
    contDiff_torusValue_lift P.laplacian
  have hr : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ r (torusQuotient x)) :=
    hPL.neg.sub hH
  let R : SmoothPair 1 := SmoothPair.ofTorusContDiffLift r hr
  have hw := hweak R
  have hp := torus_negativeLaplacian_selfAdjoint P R
  change (∫ x, P.torusValue x * (-R.laplacian.torusValue x) ∂torusMeasure) =
    ∫ x, (-P.laplacian.torusValue x) * r x ∂torusMeasure at hp
  rw [hp] at hw
  change (∫ x, (-P.laplacian.torusValue x) * r x ∂torusMeasure) =
    ∫ x, H x * r x ∂torusMeasure at hw
  have hA : Integrable (fun x ↦ (-P.laplacian.torusValue x) * r x) torusMeasure :=
    integrable_continuous_torus torusMeasure (P.laplacian.torusValue.continuous.neg.mul r.continuous)
  have hB : Integrable (fun x ↦ H x * r x) torusMeasure :=
    integrable_continuous_torus torusMeasure (H.continuous.mul r.continuous)
  have hsq : (∫ x, r x ^ 2 ∂torusMeasure) = 0 := by
    calc
      _ = ∫ x, ((-P.laplacian.torusValue x) * r x -
          H x * r x) ∂torusMeasure := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x ↦ by dsimp only [r, ContinuousMap.coe_mk]; ring
      _ = (∫ x, (-P.laplacian.torusValue x) * r x ∂torusMeasure) -
          (∫ x, H x * r x ∂torusMeasure) := integral_sub hA hB
      _ = 0 := sub_eq_zero.mpr hw
  have hae : (fun x ↦ r x ^ 2) =ᵐ[torusMeasure] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg (r x))
      (integrable_continuous_torus torusMeasure (r.continuous.pow 2))).mp hsq
  have hr0 : (r : Torus → ℝ) =ᵐ[torusMeasure] (fun _ ↦ 0) := by
    filter_upwards [hae] with x hx
    change r x ^ 2 = 0 at hx
    exact sq_eq_zero_iff.mp hx
  have heq : (r : Torus → ℝ) = fun _ ↦ 0 :=
    (r.continuous.ae_eq_iff_eq (μ := torusMeasure) continuous_const).mp hr0
  intro x
  have hh := congrFun heq x
  change -P.laplacian.torusValue x - H x = 0 at hh
  exact sub_eq_zero.mp hh

/-- The actual weak equation is upgraded to the pointwise ordinary
Laplacian by the preceding smooth-residual argument. -/
theorem fixedPoint_poisson_pointwise {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure)
    (hmass : (∫ x, f x ∂torusMeasure) = 1) (β : ℝ)
    (hfix : f =ᵐ[torusMeasure] representative β f) :
    let U : C(Torus, ℝ) := ⟨densityPotential f, continuous_densityPotential hf⟩
    let hU := contDiff_densityPotential_of_fixedPoint hf β hfix
    ∀ x, torusNegativeLaplacian U hU x =
      (2 * Real.pi) * (representative β f x - 1) := by
  let U : C(Torus, ℝ) := ⟨densityPotential f, continuous_densityPotential hf⟩
  let hU := contDiff_densityPotential_of_fixedPoint hf β hfix
  let P : SmoothPair 1 := SmoothPair.ofTorusContDiffLift U hU
  let H : C(Torus, ℝ) := ⟨fun x ↦ (2 * Real.pi) * (representative β f x - 1),
    continuous_const.mul ((continuous_representative hf β).sub continuous_const)⟩
  have hH : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ H (torusQuotient x)) :=
    contDiff_const.mul ((contDiff_representative_of_fixedPoint hf β hfix).sub contDiff_const)
  apply poisson_pointwise_of_smooth_weak P H hH
  intro φ
  have hh := potential_weak_poisson hf hmass φ
  change (∫ x, densityPotential f x * (-φ.laplacian.torusValue x) ∂torusMeasure) =
    ∫ x, ((2 * Real.pi) * (representative β f x - 1)) * φ.torusValue x ∂torusMeasure
  rw [hh]
  calc
    _ = (2 * Real.pi) * (∫ x, (representative β f x - 1) * φ.torusValue x ∂torusMeasure) := by
      congr 1
      apply integral_congr_ae
      exact hfix.mono fun x hx ↦ by
        change (f x - 1) * φ.torusValue x = (representative β f x - 1) * φ.torusValue x
        rw [hx]
    _ = _ := by simp only [mul_assoc, integral_const_mul]

def solution (β : ℝ) (f : Torus → ℝ) (x : Torus) : ℝ :=
  β * densityPotential f x

theorem continuous_solution {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure) (β : ℝ) :
    Continuous (solution β f) := continuous_const.mul (continuous_densityPotential hf)

theorem contDiff_solution_of_fixedPoint {f : Torus → ℝ}
    (hf : MemLp f 4 torusMeasure) (β : ℝ)
    (hfix : f =ᵐ[torusMeasure] representative β f) :
    ContDiff ℝ ∞ (fun x : PlanarSpace ↦ solution β f (torusQuotient x)) :=
  contDiff_const.mul (contDiff_densityPotential_of_fixedPoint hf β hfix)

/-- The normalized mean-field equation for the actual scaled Green potential.
The weak identity used by the intermediate helper is derived here from the
original Green Poisson identity, including the mass-one correction. -/
theorem fixedPoint_meanField_pointwise {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure)
    (hmass : (∫ x, f x ∂torusMeasure) = 1) (β : ℝ)
    (hfix : f =ᵐ[torusMeasure] representative β f) :
    let u : C(Torus, ℝ) := ⟨solution β f, continuous_solution hf β⟩
    let hu := contDiff_solution_of_fixedPoint hf β hfix
    ∀ x, torusNegativeLaplacian u hu x =
      (2 * Real.pi * β) * (Real.exp (u x) /
        (∫ z, Real.exp (u z) ∂torusMeasure) - 1) := by
  let u : C(Torus, ℝ) := ⟨solution β f, continuous_solution hf β⟩
  let hu := contDiff_solution_of_fixedPoint hf β hfix
  let P : SmoothPair 1 := SmoothPair.ofTorusContDiffLift u hu
  let H : C(Torus, ℝ) := ⟨fun x ↦ (2 * Real.pi * β) * (representative β f x - 1),
    continuous_const.mul ((continuous_representative hf β).sub continuous_const)⟩
  have hH : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ H (torusQuotient x)) :=
    contDiff_const.mul ((contDiff_representative_of_fixedPoint hf β hfix).sub contDiff_const)
  apply poisson_pointwise_of_smooth_weak P H hH
  intro φ
  have hh := potential_weak_poisson hf hmass φ
  have hi : (∫ x, (f x - 1) * φ.torusValue x ∂torusMeasure) =
      ∫ x, (representative β f x - 1) * φ.torusValue x ∂torusMeasure := by
    apply integral_congr_ae
    exact hfix.mono fun x hx ↦ by
      change (f x - 1) * φ.torusValue x = (representative β f x - 1) * φ.torusValue x
      rw [hx]
  change (∫ x, (β * densityPotential f x) * (-φ.laplacian.torusValue x) ∂torusMeasure) =
    ∫ x, ((2 * Real.pi * β) * (representative β f x - 1)) * φ.torusValue x ∂torusMeasure
  simp only [mul_assoc, integral_const_mul]
  rw [hh, hi]
  ring

/-- The preceding torus identity is literally the ordinary two-dimensional
Laplacian equation on the periodic Euclidean cover. -/
theorem fixedPoint_meanField_lift {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure)
    (hmass : (∫ x, f x ∂torusMeasure) = 1) (β : ℝ)
    (hfix : f =ᵐ[torusMeasure] representative β f) (x : PlanarSpace) :
    Laplacian.laplacian (fun y : PlanarSpace ↦ solution β f (torusQuotient y)) x +
      (2 * Real.pi * β) * (Real.exp (solution β f (torusQuotient x)) /
        (∫ z, Real.exp (solution β f z) ∂torusMeasure) - 1) = 0 := by
  let u : C(Torus, ℝ) := ⟨solution β f, continuous_solution hf β⟩
  let hu := contDiff_solution_of_fixedPoint hf β hfix
  have hh := fixedPoint_meanField_pointwise hf hmass β hfix (torusQuotient x)
  have hl := torusNegativeLaplacian_lift_eq u hu x
  change torusNegativeLaplacian u hu (torusQuotient x) = _ at hh
  rw [hl] at hh
  change -Laplacian.laplacian (fun y : PlanarSpace ↦ solution β f (torusQuotient y)) x =
    (2 * Real.pi * β) * (Real.exp (solution β f (torusQuotient x)) /
      (∫ z, Real.exp (solution β f z) ∂torusMeasure) - 1) at hh
  linarith only [hh]

theorem source_parameter_range {β : ℝ} (hβ : 0 ≤ β) (hβ4 : β ≤ 4) :
    0 ≤ 2 * Real.pi * β ∧ 2 * Real.pi * β ≤ 8 * Real.pi := by
  constructor
  · exact mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hβ
  · nlinarith [Real.pi_pos]

@[simp] theorem representative_zero (f : Torus → ℝ) (x : Torus) :
    representative 0 f x = 1 := by
  simp [representative, normalizer]

theorem original_fixedPoint_zero {f : Torus → ℝ}
    (hfix : f =ᵐ[torusMeasure] fun x ↦
      Real.exp ((0 : ℝ) * ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure) /
        (∫ z, Real.exp ((0 : ℝ) * ∫ y, greenRealRepresentative (z - y) * f y ∂torusMeasure)
          ∂torusMeasure)) :
    f =ᵐ[torusMeasure] (fun _ ↦ 1) := by
  simpa only [zero_mul, Real.exp_zero, integral_const, probReal_univ, one_smul, div_one]
    using hfix

/-- The complete source regularity passage from the literal original-Green
L4 probability fixed point. No differential or smoothness premise is imposed
on the input. Stationary uniqueness is a separate theorem. -/
theorem original_fixedPoint_regularity {f : Torus → ℝ}
    (hf : MemLp f 4 torusMeasure) (hmass : (∫ x, f x ∂torusMeasure) = 1)
    {β : ℝ} (hβ : 0 ≤ β) (hβ4 : β ≤ 4)
    (hfix : f =ᵐ[torusMeasure] fun x ↦
      Real.exp (β * ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure) /
        (∫ z, Real.exp (β * ∫ y, greenRealRepresentative (z - y) * f y ∂torusMeasure)
          ∂torusMeasure)) :
    ∃ U u r : C(Torus, ℝ),
      ∃ hU : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ U (torusQuotient x)),
      ∃ hu : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ u (torusQuotient x)),
      ContDiff ℝ ∞ (fun x : PlanarSpace ↦ r (torusQuotient x)) ∧
      f =ᵐ[torusMeasure] (r : Torus → ℝ) ∧
      (∀ x, U x = ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure) ∧
      (∀ x, u x = β * U x) ∧
      (∀ x, r x = Real.exp (u x) / (∫ z, Real.exp (u z) ∂torusMeasure)) ∧
      (∫ x, r x ∂torusMeasure) = 1 ∧
      (∀ x, 0 < r x) ∧
      (∃ m M : ℝ, 0 < m ∧ ∀ x, m ≤ r x ∧ r x ≤ M) ∧
      (∀ x, torusNegativeLaplacian U hU x = (2 * Real.pi) * (r x - 1)) ∧
      (∀ x, torusNegativeLaplacian u hu x = (2 * Real.pi * β) * (r x - 1)) ∧
      (0 ≤ 2 * Real.pi * β ∧ 2 * Real.pi * β ≤ 8 * Real.pi) := by
  have he := original_fixedPoint_ae hf β hfix
  let U : C(Torus, ℝ) := ⟨densityPotential f, continuous_densityPotential hf⟩
  let u : C(Torus, ℝ) := ⟨solution β f, continuous_solution hf β⟩
  let r : C(Torus, ℝ) := ⟨representative β f, continuous_representative hf β⟩
  have hU : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ U (torusQuotient x)) :=
    contDiff_densityPotential_of_fixedPoint hf β he
  have hu : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ u (torusQuotient x)) :=
    contDiff_solution_of_fixedPoint hf β he
  refine ⟨U, u, r, hU, hu, contDiff_representative_of_fixedPoint hf β he, he,
    densityPotential_eq_original hf, (fun _ ↦ rfl), (fun _ ↦ rfl),
    representative_mass hf β, representative_pos hf β, ?_, ?_, ?_, source_parameter_range hβ hβ4⟩
  · refine ⟨Real.exp (-(|β| * potentialBound f)) / normalizer β f,
      Real.exp (|β| * potentialBound f) / normalizer β f,
      div_pos (Real.exp_pos _) (normalizer_pos hf β), ?_⟩
    exact representative_bounds hf β
  · exact fixedPoint_poisson_pointwise hf hmass β he
  · exact fixedPoint_meanField_pointwise hf hmass β he

end PeriodicAttractiveLogGas.StationaryFixedPointRegularity
