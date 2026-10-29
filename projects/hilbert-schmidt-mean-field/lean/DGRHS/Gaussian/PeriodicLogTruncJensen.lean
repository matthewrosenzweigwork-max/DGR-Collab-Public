import DGRHS.Gaussian.PeriodicLogTruncatedLaplace
import DGRHS.Gaussian.PeriodicConvolutionMultiplier
import DGRHS.Gaussian.PeriodicHeatMassControl
import DGRHS.Gaussian.PeriodicL1FourierUniqueness
import DGRHS.Gaussian.PeriodicLogKernelSections

/-!
Packet P11b, unit 2 (clause 2, step 1): the heat-shifted periodic LOG kernel is the convolution of the
exact kernel with the positive normalized periodic heat kernel,
`g_τ = P_τ ⋆ g` (`periodicLogTruncKernel_ae_eq_conv`), hence (Jensen, weights `P_τ ≥ 0`, `∫ P_τ = 1`)
`∫ |g_τ|^p ≤ ∫ |g|^p` uniformly in the heat shift `τ > 0`
(`periodicLogTruncKernel_integral_pow_le`).  This is the torus substitute for the Euclidean pointwise
short-range factorial-moment computation of `GaussianLogShortRangeFactorial`.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal Convolution
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The real periodic heat kernel with Fourier multiplier `exp(-τ ‖k‖²)`. -/
def periodicHeatDensity (τ : ℝ) (x : PeriodicTorus ι) : ℝ := (periodicGaussianHeat τ x).re

lemma periodicHeatDensity_continuous (τ : ℝ) (hτ : 0 < τ) :
    Continuous (periodicHeatDensity (ι := ι) τ) :=
  Complex.continuous_re.comp (periodicGaussianHeat_continuous τ hτ)

lemma periodicHeatDensity_nonneg (τ : ℝ) (hτ : 0 < τ) (x : PeriodicTorus ι) :
    0 ≤ periodicHeatDensity τ x := (periodicGaussianHeat_real_nonneg τ hτ x).1

lemma periodicHeatDensity_integrable (τ : ℝ) (hτ : 0 < τ) :
    Integrable (periodicHeatDensity (ι := ι) τ) (periodicHaar ι) :=
  (periodicHeatDensity_continuous τ hτ).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma periodicHeatDensity_integral (τ : ℝ) (hτ : 0 < τ) :
    ∫ x, periodicHeatDensity (ι := ι) τ x ∂periodicHaar ι = 1 :=
  periodicGaussianHeat_real_integral τ hτ

/-- Jensen's inequality for a nonnegative weight of total mass one: `|∫ P f|^p ≤ ∫ P |f|^p`. -/
lemma weighted_abs_pow_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (P f : α → ℝ) (hP0 : ∀ x, 0 ≤ P x) (hPm : Measurable P) (hP1 : ∫ x, P x ∂μ = 1)
    (hPi : Integrable P μ) (p : ℕ) (hp : 1 ≤ p)
    (hf : Integrable (fun t => P t * f t) μ) (hfp : Integrable (fun t => P t * |f t| ^ p) μ) :
    |∫ t, P t * f t ∂μ| ^ p ≤ ∫ t, P t * |f t| ^ p ∂μ := by
  set ν : Measure α := μ.withDensity (fun t => ENNReal.ofReal (P t)) with hν
  have hmeas : Measurable (fun t => ENNReal.ofReal (P t)) := ENNReal.measurable_ofReal.comp hPm
  have hlt : ∀ᵐ t ∂μ, ENNReal.ofReal (P t) < ∞ := Filter.Eventually.of_forall fun _ => by simp
  have htr (t : α) : (ENNReal.ofReal (P t)).toReal = P t := ENNReal.toReal_ofReal (hP0 t)
  have hprob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hPi (Filter.Eventually.of_forall hP0), hP1]
    simp
  have hint (g : α → ℝ) : ∫ t, g t ∂ν = ∫ t, P t * g t ∂μ := by
    rw [hν, integral_withDensity_eq_integral_toReal_smul hmeas hlt]
    simp only [htr, smul_eq_mul]
  have hiff (g : α → ℝ) (hg : Integrable (fun t => P t * g t) μ) : Integrable g ν := by
    rw [hν, integrable_withDensity_iff_integrable_smul' hmeas hlt]
    simpa only [htr, smul_eq_mul] using hg
  have hfabs : Integrable (fun t => P t * |f t|) μ := by
    have := hf.norm
    simpa only [norm_mul, Real.norm_of_nonneg (hP0 _), Real.norm_eq_abs] using this
  have hfν : Integrable f ν := hiff f hf
  have habsν : Integrable (fun t => |f t|) ν := hiff _ hfabs
  have hpν : Integrable (fun t => |f t| ^ p) ν := hiff _ hfp
  have h1 : |∫ t, f t ∂ν| ≤ ∫ t, |f t| ∂ν := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := ν) f
  have h2 : (∫ t, |f t| ∂ν) ^ p ≤ ∫ t, |f t| ^ p ∂ν :=
    (convexOn_pow p).map_integral_le (continuous_pow p).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun t => abs_nonneg (f t)) habsν hpν
  have h3 := (pow_le_pow_left₀ (abs_nonneg _) h1 p).trans h2
  rw [hint, hint] at h3
  exact h3

/-- The heat-shifted LOG kernel is a.e. the convolution `P_τ ⋆ g` of the exact kernel with the
positive normalized periodic heat kernel. -/
theorem periodicLogTruncKernel_ae_eq_conv (τ : ℝ) (hτ : 0 < τ) :
    periodicLogTruncKernel (ι := ι) τ =ᵐ[periodicHaar ι]
      (fun x => ∫ t, periodicHeatDensity τ t * periodicLogKernel (x - t) ∂periodicHaar ι) := by
  have ha := periodicLogTruncCoeff_nonneg (ι := ι) τ
  have hsum := periodicLogTruncCoeff_summable (ι := ι) τ hτ
  have hev := periodicLogTruncCoeff_neg (ι := ι) τ
  set F : PeriodicTorus ι → ℂ := periodicGaussianHeat τ with hFdef
  set G : PeriodicTorus ι → ℂ := fun x => (periodicLogKernel x : ℂ) with hGdef
  have hF : Integrable F (periodicHaar ι) := periodicGaussianHeat_integrable τ hτ
  have hG : Integrable G (periodicHaar ι) := periodicLogKernel_integrable.ofReal
  have hT : Integrable (fun x : PeriodicTorus ι => (periodicLogTruncKernel τ x : ℂ))
      (periodicHaar ι) :=
    ((periodicPositiveFourierKernel_continuous _ ha hsum).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).ofReal
  have hconv := hF.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hG
  have h := periodicL1_fourier_unique (fun x => (periodicLogTruncKernel τ x : ℂ))
    (F ⋆[ContinuousLinearMap.mul ℂ ℂ, periodicHaar ι] G) hT hconv (fun k => by
      rw [periodicPositiveFourierKernel_fourierCoeff _ ha hsum hev,
        periodic_mFourierCoeff_convolution hF hG k, hFdef, periodicGaussianHeat_fourierCoeff τ hτ k,
        hGdef, periodicLogKernel_fourierCoeff k, periodicLogFourierCoeff_eq_ofReal]
      unfold periodicLogTruncCoeff
      rw [show -τ * ‖periodicFrequencyVector k‖ ^ 2 = -(‖periodicFrequencyVector k‖ ^ 2 * τ) by ring]
      push_cast
      rfl)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (periodicGaussianHeat_continuous (ι := ι) τ hτ).continuousOn
  filter_upwards [h] with x hx
  have hx' := congrArg Complex.re hx
  rw [Complex.ofReal_re] at hx'
  rw [hx']
  have hGx : Integrable (fun t => G (x - t)) (periodicHaar ι) := hG.comp_sub_left x
  have hint : Integrable (fun t => F t * G (x - t)) (periodicHaar ι) :=
    hGx.bdd_mul (periodicGaussianHeat_continuous (ι := ι) τ hτ).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => hC t (Set.mem_univ t))
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  refine (integral_re hint).symm.trans ?_
  congr 1
  funext t
  simp [hFdef, hGdef, periodicHeatDensity, Complex.mul_re]

/-- Uniform `p`-th moment bound for the heat-shifted LOG kernel: `∫ |g_τ|^p ≤ ∫ |g|^p` for every
`τ > 0` (Jensen against the heat kernel). -/
theorem periodicLogTruncKernel_integral_pow_le (τ : ℝ) (hτ : 0 < τ) (p : ℕ) (hp : 1 ≤ p)
    (hI : Integrable (fun x => |periodicLogKernel (ι := ι) x| ^ p) (periodicHaar ι)) :
    ∫ x, |periodicLogTruncKernel (ι := ι) τ x| ^ p ∂periodicHaar ι ≤
      ∫ x, |periodicLogKernel (ι := ι) x| ^ p ∂periodicHaar ι := by
  set P : PeriodicTorus ι → ℝ := periodicHeatDensity τ with hPdef
  have hPc : Continuous P := periodicHeatDensity_continuous τ hτ
  have hP0 : ∀ x, 0 ≤ P x := periodicHeatDensity_nonneg τ hτ
  have hPi : Integrable P (periodicHaar ι) := periodicHeatDensity_integrable τ hτ
  have hP1 : ∫ x, P x ∂periodicHaar ι = 1 := periodicHeatDensity_integral τ hτ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hPc.continuousOn
  have hg := periodicLogKernel_integrable (ι := ι)
  have hgτ : Continuous (periodicLogTruncKernel (ι := ι) τ) :=
    periodicPositiveFourierKernel_continuous _ (periodicLogTruncCoeff_nonneg τ)
      (periodicLogTruncCoeff_summable τ hτ)
  have hLint : Integrable (fun x => |periodicLogTruncKernel (ι := ι) τ x| ^ p) (periodicHaar ι) :=
    ((hgτ.abs.pow p)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hconv := (periodicHeatDensity_integrable (ι := ι) τ hτ).integrable_convolution
    (ContinuousLinearMap.mul ℝ ℝ) hI
  have hpt : ∀ᵐ x ∂periodicHaar ι, |periodicLogTruncKernel (ι := ι) τ x| ^ p ≤
      (P ⋆[ContinuousLinearMap.mul ℝ ℝ, periodicHaar ι] (fun z => |periodicLogKernel (ι := ι) z| ^ p)) x := by
    filter_upwards [periodicLogTruncKernel_ae_eq_conv (ι := ι) τ hτ] with x hx
    rw [hx]
    have h1 : Integrable (fun t => P t * periodicLogKernel (ι := ι) (x - t)) (periodicHaar ι) :=
      (hg.comp_sub_left x).bdd_mul hPc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => by simpa using hC t (Set.mem_univ t)) |>.congr
        (Filter.Eventually.of_forall fun t => rfl)
    have h2 : Integrable (fun t => P t * |periodicLogKernel (ι := ι) (x - t)| ^ p) (periodicHaar ι) :=
      (hI.comp_sub_left x).bdd_mul hPc.aestronglyMeasurable
        (Filter.Eventually.of_forall fun t => by simpa using hC t (Set.mem_univ t)) |>.congr
        (Filter.Eventually.of_forall fun t => rfl)
    have := weighted_abs_pow_le (periodicHaar ι) P (fun t => periodicLogKernel (ι := ι) (x - t)) hP0
      hPc.measurable hP1 hPi p hp h1 h2
    simpa only [convolution_def, ContinuousLinearMap.mul_apply'] using this
  calc ∫ x, |periodicLogTruncKernel (ι := ι) τ x| ^ p ∂periodicHaar ι
      ≤ ∫ x, (P ⋆[ContinuousLinearMap.mul ℝ ℝ, periodicHaar ι]
          (fun z => |periodicLogKernel (ι := ι) z| ^ p)) x ∂periodicHaar ι :=
        integral_mono_ae hLint hconv hpt
    _ = (∫ x, P x ∂periodicHaar ι) * ∫ x, |periodicLogKernel (ι := ι) x| ^ p ∂periodicHaar ι := by
        rw [integral_convolution (ContinuousLinearMap.mul ℝ ℝ) hPi hI]
        rfl
    _ = _ := by rw [hP1, one_mul]

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicHeatDensity_nonneg
#print axioms DGRHS.Periodic.periodicHeatDensity_integral
#print axioms DGRHS.Periodic.weighted_abs_pow_le
#print axioms DGRHS.Periodic.periodicLogTruncKernel_ae_eq_conv
#print axioms DGRHS.Periodic.periodicLogTruncKernel_integral_pow_le
