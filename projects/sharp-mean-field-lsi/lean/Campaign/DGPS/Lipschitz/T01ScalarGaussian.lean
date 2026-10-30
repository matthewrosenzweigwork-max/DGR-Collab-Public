import DGPS.Lipschitz.T01GaussianPerturbation
import DGPS.Lipschitz.T01TiltEnergy
import DGPS.Lipschitz.T01PotentialTaylor

/-!
# Scalar rate upper bound from actual inverse-Hessian tilts

This is the analytic comparison on continuous Lipschitz centered tests. Passage to
any spectral/form-domain infimum is a separate downstream step.
-/

open MeasureTheory Filter Topology
open scoped RealInnerProductSpace ENNReal NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- A positive quadratic tilt and its exact dissipation expansion bound the scalar rate. -/
theorem scalarRate_le_of_tilt_expansions (A : InteractionData d) (b : AbsoluteDrift A)
    (F J : ℝ → ℝ) {Q E : ℝ} (hQ : 0 < Q)
    (hF : Tendsto (fun t => F t / t ^ 2) (𝓝[≠] 0) (𝓝 (Q / 2)))
    (hJ : Tendsto J (𝓝[≠] 0) (𝓝 E))
    (hρ : ∀ᶠ t : ℝ in 𝓝[≠] 0, ∃ ρ : AbsoluteDensity d,
      ((scalarGap A ρ : ℝ≥0) : ℝ) = F t ∧
      scalarDissipation A b ρ = ENNReal.ofReal (t ^ 2 * J t)) :
    scalarRate A b ≤ ENNReal.ofReal (E / Q) := by
  have hlim : Tendsto (fun t => ENNReal.ofReal (J t / (2 * (F t / t ^ 2))))
      (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (E / Q))) := by
    have he := ENNReal.tendsto_ofReal (hJ.div (hF.const_mul 2) (by positivity))
    have heq : 2 * (Q / 2) = Q := by ring
    simpa only [heq, Pi.div_apply] using he
  refine ge_of_tendsto hlim ?_
  have hpos : ∀ᶠ t : ℝ in 𝓝[≠] 0, 0 < F t / t ^ 2 :=
    hF.eventually (Ioi_mem_nhds (by positivity : 0 < Q / 2))
  filter_upwards [hρ, hpos, self_mem_nhdsWithin] with t ht hp ht0
  obtain ⟨ρ, hgap, hD⟩ := ht
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
  have hFt : 0 < F t := by
    rcases div_pos_iff.mp hp with hp | hp
    · exact hp.1
    · exact False.elim (not_lt_of_ge ht2.le hp.2)
  have hρp : 0 < scalarGap A ρ := by
    rw [← NNReal.coe_pos, hgap]
    exact hFt
  refine (scalarRate_le_quotient A b ρ hρp).trans_eq ?_
  have hden : 2 * (scalarGap A ρ : ℝ≥0∞) = ENNReal.ofReal (2 * F t) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ← hgap,
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_ofNat]
  unfold scalarQuotient
  rw [hD, hden, ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp [ht0, hFt.ne']

/-- The exact per-test scalar comparison. The mean-zero tilt solves the linear
Euler equation pointwise, while the gradient and score identities are a.e. -/
theorem scalarRate_le_continuous_tilt (A : InteractionData d) (hA : LipschitzData A)
    (b : AbsoluteDrift A) (μ : ProbabilityMeasure (Torus d))
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν)
    (h g : C(Torus d, ℝ)) {Lh Lg : ℝ}
    (hLip : TorusLipschitzWith Lh (fun x => h x))
    (gLip : TorusLipschitzWith Lg (fun x => g x))
    (hmean : ∫ x, h x ∂(μ : Measure (Torus d)) = 0)
    (hsum : ∀ x, h x + centeredOperatorC A (μ : Measure (Torus d)) h x = g x)
    (hQ : 0 < ∫ x, g x * h x ∂(μ : Measure (Torus d))) :
    scalarRate A b ≤ ENNReal.ofReal ((∫ x, ‖smoothGrad (fun y => g y) x‖ ^ 2
      ∂(μ : Measure (Torus d))) / (∫ x, g x * h x ∂(μ : Measure (Torus d)))) := by
  let m : Measure (Torus d) := μ
  let G : Torus d → Tangent d := smoothGrad (fun y => g y)
  let B : Torus d → Tangent d := smoothGrad (fun y => centeredOperatorC A m h y)
  let J : ℝ → ℝ := fun t => ∫ x, t01TiltEnergy (fun y => h y) G B t x ∂m
  let F : ℝ → ℝ := fun t => lip034_potential (A := A) m (t • h)
  have hac : m ≪ haar d := by
    change (μ : Measure (Torus d)) ≪ haar d
    rw [minimizer_eq_gibbs A μ hmin, gibbsMeasure_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _
  obtain ⟨M, hM0, hM⟩ := exists_abs_bound h.continuous
  obtain ⟨LT, hT⟩ := lip034_centeredOperatorC_lipschitz (μ := μ) hA h
  have hg : ∀ᵐ x ∂m, ‖G x‖ ≤ |Lg| :=
    hac.ae_le (ae_norm_smoothGrad_le (abs_nonneg _) (lip034_lipschitz_abs gLip))
  have hb : ∀ᵐ x ∂m, ‖B x‖ ≤ |LT| :=
    hac.ae_le (ae_norm_smoothGrad_le (abs_nonneg _) (lip034_lipschitz_abs hT))
  have hJ : Tendsto J (𝓝[≠] (0 : ℝ)) (𝓝 (∫ x, ‖G x‖ ^ 2 ∂m)) :=
    (tendsto_t01_tilt_energy m (fun y => h y) h.continuous.measurable G B
    measurable_smoothGrad measurable_smoothGrad hM0.le (abs_nonneg Lg) (abs_nonneg LT)
    hM hg hb).mono_left nhdsWithin_le_nhds
  have hquad : (∫ x, h x ^ 2 ∂m) +
      (∫ x, h x * centeredOperatorC A m h x ∂m) = ∫ x, g x * h x ∂m := by
    have ih2 : Integrable (fun x => h x ^ 2) m :=
      (h.continuous.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have ihT : Integrable (fun x => h x * centeredOperatorC A m h x) m :=
      (h.continuous.mul (centeredOperatorC A m h).continuous).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [← integral_add ih2 ihT]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change h x ^ 2 + h x * centeredOperatorC A m h x = g x * h x
    rw [← hsum x]
    ring
  have hF := t01_potential_second_variation A μ h hmean
  change Tendsto (fun t => F t / t ^ 2) _ _ at hF
  rw [hquad] at hF
  refine scalarRate_le_of_tilt_expansions A b F J hQ hF hJ ?_
  have hsmall : ∀ᶠ t : ℝ in 𝓝[≠] 0, |t| ≤ 1 ∧ |t| * M ≤ 1 / 2 := by
    have h1 : ∀ᶠ t : ℝ in 𝓝 0, |t| ≤ 1 :=
      (continuous_abs.tendsto' 0 0 (by simp)).eventually (ge_mem_nhds (by norm_num))
    have h2 : ∀ᶠ t : ℝ in 𝓝 0, |t| * M ≤ 1 / 2 :=
      ((continuous_abs.mul continuous_const).tendsto' 0 0 (by simp)).eventually
        (ge_mem_nhds (by norm_num))
    exact (h1.and h2).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall] with t ht
  have hpos : ∀ x, 0 < 1 + t * h x := by
    intro x
    have hth : |t * h x| ≤ 1 / 2 := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)).trans ht.2
    linarith [(abs_le.mp hth).1]
  have htmean : ∫ x, (t • h) x ∂m = 0 := by
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [integral_const_mul, hmean, mul_zero]
  obtain ⟨ρ, hρ, hscore⟩ := exists_t01_tilt_score A hA μ hmin (t • h)
    (lip034_lipschitz_smul hLip t) hpos htmean
  refine ⟨ρ, lip034_gap_eq_potential hmin hpos htmean ρ hρ, ?_⟩
  have hsc : scalarScore A b ρ =ᵐ[haar d] fun x => ρ.sqrt x •
      (t • ((1 + t * h x)⁻¹ • (G x + (t * h x) • B x))) := by
    have hs := hscore b
    simp only [map_smul, ContinuousMap.smul_apply, smul_eq_mul] at hs
    filter_upwards [hs, ae_t01_tilt_euler_gradient A hA μ h g hLip hsum t hpos]
      with x hx hy
    rw [hx, hy]
  exact t01_tilt_dissipation_eq A b ρ m (fun y => h y) h.continuous.measurable G B
    measurable_smoothGrad measurable_smoothGrad t hpos hρ hsc
    (t01_tilt_energy_integrable m _ h.continuous.measurable G B measurable_smoothGrad
      measurable_smoothGrad hM0.le (abs_nonneg Lg) (abs_nonneg LT) hM hg hb ht.1 ht.2)

/-- Scalar rate comparison with the actual inverse density Hessian on every
continuous Lipschitz representative of a centered L2 test. -/
theorem scalarRate_le_covariance_quotient (A : InteractionData d) (hA : LipschitzData A)
    (b : AbsoluteDrift A) (μ : ProbabilityMeasure (Torus d))
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν)
    (hH : IsCoerciveDensityHessian A μ) (f : centeredL2 μ) (g : C(Torus d, ℝ))
    (hfg : (fun x => g x) =ᵐ[(μ : Measure (Torus d))] (f : Lp ℝ 2 (μ : Measure (Torus d))))
    {Lg : ℝ} (hg : TorusLipschitzWith Lg (fun x => g x))
    (hQ : 0 < inner ℝ f (densityCovariance A μ hH f)) :
    scalarRate A b ≤ ENNReal.ofReal ((∫ x, ‖smoothGrad (fun y => g y) x‖ ^ 2
      ∂(μ : Measure (Torus d))) / inner ℝ f (densityCovariance A μ hH f)) := by
  letI : (μ : Measure (Torus d)).IsOpenPosMeasure := isOpenPosMeasure_of_minimizer hmin
  obtain ⟨h, ⟨Lh, hLip⟩, -, hmean, hsum, hquad⟩ :=
    exists_t01_covariance_perturbation A hA μ hH f g hfg hg
  rw [← hquad] at hQ ⊢
  exact scalarRate_le_continuous_tilt A hA b μ hmin h g hLip hg hmean hsum hQ

end DGPS.Lipschitz
