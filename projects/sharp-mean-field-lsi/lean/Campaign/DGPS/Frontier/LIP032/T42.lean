import DGPS.Frontier.LIP032.T18
import DGPS.Foundations.SobolevEmbedding
import DGPS.Analysis.CircleMoments

/-!
# LIP032.42: Explicit positive trial density

Task id and title: LIP032.42, "Explicit positive trial density" (node LIP032, contractibility of the
minimizer set; leaf formalization). The statement is a pure density statement: no positive-rate or
flow hypothesis of the conditional branch occurs in it.

## Provides
* `DGPS.Frontier.LIP032.gammaCos_LIP03242` : the circle function `γ(x) = cos(2π x)` on `𝕋¹`, realized
  as the real part of the first Fourier character at the coordinate `x 0`.
* `DGPS.Frontier.LIP032.trialDensity_LIP03242` : the trial density `f_* = 1 + γ / 2`.
* `DGPS.Frontier.LIP032.lip032_42_explicit_positive_trial_density` : the main statement, the
  conjunction of the bounds, the mass identity, the moment identity, the entropy bound and the
  finiteness of the entropy.
* `DGPS.Frontier.LIP032.lip032_42_explicit_positive_trial_density_bounds` : `1/2 ≤ f_* ≤ 3/2`.
* `DGPS.Frontier.LIP032.lip032_42_explicit_positive_trial_density_mass` : `∫ f_* dm = 1`.
* `DGPS.Frontier.LIP032.lip032_42_explicit_positive_trial_density_moment` : `∫ γ dμ_{f_*} = 1/4`.
* `DGPS.Frontier.LIP032.lip032_42_explicit_positive_trial_density_entropy` : the relative entropy of
  `μ_{f_*}` with respect to `m` is at most `1/8` and is not infinite.
* `DGPS.Frontier.LIP032.lip032_42_explicit_positive_trial_density_probability` : `μ_{f_*}` is a
  probability measure.

## R5 notes
* `m` is `haar 1`, the normalized Haar probability on `𝕋¹ = Torus 1`. The circle is the
  one-dimensional torus; the coordinate is `x 0 : AddCircle 1`.
* `γ(x) = cos(2π x)` is defined through the Mathlib Fourier character `fourier 1`, taking its real
  part. The value on the lifts `torusLift (fun _ => t)` is the real cosine `Real.cos (2π t)`; this is
  proved as a helper, not assumed.
* The cosine moment `M(ν) = ∫ γ dν` is written out as
  `∫ x, gammaCos_LIP03242 x ∂densityMeasure_LIP03218 trialDensity_LIP03242`. No declaration of the
  LIP032.41 model is used, since that unit is not integrated into this worktree.
* `μ_f` is `densityMeasure_LIP03218 f` from LIP032.18. The probability-measure subtype is not formed;
  `IsProbabilityMeasure` is proved instead, and the moment identity is taken from the LIP032.18
  bridge.
* The entropy `H(μ ∣ m)` is `DGPS.relativeEntropy μ m` with values in the extended nonnegative
  reals. "Its entropy is finite" is read as `≠ ⊤`. The bound uses the explicit formula
  `∫⁻ ofReal (f log f - f + 1)` and the inequality `log t ≤ t - 1` for `t > 0`.
* The bounds `1/2 ≤ f_* ≤ 3/2` are stated for every point of `𝕋¹`. Continuity, nonnegativity and mass
  one of `f_*` are derived from the definition rather than assumed.
* The main statement has no hypothesis: the specification's conditional branch (positive rate,
  flow data, interaction-gradient data) is not inherited by this pure density statement.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

/-- The circle function `γ(x) = cos(2π x)` on `𝕋¹`, realized as the real part of the first Fourier
character evaluated at the coordinate `x 0`. -/
noncomputable def gammaCos_LIP03242 (x : Torus 1) : ℝ := (fourier (1 : ℤ) (x 0)).re

/-- The explicit trial density `f_* = 1 + γ / 2` on `𝕋¹`. -/
noncomputable def trialDensity_LIP03242 (x : Torus 1) : ℝ := 1 + gammaCos_LIP03242 x / 2

theorem continuous_gammaCos_LIP03242 : Continuous gammaCos_LIP03242 :=
  Complex.continuous_re.comp ((fourier (1 : ℤ)).continuous.comp (continuous_apply 0))

theorem abs_gammaCos_le_one_LIP03242 (x : Torus 1) : |gammaCos_LIP03242 x| ≤ 1 := by
  refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
  simp

theorem gammaCos_lift_LIP03242 (t : ℝ) :
    gammaCos_LIP03242 (torusLift fun _ => t) = Real.cos (2 * Real.pi * t) := by
  show (fourier (1 : ℤ) ((t : ℝ) : AddCircle (1 : ℝ))).re = _
  rw [fourier_coe_apply]
  have h : 2 * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) * (t : ℂ) / ((1 : ℝ) : ℂ) =
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_ofReal_mul_I_re]

theorem continuous_cosCircle_LIP03242 : Continuous fun t : ℝ => Real.cos (2 * Real.pi * t) := by
  fun_prop

theorem integral_gammaCos_LIP03242 : ∫ x, gammaCos_LIP03242 x ∂haar 1 = 0 := by
  rw [DGPS.integral_haar_one _ continuous_gammaCos_LIP03242]
  simp only [gammaCos_lift_LIP03242]
  exact DGPS.Analysis.CircleMoments.integral_cos_two_pi

theorem continuous_gammaCos_sq_LIP03242 : Continuous fun x => gammaCos_LIP03242 x ^ 2 :=
  continuous_gammaCos_LIP03242.pow 2

theorem integral_gammaCos_sq_LIP03242 : ∫ x, gammaCos_LIP03242 x ^ 2 ∂haar 1 = 1 / 2 := by
  rw [DGPS.integral_haar_one _ continuous_gammaCos_sq_LIP03242]
  simp only [gammaCos_lift_LIP03242]
  exact DGPS.Analysis.CircleMoments.integral_cos_sq_two_pi

theorem continuous_trialDensity_LIP03242 : Continuous trialDensity_LIP03242 :=
  continuous_const.add (continuous_gammaCos_LIP03242.div_const 2)

theorem trialDensity_lift_LIP03242 (t : ℝ) :
    trialDensity_LIP03242 (torusLift fun _ => t) = 1 + Real.cos (2 * Real.pi * t) / 2 := by
  unfold trialDensity_LIP03242
  rw [gammaCos_lift_LIP03242]

theorem lip032_42_explicit_positive_trial_density_bounds :
    ∀ x : Torus 1, 1 / 2 ≤ trialDensity_LIP03242 x ∧ trialDensity_LIP03242 x ≤ 3 / 2 := by
  intro x
  obtain ⟨h1, h2⟩ := abs_le.mp (abs_gammaCos_le_one_LIP03242 x)
  unfold trialDensity_LIP03242
  constructor <;> linarith

theorem trialDensity_nonneg_LIP03242 (x : Torus 1) : 0 ≤ trialDensity_LIP03242 x := by
  have h := (lip032_42_explicit_positive_trial_density_bounds x).1
  linarith

theorem lip032_42_explicit_positive_trial_density_mass :
    ∫ x, trialDensity_LIP03242 x ∂haar 1 = 1 := by
  rw [DGPS.integral_haar_one _ continuous_trialDensity_LIP03242]
  simp only [trialDensity_lift_LIP03242]
  have hi1 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) MeasureTheory.volume 0 1 :=
    continuous_const.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ => Real.cos (2 * Real.pi * t) / 2)
      MeasureTheory.volume 0 1 :=
    (continuous_cosCircle_LIP03242.div_const 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_div,
    DGPS.Analysis.CircleMoments.integral_cos_two_pi]
  norm_num

theorem lip032_42_explicit_positive_trial_density_moment :
    ∫ x, gammaCos_LIP03242 x ∂densityMeasure_LIP03218 trialDensity_LIP03242 = 1 / 4 := by
  have hprod : Continuous fun x => trialDensity_LIP03242 x * gammaCos_LIP03242 x :=
    continuous_trialDensity_LIP03242.mul continuous_gammaCos_LIP03242
  rw [(lip032_18_density_probability_test_integral_bridge_integral
      continuous_trialDensity_LIP03242 trialDensity_nonneg_LIP03242
      lip032_42_explicit_positive_trial_density_mass continuous_gammaCos_LIP03242.measurable
      ⟨1, abs_gammaCos_le_one_LIP03242⟩).2,
    DGPS.integral_haar_one _ hprod]
  simp only [trialDensity_lift_LIP03242, gammaCos_lift_LIP03242]
  have key : ∀ t : ℝ, (1 + Real.cos (2 * Real.pi * t) / 2) * Real.cos (2 * Real.pi * t) =
      Real.cos (2 * Real.pi * t) + 1 / 2 * Real.cos (2 * Real.pi * t) ^ 2 := fun t => by ring
  simp only [key]
  have hi1 : IntervalIntegrable (fun t : ℝ => Real.cos (2 * Real.pi * t))
      MeasureTheory.volume 0 1 :=
    continuous_cosCircle_LIP03242.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t : ℝ => 1 / 2 * Real.cos (2 * Real.pi * t) ^ 2)
      MeasureTheory.volume 0 1 :=
    (continuous_const.mul (continuous_cosCircle_LIP03242.pow 2)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul,
    DGPS.Analysis.CircleMoments.integral_cos_two_pi,
    DGPS.Analysis.CircleMoments.integral_cos_sq_two_pi]
  norm_num

theorem integral_gammaCos_sq_div_four_LIP03242 :
    ∫ x, gammaCos_LIP03242 x ^ 2 / 4 ∂haar 1 = 1 / 8 := by
  rw [MeasureTheory.integral_div, integral_gammaCos_sq_LIP03242]
  norm_num

theorem real_entropy_ineq_LIP03242 {t : ℝ} (ht : 0 < t) :
    t * Real.log t - t + 1 ≤ (t - 1) ^ 2 := by
  have h := Real.log_le_sub_one_of_pos ht
  nlinarith [mul_le_mul_of_nonneg_left h ht.le]

theorem entropy_pointwise_LIP03242 (x : Torus 1) :
    trialDensity_LIP03242 x * Real.log (trialDensity_LIP03242 x) - trialDensity_LIP03242 x + 1 ≤
      gammaCos_LIP03242 x ^ 2 / 4 := by
  have hpos : 0 < trialDensity_LIP03242 x := by
    linarith [(lip032_42_explicit_positive_trial_density_bounds x).1]
  refine (real_entropy_ineq_LIP03242 hpos).trans (le_of_eq ?_)
  unfold trialDensity_LIP03242
  ring

theorem lip032_42_explicit_positive_trial_density_entropy :
    DGPS.relativeEntropy (densityMeasure_LIP03218 trialDensity_LIP03242) (haar 1) ≤
        ENNReal.ofReal (1 / 8) ∧
      DGPS.relativeEntropy (densityMeasure_LIP03218 trialDensity_LIP03242) (haar 1) ≠ ⊤ := by
  have hnn : 0 ≤ᵐ[haar 1] trialDensity_LIP03242 :=
    Filter.Eventually.of_forall trialDensity_nonneg_LIP03242
  have hmeas : AEMeasurable trialDensity_LIP03242 (haar 1) :=
    continuous_trialDensity_LIP03242.measurable.aemeasurable
  have hent : DGPS.relativeEntropy (densityMeasure_LIP03218 trialDensity_LIP03242) (haar 1) =
      ∫⁻ x, ENNReal.ofReal (trialDensity_LIP03242 x * Real.log (trialDensity_LIP03242 x)
        - trialDensity_LIP03242 x + 1) ∂haar 1 := by
    rw [densityMeasure_LIP03218, DGPS.relativeEntropy_withDensity hnn hmeas,
      DGPS.entropy_mass_one lip032_42_explicit_positive_trial_density_mass]
  have hsq : Integrable (fun x => gammaCos_LIP03242 x ^ 2 / 4) (haar 1) :=
    integrable_continuous_LIP03218 ((continuous_gammaCos_LIP03242.pow 2).div_const 4)
  have hsq_nn : 0 ≤ᵐ[haar 1] fun x => gammaCos_LIP03242 x ^ 2 / 4 :=
    Filter.Eventually.of_forall fun x => div_nonneg (sq_nonneg _) (by norm_num)
  have hbound : ∫⁻ x, ENNReal.ofReal (trialDensity_LIP03242 x * Real.log (trialDensity_LIP03242 x)
        - trialDensity_LIP03242 x + 1) ∂haar 1 ≤
      ∫⁻ x, ENNReal.ofReal (gammaCos_LIP03242 x ^ 2 / 4) ∂haar 1 :=
    lintegral_mono fun x => ENNReal.ofReal_le_ofReal (entropy_pointwise_LIP03242 x)
  have hval : ∫⁻ x, ENNReal.ofReal (gammaCos_LIP03242 x ^ 2 / 4) ∂haar 1 =
      ENNReal.ofReal (1 / 8) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hsq hsq_nn, integral_gammaCos_sq_div_four_LIP03242]
  have hle := hbound.trans_eq hval
  rw [hent]
  exact ⟨hle, ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle⟩

theorem lip032_42_explicit_positive_trial_density_probability :
    IsProbabilityMeasure (densityMeasure_LIP03218 trialDensity_LIP03242) :=
  isProbabilityMeasure_density_LIP03218 continuous_trialDensity_LIP03242
    trialDensity_nonneg_LIP03242 lip032_42_explicit_positive_trial_density_mass

/-- **LIP032.42.** Explicit positive trial density: `f_* = 1 + γ/2` satisfies `1/2 ≤ f_* ≤ 3/2`,
`∫ f_* dm = 1`, the cosine moment of `μ_{f_*}` is `1/4`, and its relative entropy with respect to
`m` is at most `1/8` and finite. -/
theorem lip032_42_explicit_positive_trial_density :
    (∀ x : Torus 1, 1 / 2 ≤ trialDensity_LIP03242 x ∧ trialDensity_LIP03242 x ≤ 3 / 2) ∧
      ∫ x, trialDensity_LIP03242 x ∂haar 1 = 1 ∧
      ∫ x, gammaCos_LIP03242 x ∂densityMeasure_LIP03218 trialDensity_LIP03242 = 1 / 4 ∧
      DGPS.relativeEntropy (densityMeasure_LIP03218 trialDensity_LIP03242) (haar 1) ≤
        ENNReal.ofReal (1 / 8) ∧
      DGPS.relativeEntropy (densityMeasure_LIP03218 trialDensity_LIP03242) (haar 1) ≠ ⊤ :=
  ⟨lip032_42_explicit_positive_trial_density_bounds,
    lip032_42_explicit_positive_trial_density_mass,
    lip032_42_explicit_positive_trial_density_moment,
    (lip032_42_explicit_positive_trial_density_entropy).1,
    (lip032_42_explicit_positive_trial_density_entropy).2⟩

end DGPS.Frontier.LIP032
