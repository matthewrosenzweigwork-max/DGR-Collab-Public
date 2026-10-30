import DGPS.Examples.EngineeredRankOneSineMoment
import DGPS.Examples.EngineeredRankOneGauge
import DGPS.Examples.EngineeredUniqueness
import DGPS.Lipschitz.T01ScalarGaussian

/-!
# Actual sine competitor for the engineered scalar rate

The actual reference and feature are even, so the odd sine is centered and
annihilated by the rank-one centered interaction. The existing genuine tilt
comparison therefore gives its ordinary Rayleigh bound. The actual sine moment
then yields a uniform scalar upper bound of order `a0*h` at coupling one.
-/

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace DGPS.Examples

open DGPS.Circle.AngularNormalization DGPS.Models DGPS.PositiveRankOne
open DGPS.Examples.EngineeredRankOne DGPS.Examples.EngineeredUniqueness

private theorem angular_odd_integral_zero (F : AngCircle → ℝ)
    (hF : ∀ θ, F (-θ) = -F θ) : ∫ θ, F θ ∂angHaar = 0 := by
  have hi := integral_neg_eq_self F angHaar
  have he : (fun θ => F (-θ)) = fun θ => -F θ := funext hF
  rw [he, integral_neg] at hi
  linarith

private noncomputable def angularSine : AngCircle → ℝ := fun θ => Real.Angle.sin θ
private noncomputable def angularCosine : AngCircle → ℝ := fun θ => Real.Angle.cos θ

private theorem angularSine_neg (θ : AngCircle) : angularSine (-θ) = -angularSine θ :=
  Real.Angle.sin_neg θ

private theorem angularCosine_neg (θ : AngCircle) : angularCosine (-θ) = angularCosine θ :=
  Real.Angle.cos_neg θ

private theorem angular_U_even (θ : AngCircle) : Uang (-θ) = Uang θ := by
  change 1 - angularCosine (-θ) = 1 - angularCosine θ
  rw [angularCosine_neg]

private theorem angular_q_even (h : ℝ) (θ : AngCircle) : qAng h (-θ) = qAng h θ := by
  unfold qAng logq
  rw [angular_U_even]

private theorem angular_feature_even (h : ℝ) (θ : AngCircle) : Eang h (-θ) = Eang h θ := by
  unfold Eang
  rw [angular_U_even]

private theorem smooth_angular_sine : IsSmoothAngular angularSine := by
  change ContDiff ℝ ∞ (Real.sin : ℝ → ℝ)
  exact Real.contDiff_sin

private theorem angular_sine_derivative (θ : AngCircle) :
    angDeriv angularSine θ = angularCosine θ := by
  change deriv Real.sin (angSec θ) = angularCosine θ
  rw [Real.deriv_sin]
  have he : angularCosine (((angSec θ : ℝ) : AngCircle)) = Real.cos (angSec θ) :=
    Real.Angle.cos_coe (angSec θ)
  have hsec : ((angSec θ : ℝ) : AngCircle) = θ := by
    unfold angSec
    exact AddCircle.coe_equivIoc
  rw [hsec] at he
  exact he.symm

/-- An actual order-h upper competitor for the normalized rank-one model data.
No test-family, inverse-Hessian estimate or Lipschitz provider is assumed. -/
theorem engineered_scalar_sine_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : ℝ) (hh : 2 ≤ h),
      ∀ b : AbsoluteDrift (engineeredModel h hh).data,
        scalarRate (engineeredModel h hh).data b ≤ ENNReal.ofReal (C * a0 * h) := by
  obtain ⟨c, hc, hmoment⟩ := engineered_sine_second_moment_lower_bound
  refine ⟨c⁻¹, inv_pos.2 hc, fun h hh b => ?_⟩
  have hp : 0 < h := by linarith
  let M := engineeredModel h hh
  let μ := rankOneRef M
  let S : C(Torus 1, ℝ) := ⟨angularSine ∘ angEquiv,
    ((isSmoothPeriodic_comp_iff _).2 smooth_angular_sine).continuous_torus⟩
  have hSm : IsSmoothPeriodic (fun x => S x) :=
    (isSmoothPeriodic_comp_iff _).2 smooth_angular_sine
  have hmean : ∫ x, S x ∂(μ : Measure (Torus 1)) = 0 := by
    rw [show (μ : Measure (Torus 1)) = M.ref.measure from rfl, EngineeredUniqueness.integral_ref M]
    change (∫ x, (fun θ : AngCircle => qAng h θ * angularSine θ) (angEquiv x) ∂haar 1) = 0
    rw [integral_comp_angEquiv (fun θ : AngCircle => qAng h θ * angularSine θ)]
    apply angular_odd_integral_zero
    intro θ
    rw [angular_q_even, angularSine_neg]
    ring
  have hφsin : ∫ x, M.φ x * S x ∂(μ : Measure (Torus 1)) = 0 := by
    rw [show (μ : Measure (Torus 1)) = M.ref.measure from rfl, EngineeredUniqueness.integral_ref M]
    change (∫ x, (fun θ : AngCircle => qAng h θ * (Eang h θ * angularSine θ)) (angEquiv x)
      ∂haar 1) = 0
    rw [integral_comp_angEquiv (fun θ : AngCircle => qAng h θ * (Eang h θ * angularSine θ))]
    apply angular_odd_integral_zero
    intro θ
    rw [angular_q_even, angular_feature_even, angularSine_neg]
    ring
  have hQlower : c / h ≤ ∫ x, S x * S x ∂(μ : Measure (Torus 1)) := by
    rw [show (μ : Measure (Torus 1)) = M.ref.measure from rfl, EngineeredUniqueness.integral_ref M]
    have he : (fun x => M.q x * (S x * S x)) =
        fun x => (fun θ : AngCircle => angularSine θ ^ 2 * qAng h θ) (angEquiv x) := by
      funext x
      change qAng h (angEquiv x) * (angularSine (angEquiv x) * angularSine (angEquiv x)) =
        angularSine (angEquiv x) ^ 2 * qAng h (angEquiv x)
      ring
    rw [he, integral_comp_angEquiv (fun θ : AngCircle => angularSine θ ^ 2 * qAng h θ)]
    exact hmoment h hh
  have hQ : 0 < ∫ x, S x * S x ∂(μ : Measure (Torus 1)) :=
    (div_pos hc hp).trans_le hQlower
  have hOp (x : Torus 1) : DGPS.Lipschitz.centeredOperatorC M.data
      (μ : Measure (Torus 1)) S x = 0 := by
    change DGPS.Lipschitz.Tcont M.data (μ : Measure (Torus 1))
      (ContinuousMap.toLp 2 (μ : Measure (Torus 1)) ℝ S) x = 0
    rw [DGPS.Lipschitz.Tcont_apply]
    calc
      _ = ∫ y, M.η * (M.φ x * M.φ y) * S y ∂(μ : Measure (Torus 1)) := by
        apply integral_congr_ae
        filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (μ := (μ : Measure (Torus 1)))
          (𝕜 := ℝ) S] with y hy
        rw [hy]
        have hk := rankOne_centeredKernel M x y
        change DGPS.Lipschitz.centeredKernel M.data (μ : Measure (Torus 1)) x y = _ at hk
        rw [hk]
      _ = (M.η * M.φ x) * ∫ y, M.φ y * S y ∂(μ : Measure (Torus 1)) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun y => by ring
      _ = 0 := by rw [hφsin]; ring
  have hmin : ∀ ν : ProbabilityMeasure (Torus 1), freeEnergy M.data μ ≤ freeEnergy M.data ν := by
    have heq := (rankOne_equilibrium_iff M μ).2 rfl
    intro ν
    rw [heq]
    exact iInf_le (fun ν => freeEnergy M.data ν) ν
  obtain ⟨L, _, hLip⟩ := DGPS.Lipschitz.exists_smooth_lipschitz hSm
  have htrial := DGPS.Lipschitz.scalarRate_le_continuous_tilt M.data
    (normalizedLipschitz h hh) b μ hmin S S hLip hLip hmean
    (fun x => by rw [hOp, add_zero]) hQ
  have hgrad (x : Torus 1) : ‖smoothGrad (fun y => S y) x‖ ^ 2 ≤ a0 := by
    rw [RankOneModel.norm_sq_tangent, smoothGrad_apply]
    change (coordPartial 0 (angularSine ∘ angEquiv) x) ^ 2 ≤ a0
    rw [coordPartial_comp_angEquiv (ψ := angularSine) smooth_angular_sine x, angular_sine_derivative]
    have hm := Uang_mem (angEquiv x)
    change 0 ≤ 1 - angularCosine (angEquiv x) ∧ 1 - angularCosine (angEquiv x) ≤ 2 at hm
    have hc2 : angularCosine (angEquiv x) ^ 2 ≤ 1 := by
      nlinarith [mul_nonneg (show 0 ≤ 1 - angularCosine (angEquiv x) by linarith [hm.1])
        (show 0 ≤ 1 + angularCosine (angEquiv x) by linarith [hm.2])]
    unfold a0
    nlinarith [mul_nonneg (sq_nonneg (2 * Real.pi)) (sub_nonneg.mpr hc2)]
  have hE : (∫ x, ‖smoothGrad (fun y => S y) x‖ ^ 2 ∂(μ : Measure (Torus 1))) ≤ a0 := by
    calc _ ≤ ∫ _x, a0 ∂(μ : Measure (Torus 1)) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall hgrad)
      _ = a0 := by simp
  refine htrial.trans (ENNReal.ofReal_le_ofReal ?_)
  calc
    _ ≤ a0 / (∫ x, S x * S x ∂(μ : Measure (Torus 1))) :=
      div_le_div_of_nonneg_right hE hQ.le
    _ ≤ a0 / (c / h) := div_le_div_of_nonneg_left a0_pos.le (div_pos hc hp) hQlower
    _ = c⁻¹ * a0 * h := by field_simp [hc.ne', hp.ne']

end DGPS.Examples
