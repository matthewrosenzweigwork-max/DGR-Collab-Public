import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootFormDomain
import DGPS.Structural.SmallRateCircle

/-!
# Exact native variance and energy in the actual ordinary angular chart

These identities transport the original full weighted form domain. The physical energy
has the factor `a0 = 4*pi^2`; no Poincare or Hessian bound is a premise.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Exact integration against a probability represented by the actual angular chart. -/
theorem ordinaryChart_integral_native (h : ℝ) (v : ℝ → ℝ) (σ : AbsoluteDensity 1)
    (hσ : ∀ θ : AngCircle, σ.density (angEquiv.symm θ) = rhoT_STR02901 h v (angSec θ))
    (g : Torus 1 → ℝ) :
    (∫ x, g x ∂(densityMeasure σ : Measure (Torus 1))) =
      normInt_STR02933 (fun t => rhoT_STR02901 h v t * g (angEquiv.symm (t : AngCircle))) := by
  rw [Structural.budget_integral_densityMeasure]
  have hfun : (fun x => σ.density x * g x) =
      (fun θ : AngCircle => rhoT_STR02901 h v (angSec θ) * g (angEquiv.symm θ)) ∘ angEquiv := by
    funext x
    have hh := hσ (angEquiv x)
    simpa only [Function.comp_apply, angEquiv.symm_apply_apply] using congrArg (fun a => a * g x) hh
  rw [hfun]
  change (∫ x, (fun θ : AngCircle => rhoT_STR02901 h v (angSec θ) *
    g (angEquiv.symm θ)) (angEquiv x) ∂haar 1) = _
  rw [integral_comp_angEquiv (fun θ : AngCircle =>
    rhoT_STR02901 h v (angSec θ) * g (angEquiv.symm θ))]
  have hsec : (fun θ : AngCircle => rhoT_STR02901 h v (angSec θ) * g (angEquiv.symm θ)) =
      fun θ => (fun t : ℝ => rhoT_STR02901 h v t * g (angEquiv.symm (t : AngCircle))) (angSec θ) := by
    funext θ
    change rhoT_STR02901 h v (angSec θ) * g (angEquiv.symm θ) =
      rhoT_STR02901 h v (angSec θ) * g (angEquiv.symm ((angSec θ : ℝ) : AngCircle))
    rw [coe_angSec_STR02962]
  rw [hsec, integral_angSec_STR02962 (fun t =>
    rhoT_STR02901 h v t * g (angEquiv.symm (t : AngCircle)))]
  exact (normInt_eq_meanT_STR02962 _).symm

/-- Exact native variance in the angular quadratic form, on the full weighted H1 domain. -/
theorem ordinaryChart_native_variance (h : ℝ) (v : ℝ → ℝ) (σ : AbsoluteDensity 1)
    (hσ : ∀ θ : AngCircle, σ.density (angEquiv.symm θ) = rhoT_STR02901 h v (angSec θ))
    (f : WeakH1Test (densityMeasure σ)) :
    weightedVariance (densityMeasure σ) f.fn =
      normInt_STR02933 (fun t => rhoT_STR02901 h v t * f.fn (angEquiv.symm (t : AngCircle)) ^ 2) -
      (normInt_STR02933 (fun t => rhoT_STR02901 h v t * f.fn (angEquiv.symm (t : AngCircle)))) ^ 2 := by
  have hv : ProbabilityTheory.variance f.fn (densityMeasure σ : Measure (Torus 1)) =
      weightedVariance (densityMeasure σ) f.fn :=
    (ProbabilityTheory.variance_eq_integral f.isWeak.memLp.aestronglyMeasurable.aemeasurable).trans rfl
  rw [← hv, ProbabilityTheory.variance_eq_sub f.isWeak.memLp]
  change (∫ x, f.fn x ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) -
    (∫ x, f.fn x ∂(densityMeasure σ : Measure (Torus 1))) ^ 2 = _
  rw [ordinaryChart_integral_native h v σ hσ (fun x => f.fn x ^ 2),
    ordinaryChart_integral_native h v σ hσ f.fn]

/-- Exact physical energy as `a0` times the actual angular energy. No boundedness or
smoothness of the native weighted H1 test is imposed. -/
theorem ordinaryChart_native_energy (h : ℝ) (v : ℝ → ℝ) (σ : AbsoluteDensity 1)
    (hσ : ∀ θ : AngCircle, σ.density (angEquiv.symm θ) = rhoT_STR02901 h v (angSec θ))
    (f : WeakH1Test (densityMeasure σ)) :
    dirichletEnergy (densityMeasure σ) f =
      ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 *
        normInt_STR02933 (fun t => rhoT_STR02901 h v t *
          ((2 * Real.pi)⁻¹ * f.grad (angEquiv.symm (t : AngCircle)) 0) ^ 2)) := by
  have hn : ∀ z : Tangent 1, ‖z‖ ^ 2 = (z 0) ^ 2 := by
    intro z
    simp [EuclideanSpace.norm_sq_eq]
  have hgi : Integrable (fun x => ‖f.grad x‖ ^ 2) (densityMeasure σ : Measure (Torus 1)) :=
    f.isWeak.memLp_grad.norm.integrable_sq
  have hE : dirichletEnergy (densityMeasure σ) f =
      ENNReal.ofReal (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure σ : Measure (Torus 1))) := by
    unfold dirichletEnergy
    rw [ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun _ => sq_nonneg _)]
    apply lintegral_congr
    intro x
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [hE]
  congr 1
  simp_rw [hn]
  rw [ordinaryChart_integral_native h v σ hσ (fun x => (f.grad x 0) ^ 2),
    ← normInt_mul_const_STR02933]
  apply congrArg normInt_STR02933
  funext t
  unfold DGPS.Circle.AngularNormalization.a0
  field_simp [Real.two_pi_pos.ne']
  ring

end DGPS.Examples.ThreeSpeciesCircle
