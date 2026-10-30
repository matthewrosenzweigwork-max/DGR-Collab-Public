import DGPS.Lipschitz.T01ScalarGaussian
import DGPS.Structural.AmplitudeComparison
import DGPS.Structural.AmplitudePoincare

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGPS.Structural
variable {d : ℕ}

/-- The scalar rate is bounded by the smooth Rayleigh quotient times the full-product
interaction amplitude.  Centering does not change the gradient; the inverse-Hessian
quadratic bound supplies the denominator. -/
theorem t06_scalarRate_le_smooth_rayleigh (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) (μ : ProbabilityMeasure (Torus d))
    (hmin : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν)
    (hH : IsCoerciveDensityHessian A μ) (u : Torus d → ℝ) (hu : IsSmoothPeriodic u)
    (hvar : 0 < weightedVariance μ u) :
    scalarRate A b ≤ ENNReal.ofReal ((1 + DGPS.interactionOscillation A / 2) *
      (∫ x, ‖smoothGrad u x‖ ^ 2 ∂(μ : Measure (Torus d))) / weightedVariance μ u) := by
  let c : ℝ := ∫ x, u x ∂(μ : Measure (Torus d))
  let g : C(Torus d, ℝ) := ⟨fun x => u x - c, hu.continuous_torus.sub continuous_const⟩
  have hgu : IsSmoothPeriodic (fun x => g x) := hu.sub contDiff_const
  have hgLp : MemLp (fun x => g x) 2 (μ : Measure (Torus d)) :=
    g.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have huLp : MemLp u 2 (μ : Measure (Torus d)) :=
    hu.continuous_torus.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hg0 : ∫ x, g x ∂(μ : Measure (Torus d)) = 0 := by
    change ∫ x, (u x - c) ∂(μ : Measure (Torus d)) = 0
    rw [integral_sub (huLp.integrable one_le_two) (integrable_const c)]
    simp [c]
  let f : centeredL2 μ := ⟨hgLp.toLp (fun x => g x), by
    rw [mem_centeredL2, integral_congr_ae hgLp.coeFn_toLp]
    exact hg0⟩
  have hfg : (fun x => g x) =ᵐ[(μ : Measure (Torus d))]
      (f : Lp ℝ 2 (μ : Measure (Torus d))) := hgLp.coeFn_toLp.symm
  have hnorm : ‖f‖ ^ 2 = weightedVariance μ u := by
    change ‖(f : Lp ℝ 2 (μ : Measure (Torus d)))‖ ^ 2 = _
    rw [norm_sq_eq_integral_sq]
    exact integral_congr_ae (hfg.symm.mono fun x hx => congrArg (fun z : ℝ => z ^ 2) hx)
  have hB : 0 ≤ DGPS.interactionOscillation A := DGPS.interactionOscillation_nonneg A
  have hΛ : 0 < 1 + DGPS.interactionOscillation A / 2 := by positivity
  have hcov := norm_sq_div_le_inner_densityCovariance A μ hH f
  change ‖f‖ ^ 2 / (1 + DGPS.interactionOscillation A / 2) ≤ _ at hcov
  rw [hnorm] at hcov
  have hQ : 0 < inner ℝ f (densityCovariance A μ hH f) :=
    (div_pos hvar hΛ).trans_le hcov
  obtain ⟨L, -, hgLip⟩ := DGPS.Lipschitz.exists_smooth_lipschitz hgu
  have hs := DGPS.Lipschitz.scalarRate_le_covariance_quotient A hLip b μ hmin hH f g hfg hgLip hQ
  have hgrad : smoothGrad (fun x => g x) = smoothGrad u := by
    have he : (fun x => g x) = (fun x => -c + u x) := by funext x; simp [g]; ring
    rw [he]
    funext x
    exact DGPS.Lipschitz.lip034_smoothGrad_const_add u (-c) x
  rw [hgrad] at hs
  refine hs.trans (ENNReal.ofReal_le_ofReal ?_)
  have hE : 0 ≤ ∫ x, ‖smoothGrad u x‖ ^ 2 ∂(μ : Measure (Torus d)) :=
    integral_nonneg fun _ => sq_nonneg _
  calc (∫ x, ‖smoothGrad u x‖ ^ 2 ∂(μ : Measure (Torus d))) /
        inner ℝ f (densityCovariance A μ hH f)
      ≤ (∫ x, ‖smoothGrad u x‖ ^ 2 ∂(μ : Measure (Torus d))) /
          (weightedVariance μ u / (1 + DGPS.interactionOscillation A / 2)) :=
        div_le_div_of_nonneg_left hE (div_pos hvar hΛ) hcov
    _ = _ := by field_simp

end DGPS.Structural
