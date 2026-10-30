import DGPS.Model.ScalarRate

/-!
# Exact dissipation from a relative score

The equality is extended-valued and needs no finiteness premise. In the Gaussian
perturbation it is used with reference weight `1 + t h` and its actual Euler gradient.
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- Transfer the exact square-root score to the actual perturbed reference measure.
The same absolute density occurs in the score and change-of-measure hypotheses. -/
theorem scalarDissipation_eq_reference_score (A : InteractionData d) (b : AbsoluteDrift A)
    (ρ : AbsoluteDensity d) (μ : Measure (Torus d)) (a : Torus d → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x) (G : Torus d → Tangent d)
    (hG : Measurable G)
    (hρ : (densityMeasure ρ : Measure (Torus d)) =
      μ.withDensity (fun x => ENNReal.ofReal (a x)))
    (hscore : scalarScore A b ρ =ᵐ[haar d] fun x => ρ.sqrt x • G x) :
    scalarDissipation A b ρ = ∫⁻ x, ENNReal.ofReal (a x * ‖G x‖ ^ 2) ∂μ := by
  have hgm : Measurable (fun x => ENNReal.ofReal (‖G x‖ ^ 2)) :=
    (hG.norm.pow_const 2).ennreal_ofReal
  have hdm : AEMeasurable (fun x => ENNReal.ofReal (ρ.sqrt x ^ 2)) (haar d) :=
    (ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  calc scalarDissipation A b ρ
      = ∫⁻ x, ENNReal.ofReal (ρ.sqrt x ^ 2) * ENNReal.ofReal (‖G x‖ ^ 2) ∂haar d := by
          apply lintegral_congr_ae
          filter_upwards [hscore] with x hx
          change ENNReal.ofReal (‖scalarScore A b ρ x‖ ^ 2) = _
          rw [hx, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
            ENNReal.ofReal_mul (sq_nonneg _)]
    _ = ∫⁻ x, ENNReal.ofReal (‖G x‖ ^ 2) ∂(densityMeasure ρ : Measure (Torus d)) := by
          rw [densityMeasure_coe, lintegral_withDensity_eq_lintegral_mul₀ hdm hgm.aemeasurable]
          rfl
    _ = ∫⁻ x, ENNReal.ofReal (a x * ‖G x‖ ^ 2) ∂μ := by
          rw [hρ, lintegral_withDensity_eq_lintegral_mul _ ha.ennreal_ofReal hgm]
          exact lintegral_congr fun x => (ENNReal.ofReal_mul (ha0 x)).symm

end DGPS.Lipschitz
