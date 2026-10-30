import DGPS.Lipschitz.T01ConditionalInformation

/-!
# Integration of the actual pointwise conditional-density inequality

Both the scalar and species routes use the same conditional disintegration. The input is a
pointwise rate inequality for the actual conditional densities; the conclusion integrates it
without assuming finite dissipation on every conditional fiber. Only the joint score integrals
need be finite, as supplied by the regularized joint-density data.
-/

open MeasureTheory InformationTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

/-- Integrate a pointwise inequality for the actual conditional densities. Negative left sides
are allowed, so no nonnegativity of a centered interaction correction is silently assumed. -/
theorem integrate_conditional_density_bound {d N : ℕ}
    {Q : SharpLSI.Config N d → ℝ} {c C : ℝ} (hQ : SharpLSI.FL.IsBddDens Q c C)
    (ν : Measure (SharpLSI.Config N d)) [IsProbabilityMeasure ν]
    (hν : ν = SharpLSI.FL.qMeasure Q) (S : Finset (Fin N))
    (L : (S → Torus d) → ℝ)
    (hL : Integrable (fun X => L (SharpLSI.FL.restrictS S X)) ν)
    (H : Fin N → (S → Torus d) → Torus d → ℝ)
    (hHm : ∀ i ∈ Sᶜ, Measurable (Function.uncurry (H i)))
    (hH0 : ∀ i ∈ Sᶜ, ∀ a x, 0 ≤ H i a x)
    (hHi : ∀ i ∈ Sᶜ, Integrable
      (fun X => H i (SharpLSI.FL.restrictS S X) (X i)) ν)
    (hpoint : ∀ᵐ X ∂ν,
      ENNReal.ofReal (L (SharpLSI.FL.restrictS S X)) ≤ ENNReal.ofReal ((Sᶜ.card : ℝ)⁻¹) *
        ∑ i ∈ Sᶜ, ∫⁻ x, ENNReal.ofReal
          (SharpLSI.FL.condDensS Q S i (SharpLSI.FL.restrictS S X) x) *
          ENNReal.ofReal (H i (SharpLSI.FL.restrictS S X) x) ∂haar d) :
    (∫ X, L (SharpLSI.FL.restrictS S X) ∂ν) ≤
      (Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        ∫ X, H i (SharpLSI.FL.restrictS S X) (X i) ∂ν := by
  classical
  let T : Fin N → (S → Torus d) → ℝ≥0∞ := fun i a =>
    ∫⁻ x, ENNReal.ofReal (SharpLSI.FL.condDensS Q S i a x) * ENNReal.ofReal (H i a x) ∂haar d
  have hTm : ∀ i ∈ Sᶜ, Measurable (T i) := by
    intro i hi
    exact (((SharpLSI.FL.measurable_condDensS hQ S i).ennreal_ofReal).mul
      (hHm i hi).ennreal_ofReal).lintegral_prod_right'
  have hdis : ∀ i ∈ Sᶜ,
      (∫⁻ X, T i (SharpLSI.FL.restrictS S X) ∂ν) =
        ∫⁻ X, ENNReal.ofReal (H i (SharpLSI.FL.restrictS S X) (X i)) ∂ν := by
    intro i hi
    have hmF : Measurable (Function.uncurry (fun a x => ENNReal.ofReal (H i a x))) := by
      change Measurable (fun p : (S → Torus d) × Torus d => ENNReal.ofReal (H i p.1 p.2))
      exact (hHm i hi).ennreal_ofReal
    exact (SharpLSI.FL.lintegral_pair_eq_lintegral_condDensS hQ hν
      (Finset.mem_compl.mp hi) (F := fun a x => ENNReal.ofReal (H i a x)) hmF).symm
  have hpt := hpoint
  have hlin : (∫⁻ X, ENNReal.ofReal (L (SharpLSI.FL.restrictS S X)) ∂ν) ≤
      ENNReal.ofReal ((Sᶜ.card : ℝ)⁻¹ * ∑ i ∈ Sᶜ,
        ∫ X, H i (SharpLSI.FL.restrictS S X) (X i) ∂ν) := by
    calc
      (∫⁻ X, ENNReal.ofReal (L (SharpLSI.FL.restrictS S X)) ∂ν) ≤
          ∫⁻ X, ENNReal.ofReal ((Sᶜ.card : ℝ)⁻¹) *
            ∑ i ∈ Sᶜ, T i (SharpLSI.FL.restrictS S X) ∂ν := lintegral_mono_ae hpt
      _ = ENNReal.ofReal ((Sᶜ.card : ℝ)⁻¹) *
          ∑ i ∈ Sᶜ, ∫⁻ X, ENNReal.ofReal (H i (SharpLSI.FL.restrictS S X) (X i)) ∂ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        calc
          (∫⁻ X, ∑ i ∈ Sᶜ, T i (SharpLSI.FL.restrictS S X) ∂ν) =
              ∑ i ∈ Sᶜ, ∫⁻ X, T i (SharpLSI.FL.restrictS S X) ∂ν := by
            simpa only [Function.comp_apply] using lintegral_finsetSum' Sᶜ (fun i hi =>
              ((hTm i hi).comp (SharpLSI.FL.measurable_restrictS S)).aemeasurable)
          _ = _ := Finset.sum_congr rfl fun i hi => hdis i hi
      _ = _ := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_sum_of_nonneg
          (fun i hi => integral_nonneg (fun X => hH0 i hi _ _))]
        congr 1
        exact Finset.sum_congr rfl fun i hi =>
          (ofReal_integral_eq_lintegral_ofReal (hHi i hi)
            (Eventually.of_forall fun X => hH0 i hi _ _)).symm
  exact (SharpLSI.integral_le_toReal_lintegral_ofReal hL).trans
    (ENNReal.toReal_le_of_le_ofReal
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun i hi => integral_nonneg (fun X => hH0 i hi _ _))) hlin)

end DGPS.Lipschitz
