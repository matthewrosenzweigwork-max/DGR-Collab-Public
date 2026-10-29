import SharpSymmetricLSI.Paper.CircleLSIExt
import DGPS.Analysis.LSITensorization
import DGPS.Foundations.AbsoluteDensity
import DGPS.Foundations.RelativeEntropy

/-!
# Circle quantitative LSI on the absolute domain (FOU016)

For every absolute-admissible density `ρ = u²` on the unit circle, with `a0 = 4π²`,
`I(ρ) ≥ 2 a0 H(ρ|m) + (a0/6) H(ρ|m)²` and `H(ρ|m) ≤ 6 log (1 + I(ρ)/(12 a0))`, where
`I(ρ) = 4 ∫ |u'|² dm` (weak gradient of the `H¹` square root) and `H(ρ|m)` is the homogeneous
entropy of `ρ`; both are finite (zero sets of `ρ` included). The proof transfers to the legacy
`SharpLSI.circle_quantitative_lsi_aux` (heat-flow argument) through the weak-gradient bridge.
-/

open MeasureTheory

namespace DGPS.Analysis

/-- Circle Fisher information of an absolute-admissible density. -/
noncomputable def circleFisherInformation (ρ : AbsoluteDensity 1) : ℝ :=
  4 * ∫ x, ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar 1

/-- Circle relative entropy `H(ρ|m)` as a real number. -/
noncomputable def circleEntropy (ρ : AbsoluteDensity 1) : ℝ :=
  (homogeneousEntropy (haar 1) ρ.density).toReal

theorem circle_quantitative_lsi_on_the_absolute_domain (ρ : AbsoluteDensity 1) :
    homogeneousEntropy (haar 1) ρ.density ≠ ⊤ ∧
    Integrable (fun x => ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2) (haar 1) ∧
    2 * (4 * Real.pi ^ 2) * circleEntropy ρ + (4 * Real.pi ^ 2) / 6 * circleEntropy ρ ^ 2 ≤
      circleFisherInformation ρ ∧
    circleEntropy ρ ≤ 6 * Real.log (1 + circleFisherInformation ρ / (12 * (4 * Real.pi ^ 2))) := by
  set g := weakGradient ρ.sqrt ρ.sqrt_mem with hg
  have hw : IsWeakGradient ρ.sqrt g := isWeakGradient_weakGradient ρ.sqrt_mem
  have hae : (fun x => Real.sqrt (ρ.density x)) =ᵐ[haar 1] ρ.sqrt := by
    filter_upwards [ρ.sqrt_nonneg] with x hx
    simp [AbsoluteDensity.density, Real.sqrt_sq hx]
  have hw' : IsWeakGradient (fun x => Real.sqrt (ρ.density x)) g :=
    hw.congr_ae hae.symm (Filter.EventuallyEq.refl _ _)
  obtain ⟨hH, hgrad⟩ := legacy_memH1 hw'
  have key := SharpLSI.circle_quantitative_lsi_aux ρ.density_nonneg ρ.mass_one hH
  have hI := SharpLSI.fisherInfo_densMeasure_eq ρ.density_nonneg ρ.mass_one hH
  have hEq : InformationTheory.klDiv (SharpLSI.densMeasure ρ.density) (SharpLSI.haar 1) =
      homogeneousEntropy (haar 1) ρ.density := by
    rw [SharpLSI.klDiv_densMeasure ρ.density_nonneg ρ.mass_one, entropy_mass_one (v := ρ.density) ρ.mass_one]
    refine lintegral_congr fun x => ?_
    simp only [InformationTheory.klFun]
    congr 1; ring
  have hnorm : ∀ᵐ x ∂haar 1, SharpLSI.weakGrad (fun x => Real.sqrt (ρ.density x)) x 0 ^ 2 =
      ‖g x‖ ^ 2 := by
    filter_upwards [hgrad] with x hx
    rw [hx, tangent_norm_sq]
    simp
  have hint : Integrable (fun x => ‖g x‖ ^ 2) (haar 1) := hw.memLp_grad.norm.integrable_sq
  have hInt : ∫ x, SharpLSI.weakGrad (fun x => Real.sqrt (ρ.density x)) x 0 ^ 2 ∂haar 1 =
      ∫ x, ‖g x‖ ^ 2 ∂haar 1 := integral_congr_ae hnorm
  have hF : (SharpLSI.fisherInfo (SharpLSI.densMeasure ρ.density) (SharpLSI.haar 1)).toReal =
      circleFisherInformation ρ := by
    rw [hI, ENNReal.toReal_ofReal, hInt]
    · rfl
    · positivity
  obtain ⟨hk, -, hlog, hq⟩ := key
  rw [hEq] at hk hlog hq
  rw [hF] at hlog hq
  refine ⟨hk, hint, ?_, hlog⟩
  have : (4 * Real.pi ^ 2) = SharpLSI.aCos := rfl
  rw [this]
  unfold circleEntropy
  linarith

end DGPS.Analysis
