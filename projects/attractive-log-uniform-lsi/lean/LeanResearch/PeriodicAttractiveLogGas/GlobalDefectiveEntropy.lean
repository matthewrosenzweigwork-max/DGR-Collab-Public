import LeanResearch.PeriodicAttractiveLogGas.ResolutionIteration
import LeanResearch.PeriodicAttractiveLogGas.StationaryUniqueness

/-! Source Corollary 7.6: global defective entropy from the actual light
piece and the completed successive-resolution comparison. The displayed
coefficients are exactly the source coefficients, with N^{-1} enlarged
only at the last step. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal BigOperators
namespace PeriodicAttractiveLogGas.GlobalDefectiveEntropy
open ConditionalLawEstimates GreenGradientOscillation ResidualFarExponential
  ResidualNearExponential ReferenceResidual ResolutionCutoffs ResolutionEnergy
  ResolutionIteration HeavyLocalization

def energyCoefficient (J : ℕ) (β₀ t C₂ cFar : ℝ) : ℝ :=
  LightRegionEntropy.energyConstant J β₀ t (t / 2) C₂ cFar +
    ResolutionCoefficients.entropyConstant J β₀ t C₂

def massCoefficient (J : ℕ) (β₀ t C₂ cFar : ℝ) : ℝ :=
  LightRegionEntropy.massConstant J β₀ t (t / 2) C₂ cFar +
    energyCoefficient J β₀ t C₂ cFar * angleConstant t * (J : ℝ) ^ 2

def particleThreshold (J : ℕ) (β₀ t cFar : ℝ) : ℕ :=
  max (FullLabelEntropy.particleThreshold J β₀ t (t / 2) cFar)
    (ResolutionCoefficients.threshold J β₀ t)

theorem coefficients_nonneg {J : ℕ} (hJ : 0 < J) {β₀ t C₂ cFar : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ht : 0 < t) (hC : 0 ≤ C₂) (hcFar : 0 < cFar) :
    0 ≤ energyCoefficient J β₀ t C₂ cFar ∧ 0 ≤ massCoefficient J β₀ t C₂ cFar := by
  obtain ⟨hA, hB⟩ := LightRegionEntropy.constants_nonneg hJ hβ₀ hsub hcFar t (t / 2) C₂
  have hH := ResolutionCoefficients.entropyConstant_nonneg hJ hβ₀ hsub ht hC
  have hθ := angleConstant_nonneg t
  have hE : 0 ≤ energyCoefficient J β₀ t C₂ cFar := add_nonneg hA hH
  exact ⟨hE, add_nonneg hB (mul_nonneg (mul_nonneg hE hθ) (sq_nonneg _))⟩

theorem global_defective_entropy_of_far {N J : ℕ} {β β₀ t C₂ cFar : ℝ}
    (hβ : 0 ≤ β) (hβle : β ≤ β₀) (hsub : β₀ < 4)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (hmeshY : 8 * (chosenRadius β₀ C₂ + 1) ≤ J)
    (ht : 0 < t) (htC : t < occupationBound β₀)
    (hcap : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
      nearScale (chosenRadius β₀ C₂) * t ≤ 1)
    (hscale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t))
    (hsmall : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1)
    (hnearJ : OccupationNearContraction.nearMeshThreshold β₀ ≤ J)
    (hres : HeavyScales.sourceResolution β₀ (t / 4) ≤ J)
    (hsmallJ : 1 / (J ^ 2 : ℕ) < t / 8) (hcFar : 0 < cFar)
    (hlarge : particleThreshold J β₀ t cFar ≤ N)
    (hfar : OccupationCoercivity.FarImbalance (N := N) (t := t) (mesh_pos hmesh) β β₀ cFar)
    (f : C(Configuration N, ℝ)) {K : ℝ≥0}
    (hf : LipschitzWith K (fun y ↦ f (configurationQuotient N y))) :
    entropy (gibbsMeasure greenRealRepresentative N β) (fun X ↦ f X ^ 2) ≤
      ((energyCoefficient J β₀ t C₂ cFar * energy β f +
        massCoefficient J β₀ t C₂ cFar * squareIntegral β f : ℝ) : EReal) := by
  have hlargeL : FullLabelEntropy.particleThreshold J β₀ t (t / 2) cFar ≤ N :=
    (le_max_left _ _).trans hlarge
  have hlargeH : ResolutionCoefficients.threshold J β₀ t ≤ N :=
    (le_max_right _ _).trans hlarge
  have hβ₀ := hβ.trans hβle
  have hδ := (chosen_parameters β₀ hβ₀).2.1
  have ht1 : t / 4 < 1 := by linarith
  have hN : 2 ≤ N := threshold_ge_two ht ht1 hlargeH
  have hJ : 0 < J := mesh_pos hmesh
  have hJ3 : 3 ≤ J := mesh_three_le hmesh
  let G := lightPiece N J hJ t f 0
  obtain ⟨L, hG⟩ := lightPiece_lipschitz N J (by omega) hJ3 ht f hf 0
  have hp := first_cutoff_properties (by omega : 0 < N) hJ3 ht β f hf
  have hr : HeavyScales.sourceResolution β₀ ((t / 2) / 2) ≤ J := by
    simpa only [div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hres
  have hlight := LightRegionEntropy.light_entropy_of_far hβ hβle hsub hC hk hmesh hmeshY ht htC
    hcap hscale hsmall (by linarith : 0 < t / 2) (by linarith : t / 2 < 3 * t / 4)
    hnearJ hr hsmallJ (by linarith : 1 / (J ^ 2 : ℕ) < t / 2) hcFar hlargeL hfar
    (configurationEuclideanLipschitzWith_iff_lift.mpr hG) hp.1
  have hiter := entropy_resolution_iteration hβ hβle hsub ht htC hmesh hC hk hscale hsmall hres hlargeH f hf
  rw [continuous_entropy_eq, continuous_entropy_eq, ← EReal.coe_add] at hiter
  rw [continuous_entropy_eq] at hlight
  have hLi := EReal.coe_le_coe_iff.mp hlight
  have hHi := EReal.coe_le_coe_iff.mp hiter
  rw [← energy_eq_physical β _ hG] at hLi
  have hmass : squareIntegral β G ≤ squareIntegral β f := by
    exact integral_mono (integrable_continuous_sq _ G) (integrable_continuous_sq _ f) hp.2.1
  obtain ⟨hAL, hBL⟩ := LightRegionEntropy.constants_nonneg hJ hβ₀ hsub hcFar t (t / 2) C₂
  have henergy := mul_le_mul_of_nonneg_left hp.2.2 hAL
  have hmass' := mul_le_mul_of_nonneg_left hmass hBL
  have hfirst : Rothaus.squareEntropy (gibbsMeasure greenRealRepresentative N β) f ≤
      energyCoefficient J β₀ t C₂ cFar * initialBound J t β f +
        LightRegionEntropy.massConstant J β₀ t (t / 2) C₂ cFar * squareIntegral β f := by
    unfold energyCoefficient
    change Rothaus.squareEntropy (gibbsMeasure greenRealRepresentative N β) G ≤
      LightRegionEntropy.energyConstant J β₀ t (t / 2) C₂ cFar * energy β G +
        LightRegionEntropy.massConstant J β₀ t (t / 2) C₂ cFar * squareIntegral β G at hLi
    linarith only [hHi, hLi, henergy, hmass']
  have hcoeff := (coefficients_nonneg hJ hβ₀ hsub ht hC hcFar).1
  have hθ := angleConstant_nonneg t
  have hS := squareIntegral_nonneg β f
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hdrop : angleConstant t * (J : ℝ) ^ 2 / N ≤ angleConstant t * (J : ℝ) ^ 2 :=
    div_le_self (mul_nonneg hθ (sq_nonneg _)) hNreal
  have hdrop' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hdrop hS) hcoeff
  rw [continuous_entropy_eq]
  apply EReal.coe_le_coe_iff.mpr
  unfold initialBound at hfirst
  unfold massCoefficient
  nlinarith only [hfirst, hdrop']

end PeriodicAttractiveLogGas.GlobalDefectiveEntropy
