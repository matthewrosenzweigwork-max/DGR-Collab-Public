import LeanResearch.PeriodicAttractiveLogGas.LocalPointEstimates

/-! The exact source P-star, L-star and S-star constants from Proposition
3.4, and their application to actual capped Green point laws. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.OneSiteConstants

open DensityEntropy MeshCells GreenPointWeights ConditionalParameters LabelOccupations LocalPointEstimates

def poincare (c K : ℝ) : ℝ :=
  max (poincareConstant squareSobolevConstant c 4 K)
    (poincareConstant rectangleSobolevConstant c 4 K)

def logSobolev (c K : ℝ) : ℝ :=
  max (logSobolevConstant squareSobolevConstant c 4 K)
    (logSobolevConstant rectangleSobolevConstant c 4 K)

def fourthMoment (c K : ℝ) : ℝ :=
  2 * K ^ (1 / 4 : ℝ) * rectangleSobolevConstant (16 / 3) * c ^ (-1 / 2 : ℝ)

theorem fourthMoment_eq (c K : ℝ) :
    fourthMoment c K = momentConstant rectangleSobolevConstant c 4 K 4 := by
  norm_num [fourthMoment, momentConstant]

theorem squareSobolevConstant_le_rectangle (r : ℝ) :
    squareSobolevConstant r ≤ rectangleSobolevConstant r := by
  unfold squareSobolevConstant rectangleSobolevConstant
  nlinarith [torusSobolevConstant_nonneg r]

theorem source_exponent_norms_finite :
    eLpNorm greenGradient (ENNReal.ofReal (youngExponent (8 / 3))) torusMeasure < ⊤ ∧
      eLpNorm greenGradient (ENNReal.ofReal (youngExponent 4)) torusMeasure < ⊤ ∧
      eLpNorm greenGradient (ENNReal.ofReal (youngExponent (16 / 3))) torusMeasure < ⊤ := by
  exact ⟨torusSobolevConstant_finite (by norm_num),
    torusSobolevConstant_finite (by norm_num), torusSobolevConstant_finite (by norm_num)⟩

theorem poincare_le (b : Patch) (c K : ℝ) :
    poincareConstant (RectangleDilation.sobolevConstant (TorusPatchDensity.kind (shape b))) c 4 K ≤
      poincare c K := by
  cases b with
  | cell => exact le_max_left _ _
  | edge j => exact le_max_right _ _

theorem logSobolev_le (b : Patch) (c K : ℝ) :
    logSobolevConstant (RectangleDilation.sobolevConstant (TorusPatchDensity.kind (shape b))) c 4 K ≤
      logSobolev c K := by
  cases b with
  | cell => exact le_max_left _ _
  | edge j => exact le_max_right _ _

theorem fourthMoment_le (b : Patch) {c K : ℝ} (hc : 0 ≤ c) (hK : 0 ≤ K) :
    momentConstant (RectangleDilation.sobolevConstant (TorusPatchDensity.kind (shape b))) c 4 K 4 ≤
      fourthMoment c K := by
  rw [fourthMoment_eq]
  cases b with
  | edge j => exact le_rfl
  | cell =>
    change momentConstant squareSobolevConstant c 4 K 4 ≤ _
    unfold momentConstant
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (squareSobolevConstant_le_rectangle _)
        (mul_nonneg (by norm_num) (Real.rpow_nonneg hK _))) (Real.rpow_nonneg hc _)

/-- Taking the actual maxima never changes the measure, gradient or
normalization of the previously proved patch estimates. -/
theorem uniform_estimates {J : ℕ} (hJ : 0 < J) (b : Patch) {c K : ℝ}
    (hc : 0 ≤ c) (hK : 0 ≤ K) {ν : Measure Torus} {f : Torus → ℝ}
    (h : TorusPatchDensity.Estimates
      (RectangleDilation.sobolevConstant (TorusPatchDensity.kind (shape b))) J c 4 K ν f) :
    ProbabilityTheory.variance f ν ≤ (poincare c K / (J : ℝ) ^ 2) *
      (∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν) ∧
    entropy ν (fun z ↦ f z ^ 2) ≤
      (((logSobolev c K / (J : ℝ) ^ 2) * (∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν) : ℝ) : EReal) ∧
    MemLp (fun z ↦ f z - ∫ w, f w ∂ν) 4 ν ∧
    lpNorm (fun z ↦ f z - ∫ w, f w ∂ν) 4 ν ≤
      (fourthMoment c K / (J : ℝ)) * lpNorm (torusOrdinaryGradient f) 2 ν := by
  have hJr : (0 : ℝ) < J := by exact_mod_cast hJ
  have hE : 0 ≤ ∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν :=
    integral_nonneg fun z ↦ sq_nonneg _
  have hp := poincare_le b c K
  have hl := logSobolev_le b c K
  have hs := fourthMoment_le b hc hK
  have hm := h.2.2.2.2 4 (by norm_num)
  simp only [ENNReal.ofReal_ofNat] at hm
  refine ⟨h.2.2.1.trans ?_, h.2.2.2.1.trans ?_, hm.1, hm.2.trans ?_⟩
  · gcongr
  · apply EReal.coe_le_coe_iff.mpr
    gcongr
  · gcongr
    exact lpNorm_nonneg

theorem capped_pointWeight_uniform_estimates {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : LabelVector J N) (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (I : Finset (Fin N)) (X : Configuration N)
    (hX : ∀ i ∈ I, X i ∈ closure (meshCell J hJ (η i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (TorusPatchDensity.domain (shape b) J hJ a))) :
    let ν := pointLaw (patchMeasure J hJ a b) (fun i : I ↦ X i) (fun i : I ↦ w i)
    let c := fixedLower β₀ C₀ C₁
    let K := fixedNorm β₀ C₀ C₁
    ProbabilityTheory.variance f ν ≤ (poincare c K / (J : ℝ) ^ 2) *
      (∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν) ∧
    entropy ν (fun z ↦ f z ^ 2) ≤
      (((logSobolev c K / (J : ℝ) ^ 2) * (∫ z, ‖torusOrdinaryGradient f z‖ ^ 2 ∂ν) : ℝ) : EReal) ∧
    MemLp (fun z ↦ f z - ∫ w, f w ∂ν) 4 ν ∧
    lpNorm (fun z ↦ f z - ∫ w, f w ∂ν) 4 ν ≤
      (fourthMoment c K / (J : ℝ)) * lpNorm (torusOrdinaryGradient f) 2 ν := by
  have h := capped_pointWeight_functional_estimates hJ hN hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh
    η hη I X hX w hw₀ hw a b hf
  have hd := lt_of_lt_of_le zero_lt_one (distanceBound_one_le (nearRadius_one_le β₀ C₁))
  have hc : 0 < fixedLower β₀ C₀ C₁ := sourceLowerConstant_pos hd _ _
  have hK : 0 < fixedNorm β₀ C₀ C₁ := sourceNormConstant_pos hd _ _
  exact uniform_estimates hJ b hc.le hK.le h

end PeriodicAttractiveLogGas.OneSiteConstants
