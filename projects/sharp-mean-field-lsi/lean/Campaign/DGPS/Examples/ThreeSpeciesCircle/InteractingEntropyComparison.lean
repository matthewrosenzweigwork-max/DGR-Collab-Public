import DGPS.Examples.ThreeSpeciesCircle.InteractingDeficitExpansion
import DGPS.Structural.PositivityFromResidual

/-!
# Actual finite-family entropy comparison for the elementary interaction

The centered compact kernel and Pinsker control the quadratic correction uniformly over
all finite weighted families. The coupling threshold is chosen after h is fixed.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual model correction at unit coupling is the unscaled elementary quadratic form. -/
theorem elementaryQ_eq_centeredCorrection {h : ℝ} (hh : 0 < h)
    (ν : ProbabilityMeasure (Torus 1)) :
    Structural.centeredCorrection (modelData h 1) (refProb hh) ν =
      elementaryQ h (ν : Measure (Torus 1)) := by
  unfold Structural.centeredCorrection
  rw [Structural.integral_kernelPotential_self, sub_zero]
  have hp : ∀ x, Structural.kernelPotential (modelData h 1) (refProb hh) ν x =
      elementaryKernelMean h (ν : Measure (Torus 1)) x := by
    intro x
    unfold Structural.kernelPotential
    simp_rw [centeredKernel_model hh, one_mul]
    change (∫ y, kernelK h x y ∂(ν : Measure (Torus 1))) -
      (∫ y, kernelK h x y ∂threefoldReference h) = _
    rw [integral_kernelK_right hh, sub_zero, integral_kernelK_eq_mean]
  simp_rw [hp]
  rfl

/-- A genuine entropy bound for the actual quadratic correction, uniform over every
finite count and every positive weight. No lower bound on a weight is used. -/
theorem elementaryQ_family_entropy_bound {h : ℝ} (hh : 0 < h) :
    ∃ K : ℝ, 0 < K ∧ ∀ F : SpeciesFamily 1,
      |elementaryQ h (densityMeasure (barycenter F))| ≤
        K * ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal := by
  let B : (Torus 1 × Torus 1) →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun p => kernelK h p.1 p.2, continuous_kernelK h⟩
  let Kb : ℝ := ‖B‖
  have hKb : 0 ≤ Kb := norm_nonneg _
  have hK : ∀ x y, |centeredKernel (modelData h 1) (refProb hh) x y| ≤ Kb := by
    intro x y
    rw [centeredKernel_model hh, one_mul]
    exact (show ‖B (x, y)‖ ≤ ‖B‖ from BoundedContinuousFunction.norm_coe_le_norm B (x, y))
  refine ⟨2 * (Kb + 1), by positivity, fun F => ?_⟩
  let ν := densityMeasure (barycenter F)
  let E := ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal
  have hE : 0 ≤ E := Finset.sum_nonneg fun s _ =>
    mul_nonneg (F.weight_nonneg s) ENNReal.toReal_nonneg
  have hbar : (relativeEntropy (ν : Measure (Torus 1)) (threefoldReference h)).toReal ≤ E :=
    Structural.relativeEntropy_barycenter_le_sum F (ordinaryReference h)
  have hpin := pinsker_fullVariation_real (ν : Measure (Torus 1)) (threefoldReference h)
    (Structural.relativeEntropy_reference (ordinaryReference h) (barycenter F)).1
  have hQ := Structural.abs_centeredCorrection_le (modelData h 1) (refProb hh) ν hKb hK
  rw [elementaryQ_eq_centeredCorrection hh] at hQ
  have hTV : fullVariation (ν : Measure (Torus 1)) (threefoldReference h) ^ 2 ≤ 2 * E :=
    hpin.trans (by linarith)
  change |elementaryQ h (ν : Measure (Torus 1))| ≤ 2 * (Kb + 1) * E
  calc
    _ ≤ Kb * fullVariation (ν : Measure (Torus 1)) (threefoldReference h) ^ 2 := hQ
    _ ≤ Kb * (2 * E) := mul_le_mul_of_nonneg_left hTV hKb
    _ ≤ _ := by nlinarith

/-- On a genuine h-dependent coupling interval, the actual gap is uniformly comparable
to the sum of ordinary reference entropies for EVERY original finite family. -/
theorem elementaryModel_speciesGap_entropy_comparable {h : ℝ} (hh : 0 < h) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ F : SpeciesFamily 1,
        (1 / 2 : ℝ) * (∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal) ≤
          (speciesGap (modelData h ε) F : ℝ) ∧
        (speciesGap (modelData h ε) F : ℝ) ≤
          (3 / 2 : ℝ) * (∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal) := by
  obtain ⟨K, hK, hQ⟩ := elementaryQ_family_entropy_bound hh
  let ε0 := min (epsMax h) K⁻¹
  refine ⟨ε0, lt_min (epsMax_pos h) (inv_pos.mpr hK), min_le_left _ _, fun ε hε hε0 F => ?_⟩
  have hεmax : ε < epsMax h := hε0.trans_le (min_le_left _ _)
  have hεK : ε * K ≤ 1 := by
    have he : ε < K⁻¹ := hε0.trans_le (min_le_right _ _)
    have hm := mul_lt_mul_of_pos_right he hK
    rw [inv_mul_cancel₀ hK.ne'] at hm
    exact hm.le
  let E := ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal
  have hE : 0 ≤ E := Finset.sum_nonneg fun s _ =>
    mul_nonneg (F.weight_nonneg s) ENNReal.toReal_nonneg
  have hg := elementaryModel_speciesGap_expansion hh hε hεmax F
  have hQlo := (abs_le.mp (hQ F)).1
  have hQhi := (abs_le.mp (hQ F)).2
  have hlo := mul_le_mul_of_nonneg_left hQlo hε.le
  have hhi := mul_le_mul_of_nonneg_left hQhi hε.le
  have hm := mul_le_mul_of_nonneg_right hεK hE
  change (1 / 2 : ℝ) * E ≤ (speciesGap (modelData h ε) F : ℝ) ∧
    (speciesGap (modelData h ε) F : ℝ) ≤ 3 / 2 * E
  change (speciesGap (modelData h ε) F : ℝ) = E + ε / 2 *
    elementaryQ h (densityMeasure (barycenter F)) at hg
  constructor <;> nlinarith

end DGPS.Examples.ThreeSpeciesCircle
