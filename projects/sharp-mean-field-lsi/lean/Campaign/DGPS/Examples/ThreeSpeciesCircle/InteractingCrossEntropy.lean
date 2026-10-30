import DGPS.Examples.ThreeSpeciesCircle.InteractingEntropyComparison
import DGPS.Examples.ThreeSpeciesCircle.InteractingGeneratorCentering

/-!
# The actual noncommuting generator correction is controlled by entropy

Both factors are genuine centered moments. Compactness bounds each smooth feature and
its actual physical generator; full variation and Pinsker then control their product.
All constants are chosen after h and before the finite family or its weights.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace DGPS.Examples.ThreeSpeciesCircle

/-- A centered feature moment times an actual generator moment is controlled by the
sum of ordinary entropies for every full-domain finite family. -/
theorem elementary_generator_product_entropy_bound (h : ℝ) (φ ψ : Torus 1 → ℝ)
    (hφ : IsSmoothPeriodic φ) (hψ : IsSmoothPeriodic ψ)
    (hφ0 : (∫ x, φ x ∂threefoldReference h) = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ F : SpeciesFamily 1,
      |(∫ x, φ x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) *
        (∫ x, elementaryFeatureGenerator h ψ x
          ∂(densityMeasure (barycenter F) : Measure (Torus 1)))| ≤
        K * ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal := by
  let B : Torus 1 →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨φ, hφ.continuous_torus⟩
  let G : Torus 1 →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨elementaryFeatureGenerator h ψ, continuous_elementaryFeatureGenerator h ψ hψ⟩
  refine ⟨2 * ‖B‖ * ‖G‖, by positivity, fun F => ?_⟩
  let ν := densityMeasure (barycenter F)
  let T := fullVariation (ν : Measure (Torus 1)) (threefoldReference h)
  let E := ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal
  have hT : 0 ≤ T := fullVariation_nonneg _ _
  have hB := Structural.abs_integral_sub_le_fullVariation
    (ν : Measure (Torus 1)) (threefoldReference h) B
  change |(∫ x, φ x ∂(ν : Measure (Torus 1))) - ∫ x, φ x ∂threefoldReference h| ≤ ‖B‖ * T at hB
  rw [hφ0, sub_zero] at hB
  have hG := Structural.abs_integral_sub_le_fullVariation
    (ν : Measure (Torus 1)) (threefoldReference h) G
  change |(∫ x, elementaryFeatureGenerator h ψ x ∂(ν : Measure (Torus 1))) -
    ∫ x, elementaryFeatureGenerator h ψ x ∂threefoldReference h| ≤ ‖G‖ * T at hG
  rw [elementaryFeatureGenerator_reference_mean_zero h ψ hψ, sub_zero] at hG
  have hprod := mul_le_mul hB hG (abs_nonneg _) (mul_nonneg (norm_nonneg _) hT)
  rw [← abs_mul] at hprod
  have hbar : (relativeEntropy (ν : Measure (Torus 1)) (threefoldReference h)).toReal ≤ E :=
    Structural.relativeEntropy_barycenter_le_sum F (ordinaryReference h)
  have hp := pinsker_fullVariation_real (ν : Measure (Torus 1)) (threefoldReference h)
    (Structural.relativeEntropy_reference (ordinaryReference h) (barycenter F)).1
  have hTV : T ^ 2 ≤ 2 * E := hp.trans (by linarith)
  calc
    _ ≤ (‖B‖ * T) * (‖G‖ * T) := hprod
    _ = (‖B‖ * ‖G‖) * T ^ 2 := by ring
    _ ≤ (‖B‖ * ‖G‖) * (2 * E) :=
      mul_le_mul_of_nonneg_left hTV (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by ring

/-- The actual C correction is O(E) for every original finite family. The feature and
its physical generator stay distinct; no kernel-generator commutation is used. -/
theorem elementaryC_family_entropy_bound {h : ℝ} (hh : 0 < h) (a : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ F : SpeciesFamily 1,
      |elementaryC h a (barycenter F)| ≤
        K * ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal := by
  obtain ⟨hc, hs, hb, _⟩ := elementaryFeatures_centered_independent hh
  obtain ⟨KC, hKC, hC⟩ := elementary_generator_product_entropy_bound h
    (featureC h) (featureC h) (smooth_featureC h) (smooth_featureC h) hc
  obtain ⟨KS, hKS, hS⟩ := elementary_generator_product_entropy_bound h
    (featureS h) (featureS h) (smooth_featureS h) (smooth_featureS h) hs
  obtain ⟨KB, hKB, hB⟩ := elementary_generator_product_entropy_bound h
    (featureB h) (featureB h) (smooth_featureB h) (smooth_featureB h) hb
  obtain ⟨KQ, hKQ, hQ⟩ := elementaryQ_family_entropy_bound hh
  let K := 2 * kAlpha * (KC + KS) + 2 * kBeta * KB + |a| * KQ + 1
  have hK : 0 < K := by
    dsimp [K]
    have := kAlpha_pos
    have := kBeta_pos
    positivity
  have hkAlpha : 0 ≤ kAlpha := kAlpha_pos.le
  have hkBeta : 0 ≤ kBeta := kBeta_pos.le
  refine ⟨K, hK, fun F => ?_⟩
  let ν := densityMeasure (barycenter F)
  let E := ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal
  let PC := momC h ν * ∫ x, elementaryFeatureGenerator h (featureC h) x ∂(ν : Measure (Torus 1))
  let PS := momS h ν * ∫ x, elementaryFeatureGenerator h (featureS h) x ∂(ν : Measure (Torus 1))
  let PB := momB h ν * ∫ x, elementaryFeatureGenerator h (featureB h) x ∂(ν : Measure (Torus 1))
  have hPC : |PC| ≤ KC * E := hC F
  have hPS : |PS| ≤ KS * E := hS F
  have hPB : |PB| ≤ KB * E := hB F
  have hQE : |elementaryQ h ν| ≤ KQ * E := hQ F
  have hE : 0 ≤ E := Finset.sum_nonneg fun s _ =>
    mul_nonneg (F.weight_nonneg s) ENNReal.toReal_nonneg
  have hactual : elementaryC h a (barycenter F) =
      2 * kAlpha * (PC + PS) - 2 * kBeta * PB - a * elementaryQ h ν := by
    rw [elementaryC_moments, elementaryQ_moments]
    dsimp only [PC, PS, PB, ν]
    ring
  rw [hactual]
  calc
    _ ≤ |2 * kAlpha * (PC + PS) - 2 * kBeta * PB| + |a * elementaryQ h ν| := abs_sub _ _
    _ ≤ (|2 * kAlpha * (PC + PS)| + |2 * kBeta * PB|) + |a * elementaryQ h ν| :=
      add_le_add (abs_sub _ _) le_rfl
    _ = 2 * kAlpha * |PC + PS| + 2 * kBeta * |PB| + |a| * |elementaryQ h ν| := by
      rw [abs_mul (2 * kAlpha) (PC + PS), abs_of_pos (mul_pos (by norm_num) kAlpha_pos),
        abs_mul (2 * kBeta) PB, abs_of_pos (mul_pos (by norm_num) kBeta_pos),
        abs_mul a (elementaryQ h ν)]
    _ ≤ 2 * kAlpha * (|PC| + |PS|) + 2 * kBeta * |PB| + |a| * |elementaryQ h ν| := by
      gcongr
      exact abs_add_le _ _
    _ ≤ 2 * kAlpha * (KC * E + KS * E) + 2 * kBeta * (KB * E) + |a| * (KQ * E) := by
      gcongr
    _ ≤ K * E := by dsimp [K]; nlinarith

end DGPS.Examples.ThreeSpeciesCircle
