import LeanResearch.PeriodicAttractiveLogGas.GreenCovarianceBounds
import LeanResearch.PeriodicAttractiveLogGas.CollectiveGradientBounds

/-! The actual covariance sum and conditional-average field in Proposition 3.11.
The identification of this field with the named conditional mean's derivative
is supplied separately by the physical source-chart transport. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.CollectiveCovarianceBounds

open MeshCells MeshAdjacentCells LabelOccupations OneCoordinateConditionals GreenPointWeights
  ConditionalLawEstimates GreenCovarianceBounds CollectiveGradientBounds
  MovingPoleCalculus GreenGradientOscillation
open GreenConditionalInfluence hiding patchDomain

/-- The exact constant C-nabla in the source's average-constant equation. -/
def averageConstant (β₀ δ : ℝ) : ℝ :=
  β₀ ^ 2 * (2 * (2 * (radius β₀ : ℝ) + 5) ^ 2 * δ * nearCoefficient β₀ +
    farCoefficient β₀ hessianConstant (radius β₀))

theorem averageConstant_eq (β₀ δ : ℝ) :
    averageConstant β₀ δ = β₀ ^ 2 * fourthMomentBound β₀ ^ 2 *
      (2 * (2 * (radius β₀ : ℝ) + 5) ^ 2 * δ * densityNormBound β₀ ^ (3 / 2 : ℝ) *
        kernelConstant ^ 2 * (1 + 9 * Real.pi) ^ (9 / 8 : ℝ) +
        5 * hessianConstant ^ 2 / (radius β₀ : ℝ) ^ 4) := by
  unfold averageConstant nearCoefficient farCoefficient
  ring

theorem averageConstant_nonneg (β₀ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ averageConstant β₀ δ := by
  unfold averageConstant
  exact mul_nonneg (sq_nonneg _) (add_nonneg
    (mul_nonneg (by positivity) (nearCoefficient_nonneg β₀))
    (farCoefficient_nonneg β₀ hessianConstant (radius β₀)))

theorem prescribedOutside_patch {n J : ℕ} (hJ : 0 < J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (Y : Configuration n) (hY : PrescribedOutside hJ η i Y) :
    PatchOutside hJ (Function.update η i a) (adjacentShapes i d) i Y := by
  intro j
  simpa [adjacentShapes, Fin.succAbove_ne, patchDomain, TorusPatchDensity.domain,
    LocalPointEstimates.shape] using hY j

/-- The literal original-N-scaled covariance sum. All pointwise near/far
bounds and the completed-label count are discharged for the actual law. -/
theorem collective_covariance {n J : ℕ} {β₀ β δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a d)
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y)
    {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationPhysicalLipschitzOn L f (DeletedConditionalPoincare.closedPatchProduct
      (mesh_pos hmesh) (Function.update η i a) (adjacentShapes i d))) :
    let ν := conditionalKernel (patchMeasure J (mesh_pos hmesh) a (.edge d)) i β Y
    β ^ 2 / (n + 1 : ℕ) ^ 2 *
        (∑ j, ‖vectorCovariance ν (fun z ↦ f (insertSite i z Y))
          (fun z ↦ greenGradient (z - Y j))‖ ^ 2) ≤
      averageConstant β₀ δ / (n + 1 : ℕ) *
        ∫ z, ‖coordinateOrdinaryGradient f i (insertSite i z Y)‖ ^ 2 ∂ν := by
  let hJ := mesh_pos hmesh
  let ν := conditionalKernel (patchMeasure J hJ a (.edge d)) i β Y
  let E := ∫ z, ‖coordinateOrdinaryGradient f i (insertSite i z Y)‖ ^ 2 ∂ν
  let C := fun j ↦ vectorCovariance ν (fun z ↦ f (insertSite i z Y))
    (fun z ↦ greenGradient (z - Y j))
  let R := radius β₀
  let A := nearCoefficient β₀
  let B := farCoefficient β₀ hessianConstant R
  let s := nearSources R hJ η i a d
  have hE : 0 ≤ E := integral_nonneg fun _ ↦ sq_nonneg _
  have hA : 0 ≤ A := nearCoefficient_nonneg β₀
  have hB : 0 ≤ B := farCoefficient_nonneg β₀ hessianConstant R
  have hp (j : Fin n) : ‖C j‖ ^ 2 ≤ A * E ∧
      (¬ NearPair J hJ R a (η (i.succAbove j)) (.edge d) .cell →
        ‖C j‖ ^ 2 ≤ B * E) := by
    have h := adjacent_section_covariance_squared hN hβ hβ₀ hsub hδ hmesh
      η i i a d hadm Y (prescribedOutside_patch hJ η i a d Y hY) hf j
    simpa [adjacentShapes, Fin.succAbove_ne, C, ν, E, A, B, R, hJ] using h
  have hs := sum_le_near_count s (fun j ↦ ‖C j‖ ^ 2) (mul_nonneg hB hE)
    (fun j _ ↦ (hp j).1) (fun j hj ↦ (hp j).2
      (fun hh ↦ hj ((mem_nearSources hJ η i a d j).mpr hh)))
  have hc := nearSources_count (R := R) hJ hδ₀ η i a d hadm
  have hs' : (∑ j, ‖C j‖ ^ 2) ≤
      2 * (2 * (R : ℝ) + 5) ^ 2 * δ * (n + 1 : ℕ) * (A * E) +
        (n + 1 : ℕ) * (B * E) :=
    hs.trans (add_le_add (mul_le_mul_of_nonneg_right hc (mul_nonneg hA hE)) le_rfl)
  have hNp : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hb : β ^ 2 / (n + 1 : ℕ) ^ 2 ≤ β₀ ^ 2 / (n + 1 : ℕ) ^ 2 :=
    div_le_div_of_nonneg_right ((sq_le_sq₀ hβ (hβ.trans hβ₀)).mpr hβ₀) (sq_nonneg _)
  calc
    _ ≤ β₀ ^ 2 / (n + 1 : ℕ) ^ 2 * (∑ j, ‖C j‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg fun j _ ↦ sq_nonneg _)
    _ ≤ β₀ ^ 2 / (n + 1 : ℕ) ^ 2 *
        (2 * (2 * (R : ℝ) + 5) ^ 2 * δ * (n + 1 : ℕ) * (A * E) +
          (n + 1 : ℕ) * (B * E)) :=
      mul_le_mul_of_nonneg_left hs' (div_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by
      change _ = (β₀ ^ 2 * (2 * (2 * (R : ℝ) + 5) ^ 2 * δ * A + B)) /
        (n + 1 : ℕ) * E
      field_simp

section MeanField

variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]
  [NormedSpace ℝ V] [CompleteSpace V] {μ : Measure X} [IsProbabilityMeasure μ]

omit [CompleteSpace V] in
/-- Probability Jensen for the genuine Bochner mean of a vector L2 function. -/
theorem norm_integral_sq_le {G : X → V} (hG : MemLp G 2 μ) :
    ‖∫ x, G x ∂μ‖ ^ 2 ≤ ∫ x, ‖G x‖ ^ 2 ∂μ := by
  have h : ‖∫ x, G x ∂μ‖ ≤ lpNorm G 2 μ := calc
    _ ≤ ∫ x, ‖G x‖ ∂μ := norm_integral_le_integral_norm G
    _ = lpNorm G 1 μ := (lpNorm_one_eq_integral_norm hG.aestronglyMeasurable).symm
    _ ≤ _ := DensityMoments.lpNorm_mono_exponent hG (by norm_num)
  exact (sq_le_sq₀ (norm_nonneg _) (lpNorm_nonneg (f := G) (p := 2) (μ := μ))).mpr h |>.trans
    (le_of_eq (DensityMoments.lpNorm_two_sq hG))

omit [MeasurableSpace X] [CompleteSpace V] [IsProbabilityMeasure μ] [NormedSpace ℝ V] in
theorem norm_sub_sq_le (u v : V) : ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := (sq_le_sq₀ (norm_nonneg (u - v)) (add_nonneg (norm_nonneg u) (norm_nonneg v))).mpr
    (norm_sub_le u v)
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

end MeanField

/-- The actual conditional expectation and covariance appearing on the
right-hand side of the source's average-derivative formula. -/
def conditionalMeanField {n : ℕ} (ν : Measure Torus) (β : ℝ)
    (f : Configuration (n + 1) → ℝ) (i : Fin (n + 1)) (Y : Configuration n)
    (j : Fin n) : PlanarSpace :=
  (∫ z, coordinateOrdinaryGradient f (i.succAbove j) (insertSite i z Y) ∂ν) -
    (β / (n + 1 : ℕ)) • vectorCovariance ν (fun z ↦ f (insertSite i z Y))
      (fun z ↦ greenGradient (z - Y j))

theorem coordinate_section_memLp {n : ℕ} {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationEuclideanLipschitzWith L f) (ν : Measure Torus) [IsFiniteMeasure ν]
    (i k : Fin (n + 1)) (Y : Configuration n) (r : ℝ≥0∞) :
    MemLp (fun z ↦ coordinateOrdinaryGradient f k (insertSite i z Y)) r ν := by
  have hm : Measurable (fun z ↦ coordinateOrdinaryGradient f k (insertSite i z Y)) :=
    (measurable_coordinateOrdinaryGradient hf.continuous k).comp
    ((measurable_insertSite i).comp (measurable_id.prodMk measurable_const))
  exact MemLp.of_bound hm.aestronglyMeasurable (L : ℝ)
    (Eventually.of_forall fun z ↦ norm_coordinateOrdinaryGradient_le hf k (insertSite i z Y))

/-- Summing probability Jensen and the two-term square inequality keeps
the literal unscaled coordinate energies and original-N covariance factor. -/
theorem conditionalMeanField_energy {n : ℕ} {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationEuclideanLipschitzWith L f) (ν : Measure Torus) [IsProbabilityMeasure ν]
    (β : ℝ) (i : Fin (n + 1)) (Y : Configuration n) :
    (∑ j, ‖conditionalMeanField ν β f i Y j‖ ^ 2) ≤
      2 * (∫ z, ∑ j : Fin n, ‖coordinateOrdinaryGradient f (i.succAbove j) (insertSite i z Y)‖ ^ 2 ∂ν) +
      2 * (β ^ 2 / (n + 1 : ℕ) ^ 2 * ∑ j, ‖vectorCovariance ν
        (fun z ↦ f (insertSite i z Y)) (fun z ↦ greenGradient (z - Y j))‖ ^ 2) := by
  have hi (j : Fin n) : Integrable
      (fun z ↦ ‖coordinateOrdinaryGradient f (i.succAbove j) (insertSite i z Y)‖ ^ 2) ν := by
    have hm := coordinate_section_memLp hf ν i (i.succAbove j) Y 2
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  have hp (j : Fin n) : ‖conditionalMeanField ν β f i Y j‖ ^ 2 ≤
      2 * (∫ z, ‖coordinateOrdinaryGradient f (i.succAbove j) (insertSite i z Y)‖ ^ 2 ∂ν) +
      2 * (β ^ 2 / (n + 1 : ℕ) ^ 2 * ‖vectorCovariance ν
        (fun z ↦ f (insertSite i z Y)) (fun z ↦ greenGradient (z - Y j))‖ ^ 2) := by
    have h := norm_sub_sq_le
      (∫ z, coordinateOrdinaryGradient f (i.succAbove j) (insertSite i z Y) ∂ν)
      ((β / (n + 1 : ℕ)) • vectorCovariance ν (fun z ↦ f (insertSite i z Y))
        (fun z ↦ greenGradient (z - Y j)))
    have hJ := norm_integral_sq_le (coordinate_section_memLp hf ν i (i.succAbove j) Y 2)
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow] at h
    exact h.trans (add_le_add (mul_le_mul_of_nonneg_left hJ (by norm_num)) le_rfl)
  calc
    _ ≤ ∑ j, (2 * (∫ z, ‖coordinateOrdinaryGradient f (i.succAbove j) (insertSite i z Y)‖ ^ 2 ∂ν) +
        2 * (β ^ 2 / (n + 1 : ℕ) ^ 2 * ‖vectorCovariance ν
          (fun z ↦ f (insertSite i z Y)) (fun z ↦ greenGradient (z - Y j))‖ ^ 2)) :=
      Finset.sum_le_sum fun j _ ↦ hp j
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
        integral_finsetSum _ (fun j _ ↦ hi j)]

/-- The conditional-average field bound with the source's exact C-nabla.
All law and covariance premises are discharged from admissibility and the
global physical Lipschitz observable; derivative identification is separate. -/
theorem adjacent_meanField_energy {n J : ℕ} {β₀ β δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a d)
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y)
    {f : Configuration (n + 1) → ℝ} {L : ℝ≥0}
    (hf : ConfigurationEuclideanLipschitzWith L f) :
    let ν := conditionalKernel (patchMeasure J (mesh_pos hmesh) a (.edge d)) i β Y
    (∑ j, ‖conditionalMeanField ν β f i Y j‖ ^ 2) ≤
      2 * (∫ z, ∑ j : Fin n, ‖coordinateOrdinaryGradient f (i.succAbove j) (insertSite i z Y)‖ ^ 2 ∂ν) +
      2 * averageConstant β₀ δ / (n + 1 : ℕ) *
        ∫ z, ‖coordinateOrdinaryGradient f i (insertSite i z Y)‖ ^ 2 ∂ν := by
  let ν := conditionalKernel (patchMeasure J (mesh_pos hmesh) a (.edge d)) i β Y
  have hb := (adjacent_conditionals hN hβ hβ₀ hsub hδ hmesh η i i a d hadm).1
    Y (prescribedOutside_patch (mesh_pos hmesh) η i a d Y hY)
  have : IsProbabilityMeasure ν := by simpa [ν, adjacentShapes] using hb.probability
  have hl : ConfigurationPhysicalLipschitzOn L f (DeletedConditionalPoincare.closedPatchProduct
      (mesh_pos hmesh) (Function.update η i a) (adjacentShapes i d)) := by
    intro X _ Z _
    simpa only [Real.dist_eq] using hf X Z
  have hc := collective_covariance hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a d hadm Y hY hl
  have hs := conditionalMeanField_energy hf ν β i Y
  exact hs.trans (by
    have h := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 2)
    convert add_le_add le_rfl h using 1
    ring)

end PeriodicAttractiveLogGas.CollectiveCovarianceBounds
