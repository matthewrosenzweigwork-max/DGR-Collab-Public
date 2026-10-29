import LeanResearch.PeriodicAttractiveLogGas.GreenGradientMoments
import LeanResearch.PeriodicAttractiveLogGas.GreenGradientOscillation
import LeanResearch.PeriodicAttractiveLogGas.InfluenceColumnCount

/-! Actual near-source counting and the collective expectation estimate in
Proposition 3.11. The original particle number is n+1 throughout. -/

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace PeriodicAttractiveLogGas.CollectiveGradientBounds

open MeshCells MeshAdjacentCells MeshNearbyGeometry GreenPointWeights
  LabelOccupations OneCoordinateConditionals GreenConditionalInfluence
  GreenGradientMoments GreenGradientOscillation

def nearSources {n J : ℕ} (R : ℕ) (hJ : 0 < J) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun j ↦ NearPair J hJ R a (η (i.succAbove j)) (.edge d) .cell

theorem mem_nearSources {n J R : ℕ} (hJ : 0 < J) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2) (j : Fin n) :
    j ∈ nearSources R hJ η i a d ↔ NearPair J hJ R a (η (i.succAbove j)) (.edge d) .cell := by
  classical
  simp [nearSources]

/-- The actual completed-label cap bounds the actual near-source set. -/
theorem nearSources_count {n J R : ℕ} (hJ : 0 < J) {δ : ℝ} (hδ : 0 ≤ δ)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible hJ δ η i a d) :
    ((nearSources R hJ η i a d).card : ℝ) ≤
      2 * (2 * (R : ℝ) + 5) ^ 2 * δ * (n + 1 : ℕ) := by
  classical
  let T := (nearSources R hJ η i a d).image i.succAbove
  have hsub : T ⊆ sourceIndices (Function.update η i a) Finset.univ
      (InfluenceColumnCount.nearCells R hJ a (.edge d)) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hnear := (mem_nearSources hJ η i a d j).mp hj
    obtain ⟨u, hu, v, hv, huv⟩ := hnear
    have hv' : v = η (i.succAbove j) := by simpa [patchCells] using hv
    subst v
    apply (mem_sourceIndices _ _ _ _).mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [Function.update_of_ne (Fin.succAbove_ne i j)]
    apply (InfluenceColumnCount.mem_nearCells hJ a _ (.edge d)).mpr
    refine ⟨u, ?_, ?_⟩
    · simpa [InfluenceColumnCount.patchCells, patchCells] using hu
    · simpa only [periodicIndexDistance_comm] using huv
  have hc := InfluenceColumnCount.count_le_of_capped_selection hJ hδ hadm.1 T a (.edge d) hsub
  have he : T.card = (nearSources R hJ η i a d).card :=
    Finset.card_image_of_injective _ (Fin.succAbove_right_injective (p := i))
  simpa only [he] using hc

/-- Paying the far allowance at most n+1 times does not require either
pointwise allowance to dominate the other. -/
theorem sum_le_near_count {n : ℕ} (s : Finset (Fin n)) (f : Fin n → ℝ)
    {A B : ℝ} (hB : 0 ≤ B) (hnear : ∀ j ∈ s, f j ≤ A)
    (hfar : ∀ j ∉ s, f j ≤ B) :
    (∑ j, f j) ≤ (s.card : ℝ) * A + (n + 1 : ℕ) * B := by
  classical
  have hp (j : Fin n) : f j ≤ (if j ∈ s then A else 0) + B := by
    split_ifs with hj
    · exact (hnear j hj).trans (le_add_of_nonneg_right hB)
    · simpa only [zero_add] using hfar j hj
  have he : (∑ j : Fin n, if j ∈ s then A else 0) = (s.card : ℝ) * A := by
    rw [← Finset.sum_filter]
    simp
  calc
    (∑ j, f j) ≤ ∑ j : Fin n, ((if j ∈ s then A else 0) + B) :=
      Finset.sum_le_sum fun j _ ↦ hp j
    _ = (s.card : ℝ) * A + (n : ℝ) * B := by rw [Finset.sum_add_distrib, he]; simp
    _ ≤ (s.card : ℝ) * A + (n + 1 : ℕ) * B := by
      exact add_le_add_right (mul_le_mul_of_nonneg_right (by norm_num) hB) _

def gradientExpectationDifference {n J : ℕ} (hJ : 0 < J) (β : ℝ)
    (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2) (Y : Configuration n) (j : Fin n) : PlanarSpace :=
  (∫ z, greenGradient (z - Y j) ∂conditionalKernel (meshCellMeasure J hJ a) i β Y) -
    ∫ z, greenGradient (z - Y j) ∂conditionalKernel
      (meshCellMeasure J hJ (nextCell J hJ a d)) i β Y

theorem gradientExpectationDifference_near_bound {n J : ℕ} {β₀ β δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (ConditionalLawEstimates.mesh_pos hmesh) δ η i a d)
    (Y : Configuration n)
    (hY : PrescribedOutside (ConditionalLawEstimates.mesh_pos hmesh) η i Y) (j : Fin n) :
    ‖gradientExpectationDifference (ConditionalLawEstimates.mesh_pos hmesh) β i a d Y j‖ ≤
      2 * ConditionalLawEstimates.densityNormBound β₀ * ConditionalLawEstimates.kernelConstant *
        J * (1 + 3 * Real.pi) ^ (3 / 4 : ℝ) := by
  obtain ⟨ha, hb⟩ := adjacent_endpoint_gradient_moments hβ hβ₀ hδ hmesh η i a d hadm Y hY (Y j)
  exact (norm_sub_le _ _).trans (by
    have h := add_le_add ha.norm_integral_le hb.norm_integral_le
    convert h using 1; ring)

/-- The precise squared constant in source equation crossing-constant.
C2 is fixed by a genuine Hessian bound, separately from n,J and the labels. -/
def crossingConstantSquared (β₀ δ C₂ : ℝ) : ℝ :=
  β₀ ^ 2 * (8 * (2 * (ConditionalLawEstimates.radius β₀ : ℝ) + 5) ^ 2 * δ *
    (ConditionalLawEstimates.densityNormBound β₀) ^ 2 * ConditionalLawEstimates.kernelConstant ^ 2 *
      ((1 + 3 * Real.pi) ^ (3 / 4 : ℝ)) ^ 2 +
        5 * C₂ ^ 2 / (ConditionalLawEstimates.radius β₀ : ℝ) ^ 4)

/-- Squaring the actual two endpoint expectations and summing over every
retained source gives the exact constant of Proposition 3.11. The derivative
identification is assembled separately with the actual chart calculus. -/
theorem collective_gradient_expectations {n J : ℕ} {β₀ β δ C₂ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ₀ : 0 ≤ δ)
    (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (ConditionalLawEstimates.mesh_pos hmesh) δ η i a d)
    (Y : Configuration n)
    (hY : PrescribedOutside (ConditionalLawEstimates.mesh_pos hmesh) η i Y) :
    β ^ 2 / (n + 1 : ℕ) ^ 2 *
        (∑ j, ‖gradientExpectationDifference (ConditionalLawEstimates.mesh_pos hmesh) β i a d Y j‖ ^ 2) ≤
      crossingConstantSquared β₀ δ C₂ * J ^ 2 / (n + 1 : ℕ) := by
  let hJ := ConditionalLawEstimates.mesh_pos hmesh
  let R := ConditionalLawEstimates.radius β₀
  let K := ConditionalLawEstimates.densityNormBound β₀
  let C := ConditionalLawEstimates.kernelConstant
  let G := (1 + 3 * Real.pi) ^ (3 / 4 : ℝ)
  let D := gradientExpectationDifference hJ β i a d Y
  let s := nearSources R hJ η i a d
  have hnear (j : Fin n) (_hj : j ∈ s) : ‖D j‖ ^ 2 ≤ (2 * K * C * J * G) ^ 2 := by
    have h := gradientExpectationDifference_near_bound hβ hβ₀ hδ hmesh η i a d hadm Y hY j
    exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans h)).mpr h
  have hfar (j : Fin n) (hj : j ∉ s) :
      ‖D j‖ ^ 2 ≤ (Real.sqrt 5 * C₂ * J / (R : ℝ) ^ 2) ^ 2 := by
    have hf : ¬ NearPair J hJ R a (η (i.succAbove j)) (.edge d) .cell :=
      fun h ↦ hj ((mem_nearSources hJ η i a d j).mpr h)
    have h := (capped_adjacent_gradient_expectations hβ hβ₀ hδ hC hk hmesh η i a d hadm Y hY j hf).2.2
    exact (sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans h)).mpr h
  have hs := sum_le_near_count s (fun j ↦ ‖D j‖ ^ 2)
    (sq_nonneg (Real.sqrt 5 * C₂ * J / (R : ℝ) ^ 2)) hnear hfar
  have hc := nearSources_count (R := R) hJ hδ₀ η i a d hadm
  have hs' : (∑ j, ‖D j‖ ^ 2) ≤
      2 * (2 * (R : ℝ) + 5) ^ 2 * δ * (n + 1 : ℕ) * (2 * K * C * J * G) ^ 2 +
        (n + 1 : ℕ) * (Real.sqrt 5 * C₂ * J / (R : ℝ) ^ 2) ^ 2 :=
    hs.trans (add_le_add (mul_le_mul_of_nonneg_right hc (sq_nonneg _)) le_rfl)
  have hN : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  have hR : (0 : ℝ) < R := by
    exact_mod_cast (show 0 < R from lt_of_lt_of_le (by omega) (ConditionalLawEstimates.radius_one_le β₀))
  have hb : β ^ 2 / (n + 1 : ℕ) ^ 2 ≤ β₀ ^ 2 / (n + 1 : ℕ) ^ 2 :=
    div_le_div_of_nonneg_right ((sq_le_sq₀ hβ (hβ.trans hβ₀)).mpr hβ₀) (sq_nonneg _)
  calc
    _ ≤ β₀ ^ 2 / (n + 1 : ℕ) ^ 2 * (∑ j, ‖D j‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hb (Finset.sum_nonneg fun j _ ↦ sq_nonneg _)
    _ ≤ β₀ ^ 2 / (n + 1 : ℕ) ^ 2 *
        (2 * (2 * (R : ℝ) + 5) ^ 2 * δ * (n + 1 : ℕ) * (2 * K * C * J * G) ^ 2 +
          (n + 1 : ℕ) * (Real.sqrt 5 * C₂ * J / (R : ℝ) ^ 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hs' (div_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by
      simp only [div_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
      change _ = β₀ ^ 2 * (8 * (2 * (R : ℝ) + 5) ^ 2 * δ * K ^ 2 * C ^ 2 * G ^ 2 +
        5 * C₂ ^ 2 / (R : ℝ) ^ 4) * J ^ 2 / (n + 1 : ℕ)
      field_simp
      ring

/-- The literal right-hand side of the source's log-ratio derivative
identity, before the chart-to-conditional-law identification. -/
def logRatioField {n J : ℕ} (hJ : 0 < J) (β : ℝ) (i : Fin (n + 1))
    (a : MeshIndex J) (d : Fin 2) (Y : Configuration n) (j : Fin n) : PlanarSpace :=
  (-β / (n + 1 : ℕ)) • gradientExpectationDifference hJ β i a d Y j

theorem sum_logRatioField_sq {n J : ℕ} (hJ : 0 < J) (β : ℝ) (i : Fin (n + 1))
    (a : MeshIndex J) (d : Fin 2) (Y : Configuration n) :
    (∑ j, ‖logRatioField hJ β i a d Y j‖ ^ 2) =
      β ^ 2 / (n + 1 : ℕ) ^ 2 * (∑ j, ‖gradientExpectationDifference hJ β i a d Y j‖ ^ 2) := by
  simp only [logRatioField, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, div_pow, neg_sq]
  rw [Finset.mul_sum]

theorem collective_logRatioField {n J : ℕ} {β₀ β δ C₂ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ₀ : 0 ≤ δ)
    (hδ : δ ≤ ConditionalLawEstimates.occupationBound β₀)
    (hC : 0 ≤ C₂) (hk : KernelHessianBound C₂)
    (hmesh : 8 * (ConditionalLawEstimates.radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (ConditionalLawEstimates.mesh_pos hmesh) δ η i a d)
    (Y : Configuration n)
    (hY : PrescribedOutside (ConditionalLawEstimates.mesh_pos hmesh) η i Y) :
    (∑ j, ‖logRatioField (ConditionalLawEstimates.mesh_pos hmesh) β i a d Y j‖ ^ 2) ≤
      crossingConstantSquared β₀ δ C₂ * J ^ 2 / (n + 1 : ℕ) := by
  rw [sum_logRatioField_sq]
  exact collective_gradient_expectations hβ hβ₀ hδ₀ hδ hC hk hmesh η i a d hadm Y hY

end PeriodicAttractiveLogGas.CollectiveGradientBounds
