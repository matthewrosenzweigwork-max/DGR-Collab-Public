import LeanResearch.PeriodicAttractiveLogGas.CollectiveCovarianceBounds
import LeanResearch.PeriodicAttractiveLogGas.LabelRatioTransport
import Mathlib.Analysis.SpecialFunctions.Sigmoid
import Mathlib.Analysis.Calculus.MeanValue

/-! The logistic chain rule and the exact probability-concavity factor
in Proposition 3.11. The actual normalizer ratio is identified here;
named-law derivative transport and joint Poincare assembly are separate. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators NNReal ENNReal

namespace PeriodicAttractiveLogGas.CrossingLogistic

open MeshCells MeshAdjacentCells LabelOccupations OneCoordinateConditionals
  ConditionalLawEstimates LabelRatioTransport CollectiveGradientBounds

theorem sigmoid_log_sub {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    Real.sigmoid (Real.log A - Real.log B) = A / (A + B) := by
  rw [Real.sigmoid_def, neg_sub, Real.exp_sub, Real.exp_log hB, Real.exp_log hA]
  field_simp

theorem bernoulli_factor_nonneg {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    0 ≤ q * (1 - q) := mul_nonneg h0 (sub_nonneg.mpr h1)

theorem bernoulli_factor_le (q : ℝ) : q * (1 - q) ≤ 1 / 4 := by
  nlinarith [sq_nonneg (q - 1 / 2)]

theorem bernoulli_factor_sq_le {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    (q * (1 - q)) ^ 2 ≤ q * (1 - q) / 4 := by
  have h := mul_le_mul_of_nonneg_left (bernoulli_factor_le q) (bernoulli_factor_nonneg h0 h1)
  nlinarith

theorem sigmoid_lipschitz : LipschitzWith (1 / 4 : ℝ≥0) Real.sigmoid := by
  apply lipschitzWith_of_nnnorm_deriv_le (fun x ↦ (Real.hasDerivAt_sigmoid x).differentiableAt)
  intro x
  apply NNReal.coe_le_coe.mp
  simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat, coe_nnnorm,
    Real.deriv_sigmoid, Real.norm_eq_abs,
    abs_of_nonneg (bernoulli_factor_nonneg (Real.sigmoid_nonneg x) (Real.sigmoid_le_one x))] using
      bernoulli_factor_le (Real.sigmoid x)

section Chain
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {u : E → ℝ} {u' : E →L[ℝ] ℝ} {x : E}

theorem hasFDerivAt_sigmoid (hu : HasFDerivAt u u' x) :
    HasFDerivAt (fun y ↦ Real.sigmoid (u y))
      ((Real.sigmoid (u x) * (1 - Real.sigmoid (u x))) • u') x := by
  simpa only [Function.comp_def] using! (Real.hasDerivAt_sigmoid (u x)).comp_hasFDerivAt x hu

omit [NormedSpace ℝ E] in
theorem sigmoid_lipschitzOn {K : ℝ≥0} {s : Set E} (hu : LipschitzOnWith K u s) :
    LipschitzOnWith ((1 / 4 : ℝ≥0) * K) (fun x ↦ Real.sigmoid (u x)) s :=
  sigmoid_lipschitz.comp_lipschitzOnWith hu

end Chain

/-- Squared logistic gradient bound, with the source's factor q(1-q)/4. -/
theorem logistic_field_squared {n : ℕ} {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (v : Fin n → V) {q B : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hv : (∑ j, ‖v j‖ ^ 2) ≤ B) :
    (∑ j, ‖(q * (1 - q)) • v j‖ ^ 2) ≤ B / 4 * (q * (1 - q)) := by
  have hs : (∑ j, ‖(q * (1 - q)) • v j‖ ^ 2) =
      (q * (1 - q)) ^ 2 * (∑ j, ‖v j‖ ^ 2) := by
    simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Finset.mul_sum]
  have hB : 0 ≤ B := (Finset.sum_nonneg fun j _ ↦ sq_nonneg _).trans hv
  rw [hs]
  calc
    _ ≤ (q * (1 - q)) ^ 2 * B := mul_le_mul_of_nonneg_left hv (sq_nonneg _)
    _ ≤ (q * (1 - q) / 4) * B :=
      mul_le_mul_of_nonneg_right (bernoulli_factor_sq_le hq0 hq1) hB
    _ = _ := by ring

def normalizerRatio {n J : ℕ} (hJ : 0 < J) (β : ℝ) (a : MeshIndex J) (d : Fin 2)
    (Y : Configuration n) : ℝ :=
  cellNormalizer hJ a β Y / (cellNormalizer hJ a β Y + cellNormalizer hJ (nextCell J hJ a d) β Y)

def logNormalizerRatio {n J : ℕ} (hJ : 0 < J) (β : ℝ) (a : MeshIndex J) (d : Fin 2)
    (Y : Configuration n) : ℝ :=
  Real.log (cellNormalizer hJ a β Y) - Real.log (cellNormalizer hJ (nextCell J hJ a d) β Y)

theorem measurable_cellNormalizer {n J : ℕ} (hJ : 0 < J) (β : ℝ) (a : MeshIndex J) :
    Measurable (fun Y : Configuration n ↦ cellNormalizer hJ a β Y) := by
  have hm : Measurable (fun p : Configuration n × Torus ↦ sourceWeight β p.1 p.2) := by
    apply Real.continuous_exp.measurable.comp
    exact Finset.measurable_sum _ fun j _ ↦
      (regularGreenRepresentative_measurable.comp
        (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))).const_mul _
  exact hm.stronglyMeasurable.integral_prod_right.measurable

theorem measurable_normalizerRatio {n J : ℕ} (hJ : 0 < J) (β : ℝ)
    (a : MeshIndex J) (d : Fin 2) : Measurable (normalizerRatio (n := n) hJ β a d) :=
  (measurable_cellNormalizer hJ β a).div
    ((measurable_cellNormalizer hJ β a).add (measurable_cellNormalizer hJ β (nextCell J hJ a d)))

/-- Both positive actual normalizers are proved from the capped endpoint
completions, including coincident outside sources and zero coupling. -/
theorem adjacent_ratio_sigmoid {n J : ℕ} {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a d)
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y) :
    normalizerRatio (mesh_pos hmesh) β a d Y =
      Real.sigmoid (logNormalizerRatio (mesh_pos hmesh) β a d Y) := by
  have h := adjacent_source_crossing hβ hβ₀ hδ hmesh η i a d hadm Y hY
  exact (sigmoid_log_sub h.2.2.1 h.2.2.2.1).symm

/-- The ratio is the probability of the actual first-cell event in the
actual adjacent conditional kernel, with its own probability normalizer. -/
theorem adjacent_ratio_eq_probability {n J : ℕ} {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a d)
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y) :
    normalizerRatio (mesh_pos hmesh) β a d Y =
      (conditionalKernel (edgeCellMeasure J (mesh_pos hmesh) a d) i β Y
        (meshCell J (mesh_pos hmesh) a)).toReal := by
  let hJ := mesh_pos hmesh
  have hYa := (prescribedOutside_update_iff hJ η i a Y).mpr hY
  have ha := capped_patch_law hJ hβ hβ₀ hδ hmesh (Function.update η i a) hadm.1 i Y hYa a .cell
  have hb := capped_patch_law hJ hβ hβ₀ hδ hmesh (Function.update η i a) hadm.1 i Y hYa
    (nextCell J hJ a d) .cell
  have he := capped_patch_law hJ hβ hβ₀ hδ hmesh (Function.update η i a) hadm.1 i Y hYa a (.edge d)
  exact (conditional_crossing_eq hJ (mesh_two_le hmesh) β β₀ i Y a d ha hb he).symm

/-- The total ratio representative is bounded even away from the capped
source domain: all normalizers are nonnegative, including a zero denominator. -/
theorem normalizerRatio_bounds {n J : ℕ} (hJ : 0 < J) (β : ℝ) (a : MeshIndex J)
    (d : Fin 2) (Y : Configuration n) :
    0 ≤ normalizerRatio hJ β a d Y ∧ normalizerRatio hJ β a d Y ≤ 1 := by
  have hA := cellNormalizer_nonneg hJ a β Y
  have hB := cellNormalizer_nonneg hJ (nextCell J hJ a d) β Y
  exact ⟨div_nonneg hA (add_nonneg hA hB), div_le_one_of_le₀ (le_add_of_nonneg_right hB)
    (add_nonneg hA hB)⟩

theorem normalizerRatio_memLp {n J : ℕ} (hJ : 0 < J) (β : ℝ) (a : MeshIndex J)
    (d : Fin 2) (μ : Measure (Configuration n)) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (normalizerRatio hJ β a d) p μ := by
  apply MemLp.of_bound (measurable_normalizerRatio hJ β a d).aestronglyMeasurable 1
  exact Eventually.of_forall fun Y ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (normalizerRatio_bounds hJ β a d Y).1]
    exact (normalizerRatio_bounds hJ β a d Y).2

/-- The literal logistic field assembled with the actual logarithmic-ratio
expectation field, prior to the separate ordinary-derivative identification. -/
def crossingField {n J : ℕ} (hJ : 0 < J) (β : ℝ) (i : Fin (n + 1))
    (a : MeshIndex J) (d : Fin 2) (Y : Configuration n) (j : Fin n) : PlanarSpace :=
  (normalizerRatio hJ β a d Y * (1 - normalizerRatio hJ β a d Y)) • logRatioField hJ β i a d Y j

theorem adjacent_crossingField_squared {n J : ℕ} {β β₀ δ : ℝ}
    (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hδ₀ : 0 ≤ δ) (hδ : δ ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (d : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a d)
    (Y : Configuration n) (hY : PrescribedOutside (mesh_pos hmesh) η i Y) :
    let q := normalizerRatio (mesh_pos hmesh) β a d Y
    (∑ j, ‖crossingField (mesh_pos hmesh) β i a d Y j‖ ^ 2) ≤
      crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant * J ^ 2 /
        (4 * (n + 1 : ℕ)) * (q * (1 - q)) := by
  have he := adjacent_ratio_sigmoid hβ hβ₀ hδ hmesh η i a d hadm Y hY
  have h0 : 0 ≤ normalizerRatio (mesh_pos hmesh) β a d Y := by rw [he]; exact Real.sigmoid_nonneg _
  have h1 : normalizerRatio (mesh_pos hmesh) β a d Y ≤ 1 := by rw [he]; exact Real.sigmoid_le_one _
  have hg := collective_logRatioField hβ hβ₀ hδ₀ hδ GreenCovarianceBounds.hessianConstant_pos.le
    GreenCovarianceBounds.kernel_hessian_bound hmesh η i a d hadm Y hY
  have h := logistic_field_squared (logRatioField (mesh_pos hmesh) β i a d Y) h0 h1 hg
  dsimp only [crossingField]
  convert h using 1
  ring

section Probability
variable {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

/-- The precise concavity step under the actual probability law. -/
theorem integral_bernoulli_factor_le {q : X → ℝ} (hq : MemLp q 2 μ) :
    (∫ x, q x * (1 - q x) ∂μ) ≤ (∫ x, q x ∂μ) * (1 - ∫ x, q x ∂μ) := by
  have hi := hq.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hs : Integrable (fun x ↦ q x ^ 2) μ := hq.integrable_sq
  have hJ := CollectiveCovarianceBounds.norm_integral_sq_le hq
  simp only [Real.norm_eq_abs, sq_abs] at hJ
  have he : (fun x ↦ q x * (1 - q x)) = (fun x ↦ q x - q x ^ 2) := by funext x; ring
  rw [he, integral_sub hi hs]
  nlinarith

end Probability

end PeriodicAttractiveLogGas.CrossingLogistic
