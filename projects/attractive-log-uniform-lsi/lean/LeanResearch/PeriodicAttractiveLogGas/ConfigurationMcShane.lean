import LeanResearch.PeriodicAttractiveLogGas.ConfigurationMetric
import LeanResearch.PeriodicAttractiveLogGas.ConfigurationLipschitzDomain

/-! The scalar McShane extension in the actual Euclidean quotient distance.

This is the literal infimum formula in the manuscript's paragraph following
Lemma 2.7. Its proof follows the supplied triangle-inequality argument, as also
implemented for an ambient metric instance in the pinned Mathlib theorem
`LipschitzOnWith.extend_real`. Here the physical metric is explicit so that the
pre-existing iterated Pi metric instance and the original constant are retained.
The domain is any nonempty subset; no closedness or measurable-subset hypothesis
is needed. No support-preservation assertion is made.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace PeriodicAttractiveLogGas

/-- The literal real infimum in the manuscript's McShane formula. -/
def configurationMcShaneExtension {N : ℕ} (A : Set (Configuration N))
    (f : A → ℝ) (K : ℝ≥0) (X : Configuration N) : ℝ :=
  ⨅ Y : A, f Y + (K : ℝ) * configurationEuclideanDist (X : Configuration N) (Y : Configuration N)

theorem configurationMcShane_bddBelow {N : ℕ} {A : Set (Configuration N)}
    (hA : A.Nonempty) (f : A → ℝ) {K : ℝ≥0}
    (hf : ∀ Y Z : A, dist (f Y) (f Z) ≤
      (K : ℝ) * configurationEuclideanDist (Y : Configuration N) (Z : Configuration N)) (X : Configuration N) :
    BddBelow (range (fun Y : A ↦ f Y + (K : ℝ) * configurationEuclideanDist (X : Configuration N) (Y : Configuration N))) := by
  obtain ⟨z, hz⟩ := hA
  let Z : A := ⟨z, hz⟩
  refine ⟨f Z - (K : ℝ) * configurationEuclideanDist X Z, ?_⟩
  rintro _ ⟨Y, rfl⟩
  have hzy : f Z - f Y ≤ (K : ℝ) * configurationEuclideanDist (Z : Configuration N) (Y : Configuration N) :=
    (le_abs_self _).trans (by simpa only [Real.dist_eq] using hf Z Y)
  have ht := mul_le_mul_of_nonneg_left
    (configurationEuclideanDist_triangle (Z : Configuration N) X Y) K.coe_nonneg
  rw [configurationEuclideanDist_comm (Z : Configuration N) X, mul_add] at ht
  linarith

theorem configurationMcShane_le {N : ℕ} {A : Set (Configuration N)}
    (hA : A.Nonempty) (f : A → ℝ) {K : ℝ≥0}
    (hf : ∀ Y Z : A, dist (f Y) (f Z) ≤
      (K : ℝ) * configurationEuclideanDist (Y : Configuration N) (Z : Configuration N)) (X : Configuration N) (Y : A) :
    configurationMcShaneExtension A f K X ≤
      f Y + (K : ℝ) * configurationEuclideanDist (X : Configuration N) (Y : Configuration N) :=
  ciInf_le (configurationMcShane_bddBelow hA f hf X) Y

/-- Agreement on the original subset, with no regularity premise beyond the
given Lipschitz inequality. -/
theorem configurationMcShane_eq {N : ℕ} {A : Set (Configuration N)}
    (hA : A.Nonempty) (f : A → ℝ) {K : ℝ≥0}
    (hf : ∀ Y Z : A, dist (f Y) (f Z) ≤
      (K : ℝ) * configurationEuclideanDist (Y : Configuration N) (Z : Configuration N)) (X : A) :
    configurationMcShaneExtension A f K X = f X := by
  let : Nonempty A := hA.to_subtype
  apply le_antisymm
  · simpa only [configurationEuclideanDist_self, mul_zero, add_zero] using
      configurationMcShane_le hA f hf X X
  · apply le_ciInf
    intro Y
    have hxy : f X - f Y ≤ (K : ℝ) * configurationEuclideanDist (X : Configuration N) (Y : Configuration N) :=
      (le_abs_self _).trans (by simpa only [Real.dist_eq] using hf X Y)
    linarith

/-- The extension has the identical physical Lipschitz constant. -/
theorem configurationMcShane_lipschitz {N : ℕ} {A : Set (Configuration N)}
    (hA : A.Nonempty) (f : A → ℝ) {K : ℝ≥0}
    (hf : ∀ Y Z : A, dist (f Y) (f Z) ≤
      (K : ℝ) * configurationEuclideanDist (Y : Configuration N) (Z : Configuration N)) :
    ConfigurationEuclideanLipschitzWith K (configurationMcShaneExtension A f K) := by
  let : Nonempty A := hA.to_subtype
  have hle (X Y : Configuration N) :
      configurationMcShaneExtension A f K X ≤
        configurationMcShaneExtension A f K Y +
          (K : ℝ) * configurationEuclideanDist (X : Configuration N) (Y : Configuration N) := by
    rw [← sub_le_iff_le_add]
    apply le_ciInf
    intro Z
    rw [sub_le_iff_le_add]
    have ht := mul_le_mul_of_nonneg_left
      (configurationEuclideanDist_triangle X Y (Z : Configuration N)) K.coe_nonneg
    rw [mul_add] at ht
    have hb := configurationMcShane_le hA f hf X Z
    linarith
  intro X Y
  rw [Real.dist_eq]
  have hxy := hle X Y
  have hyx := hle Y X
  rw [configurationEuclideanDist_comm Y X] at hyx
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The physical Lipschitz extension is continuous in the existing quotient
topology and can be used by the actual ambient smoothing construction. -/
def configurationMcShaneContinuousMap {N : ℕ} {A : Set (Configuration N)}
    (hA : A.Nonempty) (f : A → ℝ) {K : ℝ≥0}
    (hf : ∀ Y Z : A, dist (f Y) (f Z) ≤
      (K : ℝ) * configurationEuclideanDist (Y : Configuration N) (Z : Configuration N)) : C(Configuration N, ℝ) :=
  ⟨configurationMcShaneExtension A f K,
    (configurationMcShane_lipschitz hA f hf).continuous⟩

/-- The actual scalar class of the extension lies in the full ambient graph. -/
theorem configurationMcShane_ambient_value {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    {A : Set (Configuration N)} (hA : A.Nonempty) (f : A → ℝ) {K : ℝ≥0}
    (hf : ∀ Y Z : A, dist (f Y) (f Z) ≤
      (K : ℝ) * configurationEuclideanDist (Y : Configuration N) (Z : Configuration N)) :
    ambientValue (configurationLipschitzAmbient μ hμ
      (configurationMcShaneContinuousMap hA f hf)
      (configurationMcShane_lipschitz hA f hf).lift) =
        ContinuousMap.toLp 2 μ ℝ (configurationMcShaneContinuousMap hA f hf) := rfl

/-- The preceding full form-norm smoothing applies to this very extension.
Support control, when needed, still requires the separate positive-margin
theorem and is not a consequence of the extension formula. -/
theorem configurationMcShane_smooth_formNorm_approx {N : ℕ}
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] (hμ : μ ≪ referenceMeasure N)
    {A : Set (Configuration N)} (hA : A.Nonempty) (f : A → ℝ) {K : ℝ≥0}
    (hf : ∀ Y Z : A, dist (f Y) (f Z) ≤
      (K : ℝ) * configurationEuclideanDist (Y : Configuration N) (Z : Configuration N)) :
    Tendsto (fun n ↦ graphFormNorm
      ((ContinuousMap.toLp 2 μ ℝ
          (configurationLipschitzSmoothApprox (configurationMcShaneContinuousMap hA f hf) n).value,
        ContinuousMap.toLp 2 μ ℝ
          (configurationLipschitzSmoothApprox (configurationMcShaneContinuousMap hA f hf) n).gradient) -
        (configurationLipschitzAmbient μ hμ (configurationMcShaneContinuousMap hA f hf)
          (configurationMcShane_lipschitz hA f hf).lift).1)) atTop (𝓝 0) :=
  configurationLipschitzAmbient_smooth_formNorm_approx μ hμ
    (configurationMcShaneContinuousMap hA f hf)
    (configurationMcShane_lipschitz hA f hf).lift

end PeriodicAttractiveLogGas
