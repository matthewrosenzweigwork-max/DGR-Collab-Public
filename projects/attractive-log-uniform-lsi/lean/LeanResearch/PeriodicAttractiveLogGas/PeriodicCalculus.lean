import LeanResearch.PeriodicAttractiveLogGas.CoreAlgebra
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Group.Integral

/-! Ordinary differentiation and Haar integration on the configuration torus.
Source: unweighted integration by parts in prop:ambient. -/

noncomputable section

open MeasureTheory
open scoped Topology ContDiff

namespace PeriodicAttractiveLogGas

@[simp] theorem configurationQuotient_zero (N : ℕ) : configurationQuotient N 0 = 0 := by
  ext i k
  simp [configurationQuotient]

@[simp] theorem configurationQuotient_add (N : ℕ) (y z : Gradient N) :
    configurationQuotient N (y + z) = configurationQuotient N y + configurationQuotient N z := by
  ext i k
  simp [configurationQuotient]

theorem continuous_configurationQuotient (N : ℕ) : Continuous (configurationQuotient N) := by
  unfold configurationQuotient
  fun_prop

instance : (torusMeasure).IsAddLeftInvariant := by
  unfold torusMeasure
  infer_instance

instance (N : ℕ) : (referenceMeasure N).IsAddLeftInvariant := by
  exact Measure.pi.isAddLeftInvariant (fun _ : Fin N ↦ torusMeasure)

theorem SmoothPair.hasDerivAt_translate {N : ℕ} (f : SmoothPair N)
    (v : Gradient N) (x : Configuration N) (t : ℝ) :
    HasDerivAt (fun s ↦ f.value (configurationQuotient N (s • v) + x))
      (inner ℝ (f.gradient (configurationQuotient N (t • v) + x)) v) t := by
  obtain ⟨y, rfl⟩ := configurationQuotient_surjective N x
  have hline : HasDerivAt (fun s : ℝ ↦ s • v + y) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).add_const y
  have h := (f.differential (t • v + y)).comp_hasDerivAt t hline
  simpa only [configurationQuotient_add, innerSL_apply_apply] using! h

theorem SmoothPair.integral_gradient_inner_eq_zero {N : ℕ} (f : SmoothPair N)
    (v : Gradient N) : ∫ x, inner ℝ (f.gradient x) v ∂referenceMeasure N = 0 := by
  let F (t : ℝ) (x : Configuration N) := f.value (configurationQuotient N (t • v) + x)
  let D (t : ℝ) (x : Configuration N) :=
    inner ℝ (f.gradient (configurationQuotient N (t • v) + x)) v
  have hFcont (t : ℝ) : Continuous (F t) := by dsimp [F]; fun_prop
  have hDcont (t : ℝ) : Continuous (D t) := by dsimp [D]; fun_prop
  have hFint : Integrable (F 0) (referenceMeasure N) := by
    exact memLp_one_iff_integrable.mp
      (ContinuousMap.memLp (μ := referenceMeasure N) (p := 1) ℝ ⟨F 0, hFcont 0⟩)
  have hbound : ∀ᵐ x ∂referenceMeasure N, ∀ t ∈ (Set.univ : Set ℝ),
      ‖D t x‖ ≤ ‖f.gradient‖ * ‖v‖ := by
    apply Filter.Eventually.of_forall
    intro x t _
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (f.gradient.norm_coe_le_norm _) (norm_nonneg v))
  have hdiff := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := referenceMeasure N) (F := F) (F' := D) (x₀ := (0 : ℝ))
    (s := Set.univ) (bound := fun _ ↦ ‖f.gradient‖ * ‖v‖)
    Filter.univ_mem (Filter.Eventually.of_forall fun t ↦ (hFcont t).aestronglyMeasurable)
    hFint (hDcont 0).aestronglyMeasurable hbound (integrable_const _)
    (Filter.Eventually.of_forall fun x t _ ↦ f.hasDerivAt_translate v x t)
  have hconst : (fun t : ℝ ↦ ∫ x, F t x ∂referenceMeasure N) =
      fun _ ↦ ∫ x, f.value x ∂referenceMeasure N := by
    funext t
    exact integral_add_left_eq_self f.value (configurationQuotient N (t • v))
  have heq := hdiff.2.unique (hconst ▸ hasDerivAt_const (0 : ℝ)
    (∫ x, f.value x ∂referenceMeasure N))
  simpa only [D, zero_smul, configurationQuotient_zero, zero_add] using heq

theorem SmoothPair.integration_by_parts {N : ℕ} (f g : SmoothPair N)
    (v : Gradient N) :
    ∫ x, g.value x * inner ℝ (f.gradient x) v ∂referenceMeasure N =
      -(∫ x, f.value x * inner ℝ (g.gradient x) v ∂referenceMeasure N) := by
  have hf : Integrable (fun x ↦ g.value x * inner ℝ (f.gradient x) v)
      (referenceMeasure N) := by
    exact memLp_one_iff_integrable.mp
      (ContinuousMap.memLp (μ := referenceMeasure N) (p := 1) ℝ
        ⟨_, g.value.continuous.mul (f.gradient.continuous.inner continuous_const)⟩)
  have hg : Integrable (fun x ↦ f.value x * inner ℝ (g.gradient x) v)
      (referenceMeasure N) := by
    exact memLp_one_iff_integrable.mp
      (ContinuousMap.memLp (μ := referenceMeasure N) (p := 1) ℝ
        ⟨_, f.value.continuous.mul (g.gradient.continuous.inner continuous_const)⟩)
  have h := (f.mul g).integral_gradient_inner_eq_zero v
  simp only [SmoothPair.mul, ContinuousMap.coe_mk, inner_add_left, inner_smul_left,
    conj_trivial] at h
  rw [integral_add hf hg] at h
  exact eq_neg_of_add_eq_zero_left h

end PeriodicAttractiveLogGas
