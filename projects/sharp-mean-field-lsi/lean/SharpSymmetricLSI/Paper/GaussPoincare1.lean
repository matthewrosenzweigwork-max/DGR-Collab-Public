import SharpSymmetricLSI.Vendor.SLT.EfronStein
import SharpSymmetricLSI.Vendor.SLT.GaussianPoincare.Limit
import SharpSymmetricLSI.Paper.GaussForm17

/-!
# (8.10), Poincaré half (lane s42): the Gaussian Poincaré inequality on `ℝⁿ`

`Var_{γ_n}(F) ≤ ∫ |∇F|² dγ_n` for `F ∈ C_c^∞(ℝⁿ)`, `γ_n = N(0,1)^{⊗n}` (`gpi n`): the
Efron–Stein inequality (Vendor/SLT `efronStein`) reduces to the coordinate slices
`t ↦ F(x[i ↦ t])`, which are `C_c^∞(ℝ)`, where the one-dimensional Gaussian Poincaré inequality
(Vendor/SLT `GaussianPoincare.gaussianPoincare`) applies.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ContDiff

namespace SharpLSI

variable {n : ℕ}

/-- A coordinate slice of a `C_c^∞` function is `C_c^∞`. -/
theorem slice_compactlySupportedSmooth {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (x : Fin n → ℝ) (i : Fin n) :
    EfronSteinApp.CompactlySupportedSmooth (fun t => F (Function.update x i t)) := by
  have hu : ContDiff ℝ ∞ (Function.update x i) := by
    have : Function.update x i = fun t => x + (t - x i) • Pi.single i (1 : ℝ) := by
      funext t j
      by_cases h : j = i
      · subst h; simp
      · simp [Function.update_of_ne h, h]
    rw [this]
    exact contDiff_const.add ((contDiff_id.sub contDiff_const).smul contDiff_const)
  refine ⟨contDiff_infty.mp (hF.comp hu) 2, ?_⟩
  -- compact support: the slice vanishes outside a bounded set
  obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) R) fun t ht => ?_
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have h1 := hR hmem
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  apply ht
  rw [Metric.mem_closedBall, dist_zero_right]
  refine le_trans ?_ h1
  have := norm_le_pi_norm (Function.update x i t) i
  simpa using this

/-- The derivative of a slice. -/
theorem deriv_slice {F : (Fin n → ℝ) → ℝ} (hF : Differentiable ℝ F) (x : Fin n → ℝ) (i : Fin n)
    (t : ℝ) : deriv (fun t => F (Function.update x i t)) t =
      fderiv ℝ F (Function.update x i t) (Pi.single i 1) :=
  ((hF _).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_update x i t)).deriv

set_option maxHeartbeats 1600000 in
/-- **Gaussian Poincaré inequality on `ℝⁿ`** for `C_c^∞` functions. -/
theorem poincare_cc {F : (Fin n → ℝ) → ℝ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    variance F (gpi n) ≤ ∫ x, ∑ k, fderiv ℝ F x (Pi.single k 1) ^ 2 ∂gpi n := by
  set μs : Fin n → Measure ℝ := fun _ => gaussianReal 0 1
  have hgpi : gpi n = Measure.pi μs := rfl
  have hFc : Continuous F := hF.continuous
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hFc
  have hdc : ∀ k : Fin n, Continuous fun x => fderiv ℝ F x (Pi.single k 1) := fun k =>
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdF : Differentiable ℝ F := hF.differentiable (by simp)
  have hdcs : ∀ k : Fin n, HasCompactSupport fun x => fderiv ℝ F x (Pi.single k 1) := fun k =>
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single k 1))
      (by simp)
  have hL2 : MemLp F 2 (Measure.pi μs) :=
    MemLp.of_bound hFc.aestronglyMeasurable B (Eventually.of_forall hB)
  have hFi : Integrable F (Measure.pi μs) := hL2.integrable one_le_two
  have hES := efronStein (μs := μs) F hL2
  rw [hgpi]
  refine hES.trans ?_
  have hint : ∀ k : Fin n, Integrable (fun x => fderiv ℝ F x (Pi.single k 1) ^ 2)
      (Measure.pi μs) := fun k => by
    obtain ⟨D, hD⟩ := ((hdcs k).comp_left (g := fun t : ℝ => t ^ 2) (by simp)).exists_bound_of_continuous
      ((continuous_pow 2).comp (hdc k))
    exact Integrable.of_bound ((continuous_pow 2).comp (hdc k)).aestronglyMeasurable D
      (Eventually.of_forall hD)
  rw [integral_finsetSum _ fun k _ => hint k]
  refine Finset.sum_le_sum fun i _ => ?_
  -- the `i`-th term
  have hFsm : StronglyMeasurable F := hFc.stronglyMeasurable
  set h : (Fin n → ℝ) → ℝ := fun x => fderiv ℝ F x (Pi.single i 1) ^ 2
  have hhc : Continuous h := (continuous_pow 2).comp (hdc i)
  obtain ⟨D, hD⟩ := ((hdcs i).comp_left (g := fun t : ℝ => t ^ 2) (by simp)).exists_bound_of_continuous hhc
  have hhi : Integrable h (Measure.pi μs) :=
    Integrable.of_bound hhc.aestronglyMeasurable D (Eventually.of_forall hD)
  have hEb : ∀ x, |condExpExceptCoord (μs := μs) i F x| ≤ B := fun x => by
    show |∫ y, F (Function.update x i y) ∂gaussianReal 0 1| ≤ B
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |F (Function.update x i y)| ∂gaussianReal 0 1 ≤ ∫ _y, B ∂gaussianReal 0 1 :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _)
            (integrable_const _) (Eventually.of_forall fun y => by
              have := hB (Function.update x i y); rwa [Real.norm_eq_abs] at this)
      _ = B := by simp
  have hEsm := condExpExceptCoord_stronglyMeasurable (μs := μs) i F hFsm
  have hf2 : Integrable (fun x => (F x - condExpExceptCoord (μs := μs) i F x) ^ 2)
      (Measure.pi μs) := by
    refine Integrable.of_bound ((hFsm.sub hEsm).pow 2).aestronglyMeasurable ((2 * B) ^ 2)
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    have h1 : |F x - condExpExceptCoord (μs := μs) i F x| ≤ 2 * B := by
      have := hB x; rw [Real.norm_eq_abs] at this
      have := hEb x
      calc _ ≤ |F x| + |condExpExceptCoord (μs := μs) i F x| := abs_sub _ _
        _ ≤ 2 * B := by linarith
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have hEh : Integrable (condExpExceptCoord (μs := μs) i h) (Measure.pi μs) := by
    refine Integrable.of_bound
      (condExpExceptCoord_stronglyMeasurable (μs := μs) i h hhc.stronglyMeasurable).aestronglyMeasurable
      D (Eventually.of_forall fun x => ?_)
    show ‖∫ y, h (Function.update x i y) ∂gaussianReal 0 1‖ ≤ D
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ y, ‖h (Function.update x i y)‖ ∂gaussianReal 0 1 ≤ ∫ _y, D ∂gaussianReal 0 1 :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
            (integrable_const _) (Eventually.of_forall fun y => hD _)
      _ = D := by simp
  rw [expectation_sq_diff_eq_expectation_condVar (μs := μs) F i hFi hf2,
    ← condExpExceptCoord_expectation (μs := μs) i h hhi]
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => integral_nonneg fun _ =>
    sq_nonneg _) hEh (Eventually.of_forall fun x => ?_)
  -- the one-dimensional Poincaré inequality on the slice
  set g : ℝ → ℝ := fun t => F (Function.update x i t)
  have hg := slice_compactlySupportedSmooth hF hc x i
  have hP1 := GaussianPoincare.gaussianPoincare hg
  have hvar : variance (fun t => g t) GaussianPoincare.stdGaussianMeasure =
      condVarExceptCoord (μs := μs) i F x := by
    rw [variance_eq_integral hg.continuous.aemeasurable]
    rfl
  have hder : ∫ t, deriv g t ^ 2 ∂GaussianPoincare.stdGaussianMeasure =
      condExpExceptCoord (μs := μs) i h x := by
    show ∫ t, deriv g t ^ 2 ∂gaussianReal 0 1 = ∫ y, h (Function.update x i y) ∂gaussianReal 0 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    show deriv g t ^ 2 = fderiv ℝ F (Function.update x i t) (Pi.single i 1) ^ 2
    rw [deriv_slice hdF x i t]
  rw [← hvar, ← hder]
  exact hP1

end SharpLSI
