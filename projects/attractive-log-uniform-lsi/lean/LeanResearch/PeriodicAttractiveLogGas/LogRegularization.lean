/-
The regularization/line-derivative integration-by-parts proof pattern is adapted
from the Tau Ceti contributors,
TauCeti/Analysis/PDE/FundamentalSolution/Euclidean/DistributionalLaplacian.lean,
immutable commit d969ec21da00439b0479ee3923df9008da718365 (Apache 2.0).
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Upstream source and license are retained in research/discovery/.

The upstream n >= 3 Newtonian-kernel theorem is not applied here. This file
uses the planar logarithm, its already proved local integrability, and an
additional quadratic term in the domination bound for the regularized kernel.
-/
import LeanResearch.PeriodicAttractiveLogGas.LogKernel
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Weak integration by parts for the actual planar logarithm across its pole.
The positive regularizations converge under explicit locally integrable bounds.
No test is required to vanish at the singular point. -/

noncomputable section

open MeasureTheory InnerProductSpace Filter Set Topology
open scoped RealInnerProductSpace

namespace PeriodicAttractiveLogGas

/-- The logarithmic kernel with a positive parameter added to the squared norm. -/
def regularizedPlanarLogKernel (t : ℝ) (x : PlanarSpace) : ℝ :=
  -(1 / 2 : ℝ) * Real.log (‖x‖ ^ 2 + t)

/-- The actual directional derivative of the positive-parameter regularization. -/
def regularizedPlanarLogKernelDeriv (v : PlanarSpace) (t : ℝ) (x : PlanarSpace) : ℝ :=
  -(‖x‖ ^ 2 + t)⁻¹ * inner ℝ x v

theorem regularizedPlanarLogKernel_zero : regularizedPlanarLogKernel 0 = planarLogKernel := by
  funext x
  rw [regularizedPlanarLogKernel, planarLogKernel, add_zero, Real.log_pow]
  ring

theorem regularizedPlanarLogKernelDeriv_zero (v : PlanarSpace) {x : PlanarSpace}
    (hx : x ≠ 0) :
    regularizedPlanarLogKernelDeriv v 0 x = fderiv ℝ planarLogKernel x v := by
  rw [regularizedPlanarLogKernelDeriv, fderiv_planarLogKernel hx, add_zero]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]

theorem hasLineDerivAt_regularizedPlanarLogKernel (v : PlanarSpace) {t : ℝ}
    (ht : 0 < t) (x : PlanarSpace) :
    HasLineDerivAt ℝ (regularizedPlanarLogKernel t)
      (regularizedPlanarLogKernelDeriv v t x) x v := by
  have hpos : 0 < ‖x‖ ^ 2 + t := add_pos_of_nonneg_of_pos (sq_nonneg _) ht
  have h := (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const t).log hpos.ne').const_mul
    (-(1 / 2 : ℝ))
  refine (h.hasLineDerivAt v).congr_deriv ?_
  simp only [regularizedPlanarLogKernelDeriv, smul_apply, innerSL_apply_apply, smul_eq_mul]
  ring

theorem continuous_regularizedPlanarLogKernel {t : ℝ} (ht : 0 < t) :
    Continuous (regularizedPlanarLogKernel t) :=
  continuous_const.mul (((continuous_norm.pow 2).add continuous_const).log
    fun _ ↦ (add_pos_of_nonneg_of_pos (sq_nonneg _) ht).ne')

theorem continuous_regularizedPlanarLogKernelDeriv (v : PlanarSpace) {t : ℝ}
    (ht : 0 < t) : Continuous (regularizedPlanarLogKernelDeriv v t) :=
  (((((continuous_norm.pow 2).add continuous_const).inv₀
    fun _ ↦ (add_pos_of_nonneg_of_pos (sq_nonneg _) ht).ne').neg).mul
      (continuous_id.inner continuous_const))

/-- A domination valid for small nonnegative regularization parameters.
The added quadratic term controls the negative part of the regularized logarithm. -/
theorem abs_regularizedPlanarLogKernel_le {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    {x : PlanarSpace} (hx : x ≠ 0) :
    |regularizedPlanarLogKernel t x| ≤ |planarLogKernel x| + (‖x‖ ^ 2 + 1) := by
  have hr2 : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  have hpos : 0 < ‖x‖ ^ 2 + t := add_pos_of_pos_of_nonneg hr2 ht
  have hloglow : Real.log (‖x‖ ^ 2) ≤ Real.log (‖x‖ ^ 2 + t) :=
    Real.log_le_log hr2 (le_add_of_nonneg_right ht)
  have hlogup : Real.log (‖x‖ ^ 2 + t) ≤ ‖x‖ ^ 2 + 1 :=
    (Real.log_le_self hpos.le).trans (by linarith)
  have hk0 : planarLogKernel x = -(1 / 2 : ℝ) * Real.log (‖x‖ ^ 2) := by
    rw [planarLogKernel, Real.log_pow]
    ring
  have hnorm : 0 ≤ ‖x‖ ^ 2 + 1 := add_nonneg (sq_nonneg _) zero_le_one
  apply abs_le.mpr
  constructor
  · dsimp only [regularizedPlanarLogKernel]
    linarith [abs_nonneg (planarLogKernel x)]
  · have habs := le_abs_self (planarLogKernel x)
    dsimp only [regularizedPlanarLogKernel]
    linarith

theorem abs_regularizedPlanarLogKernelDeriv_le (v : PlanarSpace) {t : ℝ}
    (ht : 0 ≤ t) {x : PlanarSpace} (hx : x ≠ 0) :
    |regularizedPlanarLogKernelDeriv v t x| ≤ |regularizedPlanarLogKernelDeriv v 0 x| := by
  have hr2 : 0 < ‖x‖ ^ 2 := pow_pos (norm_pos_iff.mpr hx) 2
  simp only [regularizedPlanarLogKernelDeriv, add_zero, abs_mul, abs_neg, abs_inv,
    abs_of_nonneg (add_nonneg (sq_nonneg ‖x‖) ht), abs_of_nonneg (sq_nonneg ‖x‖)]
  exact mul_le_mul_of_nonneg_right (inv_anti₀ hr2 (le_add_of_nonneg_right ht))
    (abs_nonneg _)

theorem tendsto_regularizedPlanarLogKernel {x : PlanarSpace} (hx : x ≠ 0) :
    Tendsto (fun t ↦ regularizedPlanarLogKernel t x) (𝓝[>] (0 : ℝ))
      (𝓝 (planarLogKernel x)) := by
  have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hbase : Tendsto (fun t : ℝ ↦ ‖x‖ ^ 2 + t) (𝓝[>] (0 : ℝ)) (𝓝 (‖x‖ ^ 2)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ ‖x‖ ^ 2) (𝓝[>] (0 : ℝ))
        (𝓝 (‖x‖ ^ 2))).add hid
  rw [← regularizedPlanarLogKernel_zero]
  simpa only [regularizedPlanarLogKernel, add_zero] using
    (hbase.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).const_mul (-(1 / 2 : ℝ))

theorem tendsto_regularizedPlanarLogKernelDeriv (v : PlanarSpace) {x : PlanarSpace}
    (hx : x ≠ 0) :
    Tendsto (fun t ↦ regularizedPlanarLogKernelDeriv v t x) (𝓝[>] (0 : ℝ))
      (𝓝 (fderiv ℝ planarLogKernel x v)) := by
  have hid : Tendsto (fun t : ℝ ↦ t) (𝓝[>] (0 : ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  have hbase : Tendsto (fun t : ℝ ↦ ‖x‖ ^ 2 + t) (𝓝[>] (0 : ℝ)) (𝓝 (‖x‖ ^ 2)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ ↦ ‖x‖ ^ 2) (𝓝[>] (0 : ℝ))
        (𝓝 (‖x‖ ^ 2))).add hid
  rw [← regularizedPlanarLogKernelDeriv_zero v hx]
  simpa only [regularizedPlanarLogKernelDeriv, add_zero] using
    (hbase.inv₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))).neg.mul_const (inner ℝ x v)

/-- Multiplication by a continuous compactly supported test gives an actual integrable function. -/
theorem integrable_planarLogKernel_mul {w : PlanarSpace → ℝ}
    (hw : Continuous w) (hc : HasCompactSupport w) :
    Integrable (fun x ↦ planarLogKernel x * w x) volume :=
  locallyIntegrable_planarLogKernel.integrable_smul_right_of_hasCompactSupport hw hc

theorem integrable_fderiv_planarLogKernel_mul (v : PlanarSpace) {w : PlanarSpace → ℝ}
    (hw : Continuous w) (hc : HasCompactSupport w) :
    Integrable (fun x ↦ fderiv ℝ planarLogKernel x v * w x) volume := by
  simpa [mul_comm] using
    (locallyIntegrable_fderiv_planarLogKernel.integrable_smul_left_of_hasCompactSupport hw
      hc).apply_continuousLinearMap v

theorem integrable_planarLogKernel_mul_fderiv {g : PlanarSpace → ℝ}
    (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g) (v : PlanarSpace) :
    Integrable (fun x ↦ planarLogKernel x * fderiv ℝ g x v) volume :=
  integrable_planarLogKernel_mul
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const) (hc.fderiv_apply ℝ v)

theorem tendsto_integral_regularizedPlanarLogKernel_mul {w : PlanarSpace → ℝ}
    (hw : Continuous w) (hc : HasCompactSupport w) :
    Tendsto (fun t ↦ ∫ x, regularizedPlanarLogKernel t x * w x) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, planarLogKernel x * w x)) := by
  have hb1 : Integrable (fun x ↦ |planarLogKernel x| * |w x|) volume := by
    simpa only [abs_mul] using (integrable_planarLogKernel_mul hw hc).abs
  have hb2 : Integrable (fun x ↦ (‖x‖ ^ 2 + 1) * |w x|) volume :=
    ((((continuous_norm.pow 2).add continuous_const).mul hw.abs).integrable_of_hasCompactSupport
      hc.abs.mul_left)
  have hb : Integrable (fun x ↦ (|planarLogKernel x| + (‖x‖ ^ 2 + 1)) * |w x|) volume := by
    simpa only [Pi.add_apply, add_mul] using! hb1.add hb2
  have htpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := eventually_mem_nhdsWithin
  have htle : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ 1 :=
    (eventually_le_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ (|planarLogKernel x| + (‖x‖ ^ 2 + 1)) * |w x|)
  · filter_upwards [htpos] with t ht
    exact ((continuous_regularizedPlanarLogKernel ht).mul hw).aestronglyMeasurable
  · filter_upwards [htpos, htle] with t ht ht1
    filter_upwards [volume.ae_ne 0] with x hx
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_regularizedPlanarLogKernel_le ht.le ht1 hx)
      (abs_nonneg _)
  · exact hb
  · filter_upwards [volume.ae_ne 0] with x hx
    exact (tendsto_regularizedPlanarLogKernel hx).mul_const (w x)

theorem tendsto_integral_regularizedPlanarLogKernelDeriv_mul (v : PlanarSpace)
    {w : PlanarSpace → ℝ} (hw : Continuous w) (hc : HasCompactSupport w) :
    Tendsto (fun t ↦ ∫ x, regularizedPlanarLogKernelDeriv v t x * w x) (𝓝[>] (0 : ℝ))
      (𝓝 (∫ x, fderiv ℝ planarLogKernel x v * w x)) := by
  have htpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := eventually_mem_nhdsWithin
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x ↦ |fderiv ℝ planarLogKernel x v * w x|)
  · filter_upwards [htpos] with t ht
    exact ((continuous_regularizedPlanarLogKernelDeriv v ht).mul hw).aestronglyMeasurable
  · filter_upwards [htpos] with t ht
    filter_upwards [volume.ae_ne 0] with x hx
    simp only [Real.norm_eq_abs, abs_mul]
    rw [← regularizedPlanarLogKernelDeriv_zero v hx]
    exact mul_le_mul_of_nonneg_right (abs_regularizedPlanarLogKernelDeriv_le v ht.le hx)
      (abs_nonneg _)
  · exact (integrable_fderiv_planarLogKernel_mul v hw hc).abs
  · filter_upwards [volume.ae_ne 0] with x hx
    exact (tendsto_regularizedPlanarLogKernelDeriv v hx).mul_const (w x)

/-- Ordinary weak integration by parts across the pole, for every C1 compactly
supported real test and every constant Euclidean direction. No test vanishing
or support exclusion at the origin is assumed. -/
theorem integral_planarLogKernel_mul_fderiv_eq_neg_fderiv_mul
    {g : PlanarSpace → ℝ} (hg : ContDiff ℝ 1 g) (hc : HasCompactSupport g)
    (v : PlanarSpace) :
    (∫ x, planarLogKernel x * fderiv ℝ g x v) =
      -(∫ x, fderiv ℝ planarLogKernel x v * g x) := by
  have hg' : Continuous fun x ↦ fderiv ℝ g x v :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hcg' : HasCompactSupport fun x ↦ fderiv ℝ g x v := hc.fderiv_apply ℝ v
  have hibp : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (∫ x, regularizedPlanarLogKernel t x * fderiv ℝ g x v) =
        -(∫ x, regularizedPlanarLogKernelDeriv v t x * g x) :=
    eventually_mem_nhdsWithin.mono fun t (ht : 0 < t) ↦ by
      simpa using integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
        (B := ContinuousLinearMap.mul ℝ ℝ) (f := regularizedPlanarLogKernel t)
        (f' := regularizedPlanarLogKernelDeriv v t) (g := g) (g' := fun x ↦ fderiv ℝ g x v)
        (((continuous_regularizedPlanarLogKernelDeriv v ht).mul hg.continuous).integrable_of_hasCompactSupport
          hc.mul_left)
        (((continuous_regularizedPlanarLogKernel ht).mul hg').integrable_of_hasCompactSupport
          hcg'.mul_left)
        (((continuous_regularizedPlanarLogKernel ht).mul hg.continuous).integrable_of_hasCompactSupport
          hc.mul_left)
        (fun x _ ↦ hasLineDerivAt_regularizedPlanarLogKernel v ht x)
        (fun x _ ↦ ((hg.differentiable one_ne_zero) x).hasFDerivAt.hasLineDerivAt v)
  have hL := tendsto_integral_regularizedPlanarLogKernel_mul hg' hcg'
  have hR := tendsto_integral_regularizedPlanarLogKernelDeriv_mul v hg.continuous hc
  exact tendsto_nhds_unique (hL.congr' hibp) hR.neg

end PeriodicAttractiveLogGas
