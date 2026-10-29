/-
The derivative calculation below is adapted from the Tau Ceti contributors,
TauCeti/Analysis/PDE/FundamentalSolution/Gradient.lean, immutable commit
d969ec21da00439b0479ee3923df9008da718365 (Apache 2.0).
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
The normalization here is -log|x| on real Euclidean two-space, as in lem:kernel,
rather than the upstream -(2*pi)^(-1) log|z| on the complex plane.
Upstream source and license are retained in research/discovery/.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-! Local analytic ingredients for the logarithmic singularity. These statements
do not yet identify a pointwise representative of the periodic Green function. -/

noncomputable section

open MeasureTheory InnerProductSpace Filter
open scoped RealInnerProductSpace ContDiff

namespace PeriodicAttractiveLogGas

abbrev PlanarSpace := EuclideanSpace ℝ (Fin 2)

/-- The source singularity, with the library's harmless totalized value at zero. -/
def planarLogKernel (x : PlanarSpace) : ℝ := -Real.log ‖x‖

@[simp] theorem planarLogKernel_zero : planarLogKernel 0 = 0 := by
  simp [planarLogKernel]

@[simp] theorem planarLogKernel_neg (x : PlanarSpace) :
    planarLogKernel (-x) = planarLogKernel x := by
  simp [planarLogKernel]

theorem locallyIntegrable_planar_inv_norm :
    LocallyIntegrable (fun x : PlanarSpace ↦ ‖x‖⁻¹) volume := by
  refine locallyIntegrable_of_norm_le_rpow (C := 1) (α := 1) (by simp)
    (by norm_num) ?_ ?_
  · exact Eventually.of_forall fun x ↦ by simp [Real.rpow_neg_one]
  · exact (measurable_norm.inv).aestronglyMeasurable

theorem abs_log_le_self_add_inv {r : ℝ} (hr : 0 ≤ r) :
    |Real.log r| ≤ r + r⁻¹ := by
  apply abs_le.mpr
  constructor
  · have h := Real.neg_inv_le_log hr
    linarith
  · have h := Real.log_le_self hr
    have hi := inv_nonneg.mpr hr
    linarith

theorem locallyIntegrable_planarLogKernel : LocallyIntegrable planarLogKernel volume := by
  have h := (continuous_norm.locallyIntegrable (μ := (volume : Measure PlanarSpace))).add
    locallyIntegrable_planar_inv_norm
  refine h.mono ?_ (Eventually.of_forall fun x ↦ ?_)
  · exact (measurable_norm.log.neg).aestronglyMeasurable
  · simpa [planarLogKernel, Real.norm_eq_abs, abs_of_nonneg
      (add_nonneg (norm_nonneg x) (inv_nonneg.mpr (norm_nonneg x)))] using
      abs_log_le_self_add_inv (norm_nonneg x)

theorem hasFDerivAt_planarLogKernel {x : PlanarSpace} (hx : x ≠ 0) :
    HasFDerivAt planarLogKernel (-(‖x‖ ^ 2)⁻¹ • innerSL ℝ x) x := by
  have hsq := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hlog := hsq.log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))
  have heq : planarLogKernel = fun y : PlanarSpace ↦ -(1 / 2 : ℝ) *
      Real.log (‖y‖ ^ 2) := by
    funext y
    rw [planarLogKernel, Real.log_pow]
    ring
  have hmap : (-(1 / 2 : ℝ)) • ((‖x‖ ^ 2)⁻¹ • (2 • innerSL ℝ x)) =
      -(‖x‖ ^ 2)⁻¹ • innerSL ℝ x := by
    ext v
    simp only [smul_apply, innerSL_apply_apply]
    ring
  rw [heq, ← hmap]
  exact hlog.const_mul (-(1 / 2 : ℝ))

theorem fderiv_planarLogKernel {x : PlanarSpace} (hx : x ≠ 0) :
    fderiv ℝ planarLogKernel x = -(‖x‖ ^ 2)⁻¹ • innerSL ℝ x :=
  (hasFDerivAt_planarLogKernel hx).fderiv

theorem contDiffAt_planarLogKernel {x : PlanarSpace} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ planarLogKernel x :=
  ((contDiffAt_norm ℝ hx).log (norm_ne_zero_iff.mpr hx)).neg

theorem norm_fderiv_planarLogKernel {x : PlanarSpace} (hx : x ≠ 0) :
    ‖fderiv ℝ planarLogKernel x‖ = ‖x‖⁻¹ := by
  rw [fderiv_planarLogKernel hx, norm_smul, innerSL_apply_norm]
  rw [Real.norm_eq_abs, abs_neg, abs_inv, abs_pow, abs_of_nonneg (norm_nonneg x)]
  field_simp

theorem locallyIntegrable_fderiv_planarLogKernel :
    LocallyIntegrable (fderiv ℝ planarLogKernel) volume := by
  let D : PlanarSpace → PlanarSpace →L[ℝ] ℝ := fun x ↦
    -(‖x‖ ^ 2)⁻¹ • innerSL ℝ x
  have hD : Measurable D := by
    dsimp [D]
    fun_prop
  have heq : fderiv ℝ planarLogKernel =ᵐ[volume] D := by
    filter_upwards [volume.ae_ne 0] with x hx
    exact fderiv_planarLogKernel hx
  refine locallyIntegrable_planar_inv_norm.mono
    (hD.aestronglyMeasurable.congr heq.symm) ?_
  filter_upwards [volume.ae_ne 0] with x hx
  simp [norm_fderiv_planarLogKernel hx]

end PeriodicAttractiveLogGas
