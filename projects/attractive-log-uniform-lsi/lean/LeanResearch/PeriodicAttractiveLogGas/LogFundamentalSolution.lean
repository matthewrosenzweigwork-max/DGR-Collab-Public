/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0: https://www.apache.org/licenses/LICENSE-2.0

The orthonormal-basis integration-by-parts argument is adapted from
https://github.com/TauCetiProject/TauCeti/blob/d969ec21da00439b0479ee3923df9008da718365/TauCeti/Analysis/PDE/FundamentalSolution/Euclidean/DistributionalLaplacian.lean
Upstream source and license are retained in research/discovery/.

The upstream n >= 3 Newtonian-kernel theorem is not applied. This adaptation
uses the actual weak derivative of -log|x| on real Euclidean two-space and the
dimension-two radial FTC, giving the coefficient 2*pi for Euclidean volume.
-/
import LeanResearch.PeriodicAttractiveLogGas.LogRegularization
import LeanResearch.PeriodicAttractiveLogGas.RadialFlux
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Tactic.NormNum

/-! The planar logarithm is a fundamental solution of the negative ordinary
Laplacian with mass `2 * Real.pi`. Every real `C²` compactly supported test is
allowed, including tests nonzero at the pole. Pairing integrability is proved
separately. This does not identify a representative of the periodic Green function. -/

noncomputable section

open MeasureTheory InnerProductSpace Filter
open scoped RealInnerProductSpace Topology ContDiff Laplacian

namespace PeriodicAttractiveLogGas

theorem laplacian_eq_sum_directional_fderiv {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ 2 f) (b : OrthonormalBasis (Fin 2) ℝ PlanarSpace) (x : PlanarSpace) :
    Δ f x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ f y (b i)) x (b i) := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f b]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply
    ((hf1.differentiable one_ne_zero) x) (differentiableAt_const _)]
  simp

/-- The logarithm paired with the ordinary Laplacian of a compactly supported
`C²` test is integrable, including near the pole. -/
theorem integrable_planarLogKernel_mul_laplacian {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    Integrable (fun x ↦ planarLogKernel x * Δ f x) volume := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hgi : ∀ i, ContDiff ℝ 1 fun y ↦ fderiv ℝ f y (b i) := fun i ↦
    hf1.clm_apply contDiff_const
  simp_rw [laplacian_eq_sum_directional_fderiv hf b, Finset.mul_sum]
  exact integrable_finsetSum _ fun i _ ↦
    integrable_planarLogKernel_mul_fderiv (hgi i) (hc.fderiv_apply ℝ (b i)) (b i)

/-- Integrability of the test pairing used in the negative-Laplacian identity. -/
theorem integrable_planarLogKernel_mul_neg_laplacian {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    Integrable (fun x ↦ planarLogKernel x * (-Δ f x)) volume := by
  simpa only [Pi.neg_apply, mul_neg] using!
    (integrable_planarLogKernel_mul_laplacian hf hc).neg

/-- The gradient pairing appearing in integration by parts is also integrable. -/
theorem integrable_sum_fderiv_planarLogKernel_mul_fderiv {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (b : OrthonormalBasis (Fin 2) ℝ PlanarSpace) :
    Integrable (fun x ↦ ∑ i, fderiv ℝ planarLogKernel x (b i) *
      fderiv ℝ f x (b i)) volume := by
  exact integrable_finsetSum _ fun i _ ↦
    integrable_fderiv_planarLogKernel_mul (b i)
      ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const)
      (hc.fderiv_apply ℝ (b i))

theorem integral_planarLogKernel_mul_laplacian_eq_neg_integral_sum
    {f : PlanarSpace → ℝ} (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f)
    (b : OrthonormalBasis (Fin 2) ℝ PlanarSpace) :
    (∫ x, planarLogKernel x * Δ f x) =
      -(∫ x, ∑ i, fderiv ℝ planarLogKernel x (b i) * fderiv ℝ f x (b i)) := by
  have hf1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have hgi : ∀ i, ContDiff ℝ 1 fun y ↦ fderiv ℝ f y (b i) := fun i ↦
    hf1.clm_apply contDiff_const
  have hci : ∀ i, HasCompactSupport fun y ↦ fderiv ℝ f y (b i) := fun i ↦
    hc.fderiv_apply ℝ (b i)
  simp_rw [laplacian_eq_sum_directional_fderiv hf b, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ ↦
      integrable_planarLogKernel_mul_fderiv (hgi i) (hci i) (b i),
    integral_finsetSum _ fun i _ ↦
      integrable_fderiv_planarLogKernel_mul (b i) (hgi i).continuous (hci i),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ ↦
    integral_planarLogKernel_mul_fderiv_eq_neg_fderiv_mul (hgi i) (hci i) (b i)

theorem sum_fderiv_planarLogKernel_mul_fderiv
    (b : OrthonormalBasis (Fin 2) ℝ PlanarSpace) (f : PlanarSpace → ℝ)
    {x : PlanarSpace} (hx : x ≠ 0) :
    (∑ i, fderiv ℝ planarLogKernel x (b i) * fderiv ℝ f x (b i)) =
      -(‖x‖ ^ (-2 : ℝ) * fderiv ℝ f x x) := by
  have hx' : fderiv ℝ f x x = ∑ i, ⟪b i, x⟫ * fderiv ℝ f x (b i) := by
    simpa using congrArg (fderiv ℝ f x) (b.sum_repr' x).symm
  have hp : ‖x‖ ^ (-2 : ℝ) = (‖x‖ ^ 2)⁻¹ := by
    rw [Real.rpow_neg (norm_nonneg x), Real.rpow_two]
  rw [hp, hx', Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [fderiv_planarLogKernel hx]
  simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
  rw [real_inner_comm x]
  ring

/-- The ordinary Laplacian pairing of `-log|x|`, with Euclidean Lebesgue measure. -/
theorem integral_planarLogKernel_mul_laplacian {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    (∫ x, planarLogKernel x * Δ f x) = -(2 * Real.pi) * f 0 := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hsum : (fun x ↦ ∑ i, fderiv ℝ planarLogKernel x (b i) *
      fderiv ℝ f x (b i)) =ᵐ[volume]
      fun x ↦ -(‖x‖ ^ (-2 : ℝ) * fderiv ℝ f x x) := by
    filter_upwards [volume.ae_ne 0] with x hx
    exact sum_fderiv_planarLogKernel_mul_fderiv b f hx
  rw [integral_planarLogKernel_mul_laplacian_eq_neg_integral_sum hf hc b,
    integral_congr_ae hsum, integral_neg, neg_neg]
  exact integral_norm_rpow_neg_two_mul_fderiv_apply_self (hf.of_le (by norm_num)) hc

/-- The full distributional fundamental-solution identity for the planar
logarithm: the negative ordinary Laplacian has mass `2 * Real.pi` at the origin.
The only test hypotheses are `C²` regularity and compact support. -/
theorem integral_planarLogKernel_mul_neg_laplacian {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ 2 f) (hc : HasCompactSupport f) :
    (∫ x, planarLogKernel x * (-Δ f x)) = (2 * Real.pi) * f 0 := by
  simp_rw [mul_neg]
  rw [integral_neg, integral_planarLogKernel_mul_laplacian hf hc]
  ring

end PeriodicAttractiveLogGas
