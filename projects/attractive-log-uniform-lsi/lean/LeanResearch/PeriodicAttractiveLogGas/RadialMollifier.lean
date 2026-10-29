/-
The scalar-bump composition is adapted from Scott Armstrong and Vlad Vicol,
CKN/Foundation/Harmonic/RadialBumpDensities.lean, immutable commit
25bde5b5b47a929a510e7f06699391f484531559 (Apache 2.0).
Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
The retained source and license are in research/discovery/.

Here the domain is actual Euclidean two-space, the quadratic function is its
norm squared, and the normalization is by its actual Lebesgue integral.
-/
import LeanResearch.PeriodicAttractiveLogGas.LogKernel
import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Explicit smooth radial probability kernels. Radiality follows from composing
a scalar bump with the norm squared; no radiality of a chosen vector-space bump
is assumed. -/

noncomputable section

open MeasureTheory Metric Set
open scoped ContDiff Topology

namespace PeriodicAttractiveLogGas

def radialScalarBump (R : ℝ) (hR : 0 < R) : ContDiffBump (0 : ℝ) :=
  ⟨R ^ 2 / 4, R ^ 2, by positivity, by nlinarith [sq_pos_of_pos hR]⟩

/-- A radial bump that equals one on the ball of radius `R / 2`. -/
def rawRadialMollifier (R : ℝ) (hR : 0 < R) (x : PlanarSpace) : ℝ :=
  radialScalarBump R hR (‖x‖ ^ 2)

theorem contDiff_rawRadialMollifier (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ ∞ (rawRadialMollifier R hR) :=
  (radialScalarBump R hR).contDiff.comp (contDiff_norm_sq ℝ)

theorem rawRadialMollifier_nonneg (R : ℝ) (hR : 0 < R) (x : PlanarSpace) :
    0 ≤ rawRadialMollifier R hR x := (radialScalarBump R hR).nonneg

theorem rawRadialMollifier_le_one (R : ℝ) (hR : 0 < R) (x : PlanarSpace) :
    rawRadialMollifier R hR x ≤ 1 := (radialScalarBump R hR).le_one

theorem rawRadialMollifier_one_of_norm_le_half (R : ℝ) (hR : 0 < R)
    {x : PlanarSpace} (hx : ‖x‖ ≤ R / 2) : rawRadialMollifier R hR x = 1 := by
  apply (radialScalarBump R hR).one_of_mem_closedBall
  change dist (‖x‖ ^ 2) 0 ≤ R ^ 2 / 4
  rw [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [norm_nonneg x]

theorem rawRadialMollifier_zero (R : ℝ) (hR : 0 < R) :
    rawRadialMollifier R hR 0 = 1 :=
  rawRadialMollifier_one_of_norm_le_half R hR (by simpa only [norm_zero] using (half_pos hR).le)

theorem support_rawRadialMollifier_subset (R : ℝ) (hR : 0 < R) :
    Function.support (rawRadialMollifier R hR) ⊆ ball (0 : PlanarSpace) R := by
  intro x hx
  have hs : ‖x‖ ^ 2 ∈ Function.support (radialScalarBump R hR) := hx
  rw [(radialScalarBump R hR).support_eq] at hs
  have hs' : ‖x‖ ^ 2 < R ^ 2 := by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖x‖), radialScalarBump] using hs
  rw [mem_ball_zero_iff]
  nlinarith [norm_nonneg x]

theorem rawRadialMollifier_eq_zero_of_le_norm (R : ℝ) (hR : 0 < R)
    {x : PlanarSpace} (hx : R ≤ ‖x‖) : rawRadialMollifier R hR x = 0 := by
  apply Function.notMem_support.mp
  intro h
  exact (not_lt_of_ge hx) (mem_ball_zero_iff.mp (support_rawRadialMollifier_subset R hR h))

theorem tsupport_rawRadialMollifier_subset (R : ℝ) (hR : 0 < R) :
    tsupport (rawRadialMollifier R hR) ⊆ closedBall (0 : PlanarSpace) R :=
  closure_minimal ((support_rawRadialMollifier_subset R hR).trans ball_subset_closedBall)
    isClosed_closedBall

theorem hasCompactSupport_rawRadialMollifier (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (rawRadialMollifier R hR) :=
  (isCompact_closedBall (0 : PlanarSpace) R).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_rawRadialMollifier_subset R hR)

theorem integrable_rawRadialMollifier (R : ℝ) (hR : 0 < R) :
    Integrable (rawRadialMollifier R hR) volume :=
  (contDiff_rawRadialMollifier R hR).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_rawRadialMollifier R hR)

theorem integral_rawRadialMollifier_pos (R : ℝ) (hR : 0 < R) :
    0 < ∫ x, rawRadialMollifier R hR x :=
  (contDiff_rawRadialMollifier R hR).continuous
    |>.integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hasCompactSupport_rawRadialMollifier R hR) (rawRadialMollifier_nonneg R hR)
      (by rw [rawRadialMollifier_zero R hR]; exact one_ne_zero)

/-- The explicit radial probability kernel with support radius `R`. -/
def radialMollifier (R : ℝ) (hR : 0 < R) (x : PlanarSpace) : ℝ :=
  rawRadialMollifier R hR x / ∫ y, rawRadialMollifier R hR y

theorem contDiff_radialMollifier (R : ℝ) (hR : 0 < R) :
    ContDiff ℝ ∞ (radialMollifier R hR) :=
  (contDiff_rawRadialMollifier R hR).div_const _

theorem radialMollifier_nonneg (R : ℝ) (hR : 0 < R) (x : PlanarSpace) :
    0 ≤ radialMollifier R hR x :=
  div_nonneg (rawRadialMollifier_nonneg R hR x) (integral_rawRadialMollifier_pos R hR).le

theorem integrable_radialMollifier (R : ℝ) (hR : 0 < R) :
    Integrable (radialMollifier R hR) volume :=
  (integrable_rawRadialMollifier R hR).div_const _

theorem integral_radialMollifier (R : ℝ) (hR : 0 < R) :
    ∫ x, radialMollifier R hR x = 1 := by
  simp only [radialMollifier, integral_div]
  exact div_self (integral_rawRadialMollifier_pos R hR).ne'

theorem support_radialMollifier_subset (R : ℝ) (hR : 0 < R) :
    Function.support (radialMollifier R hR) ⊆ ball (0 : PlanarSpace) R := by
  intro x hx
  apply support_rawRadialMollifier_subset R hR
  intro hz
  exact hx (by simp only [radialMollifier, hz, zero_div])

theorem radialMollifier_eq_zero_of_le_norm (R : ℝ) (hR : 0 < R)
    {x : PlanarSpace} (hx : R ≤ ‖x‖) : radialMollifier R hR x = 0 := by
  simp only [radialMollifier, rawRadialMollifier_eq_zero_of_le_norm R hR hx, zero_div]

theorem tsupport_radialMollifier_subset (R : ℝ) (hR : 0 < R) :
    tsupport (radialMollifier R hR) ⊆ closedBall (0 : PlanarSpace) R :=
  closure_minimal ((support_radialMollifier_subset R hR).trans ball_subset_closedBall)
    isClosed_closedBall

theorem hasCompactSupport_radialMollifier (R : ℝ) (hR : 0 < R) :
    HasCompactSupport (radialMollifier R hR) :=
  (isCompact_closedBall (0 : PlanarSpace) R).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_radialMollifier_subset R hR)

theorem radialMollifier_eq_of_norm_eq (R : ℝ) (hR : 0 < R)
    {x y : PlanarSpace} (hxy : ‖x‖ = ‖y‖) :
    radialMollifier R hR x = radialMollifier R hR y := by
  simp only [radialMollifier, rawRadialMollifier, hxy]

theorem radialMollifier_neg (R : ℝ) (hR : 0 < R) (x : PlanarSpace) :
    radialMollifier R hR (-x) = radialMollifier R hR x :=
  radialMollifier_eq_of_norm_eq R hR (norm_neg x)

end PeriodicAttractiveLogGas
