/-
The constant-Hessian calculation follows the squared-norm calculation in
TauCeti/Analysis/InnerProductSpace/Laplacian/Basic.lean, immutable commit
d969ec21da00439b0479ee3923df9008da718365, lines 200–220 (Apache 2.0).
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
The retained exact source, hash, and license are recorded in
research/discovery/laplacian-geometry-reuse.json.
The two integrations by parts below use only pinned Mathlib theorems.
-/
import LeanResearch.PeriodicAttractiveLogGas.HarmonicMollification
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-! The actual quadratic term in the local periodic Green formula.
Its negative-Laplacian pairing is the constant density `-(2 * Real.pi)`
against every smooth compactly supported real test. -/

noncomputable section

open MeasureTheory InnerProductSpace Laplacian
open scoped Topology ContDiff RealInnerProductSpace

namespace PeriodicAttractiveLogGas

/-- The quadratic correction in the normalized local Green expansion. -/
def planarGreenQuadratic (x : PlanarSpace) : ℝ := (Real.pi / 2) * ‖x‖ ^ 2

theorem contDiff_planarGreenQuadratic : ContDiff ℝ ∞ planarGreenQuadratic := by
  have h : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ ‖x‖ ^ 2) := contDiff_norm_sq ℝ
  exact contDiff_const.mul h

theorem hasFDerivAt_planarGreenQuadratic (x : PlanarSpace) :
    HasFDerivAt planarGreenQuadratic (Real.pi • innerSL ℝ x) x := by
  have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (Real.pi / 2)
  have hmap : (Real.pi / 2) • (2 • innerSL ℝ x) = Real.pi • innerSL ℝ x := by
    ext v
    simp only [smul_apply, innerSL_apply_apply, smul_eq_mul]
    ring
  simpa only [planarGreenQuadratic, hmap] using! h

theorem fderiv_planarGreenQuadratic (x : PlanarSpace) :
    fderiv ℝ planarGreenQuadratic x = Real.pi • innerSL ℝ x :=
  (hasFDerivAt_planarGreenQuadratic x).fderiv

theorem fderiv_fderiv_planarGreenQuadratic (x : PlanarSpace) :
    fderiv ℝ (fderiv ℝ planarGreenQuadratic) x =
      (Real.pi • innerSL ℝ : PlanarSpace →L[ℝ] PlanarSpace →L[ℝ] ℝ) := by
  have hfun : fderiv ℝ planarGreenQuadratic =
      (Real.pi • innerSL ℝ : PlanarSpace →L[ℝ] PlanarSpace →L[ℝ] ℝ) := by
    funext y
    exact fderiv_planarGreenQuadratic y
  rw [hfun]
  exact (Real.pi • innerSL ℝ : PlanarSpace →L[ℝ] PlanarSpace →L[ℝ] ℝ).fderiv

/-- In Euclidean dimension two, the ordinary Laplacian of the quadratic correction
is exactly `2 * Real.pi`, including at the origin. -/
theorem laplacian_planarGreenQuadratic (x : PlanarSpace) :
    Δ planarGreenQuadratic x = 2 * Real.pi := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis planarGreenQuadratic b]
  have hterm (i : Fin 2) :
      iteratedFDeriv ℝ 2 planarGreenQuadratic x ![b i, b i] = Real.pi := by
    have hself : (innerSL ℝ (b i)) (b i) = (1 : ℝ) := by
      rw [innerSL_apply_apply, real_inner_self_eq_norm_sq,
        b.orthonormal.norm_eq_one i, one_pow]
    rw [iteratedFDeriv_two_apply, fderiv_fderiv_planarGreenQuadratic]
    simp [hself]
  simp only [hterm, Fin.sum_univ_two]
  ring

/-- A continuous factor times a continuous compact factor is genuinely integrable. -/
theorem integrable_planar_continuous_mul_compact {f g : PlanarSpace → ℝ}
    (hf : Continuous f) (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x ↦ f x * g x) volume :=
  (hf.mul hg).integrable_of_hasCompactSupport hgc.mul_left

/-- One integration by parts with a smooth compact right factor. The three
integrability premises of Mathlib's theorem are all proved from compact support. -/
theorem integral_mul_planarDirectionalDeriv_eq_neg
    {f g : PlanarSpace → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (v : PlanarSpace) :
    (∫ x, f x * planarDirectionalDeriv g v x) =
      -(∫ x, planarDirectionalDeriv f v x * g x) := by
  have hfg : Integrable (fun x ↦ f x * g x) volume :=
    integrable_planar_continuous_mul_compact hf.continuous hg.continuous hgc
  have hdfg : Integrable (fun x ↦ planarDirectionalDeriv f v x * g x) volume :=
    integrable_planar_continuous_mul_compact
      (contDiff_planarDirectionalDeriv hf v).continuous hg.continuous hgc
  have hfdg : Integrable (fun x ↦ f x * planarDirectionalDeriv g v x) volume :=
    integrable_planar_continuous_mul_compact hf.continuous
      (contDiff_planarDirectionalDeriv hg v).continuous
      (hasCompactSupport_planarDirectionalDeriv hgc v)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := f) (g := g) (v := v) (μ := (volume : Measure PlanarSpace))
    hdfg hfdg hfg
    (fun x _ ↦ hf.differentiable (by simp) x)
    (fun x _ ↦ hg.differentiable (by simp) x)

/-- Two integrations by parts in the same Euclidean direction. -/
theorem integral_mul_planarDirectionalDeriv_second
    {f φ : PlanarSpace → ℝ} (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (v : PlanarSpace) :
    (∫ x, f x * planarDirectionalDeriv (planarDirectionalDeriv φ v) v x) =
      ∫ x, planarDirectionalDeriv (planarDirectionalDeriv f v) v x * φ x := by
  have hfirst := integral_mul_planarDirectionalDeriv_eq_neg hf
    (contDiff_planarDirectionalDeriv hφ v)
    (hasCompactSupport_planarDirectionalDeriv hφc v) v
  have hsecond := integral_mul_planarDirectionalDeriv_eq_neg
    (contDiff_planarDirectionalDeriv hf v) hφ hφc v
  rw [hsecond, neg_neg] at hfirst
  exact hfirst

/-- The ordinary Laplacian is symmetric when one factor is a smooth compact test.
The other factor is globally smooth but need not be integrable at infinity. -/
theorem integral_planar_mul_laplacian_eq_laplacian_mul
    {f φ : PlanarSpace → ℝ} (hf : ContDiff ℝ ∞ f) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    (∫ x, f x * Δ φ x) = ∫ x, Δ f x * φ x := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  have hleft (i : Fin 2) : Integrable (fun x ↦ f x *
      planarDirectionalDeriv (planarDirectionalDeriv φ (b i)) (b i) x) volume :=
    integrable_planar_continuous_mul_compact hf.continuous
      (contDiff_planarDirectionalDeriv
        (contDiff_planarDirectionalDeriv hφ _) _).continuous
      (hasCompactSupport_planarDirectionalDeriv
        (hasCompactSupport_planarDirectionalDeriv hφc _) _)
  have hright (i : Fin 2) : Integrable (fun x ↦
      planarDirectionalDeriv (planarDirectionalDeriv f (b i)) (b i) x * φ x) volume :=
    integrable_planar_continuous_mul_compact
      (contDiff_planarDirectionalDeriv
        (contDiff_planarDirectionalDeriv hf _) _).continuous hφ.continuous hφc
  calc
    (∫ x, f x * Δ φ x) = ∑ i : Fin 2, ∫ x, f x *
        planarDirectionalDeriv (planarDirectionalDeriv φ (b i)) (b i) x := by
      simp_rw [laplacian_eq_sum_planarDirectionalDeriv hφ, Finset.mul_sum]
      exact integral_finsetSum _ fun i _ ↦ hleft i
    _ = ∑ i : Fin 2, ∫ x,
        planarDirectionalDeriv (planarDirectionalDeriv f (b i)) (b i) x * φ x :=
      Finset.sum_congr rfl fun i _ ↦ integral_mul_planarDirectionalDeriv_second hf hφ hφc _
    _ = ∫ x, Δ f x * φ x := by
      simp_rw [laplacian_eq_sum_planarDirectionalDeriv hf, Finset.sum_mul]
      exact (integral_finsetSum _ fun i _ ↦ hright i).symm

/-- The quadratic term paired with the test Laplacian is integrable. -/
theorem integrable_planarGreenQuadratic_mul_laplacian {φ : PlanarSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x ↦ planarGreenQuadratic x * Δ φ x) volume :=
  integrable_planar_continuous_mul_compact contDiff_planarGreenQuadratic.continuous
    (contDiff_laplacian_planar hφ).continuous (hasCompactSupport_laplacian_planar hφc)

/-- Integrability of the exact negative-Laplacian test pairing. -/
theorem integrable_planarGreenQuadratic_mul_neg_laplacian {φ : PlanarSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable (fun x ↦ planarGreenQuadratic x * (-Δ φ x)) volume := by
  simpa only [Pi.neg_apply, mul_neg] using!
    (integrable_planarGreenQuadratic_mul_laplacian hφ hφc).neg

/-- Both sides of the weak identity and the test itself are integrable. -/
theorem integrable_planarGreenQuadratic_test_pairings {φ : PlanarSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    Integrable φ volume ∧
      Integrable (fun x ↦ planarGreenQuadratic x * (-Δ φ x)) volume ∧
      Integrable (fun x ↦ -(2 * Real.pi) * φ x) volume := by
  have hi : Integrable φ volume := hφ.continuous.integrable_of_hasCompactSupport hφc
  exact ⟨hi, integrable_planarGreenQuadratic_mul_neg_laplacian hφ hφc, hi.const_mul _⟩

/-- The ordinary-Laplacian pairing of the quadratic correction. -/
theorem integral_planarGreenQuadratic_mul_laplacian {φ : PlanarSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, planarGreenQuadratic x * Δ φ x) = (2 * Real.pi) * ∫ x, φ x := by
  rw [integral_planar_mul_laplacian_eq_laplacian_mul
    contDiff_planarGreenQuadratic hφ hφc]
  simp_rw [laplacian_planarGreenQuadratic]
  exact integral_const_mul _ _

/-- The quadratic term contributes the constant density `-(2 * Real.pi)`
to the negative ordinary Laplacian, for every smooth compact real test. -/
theorem integral_planarGreenQuadratic_mul_neg_laplacian {φ : PlanarSpace → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    (∫ x, planarGreenQuadratic x * (-Δ φ x)) = -(2 * Real.pi) * ∫ x, φ x := by
  simp_rw [mul_neg]
  rw [integral_neg, integral_planarGreenQuadratic_mul_laplacian hφ hφc]
  ring

end PeriodicAttractiveLogGas
