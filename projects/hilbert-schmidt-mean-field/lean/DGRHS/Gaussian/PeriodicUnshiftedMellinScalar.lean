import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Scalar adapter; no torus factory is asserted.
Native reuse: Mathlib pin d13f23b723b8a846827a245b89c10fc7d3f11612,
GaussianIntegral.lean:74 and Gamma/Basic.lean:465. Apache-2.0 native
sources and authorship headers are preserved in the adjacent native directory.
The Mellin power stays in u; only the heat time is translated by τ.
-/
noncomputable section
open MeasureTheory Set

namespace DGRHS.Periodic

lemma periodicUnshiftedMellin_exp_bound (p τ u : ℝ) (hτ : 0 ≤ τ) (hu : 0 < u) :
    0 ≤ u ^ p * Real.exp (-(u + τ) / 2) ∧
      u ^ p * Real.exp (-(u + τ) / 2) ≤ u ^ p * Real.exp (-u / 2) := by
  constructor
  · exact mul_nonneg (Real.rpow_nonneg hu.le p) (Real.exp_pos _).le
  · apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hu.le p)
    apply Real.exp_le_exp.mpr
    linarith

/-- Properness needs p > -1, not p ≥ 0. The shift may be any real number
for this scalar identity; torus heat use separately requires τ ≥ 0. -/
lemma periodicUnshiftedMellin_integrable (p τ q : ℝ) (hp : -1 < p) (hq : 0 < q) :
    IntegrableOn (fun u : ℝ => u ^ p * Real.exp (-(q * (u + τ)))) (Ioi 0) := by
  have hi : IntegrableOn (fun u : ℝ => u ^ p * Real.exp (-q * u)) (Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow hp (by norm_num : (0 : ℝ) < 1) hq
  apply (hi.const_mul (Real.exp (-(q * τ)))).congr
  exact Filter.Eventually.of_forall (fun u => by
    dsimp only
    rw [show -(q * (u + τ)) = -(q * τ) + -q * u by ring, Real.exp_add]
    ring)

/-- Exact Fourier-mode scalar, before any torus Fubini or representative claim. -/
lemma periodicUnshiftedMellin_laplace (p τ q : ℝ) (hp : -1 < p) (hq : 0 < q) :
    (∫ u : ℝ in Ioi 0, u ^ p * Real.exp (-(q * (u + τ)))) =
      Real.exp (-(q * τ)) * ((1 / q) ^ (p + 1) * Real.Gamma (p + 1)) := by
  calc
    _ = ∫ u : ℝ in Ioi 0,
        Real.exp (-(q * τ)) * (u ^ p * Real.exp (-(q * u))) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun u => by
        dsimp only
        rw [show -(q * (u + τ)) = -(q * τ) + -(q * u) by ring, Real.exp_add]
        ring)
    _ = Real.exp (-(q * τ)) *
        (∫ u : ℝ in Ioi 0, u ^ p * Real.exp (-(q * u))) := integral_const_mul _ _
    _ = _ := by
      congr 1
      simpa only [add_sub_cancel_right] using
        Real.integral_rpow_mul_exp_neg_mul_Ioi (a := p + 1) (r := q) (by linarith) hq

lemma periodicUnshiftedMellin_majorant_integrable (p : ℝ) (hp : -1 < p) :
    IntegrableOn (fun u : ℝ => u ^ p * Real.exp (-u / 2)) (Ioi 0) := by
  have hi := periodicUnshiftedMellin_integrable p 0 (1 / 2) hp (by norm_num)
  apply hi.congr
  exact Filter.Eventually.of_forall (fun u => by
    dsimp only
    congr 2
    ring)

lemma periodicUnshiftedMellin_majorant_integral (p : ℝ) (hp : -1 < p) :
    (∫ u : ℝ in Ioi 0, u ^ p * Real.exp (-u / 2)) =
      (2 : ℝ) ^ (p + 1) * Real.Gamma (p + 1) := by
  have h := periodicUnshiftedMellin_laplace p 0 (1 / 2) hp (by norm_num)
  have he : (fun u : ℝ => u ^ p * Real.exp (-((1 / 2) * (u + 0)))) =
      (fun u : ℝ => u ^ p * Real.exp (-u / 2)) := by
    funext u
    congr 2
    ring
  rw [he] at h
  norm_num at h
  exact h

lemma periodicUnshiftedMellin_spectralExponent (d s : ℝ) (hsd : s < d) :
    -1 < (d - s) / 2 - 1 := by
  linarith

lemma periodicUnshiftedMellin_hilbertSchmidtExponent (d s : ℝ)
    (hs : 0 < s) (hhs : 2 * s < d) : -1 < (d - s) / 2 - 1 := by
  linarith

end DGRHS.Periodic
