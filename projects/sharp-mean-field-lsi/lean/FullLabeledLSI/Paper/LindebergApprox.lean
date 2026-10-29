import Mathlib

/-!
# Uniform approximation by `C_c^∞` functions (for Lemma 7.1, (7.11))

* `exists_smooth_approx_of_continuous`: a continuous compactly supported `f` on a finite-dimensional
  normed space is uniformly within `ε` of a `C_c^∞` function.
* `exists_smooth_approx_cutoff`: any continuous `Φ` is within `ε` of a `C_c^∞` function `g` up to the
  tail: `|Φ p - g p| ≤ ε + |Φ p| 1[ρ < ‖p‖]` (cutoff at radius `ρ`, then mollify).
-/

open scoped ContDiff

namespace SharpLSI.FL

/-- Uniform `C_c^∞` approximation of a continuous compactly supported function. -/
theorem exists_smooth_approx_of_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {f : E → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x, |f x - g x| ≤ ε := by
  borelize E
  obtain ⟨δ, hδ, hfδ⟩ := Metric.uniformContinuous_iff.mp (hc.uniformContinuous_of_continuous hf) ε hε
  set φ : ContDiffBump (0 : E) := ⟨δ / 2, δ, half_pos hδ, half_lt_self hδ⟩
  set μ : MeasureTheory.Measure E := MeasureTheory.Measure.addHaar
  have hloc : MeasureTheory.LocallyIntegrable f μ := hf.locallyIntegrable
  refine ⟨MeasureTheory.convolution (φ.normed μ) f (ContinuousLinearMap.lsmul ℝ ℝ) μ,
    φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed hloc,
    φ.hasCompactSupport_normed.convolution _ hc, fun x => ?_⟩
  rw [← Real.dist_eq, dist_comm]
  exact φ.dist_normed_convolution_le hf.aestronglyMeasurable fun y hy => (hfδ hy).le

/-- Approximation of a continuous function, exact up to `ε` inside the ball of radius `ρ` and
dominated by `|Φ|` outside. -/
theorem exists_smooth_approx_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Φ : E → ℝ} (hΦ : Continuous Φ) {ρ ε : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) :
    ∃ g : E → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      ∀ p, |Φ p - g p| ≤ ε + (if ρ < ‖p‖ then |Φ p| else 0) := by
  set χ : E → ℝ := fun p => max 0 (min 1 (2 - ‖p‖ / ρ)) with hχ
  have hχc : Continuous χ := by simp only [hχ]; fun_prop
  have hχ0 : ∀ p, 0 ≤ χ p := fun p => le_max_left _ _
  have hχ1 : ∀ p, χ p ≤ 1 := fun p => max_le zero_le_one (min_le_left _ _)
  have hχρ : ∀ p, ‖p‖ ≤ ρ → χ p = 1 := by
    intro p hp
    have : 1 ≤ 2 - ‖p‖ / ρ := by
      have := (div_le_one hρ).2 hp
      linarith
    simp [hχ, this]
  have hχ2 : ∀ p, 2 * ρ < ‖p‖ → χ p = 0 := by
    intro p hp
    have : 2 - ‖p‖ / ρ < 0 := by
      have := (lt_div_iff₀ hρ).2 hp
      linarith
    simp [hχ, min_le_of_right_le this.le]
  have hc : HasCompactSupport (fun p => χ p * Φ p) :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * ρ)) fun p hp => by
      rw [hχ2 p (by simpa [dist_zero_right] using hp), zero_mul]
  obtain ⟨g, hg, hgc, hgε⟩ := exists_smooth_approx_of_continuous (hχc.mul hΦ) hc hε
  refine ⟨g, hg, hgc, fun p => ?_⟩
  have h1 : |χ p * Φ p - g p| ≤ ε := hgε p
  have h2 : |Φ p - χ p * Φ p| ≤ if ρ < ‖p‖ then |Φ p| else 0 := by
    split_ifs with h
    · rw [← one_sub_mul, abs_mul, abs_of_nonneg (by linarith [hχ1 p])]
      exact mul_le_of_le_one_left (abs_nonneg _) (by linarith [hχ0 p])
    · rw [hχρ p (not_lt.1 h)]; simp
  calc |Φ p - g p| = |(Φ p - χ p * Φ p) + (χ p * Φ p - g p)| := by ring_nf
    _ ≤ |Φ p - χ p * Φ p| + |χ p * Φ p - g p| := abs_add_le _ _
    _ ≤ _ := by linarith

end SharpLSI.FL
