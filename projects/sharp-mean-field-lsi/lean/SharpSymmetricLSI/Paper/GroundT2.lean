import SharpSymmetricLSI.Paper.GroundT1
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# R30 groundwork: the chain rule for `e^{-u/2}`, `u` bounded

`φ_A(t) = -A - 1 + (t+A+1) s(t+A+1)` (`s` the smooth transition) is smooth, equals `t` for
`t ≥ -A` and is `≥ -A-1`; `G_A = exp(-φ_A/2)` is `C¹` with bounded derivative, so the chain rule
`isWeakGrad_comp` applies, and `G_A(u) = e^{-u/2}` when `|u| ≤ A - 1`.
-/

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

namespace SharpLSI

/-- The smooth cut `φ_A`. -/
noncomputable def phiCutH (A t : ℝ) : ℝ := -A - 1 + (t + A + 1) * smoothTransition (t + A + 1)

theorem contDiff_phiCutH (A : ℝ) : ContDiff ℝ 1 (phiCutH A) := by
  have hs : ContDiff ℝ 1 (fun t : ℝ => smoothTransition (t + A + 1)) :=
    smoothTransition.contDiff.comp (by fun_prop)
  show ContDiff ℝ 1 fun t => -A - 1 + (t + A + 1) * smoothTransition (t + A + 1)
  exact contDiff_const.add ((by fun_prop : ContDiff ℝ 1 fun t : ℝ => t + A + 1).mul hs)

theorem phiCutH_eq {A t : ℝ} (ht : -A ≤ t) : phiCutH A t = t := by
  unfold phiCutH
  rw [smoothTransition.one_of_one_le (by linarith)]; ring

theorem phiCutH_ge (A t : ℝ) : -A - 1 ≤ phiCutH A t := by
  unfold phiCutH
  rcases le_or_gt 0 (t + A + 1) with h | h
  · have := mul_nonneg h (smoothTransition.nonneg (t + A + 1)); linarith
  · rw [smoothTransition.zero_of_nonpos h.le]; linarith

theorem deriv_phiCutH_of_gt {A t : ℝ} (ht : -A < t) : deriv (phiCutH A) t = 1 := by
  have h : phiCutH A =ᶠ[𝓝 t] id := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact phiCutH_eq (le_of_lt hx)
  rw [h.deriv_eq, deriv_id]

theorem deriv_phiCutH_of_lt {A t : ℝ} (ht : t < -A - 1) : deriv (phiCutH A) t = 0 := by
  have h : phiCutH A =ᶠ[𝓝 t] fun _ => -A - 1 := by
    filter_upwards [Iio_mem_nhds ht] with x hx
    unfold phiCutH
    rw [smoothTransition.zero_of_nonpos (by simp only [mem_Iio] at hx; linarith)]; ring
  rw [h.deriv_eq, deriv_const]

theorem exists_bound_deriv_phiCutH (A : ℝ) : ∃ M, 0 ≤ M ∧ ∀ t, |deriv (phiCutH A) t| ≤ M := by
  have hc : Continuous (deriv (phiCutH A)) := (contDiff_phiCutH A).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -A - 1) (b := -A)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 1, le_max_of_le_right zero_le_one, fun t => ?_⟩
  rcases lt_or_ge t (-A - 1) with h1 | h1
  · rw [deriv_phiCutH_of_lt h1, abs_zero]; exact le_max_of_le_right zero_le_one
  rcases lt_or_ge (-A) t with h2 | h2
  · rw [deriv_phiCutH_of_gt h2, abs_one]; exact le_max_right _ _
  · have := hC t ⟨h1, h2⟩
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)

/-- `G_A = exp(-φ_A/2)`. -/
noncomputable def expCutH (A t : ℝ) : ℝ := rexp (-(phiCutH A t) / 2)

theorem contDiff_expCutH (A : ℝ) : ContDiff ℝ 1 (expCutH A) :=
  Real.contDiff_exp.comp ((contDiff_phiCutH A).neg.div_const 2)

theorem deriv_expCutH (A t : ℝ) :
    deriv (expCutH A) t = rexp (-(phiCutH A t) / 2) * (-(deriv (phiCutH A) t) / 2) := by
  have hφ : HasDerivAt (phiCutH A) (deriv (phiCutH A) t) t :=
    ((contDiff_phiCutH A).differentiable one_ne_zero t).hasDerivAt
  exact ((hφ.neg.div_const 2).exp).deriv

theorem exists_bound_deriv_expCutH (A : ℝ) : ∃ L, ∀ t, |deriv (expCutH A) t| ≤ L := by
  obtain ⟨M, hM0, hM⟩ := exists_bound_deriv_phiCutH A
  refine ⟨rexp ((A + 1) / 2) * (M / 2), fun t => ?_⟩
  rw [deriv_expCutH, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul (Real.exp_le_exp.2 (by have := phiCutH_ge A t; linarith)) ?_ (abs_nonneg _)
    (Real.exp_pos _).le
  rw [abs_div, abs_neg, abs_two]
  exact div_le_div_of_nonneg_right (hM t) zero_le_two

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **Chain rule for `e^{-u/2}`**, `u` bounded. -/
theorem isWeakGrad_exp_neg_half {u : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad u g) (hui : Integrable u volume) (hgi : ∀ k, Integrable (fun y => g y k) volume)
    {B : ℝ} (hB : ∀ y, |u y| ≤ B) :
    IsWeakGrad (fun y => rexp (-(u y) / 2)) (fun y k => -(1 / 2) * rexp (-(u y) / 2) * g y k) := by
  obtain ⟨L, hL⟩ := exists_bound_deriv_expCutH (B + 1)
  have := isWeakGrad_comp h hui hgi (contDiff_expCutH (B + 1)) hL
  have hge : ∀ y, -(B + 1) < u y := fun y => by have := (abs_le.1 (hB y)).1; linarith
  convert this using 1
  · funext y
    simp only [expCutH, phiCutH_eq (le_of_lt (hge y))]
  · funext y k
    rw [deriv_expCutH, phiCutH_eq (le_of_lt (hge y)), deriv_phiCutH_of_gt (hge y)]
    ring

end SharpLSI
