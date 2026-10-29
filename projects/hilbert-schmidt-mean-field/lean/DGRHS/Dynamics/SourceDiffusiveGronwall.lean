import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-
Source: DGR_PFunc_Current_20260902_145019_UTC.tex, thm:diffusiveMeanFieldConvergence.
Independent variable-coefficient adaptation using pinned Mathlib's AC fundamental
theorem and Lebesgue differentiation theorem. No pointwise derivative assumption.
Coefficient interval integrability is explicit here; source finiteness/measurability
interpretation is a separate obligation. No commutator estimate is proved here.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Interval

namespace DGRHS.Dynamics

theorem absolutelyContinuous_exp {f : ℝ → ℝ} {a b : ℝ}
    (hf : AbsolutelyContinuousOnInterval f a b) :
    AbsolutelyContinuousOnInterval (fun t => Real.exp (f t)) a b := by
  obtain ⟨C, hC⟩ := hf.exists_bound
  obtain ⟨K, hK⟩ := (Real.contDiff_exp.contDiffOn :
    ContDiffOn ℝ 1 Real.exp (Icc (-C) C)).exists_lipschitzOnWith
      (by decide) (convex_Icc _ _) isCompact_Icc
  apply hK.comp_absolutelyContinuousOnInterval ?_ hf
  intro t ht
  exact abs_le.mp (by simpa only [Real.norm_eq_abs] using hC t ht)

/-- Signed AC energy, genuine AE dissipation, and proper variable coefficients. -/
theorem variable_gronwall_prefix {E a b : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hE : AbsolutelyContinuousOnInterval E 0 T)
    (ha : IntervalIntegrable a volume 0 T) (hb : IntervalIntegrable b volume 0 T)
    (hd : ∀ᵐ t ∂volume, t ∈ Icc 0 T → deriv E t ≤ a t * E t + b t) :
    E T ≤ Real.exp (∫ t in 0..T, a t) * E 0 +
      Real.exp (∫ t in 0..T, a t) *
        ∫ t in 0..T, b t * Real.exp (-(∫ r in 0..t, a r)) := by
  let I : ℝ → ℝ := fun t => ∫ r in 0..t, a r
  let g : ℝ → ℝ := fun t => Real.exp (-I t)
  have hI : AbsolutelyContinuousOnInterval I 0 T :=
    ha.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hg : AbsolutelyContinuousOnInterval g 0 T := absolutelyContinuous_exp hI.neg
  have hp := hE.fun_mul hg
  have hbg : IntervalIntegrable (fun t => b t * g t) volume 0 T :=
    hb.mul_continuousOn hg.continuousOn
  have hgderiv : ∀ᵐ t ∂volume, t ∈ Icc 0 T →
      HasDerivAt g (-a t * g t) t := by
    filter_upwards [ha.ae_hasDerivAt_integral] with t ht htT
    have ht' := ht (by simpa [uIcc_of_le hT] using htT) 0 (by simp)
    simpa [I, g, mul_comm] using ht'.neg.exp
  have hle : (fun t => deriv (fun r => E r * g r) t) ≤ᵐ[volume.restrict (Icc 0 T)]
      (fun t => b t * g t) := by
    change ∀ᵐ t ∂volume.restrict (Icc 0 T),
      deriv (fun r => E r * g r) t ≤ b t * g t
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hE.ae_differentiableAt, hgderiv, hd] with t ht hgt hdt htT
    have ht' := (ht (by simpa [uIcc_of_le hT] using htT)).hasDerivAt
    change deriv (E * g) t ≤ b t * g t
    rw [(ht'.mul (hgt htT)).deriv]
    have := mul_le_mul_of_nonneg_right (hdt htT) (le_of_lt (Real.exp_pos (-I t)))
    dsimp [g] at *
    nlinarith
  have hint := intervalIntegral.integral_mono_ae_restrict hT
    hp.intervalIntegrable_deriv hbg hle
  rw [hp.integral_deriv_eq_sub] at hint
  have hzero : g 0 = 1 := by simp [g, I]
  rw [hzero, mul_one] at hint
  have hmul : Real.exp (I T) * g T = 1 := by simp [g, ← Real.exp_add]
  have hsum : E T * g T ≤ E 0 + ∫ t in 0..T, b t * g t := by linarith
  have hfinal := mul_le_mul_of_nonneg_left hsum
    (le_of_lt (Real.exp_pos (I T)))
  calc
    E T = Real.exp (I T) * (E T * g T) := by rw [mul_left_comm, hmul, mul_one]
    _ ≤ Real.exp (I T) * (E 0 + ∫ t in 0..T, b t * g t) := hfinal
    _ = _ := by simp only [mul_add, I, g]

#print axioms absolutelyContinuous_exp
#print axioms variable_gronwall_prefix
end DGRHS.Dynamics
