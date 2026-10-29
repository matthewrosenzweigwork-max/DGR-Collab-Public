import Mathlib

/-!
# Lane D: Gibbs variational inequality on the unit interval (pure real analysis)
-/

open MeasureTheory intervalIntegral InformationTheory

namespace SharpLSI.FL.Prop82

/-- Intended (parenthesised) Gibbs variational inequality; fully proved. -/
theorem gibbs_interval_paren {σ g : ℝ → ℝ} (hσ : Continuous σ) (hpos : ∀ t, 0 < σ t)
    (hg : Continuous g) (hmass : ∫ t in (0 : ℝ)..1, σ t = 1) (s : ℝ) :
    s * (∫ t in (0 : ℝ)..1, σ t * g t) - Real.log (∫ t in (0 : ℝ)..1, Real.exp (s * g t)) ≤
      ∫ t in (0 : ℝ)..1, klFun (σ t) := by
  have hE : Continuous fun t => Real.exp (s * g t) := by fun_prop
  have hLog : Continuous fun t => Real.log (σ t) := hσ.log (fun t => (hpos t).ne')
  have hSL : Continuous fun t => σ t * Real.log (σ t) := hσ.mul hLog
  have hSG : Continuous fun t => σ t * g t := hσ.mul hg
  have hZ : 0 < ∫ t in (0 : ℝ)..1, Real.exp (s * g t) :=
    intervalIntegral.intervalIntegral_pos_of_pos (hE.intervalIntegrable _ _)
      (fun t => Real.exp_pos _) zero_lt_one
  set Z := ∫ t in (0 : ℝ)..1, Real.exp (s * g t) with hZdef
  have hpt : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      σ t * (s * g t - Real.log Z) - σ t * Real.log (σ t) ≤ Real.exp (s * g t) / Z - σ t := by
    intro t _
    have hq : 0 < Real.exp (s * g t) / Z := div_pos (Real.exp_pos _) hZ
    have h1 := Real.log_le_sub_one_of_pos (div_pos hq (hpos t))
    rw [Real.log_div hq.ne' (hpos t).ne', Real.log_div (Real.exp_pos _).ne' hZ.ne',
      Real.log_exp] at h1
    have h2 := mul_le_mul_of_nonneg_left h1 (hpos t).le
    have h3 : σ t * (Real.exp (s * g t) / Z / σ t - 1) = Real.exp (s * g t) / Z - σ t := by
      field_simp [(hpos t).ne']
    nlinarith
  set L := Real.log Z with hL
  have hf1 : IntervalIntegrable (fun t => s * (σ t * g t)) MeasureTheory.volume 0 1 :=
    (hSG.const_mul s).intervalIntegrable _ _
  have hf2 : IntervalIntegrable (fun t => L * σ t) MeasureTheory.volume 0 1 :=
    (hσ.const_mul L).intervalIntegrable _ _
  have hf3 : IntervalIntegrable (fun t => σ t * Real.log (σ t)) MeasureTheory.volume 0 1 :=
    hSL.intervalIntegrable _ _
  have hf4 : IntervalIntegrable (fun t => Real.exp (s * g t) / Z) MeasureTheory.volume 0 1 :=
    (hE.div_const Z).intervalIntegrable _ _
  have hf5 : IntervalIntegrable σ MeasureTheory.volume 0 1 := hσ.intervalIntegrable _ _
  have hint := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1) zero_le_one
    (f := fun t => (s * (σ t * g t) - L * σ t) - σ t * Real.log (σ t))
    (g := fun t => Real.exp (s * g t) / Z - σ t)
    ((hf1.sub hf2).sub hf3) (hf4.sub hf5)
    (fun t ht => by have := hpt t ht; linarith)
  rw [intervalIntegral.integral_sub (hf1.sub hf2) hf3, intervalIntegral.integral_sub hf1 hf2,
    intervalIntegral.integral_sub hf4 hf5, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_div, hmass, ← hZdef,
    div_self hZ.ne'] at hint
  have hkl : ∫ t in (0 : ℝ)..1, klFun (σ t) = ∫ t in (0 : ℝ)..1, σ t * Real.log (σ t) := by
    have : (fun t => klFun (σ t)) = fun t => (σ t * Real.log (σ t) - σ t) + 1 := by
      funext t; rw [klFun_apply]; ring
    rw [this, intervalIntegral.integral_add ((hf3.sub hf5)) intervalIntegrable_const,
      intervalIntegral.integral_sub hf3 hf5, hmass]
    simp
  rw [hkl]
  rw [mul_one, sub_self] at hint
  exact sub_nonpos.mp hint


end SharpLSI.FL.Prop82
