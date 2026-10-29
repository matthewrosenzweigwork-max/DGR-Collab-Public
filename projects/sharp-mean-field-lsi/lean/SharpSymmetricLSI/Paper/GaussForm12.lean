import SharpSymmetricLSI.Paper.GaussForm11

/-!
# R32 (D1): scaling of the relaxed form

`ℰ_∞(a f) = a² ℰ_∞(f)` (`gaussForm_smul`), for `λ ≥ 0`.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ContDiff ENNReal

namespace SharpLSI

variable {γ : Measure (ℕ → ℝ)}

/-- `a • c`. -/
noncomputable def Cyl.smul (a : ℝ) (c : Cyl) : Cyl where
  J := c.J
  φ := fun x => a * c.φ x
  smooth := contDiff_const.mul c.smooth
  compact := c.compact.mul_left

/-- The zero cylinder. -/
noncomputable def Cyl.zero : Cyl where
  J := 0
  φ := fun _ => 0
  smooth := contDiff_const
  compact := HasCompactSupport.zero

theorem Cyl.smul_eval (a : ℝ) (c : Cyl) (z : ℕ → ℝ) : (c.smul a).eval z = a * c.eval z := rfl

theorem Cyl.form_smul (a : ℝ) {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i) (c : Cyl) :
    (c.smul a).form lam' γ = ENNReal.ofReal (a ^ 2) * c.form lam' γ := by
  show ∫⁻ z, ENNReal.ofReal (∑ i : Fin c.J, lam' i *
      (fderiv ℝ (fun x => a * c.φ x) (fun j => z j) (Pi.single i 1)) ^ 2) ∂γ =
    ENNReal.ofReal (a ^ 2) * ∫⁻ z, ENNReal.ofReal (∑ i : Fin c.J, lam' i *
      (fderiv ℝ c.φ (fun j => z j) (Pi.single i 1)) ^ 2) ∂γ
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun z => ?_
  rw [← ENNReal.ofReal_mul (sq_nonneg a)]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderiv_const_mul (c.smooth.differentiable (by simp) _)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem Cyl.form_zero (lam' : ℕ → ℝ) : Cyl.zero.form lam' γ = 0 := by
  show ∫⁻ z, ENNReal.ofReal (∑ i : Fin 0, lam' i *
      (fderiv ℝ (fun _ : Fin 0 → ℝ => (0 : ℝ)) (fun j => z j) (Pi.single i 1)) ^ 2) ∂γ = 0
  simp

theorem gaussForm_le_liminf {lam' : ℕ → ℝ} {f : (ℕ → ℝ) → ℝ} (u : ℕ → Cyl)
    (hu : Tendsto (fun n => eLpNorm (fun z => (u n).eval z - f z) 2 γ) atTop (𝓝 0)) :
    gaussForm lam' γ f ≤ liminf (fun n => (u n).form lam' γ) atTop :=
  iInf₂_le u hu

theorem gaussForm_zero (lam' : ℕ → ℝ) : gaussForm lam' γ (fun _ => 0) = 0 := by
  refine le_antisymm ((gaussForm_le_liminf (fun _ => Cyl.zero) (by simp [Cyl.eval, Cyl.zero])).trans
    (by simp [Cyl.form_zero])) bot_le

theorem tendsto_smul_eLpNorm {u : ℕ → Cyl} {f : (ℕ → ℝ) → ℝ}
    (hu : Tendsto (fun n => eLpNorm (fun z => (u n).eval z - f z) 2 γ) atTop (𝓝 0)) (a : ℝ) :
    Tendsto (fun n => eLpNorm (fun z => ((u n).smul a).eval z - a * f z) 2 γ) atTop (𝓝 0) := by
  have e : ∀ n, (fun z => ((u n).smul a).eval z - a * f z) = a • fun z => (u n).eval z - f z :=
    fun n => funext fun z => by simp [Cyl.smul_eval, mul_sub]
  simp_rw [e, eLpNorm_const_smul]
  have := ENNReal.Tendsto.const_mul hu (a := ‖a‖ₑ) (Or.inr enorm_ne_top)
  simpa using this

theorem gaussForm_smul_le {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i) (a : ℝ)
    (f : (ℕ → ℝ) → ℝ) :
    gaussForm lam' γ (fun z => a * f z) ≤ ENNReal.ofReal (a ^ 2) * gaussForm lam' γ f := by
  by_cases ha : a = 0
  · subst ha
    simp only [zero_mul]
    rw [gaussForm_zero]; exact bot_le
  have hc0 : ENNReal.ofReal (a ^ 2) ≠ 0 := by simp [ha]
  unfold gaussForm
  rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  refine le_iInf fun u => ?_
  rw [ENNReal.mul_iInf_of_ne hc0 ENNReal.ofReal_ne_top]
  refine le_iInf fun hu => ?_
  refine (iInf₂_le (fun n => (u n).smul a) (tendsto_smul_eLpNorm hu a)).trans (le_of_eq ?_)
  simp_rw [Cyl.form_smul a hlam]
  exact ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top

/-- **Scaling.** -/
theorem gaussForm_smul {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i) (a : ℝ) (f : (ℕ → ℝ) → ℝ) :
    gaussForm lam' γ (fun z => a * f z) = ENNReal.ofReal (a ^ 2) * gaussForm lam' γ f := by
  refine le_antisymm (gaussForm_smul_le hlam a f) ?_
  by_cases ha : a = 0
  · subst ha; simp
  have h := gaussForm_smul_le (γ := γ) hlam a⁻¹ (fun z => a * f z)
  have e : (fun z => a⁻¹ * (a * f z)) = f := funext fun z => by field_simp
  rw [e] at h
  calc ENNReal.ofReal (a ^ 2) * gaussForm lam' γ f
      ≤ ENNReal.ofReal (a ^ 2) * (ENNReal.ofReal (a⁻¹ ^ 2) * gaussForm lam' γ (fun z => a * f z)) :=
        mul_le_mul_right h _
    _ = gaussForm lam' γ (fun z => a * f z) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg a), ← mul_pow, mul_inv_cancel₀ ha]
        simp
end SharpLSI
