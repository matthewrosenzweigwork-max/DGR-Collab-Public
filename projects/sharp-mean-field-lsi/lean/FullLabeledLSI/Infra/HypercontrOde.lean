import Mathlib

/-!
# Gross's differential inequality: the scalar ODE step

`qexp a t = 1 + e^{2at}` is Gross's exponent. If `Φ > 0` satisfies
`Φ' ≤ (q'/q) Φ log Φ` on `[0, ∞)` with `q' = 2a (q - 1)`, then `log Φ / q` is non-increasing,
hence `log Φ(t) / q(t) ≤ log Φ(0) / 2`.
-/

namespace SharpLSI.FL.Gross

open Real

/-- Gross's exponent `q(t) = 1 + e^{2at}`. -/
noncomputable def qexp (a t : ℝ) : ℝ := 1 + Real.exp (2 * a * t)

lemma qexp_pos (a t : ℝ) : 0 < qexp a t := by unfold qexp; positivity

lemma one_lt_qexp (a t : ℝ) : 1 < qexp a t := by
  unfold qexp; have := Real.exp_pos (2 * a * t); linarith

lemma qexp_zero (a : ℝ) : qexp a 0 = 2 := by simp [qexp]; norm_num

lemma two_le_qexp {a t : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) : 2 ≤ qexp a t := by
  unfold qexp
  have : 1 ≤ Real.exp (2 * a * t) := Real.one_le_exp (by positivity)
  linarith

lemma exp_eq_qexp_sub_one (a t : ℝ) : Real.exp (2 * a * t) = qexp a t - 1 := by
  unfold qexp; ring

lemma hasDerivAt_qexp (a t : ℝ) : HasDerivAt (qexp a) (2 * a * (qexp a t - 1)) t := by
  have h1 : HasDerivAt (fun t : ℝ => 2 * a * t) (2 * a) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * a)
  have h2 : HasDerivAt (fun x : ℝ => 1 + Real.exp (2 * a * x))
      (Real.exp (2 * a * t) * (2 * a)) t := h1.exp.const_add 1
  have e : 2 * a * (qexp a t - 1) = Real.exp (2 * a * t) * (2 * a) := by
    rw [← exp_eq_qexp_sub_one]; ring
  rw [e]; exact h2

/-- The scalar differential inequality `Φ' ≤ (q'/q) Φ log Φ` forces `log Φ / q` to decrease. -/
theorem gross_ode {a : ℝ} (ha : 0 < a) {Φ Φ' : ℝ → ℝ} (hpos : ∀ t, 0 ≤ t → 0 < Φ t)
    (hd : ∀ t, 0 ≤ t → HasDerivAt Φ (Φ' t) t)
    (hineq : ∀ t, 0 ≤ t →
      Φ' t ≤ 2 * a * (qexp a t - 1) / qexp a t * (Φ t * Real.log (Φ t))) :
    ∀ t, 0 ≤ t → Real.log (Φ t) / qexp a t ≤ Real.log (Φ 0) / 2 := by
  set H : ℝ → ℝ := fun t => Real.log (Φ t) / qexp a t with hH
  have hHd : ∀ t, 0 ≤ t → HasDerivAt H
      ((Φ' t / Φ t * qexp a t - Real.log (Φ t) * (2 * a * (qexp a t - 1))) / qexp a t ^ 2) t := by
    intro t ht
    have h1 : HasDerivAt (fun t => Real.log (Φ t)) (Φ' t / Φ t) t :=
      (hd t ht).log (hpos t ht).ne'
    exact h1.div (hasDerivAt_qexp a t) (qexp_pos a t).ne'
  have hHanti : AntitoneOn H (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · exact fun t ht => (hHd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      exact (hHd t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht0 : 0 ≤ t := le_of_lt ht
      rw [(hHd t ht0).deriv]
      have hq := qexp_pos a t
      have hΦ := hpos t ht0
      have h1 := hineq t ht0
      have h2 : Φ' t / Φ t ≤ 2 * a * (qexp a t - 1) / qexp a t * Real.log (Φ t) := by
        rw [div_le_iff₀ hΦ]; linarith
      have h3 : Φ' t / Φ t * qexp a t ≤ Real.log (Φ t) * (2 * a * (qexp a t - 1)) := by
        have := mul_le_mul_of_nonneg_right h2 hq.le
        calc Φ' t / Φ t * qexp a t ≤ 2 * a * (qexp a t - 1) / qexp a t * Real.log (Φ t) *
              qexp a t := this
          _ = Real.log (Φ t) * (2 * a * (qexp a t - 1)) := by field_simp
      apply div_nonpos_of_nonpos_of_nonneg
      · linarith
      · positivity
  intro t ht
  have := hHanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  simpa [hH, qexp_zero] using this

end SharpLSI.FL.Gross
