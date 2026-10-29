import SharpSymmetricLSI.Paper.Defective8

/-!
# R03 (Proposition 2.2), part 12: positive bounded regularization

`T_n(t) = t / √(1 + t²/n²)` and `ψ_n(t) = √(T_n(t)² + 1/n²)`, `n ≥ 1`:
* `ψ_n` is smooth, `1/n ≤ ψ_n ≤ n + 1`, `|ψ_n'| ≤ 1` (`abs_deriv_psiReg_le`);
* `ψ_n² = T_n² + 1/n²` has a derivative bounded by `2n`;
* `ψ_n(t)² ≤ t² + 1` and `ψ_n(t)² → t²`.
Hence `f ↦ ψ_n ∘ f` maps `H¹` into bounded functions bounded below, does not increase the energy,
and `Ent((ψ_n ∘ f)²) → Ent(f²)` from below in the `liminf` sense.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace SharpLSI

/-- `T_n(t) = t / √(1 + t²/n²)`. -/
noncomputable def truncReg (n : ℕ) (t : ℝ) : ℝ := t / Real.sqrt (1 + t ^ 2 / ((n : ℝ) + 1) ^ 2)

/-- `ψ_n(t) = √(T_n(t)² + 1/(n+1)²)`. -/
noncomputable def psiReg (n : ℕ) (t : ℝ) : ℝ :=
  Real.sqrt (truncReg n t ^ 2 + 1 / ((n : ℝ) + 1) ^ 2)

theorem one_add_pos (n : ℕ) (t : ℝ) : 0 < 1 + t ^ 2 / ((n : ℝ) + 1) ^ 2 := by positivity

theorem truncReg_sq (n : ℕ) (t : ℝ) :
    truncReg n t ^ 2 = t ^ 2 / (1 + t ^ 2 / ((n : ℝ) + 1) ^ 2) := by
  unfold truncReg
  rw [div_pow, Real.sq_sqrt (one_add_pos n t).le]

theorem truncReg_sq_le (n : ℕ) (t : ℝ) : truncReg n t ^ 2 ≤ t ^ 2 := by
  rw [truncReg_sq]
  exact div_le_self (sq_nonneg _) (by have : 0 ≤ t ^ 2 / ((n : ℝ) + 1) ^ 2 := (by positivity); linarith)

theorem truncReg_sq_le' (n : ℕ) (t : ℝ) : truncReg n t ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
  rw [truncReg_sq, div_le_iff₀ (one_add_pos n t)]
  have h : 0 < ((n : ℝ) + 1) ^ 2 := by positivity
  rw [mul_add, mul_one, mul_div_cancel₀ _ h.ne']
  linarith

theorem psiReg_sq (n : ℕ) (t : ℝ) : psiReg n t ^ 2 = truncReg n t ^ 2 + 1 / ((n : ℝ) + 1) ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem psiReg_ge (n : ℕ) (t : ℝ) : 1 / ((n : ℝ) + 1) ≤ psiReg n t := by
  unfold psiReg
  rw [show 1 / ((n : ℝ) + 1) = Real.sqrt (1 / ((n : ℝ) + 1) ^ 2) by
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_one, Real.sqrt_sq (by positivity)]]
  exact Real.sqrt_le_sqrt (by have := sq_nonneg (truncReg n t); linarith)

theorem psiReg_le (n : ℕ) (t : ℝ) : psiReg n t ≤ (n : ℝ) + 2 := by
  have h1 := truncReg_sq_le' n t
  have h2 : 1 / ((n : ℝ) + 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  unfold psiReg
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem psiReg_sq_le (n : ℕ) (t : ℝ) : psiReg n t ^ 2 ≤ t ^ 2 + 1 := by
  rw [psiReg_sq]
  have h1 := truncReg_sq_le n t
  have h2 : 1 / ((n : ℝ) + 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]; nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  linarith

theorem tendsto_psiReg_sq (t : ℝ) : Tendsto (fun n => psiReg n t ^ 2) atTop (𝓝 (t ^ 2)) := by
  simp_rw [psiReg_sq, truncReg_sq]
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
    have h0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h := h0.pow 2
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num] at h
    refine h.congr fun n => ?_
    rw [div_pow, one_pow]
  have h3 : Tendsto (fun n : ℕ => 1 + t ^ 2 / ((n : ℝ) + 1) ^ 2) atTop (𝓝 1) := by
    have h := (h1.const_mul (t ^ 2)).const_add 1
    rw [mul_zero, add_zero] at h
    refine h.congr fun n => ?_
    rw [mul_one_div]
  have h2 : Tendsto (fun n : ℕ => t ^ 2 / (1 + t ^ 2 / ((n : ℝ) + 1) ^ 2)) atTop (𝓝 (t ^ 2)) := by
    have h := (tendsto_const_nhds (x := t ^ 2)).div h3 one_ne_zero
    rw [div_one] at h
    exact h.congr fun n => rfl
  have h := h2.add h1
  rw [add_zero] at h
  exact h.congr fun n => rfl

/-- `Ψ_n = ψ_n²` as an explicit function. -/
noncomputable def psiSqR (n : ℕ) (t : ℝ) : ℝ := t ^ 2 / (1 + t ^ 2 / ((n : ℝ) + 1) ^ 2) + 1 / ((n : ℝ) + 1) ^ 2

theorem psiSqR_eq (n : ℕ) (t : ℝ) : psiSqR n t = psiReg n t ^ 2 := by
  rw [psiReg_sq, truncReg_sq]; rfl

theorem psiSqR_pos (n : ℕ) (t : ℝ) : 0 < psiSqR n t := by
  unfold psiSqR; have := one_add_pos n t; positivity

theorem psiReg_eq_sqrt (n : ℕ) (t : ℝ) : psiReg n t = Real.sqrt (psiSqR n t) := by
  rw [psiSqR_eq, Real.sqrt_sq (le_trans (by positivity) (psiReg_ge n t))]

theorem hasDerivAt_psiSqR (n : ℕ) (t : ℝ) :
    HasDerivAt (psiSqR n) (2 * t / (1 + t ^ 2 / ((n : ℝ) + 1) ^ 2) ^ 2) t := by
  set a : ℝ := (n : ℝ) + 1
  have ha : 0 < a := by positivity
  have h1 : HasDerivAt (fun t : ℝ => 1 + t ^ 2 / a ^ 2) (2 * t / a ^ 2) t := by
    have := ((hasDerivAt_pow 2 t).div_const (a ^ 2)).const_add 1
    convert this using 1; push_cast; ring
  have h2 := (hasDerivAt_pow 2 t).div h1 (one_add_pos n t).ne'
  have h3 := h2.add_const (1 / a ^ 2)
  unfold psiSqR
  convert h3 using 1
  have hp := one_add_pos n t
  field_simp
  ring

theorem contDiff_psiSqR (n : ℕ) : ContDiff ℝ 1 (psiSqR n) := by
  unfold psiSqR
  refine ContDiff.add ?_ contDiff_const
  exact (contDiff_id.pow 2).div (contDiff_const.add ((contDiff_id.pow 2).div_const _))
    fun t => (one_add_pos n t).ne'

theorem contDiff_psiReg (n : ℕ) : ContDiff ℝ 1 (psiReg n) := by
  have : psiReg n = fun t => Real.sqrt (psiSqR n t) := funext (psiReg_eq_sqrt n)
  rw [this]
  exact (contDiff_psiSqR n).sqrt fun t => (psiSqR_pos n t).ne'

theorem abs_deriv_psiSqR_le (n : ℕ) (t : ℝ) : |deriv (psiSqR n) t| ≤ (n : ℝ) + 1 := by
  set a : ℝ := (n : ℝ) + 1
  have ha : 0 < a := by positivity
  rw [(hasDerivAt_psiSqR n t).deriv]
  set u := 1 + t ^ 2 / a ^ 2
  have hu : 1 ≤ u := by have : 0 ≤ t ^ 2 / a ^ 2 := (by positivity); simp only [u]; linarith
  rw [abs_div, abs_of_pos (by positivity : 0 < u ^ 2), div_le_iff₀ (by positivity)]
  have key : |2 * t| ≤ a * u := by
    rw [abs_mul, abs_two]
    have e : a * u = (a * a + t ^ 2) / a := by simp only [u]; field_simp
    rw [e, le_div_iff₀ ha]
    nlinarith [sq_nonneg (|t| - a), sq_abs t]
  calc |2 * t| ≤ a * u := key
    _ ≤ a * u ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) ha.le

theorem hasDerivAt_psiReg (n : ℕ) (t : ℝ) :
    HasDerivAt (psiReg n) (2 * t / (1 + t ^ 2 / ((n : ℝ) + 1) ^ 2) ^ 2 / (2 * psiReg n t)) t := by
  have h := (hasDerivAt_psiSqR n t).sqrt (psiSqR_pos n t).ne'
  have e : psiReg n = fun t => Real.sqrt (psiSqR n t) := funext (psiReg_eq_sqrt n)
  rw [e]
  convert h using 2

theorem abs_deriv_psiReg_le (n : ℕ) (t : ℝ) : |deriv (psiReg n) t| ≤ 1 := by
  set a : ℝ := (n : ℝ) + 1
  rw [(hasDerivAt_psiReg n t).deriv]
  set u := 1 + t ^ 2 / a ^ 2
  have hu : 1 ≤ u := by have : 0 ≤ t ^ 2 / a ^ 2 := (by positivity); simp only [u]; linarith
  have hψ : 0 < psiReg n t := lt_of_lt_of_le (by positivity) (psiReg_ge n t)
  have hψ2 : t ^ 2 / u ≤ psiReg n t ^ 2 := by
    rw [psiReg_sq, truncReg_sq]; have : 0 ≤ 1 / a ^ 2 := (by positivity); linarith
  rw [abs_div, abs_div, abs_of_pos (by positivity : 0 < u ^ 2), abs_of_pos (by positivity : 0 < 2 * psiReg n t),
    div_div, div_le_one (by positivity), abs_mul, abs_two]
  -- `|t| ≤ u² ψ`
  have h1 : t ^ 2 ≤ u * psiReg n t ^ 2 := by
    rw [div_le_iff₀ (by linarith)] at hψ2; linarith
  have h2 : |t| ≤ u ^ 2 * psiReg n t := by
    have : |t| ^ 2 ≤ (u ^ 2 * psiReg n t) ^ 2 := by
      rw [sq_abs, mul_pow]
      have hu2 : u ≤ u ^ 2 := by nlinarith
      have hu3 : u ^ 2 ≤ (u ^ 2) ^ 2 := by nlinarith
      have hu4 : u ≤ (u ^ 2) ^ 2 := hu2.trans hu3
      nlinarith [mul_le_mul_of_nonneg_right hu4 (sq_nonneg (psiReg n t))]
    exact (pow_le_pow_iff_left₀ (abs_nonneg t) (by positivity) two_ne_zero).mp this
  nlinarith [abs_nonneg t]

end SharpLSI
