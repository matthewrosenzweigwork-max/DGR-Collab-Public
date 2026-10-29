import SharpSymmetricLSI.Paper.AppAEnt5

/-!
# The entropy (6): the limit `δ → 0` of `G_δ`

`G_δ(r) = K_δ(r) - r log δ` with `K_δ(r) = r log(r + √(r² + δ²)) - √(r² + δ²)`, and for `r ≥ 0`,
`K_δ(r) → K_0(r) = r log(2r) - r` boundedly on `[0, K]` as `δ → 0`.
-/

open Real Filter Topology Set

namespace SharpLSI

noncomputable def entK (δ r : ℝ) : ℝ := r * Real.log (r + Real.sqrt (r ^ 2 + δ ^ 2)) - Real.sqrt (r ^ 2 + δ ^ 2)
noncomputable def entK0 (r : ℝ) : ℝ := r * Real.log (2 * r) - r

theorem abs_lt_sqrt_sq_add {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : |r| < Real.sqrt (r ^ 2 + δ ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)

theorem entArg_pos {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : 0 < r + Real.sqrt (r ^ 2 + δ ^ 2) := by
  have := abs_lt_sqrt_sq_add hδ r
  have := neg_abs_le r
  linarith

theorem entG_eq {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : entG δ r = entK δ r - r * Real.log δ := by
  unfold entG entK
  have h1 : r / δ + Real.sqrt (1 + (r / δ) ^ 2) = (r + Real.sqrt (r ^ 2 + δ ^ 2)) / δ := by
    rw [← delta_mul_sqrt hδ r]; field_simp
  rw [Real.arsinh, h1, Real.log_div (entArg_pos hδ r).ne' hδ.ne']
  ring

theorem sqrt_sq_add_le {δ : ℝ} (hδ : 0 ≤ δ) (r : ℝ) : Real.sqrt (r ^ 2 + δ ^ 2) ≤ |r| + δ := by
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs r, abs_nonneg r]

theorem tendsto_entK {r : ℝ} (hr : 0 ≤ r) : Tendsto (fun δ => entK δ r) (𝓝[>] 0) (𝓝 (entK0 r)) := by
  rcases hr.lt_or_eq with hr | hr
  · have h2 : r + Real.sqrt (r ^ 2 + (0 : ℝ) ^ 2) ≠ 0 := by
      rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hr.le]; linarith
    have hcont : Continuous fun δ : ℝ => r + Real.sqrt (r ^ 2 + δ ^ 2) := by fun_prop
    have hs : Continuous fun δ : ℝ => Real.sqrt (r ^ 2 + δ ^ 2) := by fun_prop
    have hc : ContinuousAt (fun δ : ℝ => r * Real.log (r + Real.sqrt (r ^ 2 + δ ^ 2)) -
        Real.sqrt (r ^ 2 + δ ^ 2)) 0 :=
      (continuousAt_const.mul (hcont.continuousAt.log h2)).sub hs.continuousAt
    have e : r * Real.log (r + Real.sqrt (r ^ 2 + (0 : ℝ) ^ 2)) - Real.sqrt (r ^ 2 + (0 : ℝ) ^ 2) =
        entK0 r := by
      rw [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hr.le]; unfold entK0; ring_nf
    rw [← e]
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  · subst hr
    simp only [entK, entK0, zero_mul, zero_sub, mul_zero, Real.log_zero, sub_zero]
    have : Tendsto (fun δ : ℝ => -Real.sqrt ((0 : ℝ) ^ 2 + δ ^ 2)) (𝓝[>] 0) (𝓝 (-Real.sqrt (0 ^ 2 + 0 ^ 2))) :=
      ((by fun_prop : Continuous fun δ : ℝ => -Real.sqrt ((0 : ℝ) ^ 2 + δ ^ 2)).tendsto 0).mono_left
        nhdsWithin_le_nhds
    simpa using this

theorem abs_entK_le {K : ℝ} (hK : 0 ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {r : ℝ} (hr : 0 ≤ r)
    (hrK : r ≤ K) : |entK δ r| ≤ K * (2 * K + 1) + 1 + (K + 1) := by
  unfold entK
  set a := r + Real.sqrt (r ^ 2 + δ ^ 2)
  have ha : 0 < a := entArg_pos hδ r
  have hs : Real.sqrt (r ^ 2 + δ ^ 2) ≤ r + δ := by
    have := sqrt_sq_add_le hδ.le r; rwa [abs_of_nonneg hr] at this
  have hs0 : 0 ≤ Real.sqrt (r ^ 2 + δ ^ 2) := Real.sqrt_nonneg _
  have har : r ≤ a := by simp only [a]; linarith
  have haK : a ≤ 2 * K + 1 := by simp only [a]; linarith
  have hlog1 : Real.log a ≤ a := (Real.log_le_sub_one_of_pos ha).trans (by linarith)
  have hlog2 : -Real.log a ≤ a⁻¹ := by
    rw [← Real.log_inv]; exact (Real.log_le_sub_one_of_pos (inv_pos.2 ha)).trans (by linarith)
  have hra : r * a⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one ha]; exact har
  have hlog : |r * Real.log a| ≤ K * (2 * K + 1) + 1 := by
    rw [abs_mul, abs_of_nonneg hr]
    have : |Real.log a| ≤ a + a⁻¹ := by
      rw [abs_le]; constructor <;> nlinarith [inv_pos.2 ha]
    calc r * |Real.log a| ≤ r * (a + a⁻¹) := mul_le_mul_of_nonneg_left this hr
      _ = r * a + r * a⁻¹ := by ring
      _ ≤ K * (2 * K + 1) + 1 := by
          have : r * a ≤ K * (2 * K + 1) := mul_le_mul hrK haK ha.le hK
          linarith
  refine (abs_sub _ _).trans (add_le_add hlog ?_)
  rw [abs_of_nonneg hs0]; linarith

end SharpLSI
