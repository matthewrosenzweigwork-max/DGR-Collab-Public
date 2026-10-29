import SharpSymmetricLSI.Paper.Rothaus
open MeasureTheory Filter Topology
namespace SharpLSI.FL.Prop82
open SharpLSI

/-- Derivative of `s ↦ s² log s²` (with the convention `log 0 = 0`). -/
theorem hasDerivAt_sq_mul_log_sq (r : ℝ) :
    HasDerivAt (fun s : ℝ => s ^ 2 * Real.log (s ^ 2)) (2 * r * (Real.log (r ^ 2) + 1)) r := by
  by_cases hr : r = 0
  · subst hr
    rw [hasDerivAt_iff_tendsto_slope_zero]
    have hc : Continuous fun t : ℝ => |2 * (|t| * Real.log |t|)| :=
      (continuous_abs.comp (continuous_const.mul
        (Real.continuous_mul_log.comp continuous_abs)))
    have h0 : Tendsto (fun t : ℝ => |2 * (|t| * Real.log |t|)|) (𝓝 0) (𝓝 0) := by
      have := hc.tendsto 0
      simpa using this
    have h1 : Tendsto (fun t : ℝ => |2 * (|t| * Real.log |t|)|) (𝓝[≠] 0) (𝓝 0) :=
      h0.mono_left nhdsWithin_le_nhds
    have h2 := squeeze_zero_norm (f := fun t : ℝ => t⁻¹ • (((0 + t) ^ 2 * Real.log ((0 + t) ^ 2)) -
        (0 ^ 2 * Real.log (0 ^ 2)))) (a := fun t : ℝ => |2 * (|t| * Real.log |t|)|) ?_ h1
    · simpa using h2
    · intro t
      by_cases ht : t = 0
      · subst ht; simp
      · have hl : Real.log (t ^ 2) = 2 * Real.log |t| := by
          rw [← sq_abs, Real.log_pow]; norm_num
        have : t⁻¹ • (((0 + t) ^ 2 * Real.log ((0 + t) ^ 2)) - (0 ^ 2 * Real.log (0 ^ 2))) =
            t * Real.log (t ^ 2) := by
          simp only [smul_eq_mul, zero_add]
          field_simp
          simp
        rw [this, Real.norm_eq_abs, hl]
        apply le_of_eq
        simp only [abs_mul, abs_abs]
        ring
  · have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have h2 : HasDerivAt (fun s : ℝ => Real.log (s ^ 2)) (2 * r / r ^ 2) r :=
      h1.log hr2
    have h3 := h1.mul h2
    convert h3 using 1
    field_simp

/-- A bound on `|w log w²|` for `|w| ≤ W`. -/
theorem abs_mul_log_sq_le {w W : ℝ} (hw : |w| ≤ W) (hW : 1 ≤ W) :
    |w * Real.log (w ^ 2)| ≤ 2 + W ^ 2 * Real.log (W ^ 2) := by
  have hM2 : 0 ≤ W ^ 2 * Real.log (W ^ 2) :=
    mul_nonneg (sq_nonneg _) (Real.log_nonneg (by nlinarith))
  rcases le_or_gt |w| 1 with h | h
  · rcases (abs_nonneg w).eq_or_lt with h0 | h0
    · have : w = 0 := abs_eq_zero.mp h0.symm
      subst this; rw [zero_mul, abs_zero]; linarith
    · have hl : Real.log (w ^ 2) = 2 * Real.log |w| := by
        rw [← sq_abs, Real.log_pow]; norm_num
      have := Real.abs_log_mul_self_lt |w| h0 h
      rw [hl, abs_mul, abs_mul, abs_two]
      rw [abs_mul, abs_abs, mul_comm] at this
      nlinarith
  · have h1 := abs_sq_log_sq_le (abs_nonneg w) hw hW
    rw [sq_abs] at h1
    have h2 : |w * Real.log (w ^ 2)| ≤ |w ^ 2 * Real.log (w ^ 2)| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg w), ← sq_abs]
      have : |w| ≤ |w| ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right this (abs_nonneg _)
    linarith

/-- Differentiation under the integral of `(u + tφ)² log (u + tφ)²`. -/
theorem hasDerivAt_integral_sq_log_sq {u φ : Torus 1 → ℝ} (hu : Measurable u) (hφ : Measurable φ)
    {K L : ℝ} (hK : ∀ x, |u x| ≤ K) (hL : ∀ x, |φ x| ≤ L) (t0 : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x, (u x + t * φ x) ^ 2 * Real.log ((u x + t * φ x) ^ 2) ∂haar 1)
      (∫ x, 2 * (u x + t0 * φ x) * φ x * (Real.log ((u x + t0 * φ x) ^ 2) + 1) ∂haar 1) t0 := by
  have : IsProbabilityMeasure (haar 1) := haar_isProbabilityMeasure 1
  have hL0 : 0 ≤ L := (abs_nonneg _).trans (hL (0 : Torus 1))
  set W : ℝ := max 1 (K + (|t0| + 1) * L) with hWdef
  have hW1 : 1 ≤ W := le_max_left _ _
  have hbd : ∀ t ∈ Set.Icc (t0 - 1) (t0 + 1), ∀ x, |u x + t * φ x| ≤ W := by
    intro t ht x
    have ht' : |t| ≤ |t0| + 1 := by
      rw [abs_le]; constructor <;> cases abs_cases t0 <;> linarith [ht.1, ht.2]
    calc |u x + t * φ x| ≤ |u x| + |t| * |φ x| := by rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ K + (|t0| + 1) * L :=
        add_le_add (hK x) (mul_le_mul ht' (hL x) (abs_nonneg _) (by positivity))
      _ ≤ W := le_max_right _ _
  refine hasDerivAt_integral_bdd (P := haar 1)
    (F := fun t x => (u x + t * φ x) ^ 2 * Real.log ((u x + t * φ x) ^ 2))
    (F' := fun t x => 2 * (u x + t * φ x) * φ x * (Real.log ((u x + t * φ x) ^ 2) + 1))
    (s := Set.Icc (t0 - 1) (t0 + 1)) (Icc_mem_nhds (by linarith) (by linarith))
    ?_ ?_ (L0 := 1 + W ^ 2 * Real.log (W ^ 2)) (L1 := 2 * L * ((2 + W ^ 2 * Real.log (W ^ 2)) + W))
    ?_ ?_ ?_
  · intro t
    have hm : Measurable fun x => u x + t * φ x := hu.add (measurable_const.mul hφ)
    exact (hm.pow_const 2).mul (Real.measurable_log.comp (hm.pow_const 2))
  · intro t
    have hm : Measurable fun x => u x + t * φ x := hu.add (measurable_const.mul hφ)
    exact (((measurable_const.mul hm).mul hφ)).mul
      ((Real.measurable_log.comp (hm.pow_const 2)).add measurable_const)
  · intro t ht x
    have := abs_sq_log_sq_le (abs_nonneg (u x + t * φ x)) (hbd t ht x) hW1
    rwa [sq_abs] at this
  · intro t ht x
    have hb := hbd t ht x
    have h1 := abs_mul_log_sq_le hb hW1
    have hlog : |(u x + t * φ x) * Real.log ((u x + t * φ x) ^ 2)| ≤ 2 + W ^ 2 * Real.log (W ^ 2) := h1
    have : 2 * (u x + t * φ x) * φ x * (Real.log ((u x + t * φ x) ^ 2) + 1) =
        2 * φ x * ((u x + t * φ x) * Real.log ((u x + t * φ x) ^ 2) + (u x + t * φ x)) := by ring
    rw [this, abs_mul, abs_mul, abs_two]
    have h3 : |(u x + t * φ x) * Real.log ((u x + t * φ x) ^ 2) + (u x + t * φ x)| ≤
        (2 + W ^ 2 * Real.log (W ^ 2)) + W :=
      (abs_add_le _ _).trans (add_le_add hlog hb)
    have hnn : 0 ≤ |(u x + t * φ x) * Real.log ((u x + t * φ x) ^ 2) + (u x + t * φ x)| :=
      abs_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hL x) (by norm_num)) h3 hnn (by positivity)
  · intro x t ht
    have h := hasDerivAt_sq_mul_log_sq (u x + t * φ x)
    have hl : HasDerivAt (fun s : ℝ => u x + s * φ x) (φ x) t := by
      simpa using ((hasDerivAt_id t).mul_const (φ x)).const_add (u x)
    refine (h.comp t hl).congr_deriv ?_
    ring

end SharpLSI.FL.Prop82
