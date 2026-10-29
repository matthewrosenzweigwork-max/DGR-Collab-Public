import SharpSymmetricLSI.Paper.AppAEnt6

/-!
# The entropy (7): the approximants `σ_δ(r) = (r² + δ²)^{1/4}` of `√r`

`σ_δ ∈ C¹` with `σ_δ'(r) = r / (2 s √s)`, `s = √(r² + δ²)`, `|σ_δ'| ≤ 1/(2√δ)`; for `r ≥ 0`,
`σ_δ(r) → √r`, `σ_δ'(r) → 1/(2√r)` (`r > 0`), `σ_δ'(0) = 0`, `|σ_δ'(r)| ≤ 1/(2√r)`.
-/

open Real Filter Topology Set

namespace SharpLSI

noncomputable def sig (δ r : ℝ) : ℝ := Real.sqrt (Real.sqrt (r ^ 2 + δ ^ 2))
noncomputable def sigp (δ r : ℝ) : ℝ :=
  r / (2 * Real.sqrt (r ^ 2 + δ ^ 2) * Real.sqrt (Real.sqrt (r ^ 2 + δ ^ 2)))

theorem hasDerivAt_sig {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : HasDerivAt (sig δ) (sigp δ r) r := by
  have hs := sqrt_sq_add_pos hδ r
  have h1 := ((hasDerivAt_pow 2 r).add_const (δ ^ 2)).sqrt (by positivity)
  have h2 := h1.sqrt hs.ne'
  unfold sig sigp
  convert h2 using 1
  have hss := Real.sqrt_pos.2 hs
  field_simp
  push_cast; ring

theorem contDiff_sig {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ 1 (sig δ) := by
  unfold sig
  have h1 : ContDiff ℝ 1 fun r : ℝ => Real.sqrt (r ^ 2 + δ ^ 2) :=
    (contDiff_id.pow 2 |>.add contDiff_const).sqrt fun r => by positivity
  exact h1.sqrt fun r => (sqrt_sq_add_pos hδ r).ne'

theorem deriv_sig {δ : ℝ} (hδ : 0 < δ) : deriv (sig δ) = sigp δ :=
  funext fun r => (hasDerivAt_sig hδ r).deriv

theorem abs_sigp_le {δ : ℝ} (hδ : 0 < δ) (r : ℝ) : |sigp δ r| ≤ 1 / (2 * Real.sqrt δ) := by
  unfold sigp
  set s := Real.sqrt (r ^ 2 + δ ^ 2)
  have hs : δ ≤ s := Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg r])
  have hs0 : 0 < s := hδ.trans_le hs
  have hrs : |r| ≤ s := (abs_lt_sqrt_sq_add hδ r).le
  have hss : Real.sqrt δ ≤ Real.sqrt s := Real.sqrt_le_sqrt hs
  have hδs : 0 < Real.sqrt δ := Real.sqrt_pos.2 hδ
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * s * Real.sqrt s), div_le_div_iff₀ (by positivity) (by positivity)]
  calc |r| * (2 * Real.sqrt δ) ≤ s * (2 * Real.sqrt s) :=
        mul_le_mul hrs (by linarith) (by positivity) hs0.le
    _ = 1 * (2 * s * Real.sqrt s) := by ring

theorem sigp_zero (δ : ℝ) : sigp δ 0 = 0 := by simp [sigp]

theorem abs_sigp_le_of_pos {δ : ℝ} (hδ : 0 < δ) {r : ℝ} (hr : 0 < r) :
    |sigp δ r| ≤ 1 / (2 * Real.sqrt r) := by
  unfold sigp
  set s := Real.sqrt (r ^ 2 + δ ^ 2)
  have hrs : r ≤ s := by have := abs_lt_sqrt_sq_add hδ r; rw [abs_of_pos hr] at this; exact this.le
  have hss : Real.sqrt r ≤ Real.sqrt s := Real.sqrt_le_sqrt hrs
  have hr2 : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  rw [abs_div, abs_of_pos hr, abs_of_pos (by positivity : 0 < 2 * s * Real.sqrt s),
    div_le_div_iff₀ (by positivity) (by positivity)]
  calc r * (2 * Real.sqrt r) ≤ s * (2 * Real.sqrt s) :=
        mul_le_mul hrs (by linarith) (by positivity) (hr.le.trans hrs)
    _ = 1 * (2 * s * Real.sqrt s) := by ring

theorem tendsto_sig {r : ℝ} (hr : 0 ≤ r) : Tendsto (fun δ => sig δ r) (𝓝[>] 0) (𝓝 (Real.sqrt r)) := by
  have hc : Continuous fun δ : ℝ => sig δ r := by unfold sig; fun_prop
  have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  convert this using 2
  simp [sig, Real.sqrt_sq hr]

theorem tendsto_sigp {r : ℝ} (hr : 0 < r) :
    Tendsto (fun δ => sigp δ r) (𝓝[>] 0) (𝓝 (1 / (2 * Real.sqrt r))) := by
  have h0 : 2 * Real.sqrt (r ^ 2 + (0 : ℝ) ^ 2) * Real.sqrt (Real.sqrt (r ^ 2 + (0 : ℝ) ^ 2)) ≠ 0 := by
    simp only [zero_pow two_ne_zero, add_zero, Real.sqrt_sq hr.le]
    have := Real.sqrt_pos.2 hr; positivity
  have hc : ContinuousAt (fun δ : ℝ => sigp δ r) 0 := by
    unfold sigp
    exact continuousAt_const.div (by fun_prop) h0
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  convert this using 2
  simp only [sigp, zero_pow two_ne_zero, add_zero, Real.sqrt_sq hr.le]
  have := Real.sqrt_pos.2 hr
  field_simp

theorem abs_sig_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) {r K : ℝ} (hr : |r| ≤ K) :
    |sig δ r| ≤ Real.sqrt (Real.sqrt (K ^ 2 + 1)) := by
  unfold sig
  rw [abs_of_nonneg (Real.sqrt_nonneg _)]
  refine Real.sqrt_le_sqrt (Real.sqrt_le_sqrt ?_)
  have : r ^ 2 ≤ K ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hr 2
  nlinarith

end SharpLSI
