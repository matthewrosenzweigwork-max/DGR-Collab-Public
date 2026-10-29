import SharpSymmetricLSI.Paper.GaussForm8

/-!
# R32 (C1): closability of (8.1) on cylinder functions

`gaussForm λ' γ c.eval = c.form λ' γ` (`gaussForm_eval_eq_of_rowVariables`), given the
positivity of the blocks of `C`, `C = (I+T)⁻¹`, row variables `Y_i ≈ (Tz)_i` and `λ' ≥ 0`:
`≤` by the constant sequence; `≥` since `ℰ(u_n) ≥ 2∫u_n(-Lc) - ℰ(c) → ℰ(c)`.
-/

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open scoped ContDiff ENNReal InnerProductSpace

namespace SharpLSI

variable {γ : Measure (ℕ → ℝ)} {C : ℕ → ℕ → ℝ} {T : ℕ → ℕ → ℝ}

theorem abs_integral_mul_le_L2 {f g : (ℕ → ℝ) → ℝ} (hf : MemLp f 2 γ) (hg : MemLp g 2 γ) :
    |∫ z, f z * g z ∂γ| ≤ (eLpNorm f 2 γ).toReal * (eLpNorm g 2 γ).toReal := by
  have e : ⟪hf.toLp f, hg.toLp g⟫_ℝ = ∫ z, f z * g z ∂γ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with z h1 h2
    rw [h1, h2]; simp [mul_comm]
  rw [← e, ← Real.norm_eq_abs]
  refine (norm_inner_le_norm _ _).trans (le_of_eq ?_)
  rw [Lp.norm_toLp, Lp.norm_toLp]

theorem gaussForm_eval_le (lam' : ℕ → ℝ) (c : Cyl) : gaussForm lam' γ c.eval ≤ c.form lam' γ := by
  unfold gaussForm
  refine (iInf₂_le (fun _ => c) ?_).trans ?_
  · simp
  · simp

theorem Cyl.memLp_eval [IsProbabilityMeasure γ] (c : Cyl) : MemLp c.eval 2 γ := by
  obtain ⟨B, hB⟩ := c.exists_eval_bound
  exact memLp_of_bdd c.measurable_eval hB

/-- **Closability**: `ℰ(c) ≤ ℰ_∞(c)`. -/
theorem form_le_gaussForm (hγ : IsCenteredGaussianCov γ C) (hPSD : ∀ N, (blockMat C N).PosSemidef)
    (hC : IsInverseOfIPlus T C) {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i))
    {lam' : ℕ → ℝ} (hlam : ∀ i, 0 ≤ lam' i) (c : Cyl) :
    c.form lam' γ ≤ gaussForm lam' γ c.eval := by
  haveI := hγ.1
  unfold gaussForm
  refine le_iInf₂ fun u hu => ?_
  set G : (ℕ → ℝ) → ℝ := fun z => -(c.gen lam' Y z)
  have hG : MemLp G 2 γ := (memLp_gen hγ hY lam' c).neg
  set a : ℕ → ℝ := fun n => ∫ z, (u n).eval z * G z ∂γ
  -- `a_n → ℰ(c)`
  have ha : Tendsto a atTop (𝓝 (c.formR lam' γ)) := by
    rw [← cyl_ibp_self hγ hPSD hC hY lam' c]
    have hd : ∀ n, |a n - ∫ z, c.eval z * G z ∂γ| ≤
        (eLpNorm (fun z => (u n).eval z - c.eval z) 2 γ).toReal * (eLpNorm G 2 γ).toReal := fun n => by
      have hm : MemLp (fun z => (u n).eval z - c.eval z) 2 γ := (u n).memLp_eval.sub c.memLp_eval
      have e : a n - ∫ z, c.eval z * G z ∂γ = ∫ z, ((u n).eval z - c.eval z) * G z ∂γ := by
        simp only [a]
        rw [← integral_sub (f := fun z => (u n).eval z * G z) (g := fun z => c.eval z * G z)
          ((u n).memLp_eval.integrable_mul hG) (c.memLp_eval.integrable_mul hG)]
        congr 1; funext z; ring
      rw [e]
      exact abs_integral_mul_le_L2 hm hG
    have h0 : Tendsto (fun n => (eLpNorm (fun z => (u n).eval z - c.eval z) 2 γ).toReal *
        (eLpNorm G 2 γ).toReal) atTop (𝓝 0) := by
      have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hu).mul_const (eLpNorm G 2 γ).toReal
      simpa using this
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => by rw [Real.norm_eq_abs]; exact hd n) h0
  -- `ℰ(u_n) ≥ 2a_n - ℰ(c)`
  have hb : Tendsto (fun n => ENNReal.ofReal (2 * a n - c.formR lam' γ)) atTop
      (𝓝 (ENNReal.ofReal (c.formR lam' γ))) := by
    refine ENNReal.tendsto_ofReal ?_
    have := (ha.const_mul 2).sub_const (c.formR lam' γ)
    convert this using 2; ring
  rw [c.form_eq_ofReal hlam, ← hb.liminf_eq]
  refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
  rw [(u n).form_eq_ofReal hlam]
  refine ENNReal.ofReal_le_ofReal ?_
  have := two_mul_le_formR hγ hPSD hC hY hlam (u n) c
  simp only [a, G]
  linarith

/-- **`ℰ_∞ = ℰ` on cylinders**, given the positivity hypotheses and the row variables. -/
theorem gaussForm_eval_eq_of_rowVariables (hγ : IsCenteredGaussianCov γ C)
    (hPSD : ∀ N, (blockMat C N).PosSemidef) (hC : IsInverseOfIPlus T C)
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable T γ i (Y i)) {lam' : ℕ → ℝ}
    (hlam : ∀ i, 0 ≤ lam' i) (c : Cyl) : gaussForm lam' γ c.eval = c.form lam' γ :=
  le_antisymm (gaussForm_eval_le lam' c) (form_le_gaussForm hγ hPSD hC hY hlam c)

end SharpLSI
