import SharpSymmetricLSI.Infra.HeatTorus5

/-!
# Appendix A, (A.1): product rule for `ρ = (√ρ)²`

If `s ∈ H¹` (weak gradient `g`, both in `L²`), then `s²` has weak gradient `2 s g`. Proof:
the smooth bounded-slope approximations `G_M(r) = M² r² / (M² + r²)` of `r²`, the chain rule
`isWeakGrad_comp`, and closedness of weak gradients under `L¹` convergence.
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff ENNReal

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem appA_isWeakGrad_weakGrad {u : UnitAddTorus ι → ℝ} (h : HasWeakGrad u) :
    IsWeakGrad u (weakGrad u) := by
  have : weakGrad u = h.choose := by simp [weakGrad, h]
  rw [this]; exact h.choose_spec

theorem appA_weakGrad_ae_eq {u : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad u g) : weakGrad u =ᵐ[volume] g :=
  weakGrad_ae_unique (appA_isWeakGrad_weakGrad ⟨g, h⟩) h

theorem appA_isWeakGrad_congr_ae {u v : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (h : IsWeakGrad u g) (huv : u =ᵐ[volume] v) : IsWeakGrad v g where
  locInt := h.locInt.congr (ae_liftT_of_ae huv)
  locInt_grad := h.locInt_grad
  ibp φ hφ hφc k := by
    rw [← h.ibp φ hφ hφc k]
    refine integral_congr_ae ?_
    filter_upwards [ae_liftT_of_ae huv] with x hx
    rw [hx]

/-! ### The approximations of `r ↦ r²` -/

/-- `G_M(r) = M² r² / (M² + r²)`. -/
noncomputable def sqApprox (M r : ℝ) : ℝ := M ^ 2 * r ^ 2 / (M ^ 2 + r ^ 2)

/-- Its derivative `2 M⁴ r / (M² + r²)²`. -/
noncomputable def sqApproxD (M r : ℝ) : ℝ := 2 * M ^ 4 * r / (M ^ 2 + r ^ 2) ^ 2

theorem hasDerivAt_sqApprox {M : ℝ} (hM : 0 < M) (r : ℝ) :
    HasDerivAt (sqApprox M) (sqApproxD M r) r := by
  have hd : M ^ 2 + r ^ 2 ≠ 0 := by positivity
  have h := ((hasDerivAt_pow 2 r).const_mul (M ^ 2)).div
    ((hasDerivAt_pow 2 r).const_add (M ^ 2)) hd
  unfold sqApprox sqApproxD
  convert h using 1
  field_simp
  ring

theorem contDiff_sqApprox {M : ℝ} (hM : 0 < M) : ContDiff ℝ 1 (sqApprox M) := by
  rw [contDiff_one_iff_deriv]
  refine ⟨fun r => (hasDerivAt_sqApprox hM r).differentiableAt, ?_⟩
  have : deriv (sqApprox M) = sqApproxD M := funext fun r => (hasDerivAt_sqApprox hM r).deriv
  rw [this]
  unfold sqApproxD
  exact Continuous.div (by fun_prop) (by fun_prop) fun r => by positivity

theorem abs_sqApproxD_le {M : ℝ} (hM : 0 < M) (r : ℝ) : |sqApproxD M r| ≤ M := by
  unfold sqApproxD
  have hd : 0 < M ^ 2 + r ^ 2 := by positivity
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (M ^ 2 + r ^ 2) ^ 2), div_le_iff₀
    (by positivity), abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * M ^ 4)]
  have h1 : 2 * M * |r| ≤ M ^ 2 + r ^ 2 := by
    nlinarith [sq_nonneg (M - |r|), sq_abs r]
  have h3 : 2 * M * |r| * M ^ 2 ≤ (M ^ 2 + r ^ 2) * (M ^ 2 + r ^ 2) :=
    mul_le_mul h1 (by nlinarith [sq_nonneg r]) (by positivity) (by positivity)
  nlinarith [h3, hM]

theorem abs_sqApproxD_le' {M : ℝ} (hM : 0 < M) (r : ℝ) : |sqApproxD M r| ≤ 2 * |r| := by
  unfold sqApproxD
  have hd : 0 < M ^ 2 + r ^ 2 := by positivity
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < (M ^ 2 + r ^ 2) ^ 2), div_le_iff₀
    (by positivity), abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * M ^ 4)]
  have : M ^ 4 ≤ (M ^ 2 + r ^ 2) ^ 2 := by nlinarith [sq_nonneg r, sq_nonneg M]
  nlinarith [abs_nonneg r]

theorem sqApprox_nonneg (M r : ℝ) : 0 ≤ sqApprox M r := by
  unfold sqApprox
  rcases eq_or_ne (M ^ 2 + r ^ 2) 0 with h | h
  · rw [h, div_zero]
  · positivity

theorem sqApprox_le (M r : ℝ) : sqApprox M r ≤ r ^ 2 := by
  unfold sqApprox
  rcases eq_or_ne (M ^ 2 + r ^ 2) 0 with h | h
  · rw [h, div_zero]; positivity
  · have hd : 0 < M ^ 2 + r ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
    rw [div_le_iff₀ hd]
    nlinarith [sq_nonneg r, sq_nonneg M, sq_nonneg (r ^ 2)]

theorem tendsto_sqApprox (r : ℝ) :
    Tendsto (fun n : ℕ => sqApprox ((n : ℝ) + 1) r) atTop (𝓝 (r ^ 2)) := by
  have h : ∀ n : ℕ, sqApprox ((n : ℝ) + 1) r = r ^ 2 / (1 + r ^ 2 / ((n : ℝ) + 1) ^ 2) := by
    intro n
    unfold sqApprox
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    field_simp
  simp_rw [h]
  have h2 : Tendsto (fun n : ℕ => r ^ 2 / ((n : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    exact this.const_div_atTop _
  have := (tendsto_const_nhds (x := r ^ 2)).div (h2.const_add 1) (by norm_num)
  rw [add_zero, div_one] at this
  exact this

theorem tendsto_sqApproxD (r : ℝ) :
    Tendsto (fun n : ℕ => sqApproxD ((n : ℝ) + 1) r) atTop (𝓝 (2 * r)) := by
  have h : ∀ n : ℕ, sqApproxD ((n : ℝ) + 1) r = 2 * r / (1 + r ^ 2 / ((n : ℝ) + 1) ^ 2) ^ 2 := by
    intro n
    unfold sqApproxD
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    field_simp
  simp_rw [h]
  have h2 : Tendsto (fun n : ℕ => r ^ 2 / ((n : ℝ) + 1) ^ 2) atTop (𝓝 0) := by
    have : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ 2) atTop atTop :=
      (tendsto_pow_atTop two_ne_zero).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    exact this.const_div_atTop _
  have := (tendsto_const_nhds (x := 2 * r)).div ((h2.const_add 1).pow 2) (by norm_num)
  rw [add_zero, one_pow, div_one] at this
  exact this

theorem continuous_sqApproxD {M : ℝ} (hM : 0 < M) : Continuous (sqApproxD M) := by
  unfold sqApproxD
  exact Continuous.div (by fun_prop) (by fun_prop) fun r => by positivity

/-! ### The product rule -/

/-- **`∇(s²) = 2 s ∇s`** for `s ∈ H¹`. -/
theorem isWeakGrad_sq {s : UnitAddTorus ι → ℝ} {g : UnitAddTorus ι → ι → ℝ}
    (hsg : IsWeakGrad s g) (hs : MemLp s 2 volume) (hg : ∀ k, MemLp (fun y => g y k) 2 volume) :
    IsWeakGrad (fun y => s y ^ 2) (fun y k => 2 * s y * g y k) := by
  have hs1 : Integrable s := hs.integrable one_le_two
  have hg1 : ∀ k, Integrable (fun y => g y k) := fun k => (hg k).integrable one_le_two
  have hs2 : Integrable fun y => s y ^ 2 := hs.integrable_sq
  have hsgk : ∀ k, Integrable fun y => s y * g y k := fun k => hs.integrable_mul (hg k)
  set M : ℕ → ℝ := fun n => (n : ℝ) + 1
  have hM : ∀ n, 0 < M n := fun n => by positivity
  have hcomp := fun n => isWeakGrad_comp hsg hs1 hg1 (contDiff_sqApprox (hM n))
    (L := M n) fun r => by rw [(hasDerivAt_sqApprox (hM n) r).deriv]; exact abs_sqApproxD_le (hM n) r
  simp_rw [fun n r => (hasDerivAt_sqApprox (hM n) r).deriv] at hcomp
  refine isWeakGrad_of_tendsto hcomp (fun n => ?_) (fun n k => ?_) hs2
    (fun k => (hsgk k).const_mul 2 |>.congr (Eventually.of_forall fun y => by ring)) ?_
    (fun k => ?_)
  · refine hs2.mono' ((contDiff_sqApprox (hM n)).continuous.comp_aestronglyMeasurable
      hs1.aestronglyMeasurable) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sqApprox_nonneg _ _)]
    exact sqApprox_le _ _
  · refine ((hsgk k).norm.const_mul 2).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact ((continuous_sqApproxD (hM n)).comp_aestronglyMeasurable
        hs1.aestronglyMeasurable).mul (hg1 k).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have := abs_sqApproxD_le' (hM n) (s y)
      nlinarith [abs_nonneg (g y k)]
  · -- `L¹` convergence of `G_M(s)` to `s²`
    have h := tendsto_lintegral_norm_of_dominated_convergence (μ := volume)
      (F := fun n y => sqApprox (M n) (s y)) (f := fun y => s y ^ 2) (bound := fun y => s y ^ 2)
      (fun n => (contDiff_sqApprox (hM n)).continuous.comp_aestronglyMeasurable
        hs1.aestronglyMeasurable) hs2.2
      (fun n => Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sqApprox_nonneg _ _)]; exact sqApprox_le _ _)
      (Eventually.of_forall fun y => tendsto_sqApprox (s y))
    simpa only [ofReal_norm] using h
  · have h := tendsto_lintegral_norm_of_dominated_convergence (μ := volume)
      (F := fun n y => sqApproxD (M n) (s y) * g y k) (f := fun y => 2 * s y * g y k)
      (bound := fun y => 2 * ‖s y * g y k‖)
      (fun n => ((continuous_sqApproxD (hM n)).comp_aestronglyMeasurable
        hs1.aestronglyMeasurable).mul (hg1 k).aestronglyMeasurable)
      (((hsgk k).norm.const_mul 2).2)
      (fun n => Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        have := abs_sqApproxD_le' (hM n) (s y)
        nlinarith [abs_nonneg (g y k)])
      (Eventually.of_forall fun y => by
        have := (tendsto_sqApproxD (s y)).mul_const (g y k)
        simpa only [M] using this)
    simpa only [ofReal_norm] using h

end SharpLSI
