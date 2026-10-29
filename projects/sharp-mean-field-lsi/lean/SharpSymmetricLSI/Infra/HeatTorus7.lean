import SharpSymmetricLSI.Infra.HeatTorus6

/-!
# The periodic heat kernel on `𝕋^ι` (I4, part 7): continuity of `∇·e^{sΔ}F` in `(s, F)`

For `s ∈ [a, b] ⊂ (0, ∞)`, `|∂ₖG_s| ≤ c_{a,b} |∂ₖG_b|`. Dominated convergence then gives
`∇·e^{sₙΔ}Fₙ (x) → ∇·e^{sΔ}F (x)` when `sₙ → s > 0` and `Fₙ → F` boundedly almost everywhere
(`tendsto_divHeatT`).
-/

open MeasureTheory Set Filter Topology
open scoped Real ContDiff ENNReal

namespace SharpLSI

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The domination constant. -/
noncomputable def domConst (ι : Type*) [Fintype ι] (a b : ℝ) : ℝ :=
  (4 * π * a) ^ (-(Fintype.card ι : ℝ) / 2) / (4 * π * b) ^ (-(Fintype.card ι : ℝ) / 2) * (b / a)

theorem abs_fderiv_heatKernel_le {a s b : ℝ} (ha : 0 < a) (has : a ≤ s) (hsb : s ≤ b)
    (y : ι → ℝ) (k : ι) :
    |fderiv ℝ (heatKernel s) y (Pi.single k 1)| ≤
      domConst ι a b * |fderiv ℝ (heatKernel b) y (Pi.single k 1)| := by
  have hs : 0 < s := ha.trans_le has
  have hb : 0 < b := hs.trans_le hsb
  rw [fderiv_heatKernel_single hs, fderiv_heatKernel_single hb, abs_neg, abs_neg]
  unfold heatKernel domConst
  set n : ℝ := (Fintype.card ι : ℝ)
  set S := ∑ j, y j ^ 2 with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have h1 : (4 * π * s) ^ (-n / 2) ≤ (4 * π * a) ^ (-n / 2) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith [Real.pi_pos])
      (by have : 0 ≤ n := Nat.cast_nonneg _; linarith)
  have h2 : Real.exp (-S / (4 * s)) ≤ Real.exp (-S / (4 * b)) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hS0 (by positivity) (by linarith)
  have hpb : 0 < (4 * π * b) ^ (-n / 2) := by positivity
  have hps : 0 < (4 * π * s) ^ (-n / 2) := by positivity
  simp only [abs_div, abs_mul, abs_of_pos hpb, abs_of_pos hps, abs_of_pos (Real.exp_pos _),
    abs_of_pos hs, abs_of_pos hb, abs_two]
  calc (4 * π * s) ^ (-n / 2) * Real.exp (-S / (4 * s)) * |y k| / (2 * s)
      ≤ (4 * π * a) ^ (-n / 2) * Real.exp (-S / (4 * b)) * |y k| / (2 * a) := by
        have hya := abs_nonneg (y k)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        have : (4 * π * s) ^ (-n / 2) * Real.exp (-S / (4 * s)) ≤
            (4 * π * a) ^ (-n / 2) * Real.exp (-S / (4 * b)) :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
        have h3 : (4 * π * s) ^ (-n / 2) * Real.exp (-S / (4 * s)) * |y k| * (2 * a) ≤
            (4 * π * a) ^ (-n / 2) * Real.exp (-S / (4 * b)) * |y k| * (2 * a) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right this hya) (by positivity)
        have h4 : (4 * π * a) ^ (-n / 2) * Real.exp (-S / (4 * b)) * |y k| * (2 * a) ≤
            (4 * π * a) ^ (-n / 2) * Real.exp (-S / (4 * b)) * |y k| * (2 * s) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        linarith
    _ = _ := by field_simp

omit [DecidableEq ι] in
theorem domConst_nonneg {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : 0 ≤ domConst ι a b := by
  unfold domConst; positivity

/-- **Joint continuity of `∇·e^{sΔ}F (x)`** along `sₙ → s > 0`, `Fₙ → F` boundedly a.e. -/
theorem tendsto_divHeatT {s : ℕ → ℝ} {s₀ : ℝ} (hs₀ : 0 < s₀) (hs : Tendsto s atTop (𝓝 s₀))
    {F : ℕ → UnitAddTorus ι → ι → ℝ} {F₀ : UnitAddTorus ι → ι → ℝ} {M : ℝ}
    (hFm : ∀ᶠ n in atTop, ∀ k, AEStronglyMeasurable (fun z => F n z k) volume)
    (hFb : ∀ᶠ n in atTop, ∀ k, ∀ᵐ z, |F n z k| ≤ M)
    (hae : ∀ k, ∀ᵐ z, Tendsto (fun n => F n z k) atTop (𝓝 (F₀ z k))) (x : UnitAddTorus ι) :
    Tendsto (fun n => divHeatT (s n) (F n) x) atTop (𝓝 (divHeatT s₀ F₀ x)) := by
  unfold divHeatT
  refine tendsto_finsetSum _ fun k _ => ?_
  have hev : ∀ᶠ n in atTop, s n ∈ Icc (s₀ / 2) (2 * s₀) :=
    hs.eventually (Icc_mem_nhds (by linarith) (by linarith))
  have hq := qmp_sub_liftT (ι := ι) x
  have hpos : ∀ᶠ n in atTop, 0 < s n := hev.mono fun n hn => by linarith [hn.1]
  -- convergence of the kernel
  have hker : ∀ y : ι → ℝ, Tendsto (fun n => fderiv ℝ (heatKernel (s n)) y (Pi.single k 1))
      atTop (𝓝 (fderiv ℝ (heatKernel s₀) y (Pi.single k 1))) := by
    intro y
    rw [fderiv_heatKernel_single hs₀]
    have hc : ContinuousAt (fun r : ℝ => -(heatKernel r y * y k / (2 * r))) s₀ := by
      unfold heatKernel
      refine ContinuousAt.neg (ContinuousAt.div (ContinuousAt.mul (ContinuousAt.mul ?_ ?_)
        continuousAt_const) (by fun_prop) (mul_ne_zero (by norm_num) hs₀.ne'))
      · exact ((continuousAt_const.mul continuousAt_id).rpow_const
          (Or.inl (mul_ne_zero (by positivity) hs₀.ne')))
      · exact (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
          (mul_ne_zero (by norm_num) hs₀.ne')).rexp
    refine (hc.tendsto.comp hs).congr' ?_
    filter_upwards [hpos] with n hn
    simp only [Function.comp_apply]
    rw [fderiv_heatKernel_single hn]
  refine tendsto_integral_filter_of_dominated_convergence
    (bound := fun y => domConst ι (s₀ / 2) (2 * s₀) *
      |fderiv ℝ (heatKernel (2 * s₀)) y (Pi.single k 1)| * M) ?_ ?_ ?_ ?_
  · filter_upwards [hpos, hFm] with n hn hm
    refine AEStronglyMeasurable.mul ?_ ((hm k).comp_quasiMeasurePreserving hq)
    simp_rw [fderiv_heatKernel_single hn]
    exact (((measurable_heatKernel (s n)).mul (measurable_pi_apply k)).div_const _ |>.neg)
      |>.aestronglyMeasurable
  · filter_upwards [hev, hFb] with n hn hb
    filter_upwards [hq.ae (hb k)] with y hy
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul (abs_fderiv_heatKernel_le (by linarith) hn.1 hn.2 y k) hy (abs_nonneg _)
      (mul_nonneg (domConst_nonneg (by linarith) (by linarith)) (abs_nonneg _))
  · exact (((integrable_fderiv_heatKernel (by linarith : (0 : ℝ) < 2 * s₀) k).abs).const_mul
      _).mul_const _
  · filter_upwards [hq.ae (hae k)] with y hy
    exact (hker y).mul hy

end SharpLSI
