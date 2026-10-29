import LeanResearch.PeriodicAttractiveLogGas.PositiveLogPoleMoments
import LeanResearch.PeriodicAttractiveLogGas.ResidualDoubleCentering

/-! The analytic near-residual step in source lines 2568–2578. Geometric
chart domination is explicit. The exact R+1 cell lifts and their mesh threshold
are separate obligations; no factorial moment of the kernel is assumed. -/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal

namespace PeriodicAttractiveLogGas.NearLogMomentBounds
open PositiveLogPoleMoments

def nearMomentBase (b : ℝ) : ℝ := (21 / 10 : ℝ) * (2 * b + 1)
def nearResidualScale (b : ℝ) : ℝ := (42 * Real.exp 1 / 5) * (2 * b + 1)

theorem nearMomentBase_nonneg {b : ℝ} (hb : 0 ≤ b) : 0 ≤ nearMomentBase b := by
  unfold nearMomentBase
  positivity

theorem nearResidualScale_nonneg {b : ℝ} (hb : 0 ≤ b) : 0 ≤ nearResidualScale b := by
  unfold nearResidualScale
  positivity

theorem le_nat_pow_of_one_le {a : ℝ} (ha : 1 ≤ a) {p : ℕ} (hp : 1 ≤ p) : a ≤ a ^ p := by
  have hn : 1 ≤ a ^ (p - 1) := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) ha (p - 1)
  calc
    a = a * 1 := by ring
    _ ≤ a * a ^ (p - 1) := mul_le_mul_of_nonneg_left hn (by linarith)
    _ = a ^ p := by rw [← pow_succ', Nat.sub_add_cancel hp]

theorem add_pow_le_two_pow {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (p : ℕ) :
    (u + v) ^ p ≤ (2 : ℝ) ^ p / 2 * (u ^ p + v ^ p) := by
  have h := Real.pow_arith_mean_le_arith_mean_pow (Finset.univ : Finset (Fin 2))
    (fun _ => (1 / 2 : ℝ)) ![2 * u, 2 * v] (by intro i _; norm_num)
    (by norm_num) (by intro i _; fin_cases i <;> simp <;> positivity) p
  simpa [Fin.sum_univ_two, mul_pow, mul_add, add_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- The source's scalar bookkeeping, keeping the exact 21/10 constant. -/
theorem near_moment_scalar_bound {b : ℝ} (hb : 0 ≤ b) {p : ℕ} (hp : 1 ≤ p) :
    (2 : ℝ) ^ p / 2 * (Real.pi * (p.factorial : ℝ) / 2 ^ p + b ^ p) ≤
      nearMomentBase b ^ p * (p.factorial : ℝ) := by
  have hf : (1 : ℝ) ≤ p.factorial := by exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos p)
  have hA : 1 ≤ 2 * b + 1 := by linarith
  have hAp : 1 ≤ (2 * b + 1) ^ p := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hA p
  have hbp : (2 * b) ^ p ≤ (2 * b + 1) ^ p :=
    pow_le_pow_left₀ (by positivity) (by linarith) p
  have hπ : (Real.pi + 1) / 2 ≤ (21 / 10 : ℝ) := by nlinarith [Real.pi_lt_d2]
  have hq : (Real.pi + 1) / 2 ≤ (21 / 10 : ℝ) ^ p :=
    hπ.trans (le_nat_pow_of_one_le (by norm_num) hp)
  have hF0 : (0 : ℝ) ≤ p.factorial := Nat.cast_nonneg _
  calc
    _ = Real.pi / 2 * (p.factorial : ℝ) + (2 * b) ^ p / 2 := by
      rw [mul_pow]
      field_simp
    _ ≤ Real.pi / 2 * ((2 * b + 1) ^ p * (p.factorial : ℝ)) +
        (2 * b + 1) ^ p * (p.factorial : ℝ) / 2 := by
      apply add_le_add
      · gcongr
        nlinarith
      · have hmul := mul_le_mul_of_nonneg_left hf (pow_nonneg (by linarith : 0 ≤ 2 * b + 1) p)
        linarith
    _ = (Real.pi + 1) / 2 * ((2 * b + 1) ^ p * (p.factorial : ℝ)) := by ring
    _ ≤ (21 / 10 : ℝ) ^ p * ((2 * b + 1) ^ p * (p.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_right hq (mul_nonneg (pow_nonneg (by linarith) _) hF0)
    _ = _ := by rw [nearMomentBase, mul_pow]; ring

theorem enorm_pow_eq_ofReal_abs_pow (x : ℝ) (p : ℕ) :
    ‖x‖ₑ ^ p = ENNReal.ofReal (|x| ^ p) := by
  rw [ENNReal.ofReal_pow (abs_nonneg x), ← Real.norm_eq_abs, ofReal_norm]

/-- Actual planar domination yields the full uncentered factorial moment.
The reference may be any probability dominated by planar volume. -/
theorem shifted_kernel_moment {ρ₀ : Measure PlanarSpace} [IsProbabilityMeasure ρ₀]
    (hρ₀ : ρ₀ ≤ volume) {f : PlanarSpace → ℝ} (hf : Measurable f)
    (Y : PlanarSpace) {b : ℝ} (hb : 0 ≤ b)
    (hdom : ∀ᵐ Z ∂ρ₀, |f Z| ≤ positiveLogPole Y Z + b) {p : ℕ} (hp : 1 ≤ p) :
    Integrable f ρ₀ ∧ Integrable (fun Z => |f Z| ^ p) ρ₀ ∧
    (∫ Z, |f Z| ^ p ∂ρ₀) ≤ nearMomentBase b ^ p * (p.factorial : ℝ) ∧
    (∫⁻ Z, ‖f Z‖ₑ ^ p ∂ρ₀) ≤ ENNReal.ofReal (nearMomentBase b ^ p * (p.factorial : ℝ)) := by
  have hlog := positiveLogPole_moment_le_of_measure_le hρ₀ Y hp
  have hlog₁ : Integrable (positiveLogPole Y) ρ₀ := by
    simpa only [pow_one] using (positiveLogPole_moment_le_of_measure_le hρ₀ Y (p := 1) (by omega)).1
  have hfi : Integrable f ρ₀ := (hlog₁.add (integrable_const b)).mono' hf.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs, Pi.add_apply] using hdom)
  have hm : Integrable (fun Z => (2 : ℝ) ^ p / 2 * (positiveLogPole Y Z ^ p + b ^ p)) ρ₀ :=
    (hlog.1.add (integrable_const _)).const_mul _
  have hpow : ∀ᵐ Z ∂ρ₀, |f Z| ^ p ≤
      (2 : ℝ) ^ p / 2 * (positiveLogPole Y Z ^ p + b ^ p) := by
    filter_upwards [hdom] with Z hZ
    exact (pow_le_pow_left₀ (abs_nonneg _) hZ p).trans
      (add_pow_le_two_pow (positiveLogPole_nonneg Y Z) hb p)
  have hfpm : Measurable (fun Z => |f Z| ^ p) := by
    simpa only [Real.norm_eq_abs] using hf.norm.pow_const p
  have hfpi : Integrable (fun Z => |f Z| ^ p) ρ₀ := hm.mono' hfpm.aestronglyMeasurable
    (hpow.mono fun Z hZ => by simpa only [Real.norm_eq_abs, abs_pow, abs_abs] using hZ)
  have hbound : (∫ Z, |f Z| ^ p ∂ρ₀) ≤ nearMomentBase b ^ p * (p.factorial : ℝ) := by
    calc
      _ ≤ ∫ Z, (2 : ℝ) ^ p / 2 * (positiveLogPole Y Z ^ p + b ^ p) ∂ρ₀ :=
        integral_mono_ae hfpi hm hpow
      _ = (2 : ℝ) ^ p / 2 * ((∫ Z, positiveLogPole Y Z ^ p ∂ρ₀) + b ^ p) := by
        rw [integral_const_mul, integral_add hlog.1 (integrable_const _)]
        simp
      _ ≤ (2 : ℝ) ^ p / 2 * (Real.pi * (p.factorial : ℝ) / 2 ^ p + b ^ p) := by
        gcongr
        exact hlog.2.1
      _ ≤ _ := near_moment_scalar_bound hb hp
  refine ⟨hfi, hfpi, hbound, ?_⟩
  simp_rw [enorm_pow_eq_ofReal_abs_pow]
  rw [← ofReal_integral_eq_lintegral_ofReal hfpi
    (Eventually.of_forall fun Z => pow_nonneg (abs_nonneg _) _)]
  exact ENNReal.ofReal_le_ofReal hbound

section DensityTransfer
variable {α : Type*} [MeasurableSpace α]

/-- The source density upper bound is a genuine inequality of measures. -/
theorem withDensity_le_exp_smul (ρ₀ : Measure α) (w : α → ℝ≥0∞)
    (hw : ∀ᵐ x ∂ρ₀, w x ≤ ENNReal.ofReal (Real.exp 1)) :
    ρ₀.withDensity w ≤ ENNReal.ofReal (Real.exp 1) • ρ₀ := by
  rw [← withDensity_const]
  exact withDensity_mono hw

/-- A measure-preserving square chart and a single density comparison transfer
actual logarithmic domination; there is no conditional-moment premise. -/
theorem chart_moment_of_domination (ρ₀ μ : Measure α) (φ : PlanarSpace → α)
    (hφ : MeasurePreserving φ squareLebesgue ρ₀)
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1) • ρ₀)
    {f : α → ℝ} (hf : Measurable f) (Y : PlanarSpace) {b : ℝ} (hb : 0 ≤ b)
    (hdom : ∀ᵐ Z ∂squareLebesgue, |f (φ Z)| ≤ positiveLogPole Y Z + b)
    {p : ℕ} (hp : 1 ≤ p) :
    (∫⁻ x, ‖f x‖ₑ ^ p ∂μ) ≤ ENNReal.ofReal (Real.exp 1) *
      ENNReal.ofReal (nearMomentBase b ^ p * (p.factorial : ℝ)) := by
  have hs := shifted_kernel_moment SingularRectangleMoments.squareLebesgue_le_volume
    (hf.comp hφ.measurable) Y hb hdom hp
  have hρ₀ : (∫⁻ x, ‖f x‖ₑ ^ p ∂ρ₀) ≤
      ENNReal.ofReal (nearMomentBase b ^ p * (p.factorial : ℝ)) := by
    rw [← hφ.lintegral_comp (hf.enorm.pow_const p)]
    exact hs.2.2.2
  calc
    _ ≤ ∫⁻ x, ‖f x‖ₑ ^ p ∂(ENNReal.ofReal (Real.exp 1) • ρ₀) :=
      lintegral_mono' hμ (fun _ => le_rfl)
    _ = ENNReal.ofReal (Real.exp 1) * ∫⁻ x, ‖f x‖ₑ ^ p ∂ρ₀ := by
      rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ _ := by gcongr
end DensityTransfer

/-- Absorbing the single density factor gives exactly the source 42*e/5 scale. -/
theorem centered_scale_bound {b : ℝ} (hb : 0 ≤ b) {p : ℕ} (hp : 1 ≤ p) :
    (4 : ℝ≥0∞) ^ p * (ENNReal.ofReal (Real.exp 1) *
      ENNReal.ofReal (nearMomentBase b ^ p * (p.factorial : ℝ))) ≤
        ENNReal.ofReal (nearResidualScale b ^ p * (p.factorial : ℝ)) := by
  have hB := nearMomentBase_nonneg hb
  have he1 : 1 ≤ Real.exp 1 := by
    simpa only [Real.exp_zero] using (Real.exp_le_exp.mpr (by norm_num : (0 : ℝ) ≤ 1))
  have hep := le_nat_pow_of_one_le he1 hp
  have hscale : nearResidualScale b = 4 * Real.exp 1 * nearMomentBase b := by
    unfold nearResidualScale nearMomentBase
    ring
  have hreal : (4 : ℝ) ^ p * (Real.exp 1 * (nearMomentBase b ^ p * (p.factorial : ℝ))) ≤
      nearResidualScale b ^ p * (p.factorial : ℝ) := by
    calc
      _ ≤ (4 : ℝ) ^ p * (Real.exp 1 ^ p * (nearMomentBase b ^ p * (p.factorial : ℝ))) := by
        gcongr
      _ = _ := by rw [hscale, mul_pow, mul_pow]; ring
  have h4 : ENNReal.ofReal ((4 : ℝ) ^ p) = (4 : ℝ≥0∞) ^ p := by
    rw [ENNReal.ofReal_pow (by norm_num)]
    norm_num
  calc
    _ = ENNReal.ofReal ((4 : ℝ) ^ p *
        (Real.exp 1 * (nearMomentBase b ^ p * (p.factorial : ℝ)))) := by
      conv_rhs => rw [ENNReal.ofReal_mul (show 0 ≤ (4 : ℝ) ^ p by positivity)]
      rw [h4]
      congr 1
      exact (ENNReal.ofReal_mul (Real.exp_pos 1).le).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

section ConditionalKernel
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (ρ₀ : Measure α) (σ : Measure β) (μ : Measure α) (ν : Measure β)
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
  (φ : PlanarSpace → α) (ψ : PlanarSpace → β) (K : α → β → ℝ)

/-- Complete analytic bridge from explicit geometric chart domination.
The geometric pole may depend on the retained variable; no measurable choice
of poles is needed, because each section is bounded before the AE assembly. -/
theorem near_residual_kernel_bounds
    (hφ : MeasurePreserving φ squareLebesgue ρ₀)
    (hψ : MeasurePreserving ψ squareLebesgue σ)
    (hμ : μ ≤ ENNReal.ofReal (Real.exp 1) • ρ₀)
    (hν : ν ≤ ENNReal.ofReal (Real.exp 1) • σ)
    (hK : Measurable (Function.uncurry K)) {b : ℝ} (hb : 0 ≤ b)
    (hleft : ∀ᵐ y ∂ν, ∃ Y : PlanarSpace,
      ∀ᵐ Z ∂squareLebesgue, |K (φ Z) y| ≤ positiveLogPole Y Z + b)
    (hright : ∀ᵐ x ∂μ, ∃ Y : PlanarSpace,
      ∀ᵐ Z ∂squareLebesgue, |K x (ψ Z)| ≤ positiveLogPole Y Z + b)
    {p : ℕ} (hp : 1 ≤ p) :
    Measurable (Function.uncurry (ResidualDoubleCentering.doubleCenter μ ν K)) ∧
    Integrable (Function.uncurry K) (μ.prod ν) ∧
    Integrable (Function.uncurry (ResidualDoubleCentering.doubleCenter μ ν K)) (μ.prod ν) ∧
    MemLp (Function.uncurry (ResidualDoubleCentering.doubleCenter μ ν K)) (p : ℝ≥0∞) (μ.prod ν) ∧
    (∀ᵐ y ∂ν, (∫ x, ResidualDoubleCentering.doubleCenter μ ν K x y ∂μ) = 0) ∧
    (∀ᵐ x ∂μ, (∫ y, ResidualDoubleCentering.doubleCenter μ ν K x y ∂ν) = 0) ∧
    essSup (CanonicalRowHolder.leftMoment μ (ResidualDoubleCentering.doubleCenter μ ν K) p) ν ≤
      ENNReal.ofReal (nearResidualScale b ^ p * (p.factorial : ℝ)) ∧
    essSup (CanonicalRowHolder.rightMoment ν (ResidualDoubleCentering.doubleCenter μ ν K) p) μ ≤
      ENNReal.ofReal (nearResidualScale b ^ p * (p.factorial : ℝ)) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp 1) *
    ENNReal.ofReal (nearMomentBase b ^ p * (p.factorial : ℝ))
  have hC : C < ∞ := by dsimp [C]; finiteness
  have hl : ∀ᵐ y ∂ν, (∫⁻ x, ‖K x y‖ₑ ^ p ∂μ) ≤ C := by
    filter_upwards [hleft] with y hy
    obtain ⟨Y, hY⟩ := hy
    exact chart_moment_of_domination ρ₀ μ φ hφ hμ
      (hK.comp (measurable_id.prodMk measurable_const)) Y hb hY hp
  have hr : ∀ᵐ x ∂μ, (∫⁻ y, ‖K x y‖ₑ ^ p ∂ν) ≤ C := by
    filter_upwards [hright] with x hx
    obtain ⟨Y, hY⟩ := hx
    exact chart_moment_of_domination σ ν ψ hψ hν
      (hK.comp (measurable_const.prodMk measurable_id)) Y hb hY hp
  obtain ⟨hm, hi, hri, hzl, hzr⟩ :=
    ResidualDoubleCentering.doubleCenter_properties_of_conditional_moments μ ν K hK hp hC hl hr
  obtain ⟨hmem, hml, hmr⟩ :=
    ResidualDoubleCentering.memLp_and_essSup_moments_doubleCenter μ ν K hK hp hC hl hr
  exact ⟨hm, hi, hri, hmem, hzl.mono (fun _ h => h.1), hzr.mono (fun _ h => h.1),
    hml.trans (centered_scale_bound hb hp), hmr.trans (centered_scale_bound hb hp)⟩
end ConditionalKernel

end PeriodicAttractiveLogGas.NearLogMomentBounds
