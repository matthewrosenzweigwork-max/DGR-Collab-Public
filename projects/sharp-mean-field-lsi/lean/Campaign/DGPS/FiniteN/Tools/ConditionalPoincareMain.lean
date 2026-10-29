import DGPS.FiniteN.Tools.ConditionalPoincare
import DGPS.FiniteN.Tools.IMS

/-!
# FIN021: conditional Poincare inequality near a nondegenerate minimum

Module `DGPS.FiniteN.Tools.ConditionalPoincareMain`.  The cutoff clause is proved from an
abstract Poincare hypothesis for `cond μ B`; the Poincare estimate itself follows the
Bobkov-Ledoux route (Prekopa-Leindler, then a second-order expansion of the Maurey product bound),
and the final theorem `DGPS.FiniteN.conditional_minimum_neighborhood_poincare` combines both.
-/

namespace DGPS.FiniteN.Tools.ConditionalPoincareMain

open MeasureTheory ProbabilityTheory Set Metric
open DGPS.FiniteN.Tools.ConditionalPoincare
open scoped ENNReal

/-- Cauchy-Schwarz on a set: `(∫ g)² ≤ μ(S) ∫ g²` for `g` vanishing off `S`. -/
lemma sq_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {S : Set α} (hS : MeasurableSet S) {g : α → ℝ} (hg : Integrable g μ)
    (hg2 : Integrable (fun x => g x ^ 2) μ) (hgS : ∀ x, x ∉ S → g x = 0) :
    (∫ x, g x ∂μ) ^ 2 ≤ (μ S).toReal * ∫ x, g x ^ 2 ∂μ := by
  have hind : Integrable (S.indicator (fun _ => (1 : ℝ))) μ :=
    (integrable_const (1 : ℝ)).indicator hS
  have key : ∀ s : ℝ, 0 ≤ (μ S).toReal * (s * s) + (-2 * ∫ x, g x ∂μ) * s + ∫ x, g x ^ 2 ∂μ := by
    intro s
    have h0 : 0 ≤ ∫ x, (g x ^ 2 - 2 * s * g x + s ^ 2 * S.indicator (fun _ => (1 : ℝ)) x) ∂μ := by
      refine integral_nonneg fun x => ?_
      simp only [Pi.zero_apply]
      by_cases hx : x ∈ S
      · simp only [indicator_of_mem hx]
        nlinarith [sq_nonneg (g x - s)]
      · simp [hgS x hx, indicator_of_notMem hx]
    have h1 : ∫ x, (g x ^ 2 - 2 * s * g x + s ^ 2 * S.indicator (fun _ => (1 : ℝ)) x) ∂μ
        = ∫ x, g x ^ 2 ∂μ - 2 * s * ∫ x, g x ∂μ + s ^ 2 * (μ S).toReal := by
      have e1 := integral_add (hg2.sub (hg.const_mul (2 * s))) (hind.const_mul (s ^ 2))
      have e2 := integral_sub hg2 (hg.const_mul (2 * s))
      rw [integral_const_mul] at e2
      rw [integral_const_mul, integral_indicator_const (1 : ℝ) hS] at e1
      simp only [Pi.sub_apply] at e1 e2
      rw [e1, e2]
      simp [measureReal_def]
    rw [h1] at h0
    nlinarith [h0]
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith [this]



/-- Variance expansion for a probability measure. -/
lemma integral_sub_mean_sq {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    {G : α → ℝ} (hG : Integrable G ν) (hG2 : Integrable (fun x => G x ^ 2) ν) :
    ∫ x, (G x - ∫ y, G y ∂ν) ^ 2 ∂ν = ∫ x, G x ^ 2 ∂ν - (∫ x, G x ∂ν) ^ 2 := by
  set m := ∫ y, G y ∂ν
  have e : ∀ x, (G x - m) ^ 2 = G x ^ 2 - 2 * m * G x + m ^ 2 := fun x => by ring
  simp_rw [e]
  have e1 := integral_add (hG2.sub (hG.const_mul (2 * m))) (integrable_const (m ^ 2) (μ := ν))
  have e2 := integral_sub hG2 (hG.const_mul (2 * m))
  rw [integral_const_mul] at e2
  simp only [Pi.sub_apply] at e1 e2
  rw [e1, e2]
  simp [m]
  ring

lemma cond_integral_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (B : Set α) (f : α → ℝ) :
    ∫ x, f x ∂(cond μ B) = ((μ B).toReal)⁻¹ * ∫ x in B, f x ∂μ := by
  show ∫ x, f x ∂((μ B)⁻¹ • μ.restrict B) = _
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]



/-- Cutoff clause, abstract form: from the conditional Poincare inequality on `B` (for the
conditional measure `cond μ B`), for a cutoff `χ` supported in `B` and `F` with `μ`-mean zero,
`E(χF) ≥ ρ ‖χF‖² - (ρ / μ(B)) μ({χ ≠ 1}) ‖F‖²`. -/
theorem cutoff_energy_lower_bound {k : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin k)))
    [IsFiniteMeasure μ] {B : Set (EuclideanSpace ℝ (Fin k))}
    (hμB : μ B ≠ 0) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hP : ∀ G : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ 1 G →
      ρ * ∫ x, (G x - ∫ y, G y ∂(cond μ B)) ^ 2 ∂(cond μ B) ≤
        ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂(cond μ B))
    (χ : EuclideanSpace ℝ (Fin k) → ℝ) (hχ : ContDiff ℝ 1 χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hχ1 : ∀ x, χ x ≤ 1) (hχB : ∀ x, x ∉ B → χ x = 0) (Cχ : ℝ)
    (hCχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ Cχ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ 1 F)
    (hF2 : Integrable (fun x => F x ^ 2) μ)
    (hFd : Integrable (fun x => ‖fderiv ℝ F x‖ ^ 2) μ) (hF0 : ∫ x, F x ∂μ = 0) :
    ρ * ∫ x, (χ x * F x) ^ 2 ∂μ -
        ρ / (μ B).toReal * (μ {x | χ x ≠ 1}).toReal * ∫ x, F x ^ 2 ∂μ ≤
      ∫ x, ‖fderiv ℝ (fun y => χ y * F y) x‖ ^ 2 ∂μ := by
  classical
  set G : EuclideanSpace ℝ (Fin k) → ℝ := fun y => χ y * F y with hGdef
  have hGc : ContDiff ℝ 1 G := hχ.mul hF
  have ha : 0 < (μ B).toReal := ENNReal.toReal_pos hμB (measure_ne_top μ B)
  set a := (μ B).toReal with ha_def
  have hFm : AEStronglyMeasurable F μ := hF.continuous.aestronglyMeasurable
  have hFi : Integrable F μ := by
    refine (hF2.add (integrable_const (1 : ℝ))).mono' hFm (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    simp only [Pi.add_apply]
    nlinarith [sq_abs (F x), abs_nonneg (F x), sq_nonneg (|F x| - 1)]
  have hGabs : ∀ x, |G x| ≤ |F x| := fun x => by
    simp only [hGdef, abs_mul]
    rw [abs_of_nonneg (hχ0 x)]
    exact mul_le_of_le_one_left (abs_nonneg _) (hχ1 x)
  have hGm : AEStronglyMeasurable G μ := hGc.continuous.aestronglyMeasurable
  have hGi : Integrable G μ := hFi.norm.mono' hGm (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact (hGabs x).trans (by rw [Real.norm_eq_abs]))
  have hG2i : Integrable (fun x => G x ^ 2) μ := by
    refine hF2.mono' (hGc.continuous.pow 2).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (sq_le_sq.mpr (by simpa using hGabs x))
  -- gradient integrability
  have hdG : ∀ x, ‖fderiv ℝ G x‖ ^ 2 ≤ 2 * ‖fderiv ℝ F x‖ ^ 2 + 2 * Cχ ^ 2 * F x ^ 2 := by
    intro x
    have h1 : fderiv ℝ G x = χ x • fderiv ℝ F x + F x • fderiv ℝ χ x := by
      simp only [hGdef]
      rw [fderiv_fun_mul (hχ.differentiable (by simp) x) (hF.differentiable (by simp) x)]
    have hn : ‖fderiv ℝ G x‖ ≤ ‖fderiv ℝ F x‖ + |F x| * Cχ := by
      rw [h1]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hχ0 x)]
        exact mul_le_of_le_one_left (norm_nonneg _) (hχ1 x)
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hCχ x) (abs_nonneg _)
    have h0 : 0 ≤ ‖fderiv ℝ G x‖ := norm_nonneg _
    have : ‖fderiv ℝ G x‖ ^ 2 ≤ (‖fderiv ℝ F x‖ + |F x| * Cχ) ^ 2 := pow_le_pow_left₀ h0 hn 2
    nlinarith [sq_nonneg (‖fderiv ℝ F x‖ - |F x| * Cχ), sq_abs (F x)]
  have hdGi : Integrable (fun x => ‖fderiv ℝ G x‖ ^ 2) μ := by
    refine ((hFd.const_mul 2).add (hF2.const_mul (2 * Cχ ^ 2))).mono'
      ((hGc.continuous_fderiv (by simp)).norm.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact (hdG x).trans (by simp only [Pi.add_apply]; linarith)
  -- restrict to B
  have hGzero : ∀ x, x ∉ B → G x = 0 := fun x hx => by simp [hGdef, hχB x hx]
  have hG2zero : ∀ x, x ∉ B → G x ^ 2 = 0 := fun x hx => by simp [hGzero x hx]
  have hI1 : ∫ x in B, G x ∂μ = ∫ x, G x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hGzero
  have hI2 : ∫ x in B, G x ^ 2 ∂μ = ∫ x, G x ^ 2 ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero hG2zero
  have hEB : ∫ x in B, ‖fderiv ℝ G x‖ ^ 2 ∂μ ≤ ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂μ :=
    setIntegral_le_integral hdGi (Filter.Eventually.of_forall fun x => by positivity)
  have hν : IsProbabilityMeasure (cond μ B) := cond_isProbabilityMeasure hμB
  have hGν : Integrable G (cond μ B) := (hGi.restrict).smul_measure (by simp [hμB])
  have hG2ν : Integrable (fun x => G x ^ 2) (cond μ B) :=
    (hG2i.restrict).smul_measure (by simp [hμB])
  have hmain := hP G hGc
  rw [integral_sub_mean_sq _ hGν hG2ν, cond_integral_eq, cond_integral_eq, cond_integral_eq,
    hI1, hI2] at hmain
  -- Cauchy-Schwarz for the mean
  set S : Set (EuclideanSpace ℝ (Fin k)) := {x | χ x ≠ 1} with hS
  have hSm : MeasurableSet S := (measurableSet_singleton (1 : ℝ)).compl.preimage hχ.continuous.measurable
    |>.congr (by ext x; simp [hS])
  have hg : ∀ x, (χ x - 1) * F x = G x - F x := fun x => by simp [hGdef]; ring
  have hgi : Integrable (fun x => (χ x - 1) * F x) μ := by
    simp_rw [hg]; exact hGi.sub hFi
  have hgm : AEStronglyMeasurable (fun x => (χ x - 1) * F x) μ :=
    ((hχ.continuous.sub continuous_const).mul hF.continuous).aestronglyMeasurable
  have hg2 : Integrable (fun x => ((χ x - 1) * F x) ^ 2) μ := by
    refine hF2.mono' (((hχ.continuous.sub continuous_const).mul hF.continuous).pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), mul_pow]
      have : (χ x - 1) ^ 2 ≤ 1 := by nlinarith [hχ0 x, hχ1 x]
      exact mul_le_of_le_one_left (sq_nonneg _) this
  have hgS : ∀ x, x ∉ S → (χ x - 1) * F x = 0 := fun x hx => by
    have : χ x = 1 := by simpa [hS] using hx
    simp [this]
  have hcs := sq_integral_le μ hSm hgi hg2 hgS
  have hI1' : ∫ x, G x ∂μ = ∫ x, (χ x - 1) * F x ∂μ := by
    simp_rw [hg]
    rw [integral_sub hGi hFi, hF0, sub_zero]
  have hgF : ∫ x, ((χ x - 1) * F x) ^ 2 ∂μ ≤ ∫ x, F x ^ 2 ∂μ := by
    refine integral_mono hg2 hF2 fun x => ?_
    show ((χ x - 1) * F x) ^ 2 ≤ F x ^ 2
    rw [mul_pow]
    have : (χ x - 1) ^ 2 ≤ 1 := by nlinarith [hχ0 x, hχ1 x]
    exact mul_le_of_le_one_left (sq_nonneg _) this
  have hmuS : 0 ≤ (μ S).toReal := ENNReal.toReal_nonneg
  have hI1sq : (∫ x, G x ∂μ) ^ 2 ≤ (μ S).toReal * ∫ x, F x ^ 2 ∂μ := by
    rw [hI1']
    exact hcs.trans (mul_le_mul_of_nonneg_left hgF hmuS)
  -- assemble
  have hfinal : ρ * (a⁻¹ * ∫ x, G x ^ 2 ∂μ - (a⁻¹ * ∫ x, G x ∂μ) ^ 2) ≤
      a⁻¹ * ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂μ := by
    refine hmain.trans ?_
    exact mul_le_mul_of_nonneg_left hEB (inv_nonneg.mpr ha.le)
  have h3 : ρ * (∫ x, G x ^ 2 ∂μ - (∫ x, G x ∂μ) ^ 2 / a) ≤ ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂μ := by
    have := mul_le_mul_of_nonneg_left hfinal ha.le
    have e : a * (ρ * (a⁻¹ * ∫ x, G x ^ 2 ∂μ - (a⁻¹ * ∫ x, G x ∂μ) ^ 2)) =
        ρ * (∫ x, G x ^ 2 ∂μ - (∫ x, G x ∂μ) ^ 2 / a) := by
      field_simp
    rw [e, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul] at this
    exact this
  have h4 : ρ / a * (μ S).toReal * ∫ x, F x ^ 2 ∂μ ≥ ρ * ((∫ x, G x ∂μ) ^ 2 / a) := by
    have : ρ * ((∫ x, G x ∂μ) ^ 2 / a) ≤ ρ * ((μ S).toReal * (∫ x, F x ^ 2 ∂μ) / a) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hI1sq ha.le) hρ
    refine le_of_le_of_eq this ?_
    ring
  have : (∫ x, G x ^ 2 ∂μ) = ∫ x, (χ x * F x) ^ 2 ∂μ := rfl
  nlinarith [h3, h4]



/-- Cutoff clause, exponential form: if the `μ`-mass outside `{χ = 1}` is at most `A e^{-c'N}` and
`μ(B) ≥ m₀ > 0`, then `E(χF) ≥ cN ‖χF‖² - (c A / m₀) N e^{-c'N} ‖F‖²`. -/
theorem cutoff_energy_lower_bound_exp {k : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin k)))
    [IsFiniteMeasure μ] {B : Set (EuclideanSpace ℝ (Fin k))}
    (hμB : μ B ≠ 0) (c N : ℝ) (hc : 0 ≤ c) (hN : 0 ≤ N)
    (hP : ∀ G : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ 1 G →
      c * N * ∫ x, (G x - ∫ y, G y ∂(cond μ B)) ^ 2 ∂(cond μ B) ≤
        ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂(cond μ B))
    (χ : EuclideanSpace ℝ (Fin k) → ℝ) (hχ : ContDiff ℝ 1 χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hχ1 : ∀ x, χ x ≤ 1) (hχB : ∀ x, x ∉ B → χ x = 0) (Cχ : ℝ)
    (hCχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ Cχ)
    (A c' m₀ : ℝ) (hm₀ : 0 < m₀) (hBm : m₀ ≤ (μ B).toReal)
    (hout : (μ {x | χ x ≠ 1}).toReal ≤ A * Real.exp (-(c' * N)))
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ 1 F)
    (hF2 : Integrable (fun x => F x ^ 2) μ)
    (hFd : Integrable (fun x => ‖fderiv ℝ F x‖ ^ 2) μ) (hF0 : ∫ x, F x ∂μ = 0) :
    c * N * ∫ x, (χ x * F x) ^ 2 ∂μ -
        c * A / m₀ * N * Real.exp (-(c' * N)) * ∫ x, F x ^ 2 ∂μ ≤
      ∫ x, ‖fderiv ℝ (fun y => χ y * F y) x‖ ^ 2 ∂μ := by
  have h := cutoff_energy_lower_bound μ hμB (c * N) (mul_nonneg hc hN) hP χ hχ hχ0 hχ1 hχB Cχ hCχ
    F hF hF2 hFd hF0
  refine le_trans (sub_le_sub_left ?_ _) h
  have hF2n : 0 ≤ ∫ x, F x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have ha : m₀ ≤ (μ B).toReal := hBm
  have hcN : 0 ≤ c * N := mul_nonneg hc hN
  have h1 : c * N / (μ B).toReal ≤ c * N / m₀ := div_le_div_of_nonneg_left hcN hm₀ ha
  have h2 : c * N / (μ B).toReal * (μ {x | χ x ≠ 1}).toReal ≤
      c * N / m₀ * (A * Real.exp (-(c' * N))) :=
    mul_le_mul h1 hout ENNReal.toReal_nonneg (by positivity)
  have h3 := mul_le_mul_of_nonneg_right h2 hF2n
  refine le_of_eq_of_le ?_ (le_of_le_of_eq h3 ?_) <;> ring_nf


lemma real_amgm_aux {I J K a b s : ℝ} (ha : 0 < a) (hb : 0 < b) (hs : 0 < s) (hs2 : s ^ 2 = a * b)
    (hI : 0 ≤ I) (hJ : 0 ≤ J)
    (h : I * a⁻¹ + J * b⁻¹ ≤ 2 * (K * s⁻¹)) : I * J ≤ K ^ 2 := by
  have hX : 0 ≤ I * a⁻¹ := by positivity
  have hY : 0 ≤ J * b⁻¹ := by positivity
  have h1 : (I * a⁻¹ + J * b⁻¹) ^ 2 ≤ (2 * (K * s⁻¹)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h 2
  have h2 : 4 * ((I * a⁻¹) * (J * b⁻¹)) ≤ (I * a⁻¹ + J * b⁻¹) ^ 2 := by
    nlinarith [sq_nonneg (I * a⁻¹ - J * b⁻¹)]
  have h3 : (I * a⁻¹) * (J * b⁻¹) = I * J * (s ^ 2)⁻¹ := by
    rw [hs2]; field_simp
  have h4 : (2 * (K * s⁻¹)) ^ 2 = 4 * K ^ 2 * (s ^ 2)⁻¹ := by
    field_simp
    ring
  rw [h3] at h2
  rw [h4] at h1
  have hpos : 0 < (s ^ 2)⁻¹ := by positivity
  have : I * J * (s ^ 2)⁻¹ ≤ K ^ 2 * (s ^ 2)⁻¹ := by nlinarith
  exact le_of_mul_le_mul_right this hpos

lemma lint_scale {f : ℝ → ℝ} (hf : Measurable f) (f0 : ∀ x, 0 ≤ f x) {c : ℝ} :
    ∫⁻ x, ENNReal.ofReal (f x / c) = (∫⁻ x, ENNReal.ofReal (f x)) * ENNReal.ofReal c⁻¹ := by
  have := lintegral_mul_const (μ := (volume : Measure ℝ)) (ENNReal.ofReal c⁻¹)
    (ENNReal.measurable_ofReal.comp hf)
  simp only [Function.comp] at this
  rw [← this]
  refine lintegral_congr fun x => ?_
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (f0 x)]

lemma pl1_real {f g h : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (f0 : ∀ x, 0 ≤ f x) (g0 : ∀ x, 0 ≤ g x) (h0 : ∀ x, 0 ≤ h x) {M : ℝ}
    (fM : ∀ x, f x ≤ M) (gM : ∀ x, g x ≤ M)
    (hyp : ∀ x y, f x * g y ≤ h ((x + y) / 2) ^ 2) :
    (∫⁻ x, ENNReal.ofReal (f x)) * (∫⁻ x, ENNReal.ofReal (g x)) ≤
      (∫⁻ x, ENNReal.ofReal (h x)) ^ 2 := by
  by_cases hK : ∫⁻ x, ENNReal.ofReal (h x) = ⊤
  · rw [hK]; simp
  have hbdf : BddAbove (range f) := ⟨M, by rintro _ ⟨x, rfl⟩; exact fM x⟩
  have hbdg : BddAbove (range g) := ⟨M, by rintro _ ⟨x, rfl⟩; exact gM x⟩
  set a := ⨆ x, f x with ha_def
  set b := ⨆ x, g x with hb_def
  have hfa : ∀ x, f x ≤ a := fun x => le_ciSup hbdf x
  have hgb : ∀ x, g x ≤ b := fun x => le_ciSup hbdg x
  by_cases ha0 : a = 0
  · have : f = fun _ => 0 := funext fun x => le_antisymm ((hfa x).trans ha0.le) (f0 x)
    rw [this]; simp
  by_cases hb0 : b = 0
  · have : g = fun _ => 0 := funext fun x => le_antisymm ((hgb x).trans hb0.le) (g0 x)
    rw [this]; simp
  have ha : 0 < a := lt_of_le_of_ne ((f0 0).trans (hfa 0)) (Ne.symm ha0)
  have hb : 0 < b := lt_of_le_of_ne ((g0 0).trans (hgb 0)) (Ne.symm hb0)
  set s := Real.sqrt (a * b) with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hs2 : s ^ 2 = a * b := Real.sq_sqrt (mul_pos ha hb).le
  have E := pl1_norm (f := fun x => f x / a) (g := fun x => g x / b) (h := fun x => h x / s)
    (hf.div_const _) (hg.div_const _) (hh.div_const _)
    (fun x => div_nonneg (f0 x) ha.le) (fun x => div_nonneg (g0 x) hb.le)
    (fun x => div_nonneg (h0 x) hs.le)
    (fun x => (div_le_one ha).mpr (hfa x)) (fun x => (div_le_one hb).mpr (hgb x))
    (fun t ht => by
      obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup (f := f) (show t * a < ⨆ x, f x by
        nlinarith)
      exact ⟨x, by rw [lt_div_iff₀ ha]; exact hx⟩)
    (fun t ht => by
      obtain ⟨x, hx⟩ := exists_lt_of_lt_ciSup (f := g) (show t * b < ⨆ x, g x by
        nlinarith)
      exact ⟨x, by rw [lt_div_iff₀ hb]; exact hx⟩)
    (fun x y => by
      calc f x / a * (g y / b) = f x * g y / s ^ 2 := by rw [hs2]; field_simp
        _ ≤ h ((x + y) / 2) ^ 2 / s ^ 2 := by gcongr; exact hyp x y
        _ = (h ((x + y) / 2) / s) ^ 2 := by rw [div_pow])
  rw [lint_scale hf f0, lint_scale hg g0, lint_scale hh h0] at E
  set I := ∫⁻ x, ENNReal.ofReal (f x)
  set J := ∫⁻ x, ENNReal.ofReal (g x)
  set K := ∫⁻ x, ENNReal.ofReal (h x)
  have hR : 2 * (K * ENNReal.ofReal s⁻¹) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.mul_ne_top hK ENNReal.ofReal_ne_top)
  have hI : I ≠ ⊤ := by
    intro hI
    have h1 : I * ENNReal.ofReal a⁻¹ ≠ ⊤ := ne_top_of_le_ne_top hR (le_trans le_self_add E)
    apply h1; rw [hI]
    exact ENNReal.top_mul (by simpa using ha)
  have hJ : J ≠ ⊤ := by
    intro hJ
    have h1 : J * ENNReal.ofReal b⁻¹ ≠ ⊤ := ne_top_of_le_ne_top hR (le_trans le_add_self E)
    apply h1; rw [hJ]
    exact ENNReal.top_mul (by simpa using hb)
  have E2 := ENNReal.toReal_mono hR E
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top hI ENNReal.ofReal_ne_top)
    (ENNReal.mul_ne_top hJ ENNReal.ofReal_ne_top), ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at E2
  simp only [ENNReal.toReal_ofNat] at E2
  have := real_amgm_aux ha hb hs hs2 ENNReal.toReal_nonneg ENNReal.toReal_nonneg
    E2
  have h5 : (I * J).toReal ≤ (K ^ 2).toReal := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_pow]; exact this
  exact (ENNReal.toReal_le_toReal (ENNReal.mul_ne_top hI hJ) (ENNReal.pow_ne_top hK)).mp h5



lemma iSup_min_nat (a : ℝ≥0∞) : ⨆ n : ℕ, min a (n : ℝ≥0∞) = a := by
  have : a ⊓ ⨆ n : ℕ, (n : ℝ≥0∞) = ⨆ n : ℕ, a ⊓ (n : ℝ≥0∞) := inf_iSup_eq _ _
  rw [ENNReal.iSup_natCast, inf_top_eq] at this
  exact this.symm

lemma lintegral_min_nat_mono (f : ℝ → ℝ≥0∞) : Monotone fun (n : ℕ) x => min (f x) (n : ℝ≥0∞) :=
  fun m n hmn x => min_le_min le_rfl (by exact_mod_cast hmn)

lemma lintegral_eq_iSup_min {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ⨆ n : ℕ, ∫⁻ x, min (f x) (n : ℝ≥0∞) := by
  rw [← lintegral_iSup (fun n => hf.min measurable_const) (lintegral_min_nat_mono f)]
  exact lintegral_congr fun x => by simp only [iSup_min_nat]

lemma sq_min_le {a M : ℝ≥0∞} (b : ℝ≥0∞) (h : b ≤ a ^ 2) (hM : b ≤ M ^ 2) : b ≤ (min a M) ^ 2 := by
  rcases le_total a M with h1 | h1
  · rw [min_eq_left h1]; exact h
  · rw [min_eq_right h1]; exact hM

lemma pl1_trunc {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hyp : ∀ x y, f x * g y ≤ h ((x + y) / 2) ^ 2) (n : ℕ) :
    (∫⁻ x, min (f x) (n : ℝ≥0∞)) * (∫⁻ x, min (g x) (n : ℝ≥0∞)) ≤ (∫⁻ x, h x) ^ 2 := by
  set fr : ℝ → ℝ := fun x => (min (f x) (n : ℝ≥0∞)).toReal with hfr
  set gr : ℝ → ℝ := fun x => (min (g x) (n : ℝ≥0∞)).toReal with hgr
  set hr : ℝ → ℝ := fun x => (min (h x) (n : ℝ≥0∞)).toReal with hhr
  have fin : ∀ (u : ℝ≥0∞), min u (n : ℝ≥0∞) ≠ ⊤ := fun u =>
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top n) (min_le_right _ _)
  have key := pl1_real (f := fr) (g := gr) (h := hr) (M := n)
    ((hf.min measurable_const).ennreal_toReal) ((hg.min measurable_const).ennreal_toReal)
    ((hh.min measurable_const).ennreal_toReal) (fun x => ENNReal.toReal_nonneg)
    (fun x => ENNReal.toReal_nonneg) (fun x => ENNReal.toReal_nonneg)
    (fun x => by
      have := ENNReal.toReal_mono (ENNReal.natCast_ne_top n) (min_le_right (f x) (n : ℝ≥0∞))
      simpa [hfr] using this)
    (fun x => by
      have := ENNReal.toReal_mono (ENNReal.natCast_ne_top n) (min_le_right (g x) (n : ℝ≥0∞))
      simpa [hgr] using this)
    (fun x y => by
      have h1 : min (f x) n * min (g y) n ≤ (min (h ((x + y) / 2)) n) ^ 2 := by
        refine sq_min_le _ ((mul_le_mul' (min_le_left _ _) (min_le_left _ _)).trans (hyp x y)) ?_
        rw [sq]; exact mul_le_mul' (min_le_right _ _) (min_le_right _ _)
      have h2 := ENNReal.toReal_mono (ENNReal.pow_ne_top (fin _)) h1
      rwa [ENNReal.toReal_mul, ENNReal.toReal_pow] at h2)
  have e : ∀ (u : ℝ → ℝ≥0∞), (fun x => ENNReal.ofReal (min (u x) (n : ℝ≥0∞)).toReal) =
      fun x => min (u x) (n : ℝ≥0∞) := fun u => funext fun x => ENNReal.ofReal_toReal (fin _)
  simp only [hfr, hgr, hhr, e] at key
  refine key.trans ?_
  exact pow_le_pow_left' (lintegral_mono fun x => min_le_left _ _) 2

lemma pl1_ennreal {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hyp : ∀ x y, f x * g y ≤ h ((x + y) / 2) ^ 2) :
    (∫⁻ x, f x) * (∫⁻ x, g x) ≤ (∫⁻ x, h x) ^ 2 := by
  rw [lintegral_eq_iSup_min hf, lintegral_eq_iSup_min hg, ENNReal.iSup_mul]
  refine iSup_le fun m => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  have hm : (∫⁻ x, min (f x) (m : ℝ≥0∞)) ≤ ∫⁻ x, min (f x) ((max m n : ℕ) : ℝ≥0∞) :=
    lintegral_mono fun x => lintegral_min_nat_mono f (le_max_left m n) x
  have hn : (∫⁻ x, min (g x) (n : ℝ≥0∞)) ≤ ∫⁻ x, min (g x) ((max m n : ℕ) : ℝ≥0∞) :=
    lintegral_mono fun x => lintegral_min_nat_mono g (le_max_right m n) x
  exact (mul_le_mul' hm hn).trans (pl1_trunc hf hg hh hyp _)

lemma piFinSucc_symm_mid (n : ℕ) (s t : ℝ) (x y : Fin n → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm ((s + t) / 2, fun i => (x i + y i) / 2)
    = fun i => ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (s, x) i +
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (t, y) i) / 2 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma lintegral_piFinSucc (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ z, f z = ∫⁻ s, ∫⁻ x : Fin n → ℝ,
      f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm (s, x)) := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
  have h1 : ∫⁻ z, f z = ∫⁻ p : ℝ × (Fin n → ℝ),
      f ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm p) := by
    rw [hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)]
  rw [h1]
  exact lintegral_prod _ (hf.comp (MeasurableEquiv.measurable _)).aemeasurable

theorem pl_pi (n : ℕ) {f g h : (Fin n → ℝ) → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h)
    (hyp : ∀ x y, f x * g y ≤ h (fun i => (x i + y i) / 2) ^ 2) :
    (∫⁻ x, f x) * (∫⁻ x, g x) ≤ (∫⁻ x, h x) ^ 2 := by
  induction n with
  | zero =>
    have hv : ∀ u : (Fin 0 → ℝ) → ℝ≥0∞, Measurable u → ∫⁻ x, u x = u default := by
      intro u hu
      rw [volume_pi, Measure.pi_of_empty (fun _ : Fin 0 => (volume : Measure ℝ)) default,
        lintegral_dirac' _ hu]
    rw [hv f hf, hv g hg, hv h hh]
    have := hyp default default
    have hd : (fun i : Fin 0 => ((default : Fin 0 → ℝ) i + (default : Fin 0 → ℝ) i) / 2) = default :=
      Subsingleton.elim _ _
    rwa [hd] at this
  | succ n ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with he
    rw [lintegral_piFinSucc n f hf, lintegral_piFinSucc n g hg, lintegral_piFinSucc n h hh]
    have hF : Measurable (fun p : ℝ × (Fin n → ℝ) => f (e.symm p)) := hf.comp e.symm.measurable
    have hG : Measurable (fun p : ℝ × (Fin n → ℝ) => g (e.symm p)) := hg.comp e.symm.measurable
    have hH : Measurable (fun p : ℝ × (Fin n → ℝ) => h (e.symm p)) := hh.comp e.symm.measurable
    refine pl1_ennreal ?_ ?_ ?_ ?_
    · exact hF.lintegral_prod_right'
    · exact hG.lintegral_prod_right'
    · exact hH.lintegral_prod_right'
    · intro s t
      refine ih (hF.comp measurable_prodMk_left) (hG.comp measurable_prodMk_left)
        (hH.comp measurable_prodMk_left) ?_
      intro x y
      have := hyp (e.symm (s, x)) (e.symm (t, y))
      rw [← piFinSucc_symm_mid] at this
      exact this

/-- Third-order lower bound for the exponential on `[-1,1]`. -/
lemma exp_lower_cubic {s : ℝ} (hs : |s| ≤ 1) : 1 + s + s ^ 2 / 2 - |s| ^ 3 ≤ Real.exp s := by
  have h := Real.exp_bound hs (n := 3) (by norm_num)
  have h2 := (abs_le.mp h).1
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have h3 : 0 ≤ |s| ^ 3 := by positivity
  nlinarith [h2, h3]

lemma hasDerivAt_line_second {k : ℕ} {ψ : EuclideanSpace ℝ (Fin k) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (x v : EuclideanSpace ℝ (Fin k)) (s : ℝ) :
    HasDerivAt (fun s : ℝ => ψ (x + s • v)) (fderiv ℝ ψ (x + s • v) v) s ∧
    HasDerivAt (fun s : ℝ => fderiv ℝ ψ (x + s • v) v)
      (fderiv ℝ (fderiv ℝ ψ) (x + s • v) v v) s := by
  have hline : HasDerivAt (fun s : ℝ => x + s • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have h1 : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ ψ) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  refine ⟨?_, ?_⟩
  · exact (h1 (x + s • v)).hasFDerivAt.comp_hasDerivAt s hline
  · have := ((h2 (x + s • v)).hasFDerivAt.comp_hasDerivAt s hline)
    have h3 := (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt s this
    exact h3

/-- Strong convexity midpoint inequality from the Hessian lower bound on a convex set. -/
lemma strong_convex_midpoint {k : ℕ} {ψ : EuclideanSpace ℝ (Fin k) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {B : Set (EuclideanSpace ℝ (Fin k))} (hB : Convex ℝ B) {c : ℝ}
    (hess : ∀ x ∈ B, ∀ v, c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ ψ) x v v)
    {x y : EuclideanSpace ℝ (Fin k)} (hx : x ∈ B) (hy : y ∈ B) :
    ψ ((1 / 2 : ℝ) • (x + y)) ≤ (ψ x + ψ y) / 2 - c / 8 * ‖x - y‖ ^ 2 := by
  set v := y - x with hv
  set θ : ℝ → ℝ := fun s => ψ (x + s • v) - c / 2 * ‖v‖ ^ 2 * s ^ 2 with hθ
  have hD : ∀ s, HasDerivAt θ (fderiv ℝ ψ (x + s • v) v - c * ‖v‖ ^ 2 * s) s ∧
      HasDerivAt (fun s => fderiv ℝ ψ (x + s • v) v - c * ‖v‖ ^ 2 * s)
        (fderiv ℝ (fderiv ℝ ψ) (x + s • v) v v - c * ‖v‖ ^ 2) s := by
    intro s
    obtain ⟨h1, h2⟩ := hasDerivAt_line_second hψ x v s
    have hq : HasDerivAt (fun s : ℝ => c / 2 * ‖v‖ ^ 2 * s ^ 2) (c * ‖v‖ ^ 2 * s) s := by
      have := (hasDerivAt_pow 2 s).const_mul (c / 2 * ‖v‖ ^ 2)
      convert this using 1
      simp; ring
    have hl : HasDerivAt (fun s : ℝ => c * ‖v‖ ^ 2 * s) (c * ‖v‖ ^ 2) s := by
      simpa using (hasDerivAt_id s).const_mul (c * ‖v‖ ^ 2)
    exact ⟨h1.sub hq, h2.sub hl⟩
  have hconv : ConvexOn ℝ (Icc (0 : ℝ) 1) θ := by
    refine convexOn_of_deriv2_nonneg (convex_Icc 0 1) ?_ ?_ ?_ ?_
    · exact fun s _ => (hD s).1.continuousAt.continuousWithinAt
    · exact fun s _ => (hD s).1.differentiableAt.differentiableWithinAt
    · have : deriv θ = fun s => fderiv ℝ ψ (x + s • v) v - c * ‖v‖ ^ 2 * s :=
        funext fun s => (hD s).1.deriv
      rw [this]
      exact fun s _ => (hD s).2.differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := interior_subset hs
      have : deriv θ = fun s => fderiv ℝ ψ (x + s • v) v - c * ‖v‖ ^ 2 * s :=
        funext fun s => (hD s).1.deriv
      simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
      rw [this, (hD s).2.deriv]
      have hmem : x + s • v ∈ B := by
        have := hB hx hy (a := 1 - s) (b := s) (by linarith [hs'.2]) hs'.1 (by ring)
        convert this using 1
        simp only [hv, smul_sub, sub_smul, one_smul]
        abel
      have := hess _ hmem v
      linarith
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have key := hconv.2 h0 h1 (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (by norm_num)
  simp only [hθ, smul_eq_mul] at key
  have es : (1 / 2 * 0 + 1 / 2 * 1 : ℝ) = 1 / 2 := by norm_num
  rw [es] at key
  have e : x + (1 / 2 : ℝ) • v = (1 / 2 : ℝ) • (x + y) := by
    simp only [hv, smul_sub, smul_add]
    module
  have e1 : x + (0 : ℝ) • v = x := by simp
  have e2 : x + (1 : ℝ) • v = y := by simp [hv]
  rw [e, e1, e2] at key
  have : ‖x - y‖ = ‖v‖ := by rw [hv, norm_sub_rev]
  rw [this]
  nlinarith [key]

/-- Prekopa-Leindler on `EuclideanSpace ℝ (Fin k)`. -/
theorem pl_euclid {k : ℕ} {f g h : EuclideanSpace ℝ (Fin k) → ℝ≥0∞} (hf : Measurable f)
    (hg : Measurable g) (hh : Measurable h)
    (hyp : ∀ x y, f x * g y ≤ h ((1 / 2 : ℝ) • (x + y)) ^ 2) :
    (∫⁻ x, f x) * (∫⁻ x, g x) ≤ (∫⁻ x, h x) ^ 2 := by
  have hp := PiLp.volume_preserving_toLp (Fin k)
  have conv : ∀ u : EuclideanSpace ℝ (Fin k) → ℝ≥0∞, Measurable u →
      ∫⁻ x, u x = ∫⁻ a : Fin k → ℝ, u (WithLp.toLp 2 a) := fun u hu =>
    (hp.lintegral_comp hu).symm
  have hm : Measurable (WithLp.toLp 2 : (Fin k → ℝ) → EuclideanSpace ℝ (Fin k)) :=
    hp.measurable
  rw [conv f hf, conv g hg, conv h hh]
  refine pl_pi k (hf.comp hm) (hg.comp hm) (hh.comp hm) fun a b => ?_
  have := hyp (WithLp.toLp 2 a) (WithLp.toLp 2 b)
  refine this.trans (le_of_eq ?_)
  congr 2
  ext i
  simp
  ring

lemma real_lb1 {g pp M P t : ℝ} (hM : 0 ≤ M) (hP : 0 ≤ P) (hg : |g| ≤ M) (hp0 : 0 ≤ pp)
    (hpP : pp ≤ P) (ht0 : 0 < t) (ht1 : t * (M + P) ≤ 1) (ht : t ≤ 1) :
    1 + t * g - t ^ 2 * pp + t ^ 2 * g ^ 2 / 2 - t ^ 3 * (M * P + (M + P) ^ 3) ≤
      Real.exp (t * g - t ^ 2 * pp) := by
  set s := t * g - t ^ 2 * pp with hs
  have hgM : g ≤ M := (abs_le.mp hg).2
  have hgM' : -M ≤ g := (abs_le.mp hg).1
  have hsb : |s| ≤ t * (M + P) := by
    rw [abs_le]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left hpP (sq_nonneg t), mul_nonneg ht0.le hM,
      mul_nonneg (sq_nonneg t) hp0, mul_le_mul_of_nonneg_left hgM ht0.le,
      mul_le_mul_of_nonneg_left hgM' ht0.le, mul_nonneg ht0.le hP, mul_le_mul_of_nonneg_right ht hP]
  have h1 := exp_lower_cubic (hsb.trans ht1)
  have h2 : |s| ^ 3 ≤ (t * (M + P)) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hsb 3
  have h3 : g * pp ≤ M * P := by
    have : g * pp ≤ M * pp := mul_le_mul_of_nonneg_right hgM hp0
    nlinarith [mul_le_mul_of_nonneg_left hpP hM]
  have h4 : s ^ 2 ≥ t ^ 2 * g ^ 2 - 2 * t ^ 3 * (g * pp) := by
    simp only [hs]
    nlinarith [sq_nonneg (t ^ 2 * pp)]
  have h5 : t ^ 3 * (g * pp) ≤ t ^ 3 * (M * P) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have h6 : (t * (M + P)) ^ 3 = t ^ 3 * (M + P) ^ 3 := by ring
  nlinarith [h1, h2, h4, h5, h6]

lemma real_lb2 {g M t : ℝ} (hg : |g| ≤ M) (ht0 : 0 < t) (ht1 : t * M ≤ 1) :
    1 - t * g + t ^ 2 * g ^ 2 / 2 - t ^ 3 * M ^ 3 ≤ Real.exp (-(t * g)) := by
  have hsb : |-(t * g)| ≤ t * M := by
    rw [abs_neg, abs_mul, abs_of_pos ht0]
    exact mul_le_mul_of_nonneg_left hg ht0.le
  have h1 := exp_lower_cubic (hsb.trans ht1)
  have h2 : |-(t * g)| ^ 3 ≤ (t * M) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hsb 3
  have h6 : (t * M) ^ 3 = t ^ 3 * M ^ 3 := by ring
  nlinarith [h1, h2, h6]

lemma integrable_poly3 {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsFiniteMeasure ν]
    {u v w : α → ℝ} (hu : Integrable u ν) (hv : Integrable v ν) (hw : Integrable w ν)
    (a b c d : ℝ) : Integrable (fun x => a + b * u x + c * v x + d * w x) ν :=
  (((integrable_const a).add (hu.const_mul b)).add (hv.const_mul c)).add (hw.const_mul d)

lemma integral_poly3 {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    {u v w : α → ℝ} (hu : Integrable u ν) (hv : Integrable v ν) (hw : Integrable w ν)
    (a b c d : ℝ) :
    ∫ x, (a + b * u x + c * v x + d * w x) ∂ν =
      a + b * ∫ x, u x ∂ν + c * ∫ x, v x ∂ν + d * ∫ x, w x ∂ν := by
  have e1 : ∫ x, (a + b * u x + c * v x + d * w x) ∂ν =
      ∫ x, (a + b * u x + c * v x) ∂ν + ∫ x, d * w x ∂ν :=
    integral_add (((integrable_const a).add (hu.const_mul b)).add (hv.const_mul c))
      (hw.const_mul d)
  have e2 : ∫ x, (a + b * u x + c * v x) ∂ν = ∫ x, (a + b * u x) ∂ν + ∫ x, c * v x ∂ν :=
    integral_add ((integrable_const a).add (hu.const_mul b)) (hv.const_mul c)
  have e3 : ∫ x, (a + b * u x) ∂ν = ∫ x, a ∂ν + ∫ x, b * u x ∂ν :=
    integral_add (integrable_const a) (hu.const_mul b)
  rw [e1, e2, e3, integral_const_mul, integral_const_mul, integral_const_mul]
  simp

lemma prod_alg {t I Pm C1 A B : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) (htC : C1 * t ≤ 1) (hI0 : 0 ≤ I)
    (hPm0 : 0 ≤ Pm) (hC1n : 0 ≤ C1) (hA0 : 0 ≤ A)
    (hA : (1 - t ^ 3 * C1) + t * 0 + (-t ^ 2) * Pm + (t ^ 2 / 2) * I ≤ A)
    (hB : (1 - t ^ 3 * C1) + (-t) * 0 + 0 * Pm + (t ^ 2 / 2) * I ≤ B) (hAB : A * B ≤ 1) :
    t ^ 2 * (I - Pm) ≤ t ^ 3 * (2 * C1 + (I / 2 + Pm + C1) ^ 2) := by
  obtain ⟨D, hD⟩ : ∃ D, D = I / 2 + Pm + C1 := ⟨_, rfl⟩
  rw [← hD]
  obtain ⟨a', ha'⟩ : ∃ a', a' = t ^ 2 * (I / 2 - Pm) - t ^ 3 * C1 := ⟨_, rfl⟩
  obtain ⟨b', hb'⟩ : ∃ b', b' = t ^ 2 * I / 2 - t ^ 3 * C1 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hA' : 1 + a' ≤ A := by rw [ha']; linarith
  have hB' : 1 + b' ≤ B := by rw [hb']; linarith
  have ht2 : t ^ 3 ≤ t ^ 2 := by nlinarith [sq_nonneg t]
  have ht4 : t ^ 4 ≤ t ^ 3 := by
    have : t ^ 4 = t ^ 3 * t := by ring
    nlinarith [pow_pos ht0 3]
  have ht3C : t ^ 3 * C1 ≤ t ^ 2 * C1 := mul_le_mul_of_nonneg_right ht2 hC1n
  have hb0 : 0 ≤ 1 + b' := by
    have : t ^ 3 * C1 ≤ t ^ 2 := by
      have : t ^ 3 * C1 = t ^ 2 * (C1 * t) := by ring
      rw [this]; nlinarith [sq_nonneg t]
    rw [hb']; nlinarith [mul_nonneg (sq_nonneg t) hI0]
  have hprod : (1 + a') * (1 + b') ≤ 1 := by
    calc (1 + a') * (1 + b') ≤ A * (1 + b') := mul_le_mul_of_nonneg_right hA' hb0
      _ ≤ A * B := mul_le_mul_of_nonneg_left hB' hA0
      _ ≤ 1 := hAB
  have h2I : 0 ≤ t ^ 2 * I := mul_nonneg (sq_nonneg t) hI0
  have h2P : 0 ≤ t ^ 2 * Pm := mul_nonneg (sq_nonneg t) hPm0
  have h2C : 0 ≤ t ^ 2 * C1 := mul_nonneg (sq_nonneg t) hC1n
  have h3C : 0 ≤ t ^ 3 * C1 := mul_nonneg (pow_nonneg ht0.le 3) hC1n
  have habs_a : |a'| ≤ t ^ 2 * D := by
    rw [abs_le, ha', hD]
    constructor <;> nlinarith
  have habs_b : |b'| ≤ t ^ 2 * D := by
    rw [abs_le, hb', hD]
    constructor <;> nlinarith
  have hab : -(t ^ 2 * D) ^ 2 ≤ a' * b' := by
    have h1 : |a' * b'| ≤ (t ^ 2 * D) * (t ^ 2 * D) := by
      rw [abs_mul]; exact mul_le_mul habs_a habs_b (abs_nonneg _) (by positivity)
    have := neg_abs_le (a' * b')
    nlinarith [this, h1]
  have hexp : (1 + a') * (1 + b') = 1 + a' + b' + a' * b' := by ring
  have hsum : a' + b' = t ^ 2 * (I - Pm) - 2 * t ^ 3 * C1 := by rw [ha', hb']; ring
  have hD2 : (t ^ 2 * D) ^ 2 = t ^ 4 * D ^ 2 := by ring
  have h4D : t ^ 4 * D ^ 2 ≤ t ^ 3 * D ^ 2 := mul_le_mul_of_nonneg_right ht4 (sq_nonneg _)
  nlinarith [hprod, hexp, hsum, hab, hD2, h4D]

/-- Second-order extraction: from the Maurey-type product inequality for small `t`,
`∫ G² ≤ ∫ p` for mean-zero bounded `G`. -/
lemma poincare_from_exp {α : Type*} [MeasurableSpace α] (ν : Measure α) [IsProbabilityMeasure ν]
    {G p : α → ℝ} (hG : Measurable G) (hp : Measurable p) {M P : ℝ}
    (hGM : ∀ᵐ x ∂ν, |G x| ≤ M) (hp0 : ∀ᵐ x ∂ν, 0 ≤ p x) (hpP : ∀ᵐ x ∂ν, p x ≤ P)
    (hmean : ∫ x, G x ∂ν = 0) {t₀ : ℝ} (ht₀ : 0 < t₀)
    (h : ∀ t : ℝ, 0 < t → t ≤ t₀ →
      (∫ x, Real.exp (t * G x - t ^ 2 * p x) ∂ν) * (∫ x, Real.exp (-(t * G x)) ∂ν) ≤ 1) :
    ∫ x, G x ^ 2 ∂ν ≤ ∫ x, p x ∂ν := by
  have hM : 0 ≤ M := by
    obtain ⟨x, hx⟩ := (hGM).exists
    exact (abs_nonneg _).trans hx
  have hP : 0 ≤ P := by
    obtain ⟨x, hx0, hx⟩ := (hp0.and hpP).exists
    exact hx0.trans hx
  obtain ⟨C1, hC1⟩ : ∃ C1, C1 = M * P + (M + P) ^ 3 := ⟨_, rfl⟩
  have hC1n : 0 ≤ C1 := by rw [hC1]; positivity
  have hGi : Integrable G ν := Integrable.of_bound hG.aestronglyMeasurable M
    (hGM.mono fun x hx => by rwa [Real.norm_eq_abs])
  have hG2i : Integrable (fun x => G x ^ 2) ν := Integrable.of_bound (hG.pow_const 2).aestronglyMeasurable
    (M ^ 2) (hGM.mono fun x hx => by
      rw [Real.norm_eq_abs, abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) hx 2)
  have hpi : Integrable p ν := Integrable.of_bound hp.aestronglyMeasurable P
    (hp0.mp (hpP.mono fun x h1 h0 => by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1))
  obtain ⟨I, hI⟩ : ∃ I, ∫ x, G x ^ 2 ∂ν = I := ⟨_, rfl⟩
  obtain ⟨Pm, hPm⟩ : ∃ Pm, ∫ x, p x ∂ν = Pm := ⟨_, rfl⟩
  have hI0 : 0 ≤ I := by rw [← hI]; exact integral_nonneg fun x => sq_nonneg _
  have hPm0 : 0 ≤ Pm := by rw [← hPm]; exact integral_nonneg_of_ae hp0
  rw [hI, hPm]
  have hM3 : M ^ 3 ≤ C1 := by
    have : M ^ 3 ≤ (M + P) ^ 3 := pow_le_pow_left₀ hM (by linarith) 3
    have : 0 ≤ M * P := mul_nonneg hM hP
    rw [hC1]; linarith
  -- main estimate for small t
  have main : ∀ t : ℝ, 0 < t → t ≤ t₀ → t ≤ 1 → t * (M + P) ≤ 1 → C1 * t ≤ 1 →
      t ^ 2 * (I - Pm) ≤ t ^ 3 * (2 * C1 + (I / 2 + Pm + C1) ^ 2) := by
    intro t ht0 htt0 ht1 htK htC
    have hMP : t * M ≤ 1 := by nlinarith [mul_nonneg ht0.le hP]
    have hq : Measurable fun x => t * G x - t ^ 2 * p x :=
      (hG.const_mul t).sub (hp.const_mul _)
    have hE1m : Measurable fun x => Real.exp (t * G x - t ^ 2 * p x) := Real.measurable_exp.comp hq
    have hE2m : Measurable fun x => Real.exp (-(t * G x)) :=
      Real.measurable_exp.comp (hG.const_mul t).neg
    have hE1i : Integrable (fun x => Real.exp (t * G x - t ^ 2 * p x)) ν := by
      refine Integrable.of_bound hE1m.aestronglyMeasurable (Real.exp 1) ?_
      filter_upwards [hGM, hp0, hpP] with x h1 h2 h3
      have hs : |t * G x - t ^ 2 * p x| ≤ 1 := by
        rw [abs_le]
        have hg1 := abs_le.mp h1
        constructor <;> nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg t),
          mul_nonneg ht0.le hM, mul_nonneg (sq_nonneg t) h2, mul_le_mul_of_nonneg_left hg1.1 ht0.le,
          mul_le_mul_of_nonneg_left hg1.2 ht0.le, mul_nonneg ht0.le hP,
          mul_le_mul_of_nonneg_right ht1 hP]
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (le_trans (le_abs_self _) hs)
    have hE2i : Integrable (fun x => Real.exp (-(t * G x))) ν := by
      refine Integrable.of_bound hE2m.aestronglyMeasurable (Real.exp 1) ?_
      filter_upwards [hGM] with x h1
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      refine Real.exp_le_exp.mpr ?_
      have hg1 := abs_le.mp h1
      nlinarith [mul_le_mul_of_nonneg_left hg1.1 ht0.le]
    have hA : (1 - t ^ 3 * C1) + t * 0 + (-t ^ 2) * Pm + (t ^ 2 / 2) * I ≤
        ∫ x, Real.exp (t * G x - t ^ 2 * p x) ∂ν := by
      have key := integral_mono_ae (integrable_poly3 hGi hpi hG2i (1 - t ^ 3 * C1) t (-t ^ 2)
        (t ^ 2 / 2)) hE1i (by
          filter_upwards [hGM, hp0, hpP] with x h1 h2 h3
          have := real_lb1 hM hP h1 h2 h3 ht0 htK ht1
          rw [← hC1] at this
          nlinarith [this])
      rw [integral_poly3 hGi hpi hG2i, hmean, hI, hPm] at key
      exact key
    have hB : (1 - t ^ 3 * C1) + (-t) * 0 + 0 * Pm + (t ^ 2 / 2) * I ≤
        ∫ x, Real.exp (-(t * G x)) ∂ν := by
      have key := integral_mono_ae (integrable_poly3 hGi hpi hG2i (1 - t ^ 3 * C1) (-t) 0
        (t ^ 2 / 2)) hE2i (by
          filter_upwards [hGM] with x h1
          have := real_lb2 h1 ht0 hMP
          have h3 : t ^ 3 * M ^ 3 ≤ t ^ 3 * C1 :=
            mul_le_mul_of_nonneg_left hM3 (by positivity)
          nlinarith [this, h3])
      rw [integral_poly3 hGi hpi hG2i, hmean, hI, hPm] at key
      exact key
    exact prod_alg ht0 ht1 htC hI0 hPm0 hC1n (integral_nonneg fun x => (Real.exp_pos _).le) hA hB
      (h t ht0 htt0)
  -- conclude by letting t -> 0
  by_contra hcon
  push Not at hcon
  have hδ : 0 < I - Pm := by linarith
  obtain ⟨E, hE⟩ : ∃ E, E = 2 * C1 + (I / 2 + Pm + C1) ^ 2 := ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  have hMP1 : 0 < M + P + 1 := by linarith
  have hC11 : 0 < C1 + 1 := by linarith
  have hE1 : 0 < E + 1 := by linarith
  obtain ⟨t, ht⟩ : ∃ t, t = min (min t₀ 1) (min (1 / (M + P + 1))
      (min (1 / (C1 + 1)) ((I - Pm) / (2 * (E + 1))))) := ⟨_, rfl⟩
  have htpos : 0 < t := by
    rw [ht]
    refine lt_min (lt_min ht₀ one_pos) (lt_min (by positivity) (lt_min (by positivity) (by positivity)))
  have ht1 : t ≤ t₀ := by rw [ht]; exact (min_le_left _ _).trans (min_le_left _ _)
  have ht2 : t ≤ 1 := by rw [ht]; exact (min_le_left _ _).trans (min_le_right _ _)
  have ht3 : t ≤ 1 / (M + P + 1) := by rw [ht]; exact (min_le_right _ _).trans (min_le_left _ _)
  have ht4 : t ≤ 1 / (C1 + 1) := by
    rw [ht]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have ht5 : t ≤ (I - Pm) / (2 * (E + 1)) := by
    rw [ht]; exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have htK : t * (M + P) ≤ 1 := by
    have := (le_div_iff₀ hMP1).mp ht3
    nlinarith
  have htC : C1 * t ≤ 1 := by
    have := (le_div_iff₀ hC11).mp ht4
    nlinarith
  have hm := main t htpos ht1 ht2 htK htC
  rw [← hE] at hm
  have h5 : t * (2 * (E + 1)) ≤ I - Pm := (le_div_iff₀ (by positivity)).mp ht5
  have h8 : 0 < t ^ 2 := by positivity
  have h9 : I - Pm ≤ t * E := by
    have : t ^ 2 * (I - Pm) ≤ t ^ 2 * (t * E) := by nlinarith
    exact le_of_mul_le_mul_left this h8
  nlinarith [mul_pos htpos hE1, mul_nonneg htpos.le hE0]

lemma q_bound {k : ℕ} {G : EuclideanSpace ℝ (Fin k) → ℝ} (hG : ContDiff ℝ 1 G)
    (w0 : EuclideanSpace ℝ (Fin k)) (r : ℝ) {κ η : ℝ} (hκ : 0 < κ) (hη : 0 < η) :
    ∃ t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ x ∈ ball w0 r, ∀ y ∈ ball w0 r,
      t * (G x - G y) - κ / 4 * ‖x - y‖ ^ 2 ≤ t ^ 2 * (‖fderiv ℝ G x‖ + η) ^ 2 / κ := by
  have hGd : Differentiable ℝ G := hG.differentiable (by norm_num)
  have hdc : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  have hK : IsCompact (closedBall w0 r) := isCompact_closedBall w0 r
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn hdc.continuousOn
  set M := max M0 0 with hMdef
  have hM : 0 ≤ M := le_max_right _ _
  have hMb : ∀ z ∈ closedBall w0 r, ‖fderiv ℝ G z‖ ≤ M := fun z hz => (hM0 z hz).trans (le_max_left _ _)
  have huc := hK.uniformContinuousOn_of_continuous hdc.continuousOn
  obtain ⟨δ, hδ, hδ'⟩ := Metric.uniformContinuousOn_iff.mp huc η hη
  refine ⟨κ * δ / (4 * (M + 1)), by positivity, fun t ht0 htt x hx y hy => ?_⟩
  have hxK : x ∈ closedBall w0 r := ball_subset_closedBall hx
  have hyK : y ∈ closedBall w0 r := ball_subset_closedBall hy
  set s := ‖x - y‖ with hs
  have hs0 : 0 ≤ s := norm_nonneg _
  have hRHS : 0 ≤ t ^ 2 * (‖fderiv ℝ G x‖ + η) ^ 2 / κ := by positivity
  by_cases hsδ : δ ≤ s
  · -- far case
    have hcv : Convex ℝ (ball w0 r) := convex_ball w0 r
    have h1 := hcv.norm_image_sub_le_of_norm_fderiv_le (f := G) (C := M)
      (fun z _ => hGd z) (fun z hz => hMb z (ball_subset_closedBall hz)) hy hx
    rw [Real.norm_eq_abs] at h1
    have h2 : G x - G y ≤ M * s := (le_abs_self _).trans h1
    have h3 : t * (M + 1) ≤ κ * δ / 4 := by
      have := mul_le_mul_of_nonneg_right htt (by positivity : (0 : ℝ) ≤ M + 1)
      calc t * (M + 1) ≤ κ * δ / (4 * (M + 1)) * (M + 1) := this
        _ = κ * δ / 4 := by field_simp
    have h4 : t * (G x - G y) ≤ t * M * s := by
      have := mul_le_mul_of_nonneg_left h2 ht0.le
      linarith
    have h5 : t * M * s ≤ κ / 4 * s ^ 2 := by
      have : t * M ≤ κ / 4 * s := by
        have : κ * δ / 4 ≤ κ / 4 * s := by nlinarith
        nlinarith
      nlinarith
    linarith
  · -- near case
    push Not at hsδ
    set S := ball w0 r ∩ ball x δ with hSdef
    have hSc : Convex ℝ S := (convex_ball w0 r).inter (convex_ball x δ)
    set L := fderiv ℝ G x with hL
    have hgd : ∀ z ∈ S, DifferentiableAt ℝ (fun z => G z - L z) z := fun z _ =>
      (hGd z).sub L.differentiableAt
    have hgb : ∀ z ∈ S, ‖fderiv ℝ (fun z => G z - L z) z‖ ≤ η := by
      intro z hz
      have hz1 : z ∈ ball w0 r := hz.1
      have hz2 : z ∈ ball x δ := hz.2
      have : fderiv ℝ (fun z => G z - L z) z = fderiv ℝ G z - L := by
        rw [fderiv_fun_sub (hGd z) L.differentiableAt, ContinuousLinearMap.fderiv]
      rw [this]
      have := hδ' z (ball_subset_closedBall hz1) x hxK (mem_ball.mp hz2)
      rw [dist_eq_norm] at this
      exact this.le
    have hxS : x ∈ S := ⟨hx, mem_ball_self hδ⟩
    have hyS : y ∈ S := ⟨hy, by rw [mem_ball, dist_comm, dist_eq_norm]; exact hsδ⟩
    have h1 := hSc.norm_image_sub_le_of_norm_fderiv_le hgd hgb hxS hyS
    rw [Real.norm_eq_abs] at h1
    have h2 : |G y - L y - (G x - L x)| ≤ η * s := by
      refine h1.trans ?_
      rw [norm_sub_rev]
    have h3 : ‖L (x - y)‖ ≤ ‖L‖ * s := L.le_opNorm _
    have h3' : L (x - y) ≤ ‖L‖ * s := (le_abs_self _).trans (by rwa [Real.norm_eq_abs] at h3)
    have h4 : G x - G y ≤ (‖L‖ + η) * s := by
      have h5 := (abs_le.mp h2).1
      have h6 : L (x - y) = L x - L y := map_sub _ _ _
      nlinarith
    have h5 : t * (G x - G y) ≤ t * ((‖L‖ + η) * s) := mul_le_mul_of_nonneg_left h4 ht0.le
    have h6 : t * ((‖L‖ + η) * s) - κ / 4 * s ^ 2 ≤ t ^ 2 * (‖L‖ + η) ^ 2 / κ := by
      rw [le_div_iff₀ hκ]
      nlinarith [sq_nonneg (κ * s / 2 - t * (‖L‖ + η))]
    linarith

lemma wmeas_lintegral {k : ℕ} {φ : EuclideanSpace ℝ (Fin k) → ℝ} (hφm : Measurable φ)
    {V : ℝ≥0∞} {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (hν : ν = V⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin k))).withDensity
      (fun x => ENNReal.ofReal (φ x)))
    {u : EuclideanSpace ℝ (Fin k) → ℝ≥0∞} (hu : Measurable u) :
    ∫⁻ x, u x ∂ν = V⁻¹ * ∫⁻ x, ENNReal.ofReal (φ x) * u x := by
  subst hν
  rw [lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hφm.ennreal_ofReal hu]
  rfl

lemma wmeas_prob {k : ℕ} {φ : EuclideanSpace ℝ (Fin k) → ℝ}
    {V : ℝ≥0∞} {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (hV0 : V ≠ 0) (hVt : V ≠ ⊤) (hVeq : V = ∫⁻ x, ENNReal.ofReal (φ x))
    (hν : ν = V⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin k))).withDensity
      (fun x => ENNReal.ofReal (φ x))) : IsProbabilityMeasure ν := by
  refine ⟨?_⟩
  subst hν
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul, ← hVeq, ENNReal.inv_mul_cancel hV0 hVt]

lemma wmeas_ae_ball {k : ℕ} {φ : EuclideanSpace ℝ (Fin k) → ℝ}
    {w0 : EuclideanSpace ℝ (Fin k)} {r : ℝ} (hφB : ∀ x, x ∉ ball w0 r → φ x = 0)
    {V : ℝ≥0∞} {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (hν : ν = V⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin k))).withDensity
      (fun x => ENNReal.ofReal (φ x))) : ∀ᵐ x ∂ν, x ∈ ball w0 r := by
  rw [ae_iff]
  subst hν
  have hS : MeasurableSet {a : EuclideanSpace ℝ (Fin k) | ¬ a ∈ ball w0 r} :=
    (measurableSet_ball.compl)
  rw [Measure.smul_apply, withDensity_apply _ hS]
  have : ∫⁻ x in {a : EuclideanSpace ℝ (Fin k) | ¬ a ∈ ball w0 r}, ENNReal.ofReal (φ x) = 0 := by
    rw [setLIntegral_congr_fun hS (g := fun _ => 0)
      (fun x hx => by simp [hφB x hx])]
    simp
  rw [this]; simp

lemma weighted_product {k : ℕ} {φ : EuclideanSpace ℝ (Fin k) → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ x, 0 ≤ φ x)
    {V : ℝ≥0∞} {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (hV0 : V ≠ 0) (hVt : V ≠ ⊤) (hVeq : V = ∫⁻ x, ENNReal.ofReal (φ x))
    (hν : ν = V⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin k))).withDensity
      (fun x => ENNReal.ofReal (φ x)))
    {u1 u2 : EuclideanSpace ℝ (Fin k) → ℝ} (hu1 : Measurable u1) (hu2 : Measurable u2)
    (hu10 : ∀ x, 0 ≤ u1 x) (hu20 : ∀ x, 0 ≤ u2 x)
    (hyp : ∀ x y, φ x * u1 x * (φ y * u2 y) ≤ φ ((1 / 2 : ℝ) • (x + y)) ^ 2) :
    (∫ x, u1 x ∂ν) * (∫ x, u2 x ∂ν) ≤ 1 := by
  have hA := wmeas_lintegral hφm hν hu1.ennreal_ofReal
  have hB := wmeas_lintegral hφm hν hu2.ennreal_ofReal
  have hPL := pl_euclid
    (f := fun x => ENNReal.ofReal (φ x) * ENNReal.ofReal (u1 x))
    (g := fun x => ENNReal.ofReal (φ x) * ENNReal.ofReal (u2 x))
    (h := fun x => ENNReal.ofReal (φ x))
    (hφm.ennreal_ofReal.mul hu1.ennreal_ofReal) (hφm.ennreal_ofReal.mul hu2.ennreal_ofReal)
    hφm.ennreal_ofReal (by
      intro x y
      have e : ENNReal.ofReal (φ x) * ENNReal.ofReal (u1 x) *
          (ENNReal.ofReal (φ y) * ENNReal.ofReal (u2 y)) =
          ENNReal.ofReal (φ x * u1 x * (φ y * u2 y)) := by
        rw [ENNReal.ofReal_mul (mul_nonneg (hφ0 x) (hu10 x)), ENNReal.ofReal_mul (hφ0 x),
          ENNReal.ofReal_mul (hφ0 y)]
      show ENNReal.ofReal (φ x) * ENNReal.ofReal (u1 x) *
          (ENNReal.ofReal (φ y) * ENNReal.ofReal (u2 y)) ≤ _
      rw [e, ← ENNReal.ofReal_pow (hφ0 _)]
      exact ENNReal.ofReal_le_ofReal (hyp x y))
  rw [← hVeq] at hPL
  have hAB : (∫⁻ x, ENNReal.ofReal (u1 x) ∂ν) * (∫⁻ x, ENNReal.ofReal (u2 x) ∂ν) ≤ 1 := by
    rw [hA, hB]
    calc V⁻¹ * (∫⁻ x, ENNReal.ofReal (φ x) * ENNReal.ofReal (u1 x)) *
          (V⁻¹ * ∫⁻ x, ENNReal.ofReal (φ x) * ENNReal.ofReal (u2 x))
        = V⁻¹ * V⁻¹ * ((∫⁻ x, ENNReal.ofReal (φ x) * ENNReal.ofReal (u1 x)) *
          ∫⁻ x, ENNReal.ofReal (φ x) * ENNReal.ofReal (u2 x)) := by ring
      _ ≤ V⁻¹ * V⁻¹ * V ^ 2 := by gcongr
      _ = (V⁻¹ * V) * (V⁻¹ * V) := by ring
      _ = 1 := by rw [ENNReal.inv_mul_cancel hV0 hVt]; simp
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hu10)
      hu1.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hu20)
      hu2.aestronglyMeasurable, ← ENNReal.toReal_mul]
  have := ENNReal.toReal_mono (by simp) hAB
  simpa using this


lemma poincare_meanzero {k : ℕ} {φ : EuclideanSpace ℝ (Fin k) → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ x, 0 ≤ φ x) {w0 : EuclideanSpace ℝ (Fin k)} {r : ℝ}
    (hφB : ∀ x, x ∉ ball w0 r → φ x = 0) {κ : ℝ} (hκ : 0 < κ)
    (hconv : ∀ x y, φ x * φ y ≤
      φ ((1 / 2 : ℝ) • (x + y)) ^ 2 * Real.exp (-(κ / 4 * ‖x - y‖ ^ 2)))
    {V : ℝ≥0∞} {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (hV0 : V ≠ 0) (hVt : V ≠ ⊤) (hVeq : V = ∫⁻ x, ENNReal.ofReal (φ x))
    (hν : ν = V⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin k))).withDensity
      (fun x => ENNReal.ofReal (φ x)))
    {G : EuclideanSpace ℝ (Fin k) → ℝ} (hG : ContDiff ℝ 1 G) (hmean : ∫ x, G x ∂ν = 0) :
    κ * ∫ x, G x ^ 2 ∂ν ≤ ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂ν := by
  have : IsProbabilityMeasure ν := wmeas_prob hV0 hVt hVeq hν
  have hae := wmeas_ae_ball hφB hν
  have hGc : Continuous G := hG.continuous
  have hdc : Continuous (fderiv ℝ G) := hG.continuous_fderiv (by norm_num)
  obtain ⟨M, hM⟩ := (isCompact_closedBall w0 r).exists_bound_of_continuousOn hGc.continuousOn
  obtain ⟨L, hL⟩ := (isCompact_closedBall w0 r).exists_bound_of_continuousOn hdc.continuousOn
  have hL0 : 0 ≤ L := by
    obtain ⟨x, hx⟩ := hae.exists
    exact (norm_nonneg _).trans (hL x (ball_subset_closedBall hx))
  have hdn : Continuous fun x => ‖fderiv ℝ G x‖ := hdc.norm
  have key : ∀ η : ℝ, 0 < η → η ≤ 1 →
      κ * ∫ x, G x ^ 2 ∂ν ≤ ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂ν + η * (2 * L + 1) := by
    intro η hη hη1
    obtain ⟨t₀, ht₀, hq⟩ := q_bound hG w0 r hκ hη
    have hpc : Continuous fun x => (‖fderiv ℝ G x‖ + η) ^ 2 / κ :=
      ((hdn.add continuous_const).pow 2).div_const κ
    have hmain := poincare_from_exp ν (G := G) (p := fun x => (‖fderiv ℝ G x‖ + η) ^ 2 / κ)
      hGc.measurable hpc.measurable (M := M) (P := (L + η) ^ 2 / κ)
      (hae.mono fun x hx => by simpa [Real.norm_eq_abs] using hM x (ball_subset_closedBall hx))
      (Filter.Eventually.of_forall fun x => by positivity)
      (hae.mono fun x hx => by
        have := hL x (ball_subset_closedBall hx)
        gcongr)
      hmean ht₀ (by
        intro t ht htt
        refine weighted_product hφm hφ0 hV0 hVt hVeq hν
          (u1 := fun x => Real.exp (t * G x - t ^ 2 * ((‖fderiv ℝ G x‖ + η) ^ 2 / κ)))
          (u2 := fun x => Real.exp (-(t * G x)))
          (by fun_prop) (by fun_prop) (fun x => (Real.exp_pos _).le)
          (fun x => (Real.exp_pos _).le) ?_
        intro x y
        by_cases hx : x ∈ ball w0 r
        · by_cases hy : y ∈ ball w0 r
          · have h1 := hq t ht htt x hx y hy
            have h2 := hconv x y
            have h3 : Real.exp (t * G x - t ^ 2 * ((‖fderiv ℝ G x‖ + η) ^ 2 / κ)) *
                Real.exp (-(t * G y)) ≤ Real.exp (κ / 4 * ‖x - y‖ ^ 2) := by
              rw [← Real.exp_add]
              apply Real.exp_le_exp.mpr
              have : t ^ 2 * ((‖fderiv ℝ G x‖ + η) ^ 2 / κ) =
                  t ^ 2 * (‖fderiv ℝ G x‖ + η) ^ 2 / κ := by ring
              linarith
            calc φ x * Real.exp (t * G x - t ^ 2 * ((‖fderiv ℝ G x‖ + η) ^ 2 / κ)) *
                  (φ y * Real.exp (-(t * G y)))
                = (φ x * φ y) * (Real.exp (t * G x - t ^ 2 * ((‖fderiv ℝ G x‖ + η) ^ 2 / κ)) *
                  Real.exp (-(t * G y))) := by ring
              _ ≤ (φ ((1 / 2 : ℝ) • (x + y)) ^ 2 * Real.exp (-(κ / 4 * ‖x - y‖ ^ 2))) *
                  Real.exp (κ / 4 * ‖x - y‖ ^ 2) :=
                mul_le_mul h2 h3 (by positivity) (by positivity)
              _ = φ ((1 / 2 : ℝ) • (x + y)) ^ 2 := by
                rw [mul_assoc, ← Real.exp_add]; simp
          · simp [hφB y hy, hφ0]
        · simp [hφB x hx, sq_nonneg])
    -- convert to the energy bound
    have hI : ∫ x, (‖fderiv ℝ G x‖ + η) ^ 2 / κ ∂ν =
        (∫ x, (‖fderiv ℝ G x‖ + η) ^ 2 ∂ν) / κ := integral_div _ _
    rw [hI, le_div_iff₀ hκ] at hmain
    have hi1 : Integrable (fun x => (‖fderiv ℝ G x‖ + η) ^ 2) ν :=
      Integrable.of_bound ((hdn.add continuous_const).pow 2).aestronglyMeasurable ((L + η) ^ 2)
        (hae.mono fun x hx => by
          have := hL x (ball_subset_closedBall hx)
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          gcongr)
    have hi2 : Integrable (fun x => ‖fderiv ℝ G x‖ ^ 2) ν :=
      Integrable.of_bound (hdn.pow 2).aestronglyMeasurable (L ^ 2)
        (hae.mono fun x hx => by
          have := hL x (ball_subset_closedBall hx)
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          gcongr)
    have hle : ∫ x, (‖fderiv ℝ G x‖ + η) ^ 2 ∂ν ≤
        ∫ x, (‖fderiv ℝ G x‖ ^ 2 + η * (2 * L + 1)) ∂ν := by
      refine integral_mono_ae hi1 (hi2.add (integrable_const _)) (hae.mono fun x hx => ?_)
      have := hL x (ball_subset_closedBall hx)
      have hn := norm_nonneg (fderiv ℝ G x)
      nlinarith [mul_le_mul_of_nonneg_left this hη.le, mul_le_mul_of_nonneg_left hη1 hη.le]
    rw [integral_add hi2 (integrable_const _)] at hle
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hle
    linarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hpos : 0 < 2 * L + 1 := by linarith
  have hη := lt_min one_pos (div_pos hε hpos)
  have := key (min 1 (ε / (2 * L + 1))) hη (min_le_left _ _)
  have h2 : min 1 (ε / (2 * L + 1)) * (2 * L + 1) ≤ ε :=
    (mul_le_mul_of_nonneg_right (min_le_right _ _) hpos.le).trans (le_of_eq (by field_simp))
  linarith


lemma poincare_weighted {k : ℕ} {φ : EuclideanSpace ℝ (Fin k) → ℝ} (hφm : Measurable φ)
    (hφ0 : ∀ x, 0 ≤ φ x) {w0 : EuclideanSpace ℝ (Fin k)} {r : ℝ}
    (hφB : ∀ x, x ∉ ball w0 r → φ x = 0) {κ : ℝ} (hκ : 0 < κ)
    (hconv : ∀ x y, φ x * φ y ≤
      φ ((1 / 2 : ℝ) • (x + y)) ^ 2 * Real.exp (-(κ / 4 * ‖x - y‖ ^ 2)))
    {V : ℝ≥0∞} {ν : Measure (EuclideanSpace ℝ (Fin k))}
    (hV0 : V ≠ 0) (hVt : V ≠ ⊤) (hVeq : V = ∫⁻ x, ENNReal.ofReal (φ x))
    (hν : ν = V⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin k))).withDensity
      (fun x => ENNReal.ofReal (φ x)))
    {G : EuclideanSpace ℝ (Fin k) → ℝ} (hG : ContDiff ℝ 1 G) :
    κ * ∫ x, (G x - ∫ y, G y ∂ν) ^ 2 ∂ν ≤ ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂ν := by
  have : IsProbabilityMeasure ν := wmeas_prob hV0 hVt hVeq hν
  have hae := wmeas_ae_ball hφB hν
  obtain ⟨M, hM⟩ := (isCompact_closedBall w0 r).exists_bound_of_continuousOn
    hG.continuous.continuousOn
  have hGi : Integrable G ν := Integrable.of_bound hG.continuous.aestronglyMeasurable M
    (hae.mono fun x hx => hM x (ball_subset_closedBall hx))
  have hG' : ContDiff ℝ 1 (fun x => G x - ∫ y, G y ∂ν) := hG.sub contDiff_const
  have hmean : ∫ x, (G x - ∫ y, G y ∂ν) ∂ν = 0 := by
    rw [integral_sub hGi (integrable_const _)]
    simp
  have := poincare_meanzero hφm hφ0 hφB hκ hconv hV0 hVt hVeq hν hG' hmean
  have hf : ∀ x, fderiv ℝ (fun x => G x - ∫ y, G y ∂ν) x = fderiv ℝ G x := fun x =>
    fderiv_sub_const _
  simpa [hf] using this

lemma conv_weight {k : ℕ} {ψ : EuclideanSpace ℝ (Fin k) → ℝ} (hψ : ContDiff ℝ 2 ψ)
    {w0 : EuclideanSpace ℝ (Fin k)} {r c N : ℝ} (hN : 0 ≤ N)
    (hess : ∀ x ∈ ball w0 r, ∀ v, c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ ψ) x v v)
    (x y : EuclideanSpace ℝ (Fin k)) :
    (ball w0 r).indicator (fun z => Real.exp (-(N * ψ z))) x *
        (ball w0 r).indicator (fun z => Real.exp (-(N * ψ z))) y ≤
      (ball w0 r).indicator (fun z => Real.exp (-(N * ψ z))) ((1 / 2 : ℝ) • (x + y)) ^ 2 *
        Real.exp (-(c * N / 4 * ‖x - y‖ ^ 2)) := by
  by_cases hx : x ∈ ball w0 r
  · by_cases hy : y ∈ ball w0 r
    · have hmid : (1 / 2 : ℝ) • (x + y) ∈ ball w0 r := by
        have := (convex_ball w0 r) hx hy (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
        simpa [smul_add] using this
      have hs := strong_convex_midpoint hψ (convex_ball w0 r) hess hx hy
      have hs' := mul_le_mul_of_nonneg_left hs hN
      simp only [indicator_of_mem hx, indicator_of_mem hy, indicator_of_mem hmid]
      rw [← Real.exp_add, sq, ← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [hs']
    · rw [indicator_of_notMem hy, mul_zero]; positivity
  · rw [indicator_of_notMem hx, zero_mul]; positivity


lemma imsEta_finite {k : ℕ} (N : ℝ) (ψ : EuclideanSpace ℝ (Fin k) → ℝ) :
    IsFiniteMeasure (DGPS.FiniteN.imsEta N ψ) := by
  refine ⟨?_⟩
  unfold DGPS.FiniteN.imsEta
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul]
  generalize (∫⁻ x : EuclideanSpace ℝ (Fin k), ENNReal.ofReal (Real.exp (-(N * ψ x)))) = Z
  by_cases h0 : Z = 0
  · simp [h0]
  by_cases ht : Z = ⊤
  · simp [ht]
  rw [ENNReal.inv_mul_cancel h0 ht]
  exact ENNReal.one_lt_top

lemma cond_imsEta_eq {k : ℕ} {ψ : EuclideanSpace ℝ (Fin k) → ℝ} (hψc : Continuous ψ)
    (w0 : EuclideanSpace ℝ (Fin k)) (r N : ℝ)
    (hμB : DGPS.FiniteN.imsEta N ψ (ball w0 r) ≠ 0) :
    ∃ V : ℝ≥0∞, V ≠ 0 ∧ V ≠ ⊤ ∧
      V = ∫⁻ x, ENNReal.ofReal ((ball w0 r).indicator (fun z => Real.exp (-(N * ψ z))) x) ∧
      cond (DGPS.FiniteN.imsEta N ψ) (ball w0 r) = V⁻¹ •
        (volume : Measure (EuclideanSpace ℝ (Fin k))).withDensity
          (fun x => ENNReal.ofReal ((ball w0 r).indicator (fun z => Real.exp (-(N * ψ z))) x)) := by
  have hBm : MeasurableSet (ball w0 r) := measurableSet_ball
  have hφ0m : Measurable (fun x => ENNReal.ofReal (Real.exp (-(N * ψ x)))) :=
    (Continuous.measurable (by fun_prop)).ennreal_ofReal
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = ∫⁻ x : EuclideanSpace ℝ (Fin k),
      ENNReal.ofReal (Real.exp (-(N * ψ x))) := ⟨_, rfl⟩
  have hind : (fun x => ENNReal.ofReal ((ball w0 r).indicator
      (fun z => Real.exp (-(N * ψ z))) x)) =
      (ball w0 r).indicator (fun x => ENNReal.ofReal (Real.exp (-(N * ψ x)))) := by
    funext x
    by_cases hx : x ∈ ball w0 r <;> simp [indicator, hx]
  obtain ⟨V, hV⟩ : ∃ V, V = ∫⁻ x, ENNReal.ofReal ((ball w0 r).indicator
      (fun z => Real.exp (-(N * ψ z))) x) := ⟨_, rfl⟩
  have hV' : V = ∫⁻ x in ball w0 r, ENNReal.ofReal (Real.exp (-(N * ψ x))) := by
    rw [hV, hind, lintegral_indicator hBm]
  have hDB : ((volume : Measure (EuclideanSpace ℝ (Fin k))).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-(N * ψ x))))) (ball w0 r) = V := by
    rw [withDensity_apply _ hBm, hV']
  have hμ : DGPS.FiniteN.imsEta N ψ = Z⁻¹ • (volume : Measure (EuclideanSpace ℝ (Fin k))).withDensity
      (fun x => ENNReal.ofReal (Real.exp (-(N * ψ x)))) := by
    unfold DGPS.FiniteN.imsEta; rw [hZ]
  have hμB' : Z⁻¹ * V ≠ 0 := by
    rw [hμ, Measure.smul_apply, hDB, smul_eq_mul] at hμB; exact hμB
  have hZt : Z ≠ ⊤ := by
    intro h; apply hμB'; rw [h]; simp
  have hV0 : V ≠ 0 := by
    intro h; apply hμB'; rw [h, mul_zero]
  have hVZ : V ≤ Z := by
    rw [hV', hZ]; exact setLIntegral_le_lintegral _ _
  have hVt : V ≠ ⊤ := ne_top_of_le_ne_top hZt hVZ
  have hZ0 : Z ≠ 0 := by
    intro h; apply hV0; exact le_antisymm (h ▸ hVZ) bot_le
  refine ⟨V, hV0, hVt, hV, ?_⟩
  show ((DGPS.FiniteN.imsEta N ψ) (ball w0 r))⁻¹ • (DGPS.FiniteN.imsEta N ψ).restrict (ball w0 r) = _
  rw [hμ, Measure.restrict_smul, restrict_withDensity hBm, ← withDensity_indicator hBm, Measure.smul_apply, hDB,
    smul_eq_mul, smul_smul, hind]
  congr 1
  rw [ENNReal.mul_inv (Or.inl (ENNReal.inv_ne_zero.2 hZt)) (Or.inl (ENNReal.inv_ne_top.2 hZ0)),
    inv_inv]
  calc Z * V⁻¹ * Z⁻¹ = (Z * Z⁻¹) * V⁻¹ := by ring
    _ = V⁻¹ := by rw [ENNReal.mul_inv_cancel hZ0 hZt, one_mul]

end DGPS.FiniteN.Tools.ConditionalPoincareMain

namespace DGPS.FiniteN

open MeasureTheory ProbabilityTheory Set Metric
open DGPS.FiniteN.Tools.ConditionalPoincareMain

/-- Conditional Poincare inequality near a nondegenerate minimum, with cutoff clause. -/
theorem conditional_minimum_neighborhood_poincare {k : ℕ}
    (ψ : EuclideanSpace ℝ (Fin k) → ℝ) (hψ : ContDiff ℝ 2 ψ)
    (w0 : EuclideanSpace ℝ (Fin k)) (r c : ℝ) (hc : 0 < c)
    (hess : ∀ x ∈ ball w0 r, ∀ v, c * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ ψ) x v v) :
    (∀ (N : ℝ) (G : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ 1 G →
      c * N * ∫ x, (G x - ∫ y, G y ∂(cond (imsEta N ψ) (ball w0 r))) ^ 2
          ∂(cond (imsEta N ψ) (ball w0 r)) ≤
        ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂(cond (imsEta N ψ) (ball w0 r))) ∧
    (∀ (χ : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ 1 χ → (∀ x, 0 ≤ χ x) → (∀ x, χ x ≤ 1) →
      (∀ x, x ∉ ball w0 r → χ x = 0) → ∀ Cχ : ℝ, (∀ x, ‖fderiv ℝ χ x‖ ≤ Cχ) →
      ∀ A c' m₀ : ℝ, 0 < m₀ → ∀ N : ℝ, 0 ≤ N → m₀ ≤ (imsEta N ψ (ball w0 r)).toReal →
      (imsEta N ψ {x | χ x ≠ 1}).toReal ≤ A * Real.exp (-(c' * N)) →
      ∀ F : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ 1 F →
      Integrable (fun x => F x ^ 2) (imsEta N ψ) →
      Integrable (fun x => ‖fderiv ℝ F x‖ ^ 2) (imsEta N ψ) →
      ∫ x, F x ∂(imsEta N ψ) = 0 →
      c * N * ∫ x, (χ x * F x) ^ 2 ∂(imsEta N ψ) -
          c * A / m₀ * N * Real.exp (-(c' * N)) * ∫ x, F x ^ 2 ∂(imsEta N ψ) ≤
        ∫ x, ‖fderiv ℝ (fun y => χ y * F y) x‖ ^ 2 ∂(imsEta N ψ)) := by
  have part1 : ∀ (N : ℝ) (G : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ 1 G →
      c * N * ∫ x, (G x - ∫ y, G y ∂(cond (imsEta N ψ) (ball w0 r))) ^ 2
          ∂(cond (imsEta N ψ) (ball w0 r)) ≤
        ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂(cond (imsEta N ψ) (ball w0 r)) := by
    intro N G hG
    by_cases hN : 0 < N
    · by_cases hμB : imsEta N ψ (ball w0 r) = 0
      · have h0 : cond (imsEta N ψ) (ball w0 r) = 0 := by
          show ((imsEta N ψ) (ball w0 r))⁻¹ • (imsEta N ψ).restrict (ball w0 r) = 0
          rw [Measure.restrict_eq_zero.2 hμB, smul_zero]
        rw [h0]; simp
      · obtain ⟨V, hV0, hVt, hVeq, hcond⟩ :=
          cond_imsEta_eq hψ.continuous w0 r N hμB
        rw [hcond]
        have hψm : Measurable ψ := hψ.continuous.measurable
        refine poincare_weighted (φ := (ball w0 r).indicator fun z => Real.exp (-(N * ψ z)))
          (w0 := w0) (r := r) ?_ ?_ ?_ (mul_pos hc hN)
          (conv_weight hψ hN.le hess) hV0 hVt hVeq rfl hG
        · exact Measurable.indicator (by fun_prop) measurableSet_ball
        · exact fun x => indicator_nonneg (fun z _ => (Real.exp_pos _).le) x
        · exact fun x hx => indicator_of_notMem hx _
    · have h1 : c * N ≤ 0 := mul_nonpos_iff.2 (Or.inl ⟨hc.le, not_lt.1 hN⟩)
      have h2 : 0 ≤ ∫ x, (G x - ∫ y, G y ∂(cond (imsEta N ψ) (ball w0 r))) ^ 2
          ∂(cond (imsEta N ψ) (ball w0 r)) := integral_nonneg fun x => sq_nonneg _
      have h3 : 0 ≤ ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂(cond (imsEta N ψ) (ball w0 r)) :=
        integral_nonneg fun x => sq_nonneg _
      nlinarith
  refine ⟨part1, ?_⟩
  intro χ hχ hχ0 hχ1 hχB Cχ hCχ A c' m₀ hm₀ N hN hBm hout F hF hF2 hFd hF0
  have := imsEta_finite N ψ
  have hμB : imsEta N ψ (ball w0 r) ≠ 0 := by
    intro h
    rw [h] at hBm
    simp at hBm
    linarith
  exact cutoff_energy_lower_bound_exp (imsEta N ψ) hμB c N hc.le hN (part1 N) χ hχ hχ0 hχ1 hχB
    Cχ hCχ A c' m₀ hm₀ hBm hout F hF hF2 hFd hF0

end DGPS.FiniteN
