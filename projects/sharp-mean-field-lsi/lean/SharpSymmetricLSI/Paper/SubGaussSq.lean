import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Square-exponential moments of bounded centered sums (Phase 3, lane D; R20 (5.13))

For i.i.d. centered `f(Z_l)` with `|f| ≤ B` and `c B² ≤ 1/4`,
`E exp(c (∑_{l<n} f(Z_l))² / (n+1)) ≤ ∫ e^{g²/4} dγ(g) < ∞`: write
`e^{t²s²/2} = ∫ e^{tsg} dγ(g)`, exchange the integrals, factor over `l` and apply Hoeffding's
lemma to each factor ("integrating in `t` against a narrow Gaussian", manuscript Lemma 5.3).
-/

noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal

namespace SharpLSI

/-- The Gaussian constant `∫ e^{g²/4} dγ(g)`. -/
def gaussSqConst : ℝ≥0∞ := ∫⁻ g, ENNReal.ofReal (exp (g ^ 2 / 4)) ∂gaussianReal 0 1

theorem gaussSqConst_ne_top : gaussSqConst ≠ ⊤ := by
  unfold gaussSqConst
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF 0 1)
      (by fun_prop : Measurable fun g : ℝ => ENNReal.ofReal (exp (g ^ 2 / 4)))]
  have e : ∀ g : ℝ, (gaussianPDF 0 1 * fun g => ENNReal.ofReal (exp (g ^ 2 / 4))) g =
      ENNReal.ofReal ((√(2 * π))⁻¹ * exp (-(1 / 4) * g ^ 2)) := fun g => by
    simp only [Pi.mul_apply, gaussianPDF, gaussianPDFReal]
    rw [← ENNReal.ofReal_mul (by positivity), mul_assoc, ← exp_add]
    congr 3
    show -(g - 0) ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) + g ^ 2 / 4 = -(1 / 4) * g ^ 2
    rw [NNReal.coe_one]; ring
    rw [NNReal.coe_one, mul_one]
  simp_rw [e]
  exact (((integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 4)).const_mul
    ((√(2 * π))⁻¹)).lintegral_lt_top).ne

theorem integral_exp_mul_gaussian (u : ℝ) : ∫ g, exp (u * g) ∂gaussianReal 0 1 = exp (u ^ 2 / 2) := by
  have := mgf_gaussianReal (μ := 0) (v := 1) (X := id) (p := gaussianReal 0 1)
    ⟨aemeasurable_id, by simp⟩ u
  simpa [mgf] using this

/-- Hoeffding's lemma in the form used here. -/
theorem integral_exp_mul_le {α : Type*} [MeasurableSpace α] {ν : Measure α} [IsProbabilityMeasure ν]
    [Nonempty α]
    {f : α → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ y, |f y| ≤ B) (h0 : ∫ y, f y ∂ν = 0) (u : ℝ) :
    ∫ y, exp (u * f y) ∂ν ≤ exp (B ^ 2 * u ^ 2 / 2) := by
  have hb : ∀ᵐ y ∂ν, f y ∈ Set.Icc (-B) B := Filter.Eventually.of_forall fun y =>
    ⟨(abs_le.mp (hB y)).1, (abs_le.mp (hB y)).2⟩
  have h := (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hf.aemeasurable hb h0).mgf_le u
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary _))
  have hc : (((‖B - -B‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = B ^ 2 := by
    push_cast
    rw [Real.norm_eq_abs, show B - -B = 2 * B by ring, abs_of_nonneg (by linarith)]
    ring
  rw [hc] at h
  simpa [mgf] using h

/-- **Square-exponential moment of a bounded centered i.i.d. sum.** -/
theorem lintegral_exp_sq_sum_le {α : Type*} [MeasurableSpace α] (ν : Measure α)
    [IsProbabilityMeasure ν] [Nonempty α] (n : ℕ) {f : α → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ y, |f y| ≤ B) (h0 : ∫ y, f y ∂ν = 0) {c : ℝ} (hc0 : 0 ≤ c) (hcB : c * B ^ 2 ≤ 1 / 4) :
    ∫⁻ Z, ENNReal.ofReal (exp (c * (∑ l, f (Z l)) ^ 2 / (n + 1)))
      ∂(Measure.pi fun _ : Fin n => ν) ≤ gaussSqConst := by
  set γ := gaussianReal 0 1
  set t := √(2 * c / (n + 1)) with ht
  have hn : (0 : ℝ) < n + 1 := by positivity
  have ht2 : t ^ 2 = 2 * c / (n + 1) := Real.sq_sqrt (by positivity)
  set s : (Fin n → α) → ℝ := fun Z => ∑ l, f (Z l) with hs
  have hsm : Measurable s := Finset.measurable_sum _ fun l _ => hf.comp (measurable_pi_apply l)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB (Classical.arbitrary _))
  -- step 1: the Gaussian representation
  have h1 : ∀ Z, ENNReal.ofReal (exp (c * s Z ^ 2 / (n + 1))) =
      ∫⁻ g, ENNReal.ofReal (exp (t * s Z * g)) ∂γ := fun Z => by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal _)
      (Filter.Eventually.of_forall fun _ => (exp_pos _).le), integral_exp_mul_gaussian]
    congr 2
    rw [mul_pow, ht2]; ring
  simp_rw [show ∀ Z, c * (∑ l, f (Z l)) ^ 2 / (n + 1) = c * s Z ^ 2 / (n + 1) from fun _ => rfl, h1]
  rw [lintegral_lintegral_swap (by
    exact (Measurable.ennreal_ofReal (measurable_exp.comp
      (((measurable_const.mul (hsm.comp measurable_fst)).mul measurable_snd)))).aemeasurable)]
  refine lintegral_mono fun g => ?_
  -- step 2: factor over the coordinates and apply Hoeffding
  have hfac : ∀ Z, exp (t * s Z * g) = ∏ l, exp (t * g * f (Z l)) := fun Z => by
    rw [← exp_sum]; congr 1
    simp only [hs, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hbd : ∀ y, |exp (t * g * f y)| ≤ exp (|t * g| * B) := fun y => by
    rw [abs_of_pos (exp_pos _)]
    exact exp_le_exp.mpr ((le_abs_self _).trans (by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hB y) (abs_nonneg _)))
  have hint : Integrable (fun Z : Fin n → α => ∏ l, exp (t * g * f (Z l)))
      (Measure.pi fun _ : Fin n => ν) := by
    refine Integrable.of_bound (Finset.measurable_prod _ fun l _ =>
      measurable_exp.comp (measurable_const.mul (hf.comp (measurable_pi_apply l)))
      ).aestronglyMeasurable (exp (|t * g| * B) ^ n) (Filter.Eventually.of_forall fun Z => ?_)
    rw [Real.norm_eq_abs, Finset.abs_prod]
    calc ∏ l, |exp (t * g * f (Z l))| ≤ ∏ _l : Fin n, exp (|t * g| * B) :=
          Finset.prod_le_prod₀ (fun l _ => abs_nonneg _) fun l _ => hbd _
      _ = exp (|t * g| * B) ^ n := by simp
  simp_rw [hfac]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun Z =>
    Finset.prod_nonneg fun l _ => (exp_pos _).le)]
  rw [integral_fintype_prod_eq_prod (fun (_ : Fin n) y => exp (t * g * f y))]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∏ _l : Fin n, ∫ y, exp (t * g * f y) ∂ν ≤ ∏ _l : Fin n, exp (B ^ 2 * (t * g) ^ 2 / 2) :=
        Finset.prod_le_prod₀ (fun l _ => integral_nonneg fun _ => (exp_pos _).le)
          fun l _ => integral_exp_mul_le hf hB h0 _
    _ = exp (n * (B ^ 2 * (t * g) ^ 2 / 2)) := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← exp_nat_mul]
    _ ≤ exp (g ^ 2 / 4) := by
        refine exp_le_exp.mpr ?_
        rw [mul_pow, ht2]
        have hg : 0 ≤ g ^ 2 := sq_nonneg g
        have : (n : ℝ) / (n + 1) ≤ 1 := by rw [div_le_one hn]; linarith
        calc (n : ℝ) * (B ^ 2 * (2 * c / (n + 1) * g ^ 2) / 2) =
            (n / (n + 1)) * (c * B ^ 2) * g ^ 2 := by field_simp
          _ ≤ 1 * (1 / 4) * g ^ 2 := by
              gcongr
          _ = g ^ 2 / 4 := by ring

end SharpLSI
