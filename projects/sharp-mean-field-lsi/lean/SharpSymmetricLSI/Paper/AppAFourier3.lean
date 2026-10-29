import SharpSymmetricLSI.Paper.AppAPos3

/-!
# The Laplacian kernel `ΔG_t` and `Δe^{tΔ}`

`lapKer t y = ∑ⱼ (yⱼ²/(4t²) - 1/(2t)) G_t(y)`, with `∫ lapKer(y) e^{-2πin·y} dy = -λ_n e^{-λ_n t}`;
`lapHeat t f = ∫ lapKer(y) f(x - y) dy` has coefficients `-λ_n e^{-λ_n t} f̂(n)`.
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal FourierTransform

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem continuous_gauss1 (t : ℝ) : Continuous (gauss1 t) := by unfold gauss1; fun_prop

theorem integrable_sq_mul_gauss1 {t : ℝ} (ht : 0 < t) : Integrable fun s => s ^ 2 * gauss1 t s := by
  have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / (4 * t)) (by positivity)
    (s := 2) (by norm_num)
  refine (h.const_mul ((4 * π * t) ^ (-(1 : ℝ) / 2))).congr (Eventually.of_forall fun s => ?_)
  simp only [gauss1, Real.rpow_two]
  rw [show -(1 / (4 * t)) * s ^ 2 = -s ^ 2 / (4 * t) by ring]; ring

/-- The second derivative of `g_t`. -/
noncomputable def d2gauss1 (t s : ℝ) : ℝ := (s ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gauss1 t s

theorem hasDerivAt_dgauss1 {t : ℝ} (ht : 0 < t) (s : ℝ) :
    HasDerivAt (fun s => -(s / (2 * t)) * gauss1 t s) (d2gauss1 t s) s := by
  have h1 : HasDerivAt (fun s : ℝ => -(s / (2 * t))) (-(1 / (2 * t))) s := by
    have := (hasDerivAt_id s).const_mul (-(1 / (2 * t)))
    convert this using 1
    · funext x; simp only [id]; ring
    · ring
  have := h1.mul (hasDerivAt_gauss1 t s)
  convert this using 1
  unfold d2gauss1; field_simp; ring

theorem d2gauss1_fourier {t : ℝ} (ht : 0 < t) (n : ℤ) :
    ∫ s : ℝ, (d2gauss1 t s : ℂ) * cexp (-(2 * π * I * n * s)) =
      (2 * π * I * n) ^ 2 * (Real.exp (-(4 * π ^ 2) * (n : ℝ) ^ 2 * t) : ℂ) := by
  set f : ℝ → ℂ := fun s => ((-(s / (2 * t)) * gauss1 t s : ℝ) : ℂ) with hf
  have hd : ∀ s, HasDerivAt f (d2gauss1 t s : ℂ) s := fun s => (hasDerivAt_dgauss1 ht s).ofReal_comp
  have hderiv : deriv f = fun s => (d2gauss1 t s : ℂ) := funext fun s => (hd s).deriv
  have hc := continuous_gauss1 t
  have hfi : Integrable f := by
    refine Integrable.ofReal ?_
    refine ((integrable_abs_mul_gauss1 ht).div_const (2 * t)).mono'
      ((continuous_id.div_const _).neg.mul hc).aestronglyMeasurable (Eventually.of_forall fun s => ?_)
    show |(-(s / (2 * t))) * gauss1 t s| ≤ |s| * gauss1 t s / (2 * t)
    rw [abs_mul, abs_neg, abs_div, abs_of_pos (by positivity : 0 < 2 * t),
      abs_of_pos (gauss1_pos ht s)]
    exact le_of_eq (by ring)
  have hdi : Integrable (deriv f) := by
    rw [hderiv]
    refine Integrable.ofReal ?_
    have := ((integrable_sq_mul_gauss1 ht).div_const (4 * t ^ 2)).sub
      ((integrable_gauss1 ht).div_const (2 * t))
    refine this.congr (Eventually.of_forall fun s => ?_)
    show s ^ 2 * gauss1 t s / (4 * t ^ 2) - gauss1 t s / (2 * t) =
      (s ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gauss1 t s
    ring
  have hF := congrFun (Real.fourier_deriv hfi (fun s => (hd s).differentiableAt) hdi) (n : ℝ)
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul] at hF
  have e1 : ∀ s : ℝ, cexp (((-2 * π * s * (n : ℝ) : ℝ) : ℂ) * I) • deriv f s =
      (d2gauss1 t s : ℂ) * cexp (-(2 * π * I * n * s)) := fun s => by
    rw [hderiv, smul_eq_mul, mul_comm]
    congr 2; push_cast; ring
  have e2 : ∀ s : ℝ, cexp (((-2 * π * s * (n : ℝ) : ℝ) : ℂ) * I) • f s =
      ((-(s / (2 * t)) * gauss1 t s : ℝ) : ℂ) * cexp (-(2 * π * I * n * s)) := fun s => by
    rw [hf, smul_eq_mul, mul_comm]
    congr 2; push_cast; ring
  simp_rw [e1, e2] at hF
  rw [hF, dgauss1_fourier ht n, smul_eq_mul]
  push_cast; ring

theorem integrable_d2gauss1 {t : ℝ} (ht : 0 < t) : Integrable (d2gauss1 t) := by
  have := ((integrable_sq_mul_gauss1 ht).div_const (4 * t ^ 2)).sub
    ((integrable_gauss1 ht).div_const (2 * t))
  refine this.congr (Eventually.of_forall fun s => ?_)
  show s ^ 2 * gauss1 t s / (4 * t ^ 2) - gauss1 t s / (2 * t) =
    (s ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * gauss1 t s
  ring

theorem continuous_d2gauss1 (t : ℝ) : Continuous (d2gauss1 t) := by
  unfold d2gauss1; exact (by fun_prop : Continuous fun s : ℝ => s ^ 2 / (4 * t ^ 2) - 1 / (2 * t)).mul
    (continuous_gauss1 t)

/-- One term `∂ⱼ²G_t` of the Laplacian kernel, as a product. -/
noncomputable def lapTerm (t : ℝ) (j : ι) (y : ι → ℝ) : ℝ :=
  ∏ i, if i = j then d2gauss1 t (y i) else gauss1 t (y i)

/-- The Laplacian kernel `ΔG_t = ∑ⱼ ∂ⱼ²G_t`. -/
noncomputable def lapKer (t : ℝ) (y : ι → ℝ) : ℝ := ∑ j, lapTerm t j y

theorem integrable_lapTerm {t : ℝ} (ht : 0 < t) (j : ι) : Integrable (lapTerm t j) := by
  unfold lapTerm
  exact Integrable.fintype_prod (f := fun i s => if i = j then d2gauss1 t s else gauss1 t s)
    fun i => by
      by_cases hi : i = j
      · simp only [hi, if_true]; exact integrable_d2gauss1 ht
      · simp only [hi, if_false]; exact integrable_gauss1 ht

theorem continuous_lapTerm (t : ℝ) (j : ι) : Continuous (lapTerm t j) := by
  unfold lapTerm
  refine continuous_finset_prod _ fun i _ => ?_
  by_cases hi : i = j
  · subst hi; simp only [if_true]; exact (continuous_d2gauss1 t).comp (continuous_apply _)
  · simp only [hi, if_false]; exact (continuous_gauss1 t).comp (continuous_apply i)

theorem integrable_lapKer {t : ℝ} (ht : 0 < t) : Integrable (lapKer (ι := ι) t) := by
  unfold lapKer
  exact integrable_finsetSum _ fun j _ => integrable_lapTerm ht j

theorem continuous_lapKer (t : ℝ) : Continuous (lapKer (ι := ι) t) := by
  unfold lapKer; exact continuous_finset_sum _ fun j _ => continuous_lapTerm t j

theorem lapTerm_fourier {t : ℝ} (ht : 0 < t) (j : ι) (n : ι → ℤ) :
    ∫ y : ι → ℝ, (lapTerm t j y : ℂ) * mFourier (-n) (liftT y) =
      (2 * π * I * n j) ^ 2 * (heatMult t n : ℂ) := by
  set h : ι → ℝ → ℝ := fun i s => if i = j then d2gauss1 t s else gauss1 t s with hh
  have hy : ∀ y : ι → ℝ, (lapTerm t j y : ℂ) * mFourier (-n) (liftT y) =
      ∏ i, ((h i (y i) : ℂ) * cexp (-(2 * π * I * n i * y i))) := by
    intro y
    rw [lapTerm, heat_mFourier_liftT, ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    simp only [Pi.neg_apply, Int.cast_neg]
    ring_nf
  simp_rw [hy]
  rw [volume_pi, integral_fintype_prod_eq_prod (μ := fun _ => (volume : Measure ℝ))
    (fun i s => (h i s : ℂ) * cexp (-(2 * π * I * n i * s)))]
  have hval : ∀ i, ∫ s : ℝ, (h i s : ℂ) * cexp (-(2 * π * I * n i * s)) =
      (if i = j then (2 * π * I * n j) ^ 2 else 1) *
        (Real.exp (-(4 * π ^ 2) * (n i : ℝ) ^ 2 * t) : ℂ) := by
    intro i
    by_cases hi : i = j
    · subst hi; simp only [hh, if_true]; rw [d2gauss1_fourier ht]
    · simp only [hh, if_neg hi, one_mul]; exact gauss1_fourier ht (n i)
  simp_rw [hval]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ j, if_pos (Finset.mem_univ j),
    heatMult, ofReal_prod]

theorem lapKer_fourier {t : ℝ} (ht : 0 < t) (n : ι → ℤ) :
    ∫ y : ι → ℝ, (lapKer t y : ℂ) * mFourier (-n) (liftT y) = -(lamN n : ℂ) * (heatMult t n : ℂ) := by
  have hi : ∀ j, Integrable fun y : ι → ℝ => (lapTerm t j y : ℂ) * mFourier (-n) (liftT y) := fun j =>
    ((integrable_lapTerm ht j).ofReal (𝕜 := ℂ)).mul_bdd (c := 1)
      ((mFourier (-n)).continuous.comp continuous_liftT).aestronglyMeasurable
      (Eventually.of_forall fun y => norm_mFourier_le _ _)
  simp_rw [lapKer, ofReal_sum, Finset.sum_mul]
  rw [integral_finsetSum _ fun j _ => hi j]
  simp_rw [lapTerm_fourier ht]
  rw [← Finset.sum_mul, lamN]
  push_cast
  congr 1
  rw [neg_eq_neg_one_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring_nf; rw [I_sq]; ring

/-- `Δe^{tΔ}f`. -/
noncomputable def lapHeat (t : ℝ) (f : UnitAddTorus ι → ℝ) (x : UnitAddTorus ι) : ℝ :=
  ∫ y : ι → ℝ, lapKer t y * f (x - liftT y)

theorem cf_lapHeat {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) (n : ι → ℤ) :
    cf (lapHeat t f) n = -(lamN n : ℂ) * (heatMult t n * cf f n) := by
  unfold lapHeat
  rw [cf_conv (continuous_lapKer t).measurable (integrable_lapKer ht) hf hB, lapKer_fourier ht]
  ring

theorem measurable_lapHeat_joint {t : ℝ} {ρ : ℝ → UnitAddTorus ι → ℝ}
    (hρ : Measurable (Function.uncurry ρ)) :
    Measurable fun p : ℝ × UnitAddTorus ι => lapHeat t (ρ p.1) p.2 := by
  unfold lapHeat
  have hm : StronglyMeasurable (fun q : (ℝ × UnitAddTorus ι) × (ι → ℝ) =>
      lapKer t q.2 * ρ q.1.1 (q.1.2 - liftT q.2)) :=
    (((continuous_lapKer t).measurable.comp measurable_snd).mul
      (hρ.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).sub (measurable_liftT.comp measurable_snd))))).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

theorem abs_lapHeat_le {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ} {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) (x : UnitAddTorus ι) :
    |lapHeat t f x| ≤ (∫ y, |lapKer (ι := ι) t y|) * B := by
  unfold lapHeat
  rw [← Real.norm_eq_abs, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((integrable_lapKer ht).abs.mul_const B)
    (Eventually.of_forall fun y => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)

end SharpLSI
