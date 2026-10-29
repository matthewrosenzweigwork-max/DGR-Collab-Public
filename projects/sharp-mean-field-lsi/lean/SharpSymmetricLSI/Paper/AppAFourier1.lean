import SharpSymmetricLSI.Paper.AppAPicard5
import SharpSymmetricLSI.Paper.FourierSynth

/-!
# Fourier coefficients of `e^{tΔ}` and `∇·e^{tΔ}` on `𝕋^ι`

* `cf_conv`: for an integrable kernel `K` on `ℝ^ι` and bounded measurable `F`,
  the coefficients of `x ↦ ∫ K(y) F(x - y) dy` are `K̂(n) F̂(n)`.
* `dgauss_fourier`: `∫ ∂ₖG_t(y) e^{-2πin·y} dy = 2πi nₖ e^{-4π²|n|²t}`.
* `cf_heatT`, `cf_divHeatT`: `(e^{tΔ}f)^(n) = e^{-4π²|n|²t} f̂(n)`,
  `(∇·e^{tΔ}F)^(n) = ∑ₖ 2πi nₖ e^{-4π²|n|²t} F̂ₖ(n)`.
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal FourierTransform

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem mFourier_add_pt_appA (n : ι → ℤ) (x y : UnitAddTorus ι) :
    mFourier n (x + y) = mFourier n x * mFourier n y := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- Coefficients of a torus convolution with an integrable kernel on `ℝ^ι`. -/
theorem cf_conv {K : (ι → ℝ) → ℝ} (hKm : Measurable K) (hK : Integrable K)
    {F : UnitAddTorus ι → ℝ} (hF : Measurable F) {B : ℝ} (hB : ∀ x, |F x| ≤ B) (n : ι → ℤ) :
    cf (fun x => ∫ y, K y * F (x - liftT y)) n =
      (∫ y, (K y : ℂ) * mFourier (-n) (liftT y)) * cf F n := by
  simp only [cf]
  rw [mFourierCoeff_eq_integral, mFourierCoeff_eq_integral]
  have hFm : Measurable fun p : UnitAddTorus ι × (ι → ℝ) => F (p.1 - liftT p.2) :=
    hF.comp (measurable_fst.sub (measurable_liftT.comp measurable_snd))
  set H : UnitAddTorus ι × (ι → ℝ) → ℂ := fun p =>
    mFourier (-n) p.1 * ((K p.2 : ℂ) * (F (p.1 - liftT p.2) : ℂ)) with hH
  have hHi : Integrable H (volume.prod volume) := by
    refine ((integrable_const (1 : ℝ)).mul_prod (hK.abs.mul_const B)).mono' ?_
      (Eventually.of_forall fun p => ?_)
    · exact (((mFourier (-n)).continuous.measurable.comp measurable_fst).mul
        ((Complex.measurable_ofReal.comp (hKm.comp measurable_snd)).mul
          (Complex.measurable_ofReal.comp hFm))).aestronglyMeasurable
    · simp only [hH, norm_mul, Complex.norm_real, Real.norm_eq_abs, one_mul]
      have h1 := norm_mFourier_le (-n) p.1
      have h2 := hB (p.1 - liftT p.2)
      calc ‖mFourier (-n) p.1‖ * (|K p.2| * |F (p.1 - liftT p.2)|) ≤ 1 * (|K p.2| * B) := by
            gcongr
        _ = |K p.2| * B := one_mul _
  have e1 : (fun x => mFourier (-n) x • (((∫ y, K y * F (x - liftT y)) : ℝ) : ℂ)) =
      fun x => ∫ y, H (x, y) := by
    funext x
    rw [smul_eq_mul, ← integral_complex_ofReal, ← integral_const_mul]
    congr 1; funext y; simp only [hH]; push_cast; ring
  rw [e1, integral_integral_swap hHi]
  have e2 : ∀ y, ∫ x, H (x, y) = ((K y : ℂ) * mFourier (-n) (liftT y)) *
      ∫ x, mFourier (-n) x • (F x : ℂ) := by
    intro y
    have := integral_add_right_eq_self (μ := (volume : Measure (UnitAddTorus ι)))
      (fun x => H (x, y)) (liftT y)
    rw [← this]
    simp only [hH, add_sub_cancel_right, mFourier_add_pt_appA, smul_eq_mul]
    rw [← integral_const_mul]
    congr 1; funext x; ring
  simp_rw [e2]
  rw [integral_mul_const]

/-- The Fourier transform of `g_t'` at integers: `2πi n e^{-4π²n²t}`. -/
theorem dgauss1_fourier {t : ℝ} (ht : 0 < t) (n : ℤ) :
    ∫ s : ℝ, ((-(s / (2 * t)) * gauss1 t s : ℝ) : ℂ) * cexp (-(2 * π * I * n * s)) =
      2 * π * I * n * (Real.exp (-(4 * π ^ 2) * (n : ℝ) ^ 2 * t) : ℂ) := by
  set f : ℝ → ℂ := fun s => (gauss1 t s : ℂ) with hf
  have hd : ∀ s, HasDerivAt f ((-(s / (2 * t)) * gauss1 t s : ℝ) : ℂ) s := fun s =>
    (hasDerivAt_gauss1 t s).ofReal_comp
  have hderiv : deriv f = fun s => ((-(s / (2 * t)) * gauss1 t s : ℝ) : ℂ) :=
    funext fun s => (hd s).deriv
  have hfi : Integrable f := (integrable_gauss1 ht).ofReal
  have hdi : Integrable (deriv f) := by
    rw [hderiv]
    refine Integrable.ofReal ?_
    have := (integrable_abs_mul_gauss1 ht).div_const (2 * t)
    have hc : Continuous (gauss1 t) := by unfold gauss1; fun_prop
    refine this.mono' (((continuous_id.div_const _).neg.mul hc).aestronglyMeasurable)
      (Eventually.of_forall fun s => ?_)
    show |(-(s / (2 * t))) * gauss1 t s| ≤ |s| * gauss1 t s / (2 * t)
    rw [abs_mul, abs_neg, abs_div, abs_of_pos (by positivity : 0 < 2 * t),
      abs_of_pos (gauss1_pos ht s)]
    exact le_of_eq (by ring)
  have hF := congrFun (Real.fourier_deriv hfi (fun s => (hd s).differentiableAt) hdi) (n : ℝ)
  rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul] at hF
  have e1 : ∀ s : ℝ, cexp (((-2 * π * s * (n : ℝ) : ℝ) : ℂ) * I) • deriv f s =
      ((-(s / (2 * t)) * gauss1 t s : ℝ) : ℂ) * cexp (-(2 * π * I * n * s)) := fun s => by
    rw [hderiv, smul_eq_mul, mul_comm]
    congr 2; push_cast; ring
  have e2 : ∀ s : ℝ, cexp (((-2 * π * s * (n : ℝ) : ℝ) : ℂ) * I) • f s =
      (gauss1 t s : ℂ) * cexp (-(2 * π * I * n * s)) := fun s => by
    rw [hf, smul_eq_mul, mul_comm]
    congr 2; push_cast; ring
  simp_rw [e1, e2] at hF
  rw [hF, gauss1_fourier ht n, smul_eq_mul]
  push_cast; ring

/-- The Fourier transform of `∂ₖG_t` at integer frequencies. -/
theorem dheatKernel_fourier {t : ℝ} (ht : 0 < t) (k : ι) (n : ι → ℤ) :
    ∫ y : ι → ℝ, (fderiv ℝ (heatKernel t) y (Pi.single k 1) : ℂ) * mFourier (-n) (liftT y) =
      2 * π * I * n k * (heatMult t n : ℂ) := by
  set h : ι → ℝ → ℝ := fun i s => if i = k then -(s / (2 * t)) * gauss1 t s else gauss1 t s
    with hh
  have hy : ∀ y : ι → ℝ, (fderiv ℝ (heatKernel t) y (Pi.single k 1) : ℂ) *
      mFourier (-n) (liftT y) = ∏ i, ((h i (y i) : ℂ) * cexp (-(2 * π * I * n i * y i))) := by
    intro y
    rw [fderiv_heatKernel_single ht, heat_mFourier_liftT]
    have e : -(heatKernel t y * y k / (2 * t)) = ∏ i, h i (y i) := by
      rw [heatKernel_eq_prod ht, hh]
      simp only
      rw [Finset.prod_ite, Finset.filter_eq', if_pos (Finset.mem_univ k), Finset.prod_singleton,
        ← Finset.prod_mul_prod_compl {k} (fun i => gauss1 t (y i)), Finset.prod_singleton]
      have : (Finset.univ.filter fun i => i ≠ k) = ({k} : Finset ι)ᶜ := by
        ext i; simp
      rw [this]; ring
    rw [e, ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    simp only [Pi.neg_apply, Int.cast_neg]
    ring_nf
  simp_rw [hy]
  rw [volume_pi, integral_fintype_prod_eq_prod (μ := fun _ => (volume : Measure ℝ))
    (fun i s => (h i s : ℂ) * cexp (-(2 * π * I * n i * s)))]
  have hval : ∀ i, ∫ s : ℝ, (h i s : ℂ) * cexp (-(2 * π * I * n i * s)) =
      (if i = k then 2 * π * I * n k else 1) * (Real.exp (-(4 * π ^ 2) * (n i : ℝ) ^ 2 * t) : ℂ) := by
    intro i
    by_cases hi : i = k
    · subst hi; simp only [hh, if_true]; rw [dgauss1_fourier ht]
    · simp only [hh, if_neg hi, one_mul]; exact gauss1_fourier ht (n i)
  simp_rw [hval]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k),
    heatMult, ofReal_prod]

theorem integrable_heatKernel_fderiv {t : ℝ} (ht : 0 < t) (k : ι) :
    Integrable fun y : ι → ℝ => fderiv ℝ (heatKernel t) y (Pi.single k 1) :=
  integrable_fderiv_heatKernel ht k

/-- **Fourier coefficients of `e^{tΔ}f`.** -/
theorem cf_heatT {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) (n : ι → ℤ) : cf (heatT t f) n = heatMult t n * cf f n := by
  have e : heatT t f = fun x => ∫ y, heatKernel t y * f (x - liftT y) := by
    funext x; unfold heatT; congr 1; funext y; ring
  rw [e, cf_conv (measurable_heatKernel t) (integrable_heatKernel ht) hf hB, gauss_fourier ht]

/-- The kernel gradient `∇e^{tΔ}f` (a weak gradient of `e^{tΔ}f`). -/
noncomputable def gradHeat (t : ℝ) (f : UnitAddTorus ι → ℝ) (x : UnitAddTorus ι) (j : ι) : ℝ :=
  ∫ y : ι → ℝ, fderiv ℝ (heatKernel t) y (Pi.single j 1) * f (x - liftT y)

theorem cf_gradHeat {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) (j : ι) (n : ι → ℤ) :
    cf (fun x => gradHeat t f x j) n = 2 * π * I * n j * (heatMult t n * cf f n) := by
  unfold gradHeat
  rw [cf_conv (measurable_fderiv_heatKernel ht j) (integrable_fderiv_heatKernel ht j) hf hB,
    dheatKernel_fourier ht]
  ring

theorem measurable_gradHeat {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ} (hf : Measurable f)
    (j : ι) : Measurable fun x => gradHeat t f x j := by
  unfold gradHeat
  have hm : StronglyMeasurable (fun p : UnitAddTorus ι × (ι → ℝ) =>
      fderiv ℝ (heatKernel t) p.2 (Pi.single j 1) * f (p.1 - liftT p.2)) :=
    (((measurable_fderiv_heatKernel ht j).comp measurable_snd).mul
      (hf.comp (measurable_fst.sub (measurable_liftT.comp measurable_snd)))).stronglyMeasurable
  exact hm.integral_prod_right'.measurable

theorem abs_gradHeat_le {t : ℝ} (ht : 0 < t) {f : UnitAddTorus ι → ℝ} {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) (x : UnitAddTorus ι) (j : ι) : |gradHeat t f x j| ≤ divConst t * B := by
  unfold gradHeat
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le ((integrable_fderiv_heatKernel ht j).abs.mul_const B)
    (Eventually.of_forall fun y => ?_)).trans (le_of_eq ?_)
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB _) (abs_nonneg _)
  · rw [integral_mul_const, integral_abs_fderiv_heatKernel ht j, divConst]

theorem cf_sum {κ : Type*} (s : Finset κ) {g : κ → UnitAddTorus ι → ℝ}
    (hg : ∀ k ∈ s, Integrable (g k)) (n : ι → ℤ) :
    cf (fun x => ∑ k ∈ s, g k x) n = ∑ k ∈ s, cf (g k) n := by
  simp only [cf]
  simp_rw [mFourierCoeff_eq_integral]
  push_cast
  simp_rw [Finset.smul_sum]
  refine integral_finsetSum _ fun k hk => ?_
  have := ((hg k hk).ofReal (𝕜 := ℂ)).bdd_mul (c := 1) (mFourier (-n)).continuous.aestronglyMeasurable
    (Eventually.of_forall fun y => norm_mFourier_le (-n) y)
  simp only [smul_eq_mul]
  exact this

/-- **Fourier coefficients of `∇·e^{tΔ}F`.** -/
theorem cf_divHeatT {t : ℝ} (ht : 0 < t) {F : UnitAddTorus ι → ι → ℝ}
    (hF : ∀ k, Measurable fun z => F z k) {B : ℝ} (hB : ∀ z k, |F z k| ≤ B) (n : ι → ℤ) :
    cf (divHeatT t F) n = ∑ k, 2 * π * I * n k * (heatMult t n * cf (fun z => F z k) n) := by
  have e : divHeatT t F = fun x => ∑ k, gradHeat t (fun z => F z k) x k := by
    funext x; rfl
  rw [e, cf_sum _ fun k _ => ?_]
  · exact Finset.sum_congr rfl fun k _ => cf_gradHeat ht (hF k) (fun z => hB z k) k n
  · exact (MemLp.of_bound (measurable_gradHeat ht (hF k) k).aestronglyMeasurable (divConst t * B)
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact abs_gradHeat_le ht (fun z => hB z k) x k)).integrable le_top

end SharpLSI
