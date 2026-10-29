import DGPS.Foundations.SobolevFourier
import SharpSymmetricLSI.Infra.HeatTorus

/-!
# FOU007: The periodized Gaussian heat kernel on the torus

For `t > 0` the kernel `K_t(x) = ∑_{n ∈ ℤ^d} (4πt)^{-d/2} exp(-|x+n|²/(4t))` on `𝕋^d = ℝ^d/ℤ^d`
(`DGPS.periodizedGaussian`, summed over the lattice) is identified with the Fourier-side (theta /
Poisson) kernel `SharpLSI.heatP` (`periodizedGaussian_eq_heatPL`, `heatKernelT_torusLift`); the
rest is proved for that carrier, with Fourier coefficients `e^{-4π²|k|²t}`.

Main results:
* `K_t` is positive, smooth periodic, even, of Haar integral `1`, with
  `fourierCoeff K_t k = exp(-(gradWeight k * t))` and `K_t ⋆ K_s = K_{t+s}`
  (`heatKernelT_conv`, via Fourier uniqueness for continuous functions).
* `H_t f = K_t ⋆ f` (`heatOp`, convolution `torusConv`) has Fourier multiplier
  `exp(-(gradWeight k * t))`, is self-adjoint, positivity and mass preserving,
  an `Lᵖ` contraction (`1 ≤ p < ∞`), and satisfies `H_t H_s = H_{t+s}`.
* `tendsto_eLpNorm_heatOp_sub`: `H_t f → f` in `Lᵖ` as `t → 0⁺` (Parseval for bounded continuous
  functions, interpolation, then density).
* `IsWeakGradient.heatOp`: `∇ H_t u = H_t ∇ u` componentwise; `tendsto_H1_heatOp`: strong `H¹`
  convergence.
* `DGPS.Analysis.periodized_gaussian_heat_kernel`: the FOU007 bundle.
-/

open MeasureTheory Filter Topology Set UnitAddTorus
open scoped Real ENNReal ComplexConjugate

namespace DGPS

variable {d : ℕ}

/-- The one-dimensional Gaussian `(4πt)^{-1/2} e^{-s²/(4t)}`. -/
noncomputable def gauss1 (t s : ℝ) : ℝ :=
  (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-s ^ 2 / (4 * t))

/-- The periodized Gaussian on `ℝ^d`. -/
noncomputable def periodizedGaussian (t : ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑' n : Fin d → ℤ,
    (4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(∑ j, (x j + (n j : ℝ)) ^ 2) / (4 * t))

theorem gaussian_eq_prod {t : ℝ} (ht : 0 < t) (y : Fin d → ℝ) :
    (4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(∑ j, y j ^ 2) / (4 * t)) =
      ∏ j, gauss1 t (y j) := by
  unfold gauss1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum]
  congr 1
  · rw [← Real.rpow_mul_natCast (by positivity)]
    congr 1; ring
  · congr 1
    simp only [← Finset.sum_neg_distrib, Finset.sum_div]

theorem gauss1_nonneg (t s : ℝ) (ht : 0 < t) : 0 ≤ gauss1 t s := by
  unfold gauss1; positivity

theorem gauss1_add_int {t : ℝ} (ht : 0 < t) (x : ℝ) (n : ℤ) :
    gauss1 t (x + n) = (4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2 / (4 * t)) *
      Real.exp ((-n : ℤ) * x / (2 * t) - ((-n : ℤ) : ℝ) ^ 2 / (4 * t)) := by
  unfold gauss1
  rw [mul_assoc ((4 * π * t) ^ (-(1 : ℝ) / 2)), ← Real.exp_add]
  congr 2
  push_cast
  field_simp
  ring

theorem summable_gauss1_add_int {t : ℝ} (ht : 0 < t) (x : ℝ) :
    Summable fun n : ℤ => gauss1 t (x + n) := by
  have h := (SharpLSI.summable_theta_real ht x)
  have h2 := (Equiv.neg ℤ).summable_iff.mpr h
  have h3 := h2.mul_left ((4 * π * t) ^ (-(1 : ℝ) / 2) * Real.exp (-x ^ 2 / (4 * t)))
  refine h3.congr fun n => ?_
  rw [gauss1_add_int ht]
  simp only [Function.comp_apply, Equiv.neg_apply]

theorem tsum_gauss1_add_int {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ∑' n : ℤ, gauss1 t (x + n) = SharpLSI.heatK t x := by
  have hK : SharpLSI.heatK t x =
      1 / (4 * π * t) ^ (1 / 2 : ℝ) * Real.exp (-x ^ 2 / (4 * t)) *
        ∑' n : ℤ, Real.exp (n * x / (2 * t) - n ^ 2 / (4 * t)) := by
    unfold SharpLSI.heatK
    rw [SharpLSI.heatSeries_one_eq_theta, SharpLSI.theta_eq_real ht, Complex.ofReal_re]
  rw [hK]
  simp_rw [gauss1_add_int ht]
  rw [tsum_mul_left]
  have := (Equiv.neg ℤ).tsum_eq (fun n : ℤ => Real.exp (n * x / (2 * t) - (n:ℝ) ^ 2 / (4 * t)))
  simp only [Equiv.neg_apply] at this
  rw [this]
  rw [one_div, ← Real.rpow_neg (by positivity)]
  congr 2
  norm_num

theorem prod_tsum_step (d : ℕ) (g : Fin (d+1) → ℤ → ℝ) (h0 : ∀ j m, 0 ≤ g j m) (hs : ∀ j, Summable (g j))
   (ih1 : Summable (fun n : Fin d → ℤ => ∏ j : Fin d, g j.succ (n j)))
   (ih2 : ∑' n : Fin d → ℤ, ∏ j : Fin d, g j.succ (n j) = ∏ j : Fin d, ∑' m, g j.succ m) :
    Summable (fun n : Fin (d+1) → ℤ => ∏ j : Fin (d+1), g j (n j)) ∧
      ∑' n : Fin (d+1) → ℤ, ∏ j : Fin (d+1), g j (n j) = ∏ j : Fin (d+1), ∑' m, g j m := by
  let E : (Fin (d + 1) → ℤ) ≃ ℤ × (Fin d → ℤ) := (Fin.consEquiv fun _ => ℤ).symm
  set F : ℤ × (Fin d → ℤ) → ℝ := fun z => g 0 z.1 * ∏ j : Fin d, g j.succ (z.2 j) with hF
  have key : ∀ n : Fin (d + 1) → ℤ, ∏ j : Fin (d+1), g j (n j) = F (E n) := fun n => by
    rw [Fin.prod_univ_succ]
    simp [E, F, Fin.consEquiv, Fin.tail]
  have hsum : Summable F :=
      Summable.mul_of_nonneg (f := g 0) (g := fun n : Fin d → ℤ => ∏ j : Fin d, g j.succ (n j)) (hs 0) ih1 (fun m => h0 _ _)
        (fun n => Finset.prod_nonneg fun j _ => h0 _ _)
  have hfun : (fun n : Fin (d + 1) → ℤ => ∏ j : Fin (d+1), g j (n j)) = F ∘ E := funext key
  have hS : Summable (fun n : Fin (d + 1) → ℤ => ∏ j : Fin (d+1), g j (n j)) := by
    rw [hfun]; exact (E.summable_iff (f := F)).mpr hsum
  have hT : ∑' n : Fin (d + 1) → ℤ, ∏ j : Fin (d+1), g j (n j) = ∑' z, F z := by
    rw [hfun]; exact E.tsum_eq F
  refine ⟨hS, ?_⟩
  rw [hT, Fin.prod_univ_succ, ← ih2, tsum_mul_tsum_of_summable_norm (hs 0).norm ih1.norm]

theorem summable_prod_tsum_prod_fin : ∀ (d : ℕ) (g : Fin d → ℤ → ℝ), (∀ j m, 0 ≤ g j m) →
    (∀ j, Summable (g j)) →
    Summable (fun n : Fin d → ℤ => ∏ j, g j (n j)) ∧
      ∑' n : Fin d → ℤ, ∏ j, g j (n j) = ∏ j, ∑' m, g j m
  | 0, g, _, _ => by
    have : Finite (Fin 0 → ℤ) := Finite.of_subsingleton
    refine ⟨Summable.of_finite, ?_⟩
    rw [tsum_eq_single (fun j => j.elim0) (fun n hn => absurd (Subsingleton.elim _ _) hn)]
    simp
  | d + 1, g, h0, hs => by
    obtain ⟨ih1, ih2⟩ := summable_prod_tsum_prod_fin d (fun j => g j.succ)
      (fun j m => h0 _ _) (fun j => hs _)
    exact prod_tsum_step d g h0 hs ih1 ih2

theorem periodizedGaussian_eq_heatPL {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) :
    periodizedGaussian t x = SharpLSI.heatPL t x := by
  unfold periodizedGaussian SharpLSI.heatPL
  have h1 : ∀ n : Fin d → ℤ, (4 * π * t) ^ (-(d : ℝ) / 2) *
      Real.exp (-(∑ j, (x j + (n j : ℝ)) ^ 2) / (4 * t)) = ∏ j, gauss1 t (x j + (n j : ℝ)) :=
    fun n => gaussian_eq_prod ht (fun j => x j + (n j : ℝ))
  simp_rw [h1]
  obtain ⟨_, h2⟩ := summable_prod_tsum_prod_fin d (fun j m => gauss1 t (x j + (m : ℝ)))
    (fun j m => gauss1_nonneg t _ ht) (fun j => summable_gauss1_add_int ht _)
  rw [h2]
  exact Finset.prod_congr rfl fun j _ => tsum_gauss1_add_int ht _

/-! ### The kernel on the torus -/

/-- The periodic heat kernel `K_t` on `𝕋^d` (legacy carrier `SharpLSI.heatP`), which by
`heatKernelT_torusLift` is the periodized Gaussian. -/
noncomputable abbrev heatKernelT (t : ℝ) : Torus d → ℝ := SharpLSI.heatP t

theorem heatKernelT_torusLift {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) :
    heatKernelT t (torusLift x) = periodizedGaussian t x := by
  rw [periodizedGaussian_eq_heatPL ht]
  exact SharpLSI.heatP_liftT t x

theorem periodizedGaussian_add_intVec {t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) (m : Fin d → ℤ) :
    periodizedGaussian t (x + fun j => (m j : ℝ)) = periodizedGaussian t x := by
  rw [periodizedGaussian_eq_heatPL ht, periodizedGaussian_eq_heatPL ht]
  exact SharpLSI.heatPL_add_intVec t x m


/-! ### Fourier coefficients of the kernel -/

theorem mFourier_liftT_eq (n : Fin d → ℤ) (x : Fin d → ℝ) :
    mFourier n (torusLift x) = ∏ i, Complex.exp (2 * π * Complex.I * n i * x i) := by
  simp only [mFourier, ContinuousMap.coe_mk, torusLift, SharpLSI.liftT, fourier_coe_apply,
    Complex.ofReal_one, div_one]

theorem integral_torus_eq_box' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : Torus d → E} (hg : AEStronglyMeasurable g (haar d)) :
    ∫ z, g z ∂haar d = ∫ x in SharpLSI.unitBox (Fin d), g (torusLift x) := by
  rw [haar_eq_map_unitBox] at hg ⊢
  exact integral_map SharpLSI.measurable_liftT.aemeasurable hg

theorem volume_restrict_unitBox' :
    (volume : Measure (Fin d → ℝ)).restrict (SharpLSI.unitBox (Fin d)) =
      Measure.pi fun _ => (volume : Measure ℝ).restrict (Ioc 0 1) := by
  rw [SharpLSI.unitBox, ← Measure.restrict_pi_pi, volume_pi]

theorem integral_unitBox_prod' (f : Fin d → ℝ → ℂ) :
    ∫ x in SharpLSI.unitBox (Fin d), ∏ i, f i (x i) = ∏ i, ∫ y in Ioc (0 : ℝ) 1, f i y := by
  rw [volume_restrict_unitBox']
  exact integral_fintype_prod_eq_prod (μ := fun _ => (volume : Measure ℝ).restrict (Ioc 0 1)) f

theorem prod_exp_eq (t : ℝ) (k : Fin d → ℤ) :
    ∏ i, Real.exp (-(4 * π ^ 2) * (k i : ℝ) ^ 2 * t) = Real.exp (-(gradWeight k * t)) := by
  rw [← Real.exp_sum]
  congr 1
  unfold gradWeight
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Fourier coefficients of the torus kernel (adapted from the legacy `heatP_fourier`). -/
theorem heatKernelT_fourier {t : ℝ} (ht : 0 < t) (k : Fin d → ℤ) :
    ∫ z, (heatKernelT t z : ℂ) * mFourier (-k) z ∂haar d =
      (Real.exp (-(gradWeight k * t)) : ℂ) := by
  rw [integral_torus_eq_box' (by
    exact ((Complex.continuous_ofReal.comp (SharpLSI.continuous_heatP ht)).mul
      (mFourier (-k)).continuous).aestronglyMeasurable)]
  have h : ∀ x : Fin d → ℝ, (heatKernelT t (torusLift x) : ℂ) * mFourier (-k) (torusLift x) =
      ∏ i, ((SharpLSI.heatK t (x i) : ℂ) *
        Complex.exp (-(2 * π * Complex.I * k i * x i))) := by
    intro x
    rw [heatKernelT, SharpLSI.heatP_liftT, mFourier_liftT_eq, SharpLSI.heatPL,
      Complex.ofReal_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    simp only [Pi.neg_apply, Int.cast_neg]
    ring_nf
  simp_rw [h]
  rw [integral_unitBox_prod' (fun i y => (SharpLSI.heatK t y : ℂ) *
    Complex.exp (-(2 * π * Complex.I * k i * y))), ← prod_exp_eq, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← intervalIntegral.integral_of_le zero_le_one, SharpLSI.heatK_fourier ht]

theorem integral_heatKernelT {t : ℝ} (ht : 0 < t) : ∫ z, heatKernelT t z ∂haar d = 1 := by
  have h := heatKernelT_fourier (d := d) ht 0
  simp only [neg_zero, mFourier_zero, ContinuousMap.one_apply, mul_one, gradWeight,
    Pi.zero_apply, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, mul_zero, zero_mul, neg_zero, Real.exp_zero, Complex.ofReal_one] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-! ### Evenness of the kernel -/

theorem periodizedGaussian_neg (t : ℝ) (x : Fin d → ℝ) :
    periodizedGaussian t (-x) = periodizedGaussian t x := by
  unfold periodizedGaussian
  have h0 := Equiv.tsum_eq (Equiv.neg (Fin d → ℤ)) (fun n : Fin d → ℤ =>
    (4 * π * t) ^ (-(d : ℝ) / 2) * Real.exp (-(∑ j, (x j + (n j : ℝ)) ^ 2) / (4 * t)))
  rw [← h0]
  refine tsum_congr fun n => ?_
  have hs : ∑ j, (-x j + (n j : ℝ)) ^ 2 = ∑ j, (x j + (((-n) j : ℤ) : ℝ)) ^ 2 :=
    Finset.sum_congr rfl fun j _ => by simp only [Pi.neg_apply, Int.cast_neg]; ring
  simp only [Pi.neg_apply, Equiv.neg_apply] at hs ⊢
  rw [hs]

theorem torusLift_neg (x : Fin d → ℝ) : torusLift (-x) = -torusLift x := by
  funext i
  simp [torusLift, SharpLSI.liftT]

theorem heatKernelT_neg {t : ℝ} (ht : 0 < t) (z : Torus d) :
    heatKernelT t (-z) = heatKernelT t z := by
  have hz : z = torusLift (SharpLSI.secT z) := (SharpLSI.liftT_secT z).symm
  rw [hz, ← torusLift_neg, heatKernelT_torusLift ht, heatKernelT_torusLift ht,
    periodizedGaussian_neg]

theorem heatKernelT_sub_comm {t : ℝ} (ht : 0 < t) (y w : Torus d) :
    heatKernelT t (y - w) = heatKernelT t (w - y) := by
  rw [← neg_sub, heatKernelT_neg ht]

theorem heatKernelT_pos {t : ℝ} (ht : 0 < t) (z : Torus d) : 0 < heatKernelT t z :=
  SharpLSI.heatP_pos ht z

theorem continuous_heatKernelT {t : ℝ} (ht : 0 < t) : Continuous (heatKernelT (d := d) t) :=
  SharpLSI.continuous_heatP ht

/-- `K_t` is smooth and periodic. -/
theorem isSmoothPeriodic_heatKernelT {t : ℝ} (ht : 0 < t) : IsSmoothPeriodic (heatKernelT (d := d) t) := by
  have : (heatKernelT (d := d) t) ∘ torusLift = SharpLSI.heatPL t := by
    funext x; exact SharpLSI.heatP_liftT t x
  unfold IsSmoothPeriodic
  rw [this]
  exact SharpLSI.contDiff_heatPL ht

/-! ### Convolution on the torus -/

instance haar_isNegInvariant (d : ℕ) : (haar d).IsNegInvariant := Pi.isNegInvariant_volume

/-- Convolution `(K ⋆ f)(y) = ∫ K(y - w) f(w) dm(w)` on the torus. -/
noncomputable def torusConv (K f : Torus d → ℝ) (y : Torus d) : ℝ :=
  ∫ w, K (y - w) * f w ∂haar d

/-- The periodic heat semigroup `H_t f = K_t ⋆ f`. -/
noncomputable def heatOp (t : ℝ) (f : Torus d → ℝ) : Torus d → ℝ := torusConv (heatKernelT t) f

theorem exists_abs_le_of_continuous' {ψ : Torus d → ℝ} (hψ : Continuous ψ) :
    ∃ C, 0 ≤ C ∧ ∀ x, |ψ x| ≤ C := by
  obtain ⟨C, hC⟩ := exists_abs_le_of_continuous hψ
  exact ⟨max C 0, le_max_right _ _, fun x => (hC x).trans (le_max_left _ _)⟩

theorem integrable_conv_integrand {K f : Torus d → ℝ} (hK : Continuous K)
    (hf : Integrable f (haar d)) (y : Torus d) :
    Integrable (fun w => K (y - w) * f w) (haar d) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_le_of_continuous' hK
  refine Integrable.mono' (hf.norm.const_mul C)
    ((hK.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (Eventually.of_forall fun w => ?_)
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)

theorem continuous_torusConv {K f : Torus d → ℝ} (hK : Continuous K)
    (hf : Integrable f (haar d)) : Continuous (torusConv K f) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_le_of_continuous' hK
  refine continuous_of_dominated (bound := fun w => C * ‖f w‖) (fun y => ?_) (fun y => ?_)
    (hf.norm.const_mul C) (Eventually.of_forall fun w => ?_)
  · exact (integrable_conv_integrand hK hf y).aestronglyMeasurable
  · refine Eventually.of_forall fun w => ?_
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _)
  · exact (hK.comp (continuous_id.sub continuous_const)).mul continuous_const

theorem torusConv_congr_ae (K : Torus d → ℝ) {f g : Torus d → ℝ} (h : f =ᵐ[haar d] g) :
    torusConv K f = torusConv K g := by
  funext y
  unfold torusConv
  exact integral_congr_ae (h.mono fun w hw => by simp [hw])

theorem integrable_prod_conv {K f g : Torus d → ℝ} (hK : Continuous K)
    (hf : Integrable f (haar d)) (hg : Integrable g (haar d)) :
    Integrable (fun p : Torus d × Torus d => g p.1 * (K (p.1 - p.2) * f p.2))
      ((haar d).prod (haar d)) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_le_of_continuous' hK
  have hb : Integrable (fun p : Torus d × Torus d => ‖g p.1‖ * ‖f p.2‖) ((haar d).prod (haar d)) :=
    Integrable.mul_prod (f := fun x => ‖g x‖) (g := fun x => ‖f x‖) hg.norm hf.norm
  refine Integrable.mono' (hb.const_mul C) ?_ (Eventually.of_forall fun p => ?_)
  · exact (hg.aestronglyMeasurable.comp_fst).mul
      (((hK.comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
        hf.aestronglyMeasurable.comp_snd)
  · have hK' : ‖K (p.1 - p.2)‖ ≤ C := by simpa [Real.norm_eq_abs] using hC (p.1 - p.2)
    rw [norm_mul, norm_mul]
    calc ‖g p.1‖ * (‖K (p.1 - p.2)‖ * ‖f p.2‖) = ‖K (p.1 - p.2)‖ * (‖g p.1‖ * ‖f p.2‖) := by ring
      _ ≤ C * (‖g p.1‖ * ‖f p.2‖) :=
        mul_le_mul_of_nonneg_right hK' (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-! ### Fourier coefficients, mass, positivity, self-adjointness of the convolution -/

theorem fourierCoeff_torusConv {K f : Torus d → ℝ} (hK : Continuous K)
    (hf : Integrable f (haar d)) (k : Fin d → ℤ) :
    fourierCoeff (torusConv K f) k =
      (∫ z, (K z : ℂ) * mFourier (-k) z ∂haar d) * fourierCoeff f k := by
  unfold fourierCoeff
  rw [mFourierCoeff_ofReal_eq, mFourierCoeff_ofReal_eq]
  have h1 : ∀ y, mFourier (-k) y * (torusConv K f y : ℂ) =
      ∫ w, mFourier (-k) y * ((K (y - w) * f w : ℝ) : ℂ) ∂haar d := by
    intro y
    unfold torusConv
    rw [← integral_complex_ofReal, integral_const_mul]
  simp_rw [h1]
  have hm : AEStronglyMeasurable (fun p : Torus d × Torus d => K (p.1 - p.2) * f p.2)
      ((haar d).prod (haar d)) := by
    simpa using (integrable_prod_conv hK hf (integrable_const (1 : ℝ))).aestronglyMeasurable
  have hint : Integrable (Function.uncurry fun y w =>
      mFourier (-k) y * ((K (y - w) * f w : ℝ) : ℂ)) ((haar d).prod (haar d)) := by
    refine Integrable.mono' (integrable_prod_conv hK hf (integrable_const (1 : ℝ))).norm ?_
      (Eventually.of_forall fun p => ?_)
    · exact ((mFourier (-k)).continuous.comp continuous_fst).aestronglyMeasurable.mul
        (Complex.continuous_ofReal.comp_aestronglyMeasurable hm)
    · show ‖mFourier (-k) p.1 * ((K (p.1 - p.2) * f p.2 : ℝ) : ℂ)‖ ≤
        ‖(1 : ℝ) * (K (p.1 - p.2) * f p.2)‖
      rw [norm_mul, norm_mFourier_apply, one_mul, one_mul, Complex.norm_real]
  rw [integral_integral_swap hint]
  have h2 : ∀ w, ∫ y, mFourier (-k) y * ((K (y - w) * f w : ℝ) : ℂ) ∂haar d =
      (∫ z, (K z : ℂ) * mFourier (-k) z ∂haar d) * (mFourier (-k) w * (f w : ℂ)) := by
    intro w
    refine (integral_add_right_eq_self (μ := haar d)
      (fun y => mFourier (-k) y * ((K (y - w) * f w : ℝ) : ℂ)) w).symm.trans ?_
    have : ∀ z, mFourier (-k) (z + w) * ((K (z + w - w) * f w : ℝ) : ℂ) =
        (K z : ℂ) * mFourier (-k) z * (mFourier (-k) w * (f w : ℂ)) := by
      intro z; rw [mFourier_add_pt, add_sub_cancel_right]; push_cast; ring
    simp_rw [this]
    exact integral_mul_const _ _
  simp_rw [h2]
  rw [integral_const_mul]

theorem fourierCoeff_heatOp {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ} (hf : Integrable f (haar d))
    (k : Fin d → ℤ) :
    fourierCoeff (heatOp t f) k = (Real.exp (-(gradWeight k * t)) : ℂ) * fourierCoeff f k := by
  unfold heatOp
  rw [fourierCoeff_torusConv (continuous_heatKernelT ht) hf, heatKernelT_fourier ht]

theorem integral_torusConv {K f : Torus d → ℝ} (hK : Continuous K) (hf : Integrable f (haar d)) :
    ∫ y, torusConv K f y ∂haar d = (∫ z, K z ∂haar d) * ∫ w, f w ∂haar d := by
  have hint := integrable_prod_conv hK hf (integrable_const (1 : ℝ))
  have := integral_integral_swap (f := fun y w => (1 : ℝ) * (K (y - w) * f w)) hint
  simp only [one_mul] at this
  unfold torusConv
  rw [this]
  have h2 : ∀ w, ∫ y, K (y - w) * f w ∂haar d = (∫ z, K z ∂haar d) * f w := fun w => by
    rw [integral_mul_const, integral_sub_right_eq_self K w]
  simp_rw [h2]
  rw [integral_const_mul]

theorem integral_torusConv_mul {K f g : Torus d → ℝ} (hK : Continuous K)
    (hKe : ∀ z, K (-z) = K z) (hf : Integrable f (haar d)) (hg : Integrable g (haar d)) :
    ∫ y, torusConv K f y * g y ∂haar d = ∫ w, f w * torusConv K g w ∂haar d := by
  have hint := integrable_prod_conv hK hf hg
  have e1 : ∫ y, torusConv K f y * g y ∂haar d =
      ∫ y, ∫ w, g y * (K (y - w) * f w) ∂haar d ∂haar d := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [torusConv]; rw [integral_const_mul, mul_comm]
  have e2 : ∫ w, f w * torusConv K g w ∂haar d =
      ∫ w, ∫ y, g y * (K (y - w) * f w) ∂haar d ∂haar d := by
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [torusConv]
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only []
    rw [show w - y = -(y - w) from (neg_sub y w).symm, hKe]
    ring
  rw [e1, e2]
  exact integral_integral_swap hint

theorem torusConv_nonneg {K f : Torus d → ℝ} (hK : ∀ z, 0 ≤ K z) (hf : ∀ᵐ w ∂haar d, 0 ≤ f w)
    (y : Torus d) : 0 ≤ torusConv K f y := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [hf] with w hw
  exact mul_nonneg (hK _) hw

/-! ### `Lᵖ` contraction -/

theorem integrable_of_continuous_torus {K : Torus d → ℝ} (hK : Continuous K) :
    Integrable K (haar d) := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_le_of_continuous' hK
  exact (integrable_const C).mono' hK.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x)

theorem lintegral_torusConv_rpow_le_of_measurable {K f : Torus d → ℝ} (hK : Continuous K)
    (hK0 : ∀ z, 0 ≤ K z) (hK1 : ∫ z, K z ∂haar d = 1) {p : ℝ} (hp : 1 ≤ p)
    (hf : Measurable f) :
    ∫⁻ y, ‖torusConv K f y‖ₑ ^ p ∂haar d ≤ ∫⁻ y, ‖f y‖ₑ ^ p ∂haar d := by
  have hKi : Integrable K (haar d) := integrable_of_continuous_torus hK
  have hKm : Measurable K := hK.measurable
  have hW : ∀ w, ∫⁻ y, ENNReal.ofReal (K (y - w)) ∂haar d = 1 := fun w => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hKi.comp_sub_right w)
      (Eventually.of_forall fun y => hK0 _), integral_sub_right_eq_self K w, hK1,
      ENNReal.ofReal_one]
  have hW' : ∀ y, ∫⁻ w, ENNReal.ofReal (K (y - w)) ∂haar d = 1 := fun y => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hKi.comp_sub_left y)
      (Eventually.of_forall fun w => hK0 _), integral_sub_left_eq_self K (haar d) y, hK1,
      ENNReal.ofReal_one]
  have hbound : ∀ y, ‖torusConv K f y‖ₑ ≤ ∫⁻ w, ENNReal.ofReal (K (y - w)) * ‖f w‖ₑ ∂haar d :=
    fun y => by
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      refine lintegral_congr fun w => ?_
      rw [enorm_mul, Real.enorm_of_nonneg (hK0 _)]
  have hφm : Measurable fun (p : Torus d × Torus d) => ENNReal.ofReal (K (p.1 - p.2)) :=
    ENNReal.measurable_ofReal.comp (hKm.comp (measurable_fst.sub measurable_snd))
  have hmeas : Measurable (Function.uncurry fun (y w : Torus d) =>
      ENNReal.ofReal (K (y - w)) * ‖f w‖ₑ ^ p) :=
    hφm.mul ((hf.comp measurable_snd).enorm.pow_const p)
  calc ∫⁻ y, ‖torusConv K f y‖ₑ ^ p ∂haar d
      ≤ ∫⁻ y, ∫⁻ w, ENNReal.ofReal (K (y - w)) * ‖f w‖ₑ ^ p ∂haar d ∂haar d := by
        refine lintegral_mono fun y => ?_
        calc ‖torusConv K f y‖ₑ ^ p
            ≤ (∫⁻ w, ENNReal.ofReal (K (y - w)) * ‖f w‖ₑ ∂haar d) ^ p :=
              ENNReal.rpow_le_rpow (hbound y) (by linarith)
          _ ≤ _ := rpow_lintegral_le hp
              (ENNReal.measurable_ofReal.comp (hKm.comp (measurable_const.sub measurable_id))).aemeasurable
              hf.enorm.aemeasurable (hW' y)
    _ = ∫⁻ w, ∫⁻ y, ENNReal.ofReal (K (y - w)) * ‖f w‖ₑ ^ p ∂haar d ∂haar d :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ w, ‖f w‖ₑ ^ p ∂haar d := by
        refine lintegral_congr fun w => ?_
        have hm : Measurable fun y : Torus d => ENNReal.ofReal (K (y - w)) :=
          ENNReal.measurable_ofReal.comp (hKm.comp (measurable_id.sub measurable_const))
        rw [lintegral_mul_const (‖f w‖ₑ ^ p) hm, hW w, one_mul]

theorem lintegral_torusConv_rpow_le {K f : Torus d → ℝ} (hK : Continuous K)
    (hK0 : ∀ z, 0 ≤ K z) (hK1 : ∫ z, K z ∂haar d = 1) {p : ℝ} (hp : 1 ≤ p)
    (hi : Integrable f (haar d)) :
    ∫⁻ y, ‖torusConv K f y‖ₑ ^ p ∂haar d ≤ ∫⁻ y, ‖f y‖ₑ ^ p ∂haar d := by
  set v := hi.aestronglyMeasurable.mk f with hv
  have hfv : f =ᵐ[haar d] v := hi.aestronglyMeasurable.ae_eq_mk
  rw [torusConv_congr_ae K hfv]
  calc ∫⁻ y, ‖torusConv K v y‖ₑ ^ p ∂haar d ≤ ∫⁻ y, ‖v y‖ₑ ^ p ∂haar d :=
        lintegral_torusConv_rpow_le_of_measurable hK hK0 hK1 hp
          hi.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    _ = ∫⁻ y, ‖f y‖ₑ ^ p ∂haar d :=
        (lintegral_congr_ae (hfv.mono fun y hy => by simp [hy])).symm

/-- Convolution with a nonnegative continuous unit-mass kernel is an `Lᵖ(m)` contraction. -/
theorem eLpNorm_torusConv_le {K f : Torus d → ℝ} (hK : Continuous K)
    (hK0 : ∀ z, 0 ≤ K z) (hK1 : ∫ z, K z ∂haar d = 1) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : MemLp f p (haar d)) :
    eLpNorm (torusConv K f) p (haar d) ≤ eLpNorm f p (haar d) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpr : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hp' hp
  have hi := integrable_of_memLp hp hf
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp'
      (continuous_torusConv hK hi).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hi.aestronglyMeasurable]
  exact ENNReal.rpow_le_rpow (lintegral_torusConv_rpow_le hK hK0 hK1 hpr hi) (by positivity)

theorem memLp_torusConv {K f : Torus d → ℝ} (hK : Continuous K)
    (hK0 : ∀ z, 0 ≤ K z) (hK1 : ∫ z, K z ∂haar d = 1) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : MemLp f p (haar d)) : MemLp (torusConv K f) p (haar d) :=
  (eLpNorm_torusConv_le hK hK0 hK1 hp hp' hf).trans_lt hf.eLpNorm_lt_top

/-! ### Semigroup law -/

theorem eq_of_fourierCoeff_eq {f g : Torus d → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ k, fourierCoeff f k = fourierCoeff g k) : f = g := by
  have hfi := integrable_of_continuous_torus hf
  have hgi := integrable_of_continuous_torus hg
  have hcoef : ∀ k, UnitAddTorus.mFourierCoeff (fun x => ((f x - g x : ℝ) : ℂ)) k = 0 := by
    intro k
    have e := SharpLSI.cf_sub hfi hgi k
    have e' : fourierCoeff (fun y => f y - g y) k = fourierCoeff f k - fourierCoeff g k := e
    have : fourierCoeff (fun y => f y - g y) k = 0 := by rw [e', h k, sub_self]
    exact this
  have hae := ae_eq_zero_of_mFourierCoeff_eq_zero (memLp_two_of_continuous (hf.sub hg)) hcoef
  have := (hf.sub hg).ae_eq_iff_eq (μ := haar d) continuous_const |>.mp hae
  funext x
  exact sub_eq_zero.mp (congrFun this x)

theorem fourierCoeff_heatKernelT {t : ℝ} (ht : 0 < t) (k : Fin d → ℤ) :
    fourierCoeff (heatKernelT t) k = (Real.exp (-(gradWeight k * t)) : ℂ) := by
  unfold fourierCoeff
  rw [mFourierCoeff_ofReal_eq, ← heatKernelT_fourier ht k]
  congr 1; funext x; exact mul_comm _ _

/-- Semigroup law `K_t ⋆ K_s = K_{t+s}`. -/
theorem heatKernelT_conv {t s : ℝ} (ht : 0 < t) (hs : 0 < s) :
    torusConv (heatKernelT (d := d) t) (heatKernelT s) = heatKernelT (t + s) := by
  have hi := integrable_of_continuous_torus (continuous_heatKernelT (d := d) hs)
  refine eq_of_fourierCoeff_eq (continuous_torusConv (continuous_heatKernelT ht) hi)
    (continuous_heatKernelT (add_pos ht hs)) fun k => ?_
  change fourierCoeff (heatOp t (heatKernelT s)) k = _
  rw [fourierCoeff_heatOp ht hi, fourierCoeff_heatKernelT hs, fourierCoeff_heatKernelT (add_pos ht hs),
    ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2; ring

/-! ### `L²` convergence -/

theorem memLp_heatOp {t : ℝ} (ht : 0 < t) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : Torus d → ℝ} (hf : MemLp f p (haar d)) : MemLp (heatOp t f) p (haar d) :=
  memLp_torusConv (continuous_heatKernelT ht) (fun z => (heatKernelT_pos ht z).le)
    (integral_heatKernelT ht) hp hp' hf

theorem eLpNorm_heatOp_le {t : ℝ} (ht : 0 < t) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : Torus d → ℝ} (hf : MemLp f p (haar d)) :
    eLpNorm (heatOp t f) p (haar d) ≤ eLpNorm f p (haar d) :=
  eLpNorm_torusConv_le (continuous_heatKernelT ht) (fun z => (heatKernelT_pos ht z).le)
    (integral_heatKernelT ht) hp hp' hf

theorem integral_sq_heatOp_sub {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ} (hf : MemLp f 2 (haar d)) :
    ∫ y, (heatOp t f y - f y) ^ 2 ∂haar d =
      ∑' k, (Real.exp (-(gradWeight k * t)) - 1) ^ 2 * ‖fourierCoeff f k‖ ^ 2 := by
  have hH := memLp_heatOp ht one_le_two (by simp) hf
  have hP := hasSum_sq_fourierCoeff (hH.sub hf)
  simp only [Pi.sub_apply] at hP
  rw [← hP.tsum_eq]
  congr 1; funext k
  show ‖fourierCoeff (fun y => heatOp t f y - f y) k‖ ^ 2 = _
  have hfi := hf.integrable one_le_two
  have e : fourierCoeff (fun y => heatOp t f y - f y) k =
      fourierCoeff (heatOp t f) k - fourierCoeff f k :=
    SharpLSI.cf_sub (hH.integrable one_le_two) hfi k
  have e2 : fourierCoeff (fun y => heatOp t f y - f y) k =
      ((Real.exp (-(gradWeight k * t)) - 1 : ℝ) : ℂ) * fourierCoeff f k := by
    rw [e, fourierCoeff_heatOp ht hfi]; push_cast; ring
  rw [e2, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]

theorem tendsto_integral_sq_heatOp_sub {f : Torus d → ℝ} (hf : MemLp f 2 (haar d)) :
    Tendsto (fun t : ℝ => ∫ y, (heatOp t f y - f y) ^ 2 ∂haar d) (𝓝[>] 0) (𝓝 0) := by
  have hsum : Summable fun k => ‖fourierCoeff f k‖ ^ 2 := (hasSum_sq_fourierCoeff hf).summable
  have key := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun t k => (Real.exp (-(gradWeight k * t)) - 1) ^ 2 * ‖fourierCoeff f k‖ ^ 2)
    (g := fun _ => (0 : ℝ)) (bound := fun k => ‖fourierCoeff f k‖ ^ 2) hsum
    (fun k => by
      have hc : Continuous fun t : ℝ =>
          (Real.exp (-(gradWeight k * t)) - 1) ^ 2 * ‖fourierCoeff f k‖ ^ 2 := by fun_prop
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this)
    (by
      filter_upwards [self_mem_nhdsWithin] with t ht k
      have hw : 0 ≤ gradWeight k := by unfold gradWeight; positivity
      have h1 : Real.exp (-(gradWeight k * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hw (le_of_lt (show (0:ℝ) < t from ht))])
      have h2 : 0 < Real.exp (-(gradWeight k * t)) := Real.exp_pos _
      have h3 : (Real.exp (-(gradWeight k * t)) - 1) ^ 2 ≤ 1 := by nlinarith
      rw [Real.norm_of_nonneg (by positivity)]
      calc _ ≤ 1 * ‖fourierCoeff f k‖ ^ 2 := mul_le_mul_of_nonneg_right h3 (by positivity)
        _ = _ := one_mul _)
  simp only [tsum_zero] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (integral_sq_heatOp_sub ht hf).symm

/-! ### Strong convergence in `Lᵖ` -/

theorem torusConv_sub {K f g : Torus d → ℝ} (hK : Continuous K) (hf : Integrable f (haar d))
    (hg : Integrable g (haar d)) (y : Torus d) :
    torusConv K (fun z => f z - g z) y = torusConv K f y - torusConv K g y := by
  unfold torusConv
  rw [← integral_sub (integrable_conv_integrand hK hf y) (integrable_conv_integrand hK hg y)]
  congr 1; funext w; ring

theorem abs_torusConv_le {K f : Torus d → ℝ} (hK : Continuous K) (hK0 : ∀ z, 0 ≤ K z)
    (hK1 : ∫ z, K z ∂haar d = 1) {B : ℝ} (hB : ∀ x, |f x| ≤ B) (y : Torus d) : |torusConv K f y| ≤ B := by
  have hKi : Integrable (fun w => K (y - w)) (haar d) :=
    integrable_of_continuous_torus (hK.comp (continuous_const.sub continuous_id))
  have h1 : ‖torusConv K f y‖ ≤ ∫ w, K (y - w) * B ∂haar d := by
    refine norm_integral_le_of_norm_le (hKi.mul_const B) (Eventually.of_forall fun w => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hK0 _)]
    exact mul_le_mul_of_nonneg_left (hB w) (hK0 _)
  rw [integral_mul_const, integral_sub_left_eq_self K (haar d) y, hK1, one_mul] at h1
  simpa using h1

theorem tendsto_eLpNorm_two_heatOp_sub {h : Torus d → ℝ} (hh : MemLp h 2 (haar d)) :
    Tendsto (fun t : ℝ => eLpNorm (fun y => heatOp t h y - h y) 2 (haar d)) (𝓝[>] 0) (𝓝 0) := by
  have key := ENNReal.tendsto_ofReal ((tendsto_integral_sq_heatOp_sub hh).rpow_const
    (p := (2 : ℝ)⁻¹) (Or.inr (by norm_num)))
  rw [Real.zero_rpow (by norm_num)] at key
  simp only [ENNReal.ofReal_zero] at key
  refine key.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hm := (memLp_heatOp ht one_le_two (by simp) hh).sub hh
  have := hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)
  simp only [Pi.sub_apply, ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
    sq_abs] at this
  exact this.symm

theorem tendsto_eLpNorm_heatOp_sub_of_bounded {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {h : Torus d → ℝ} (hc : Continuous h) {B : ℝ} (hB : ∀ x, |h x| ≤ B) :
    Tendsto (fun t : ℝ => eLpNorm (fun y => heatOp t h y - h y) p (haar d)) (𝓝[>] 0) (𝓝 0) := by
  have hL2 := tendsto_eLpNorm_two_heatOp_sub (memLp_two_of_continuous hc)
  have hi := integrable_of_continuous_torus hc
  have hcont : ∀ {t : ℝ}, 0 < t → Continuous fun y => heatOp t h y - h y := fun {t} ht =>
    (continuous_torusConv (continuous_heatKernelT ht) hi).sub hc
  rcases le_total p 2 with hp2 | hp2
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hL2
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact eLpNorm_le_eLpNorm_of_exponent_le hp2
  · -- `2 ≤ p`: interpolate between `L²` and the sup bound
    set q := p.toReal with hq
    have hq2 : 2 ≤ q := by
      have := ENNReal.toReal_mono hp' hp2
      simpa using this
    have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
    set M : ℝ≥0∞ := ENNReal.ofReal (2 * B) with hM
    have hMt : M ≠ ∞ := ENNReal.ofReal_ne_top
    have hlim : Tendsto (fun t : ℝ => (M ^ (q - 2) * eLpNorm (fun y => heatOp t h y - h y) 2 (haar d) ^ 2) ^ (1 / q))
        (𝓝[>] 0) (𝓝 0) := by
      have h1 : Tendsto (fun t : ℝ => eLpNorm (fun y => heatOp t h y - h y) 2 (haar d) ^ 2)
          (𝓝[>] 0) (𝓝 (0 ^ 2)) := ((ENNReal.continuous_pow 2).tendsto _).comp hL2
      have h2 := ENNReal.Tendsto.const_mul (a := M ^ (q - 2)) h1 (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by linarith) hMt))
      have h3 := ((ENNReal.continuous_rpow_const (y := 1 / q)).tendsto _).comp h2
      have h0 : (0 : ℝ≥0∞) ^ (1 / q) = 0 := ENNReal.zero_rpow_of_pos (by positivity)
      have h4 : M ^ (q - 2) * (0 : ℝ≥0∞) ^ 2 = 0 := by simp
      rw [h4, h0] at h3
      exact h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hv := hcont ht
    have hvm : AEStronglyMeasurable (fun y => heatOp t h y - h y) (haar d) := hv.aestronglyMeasurable
    have hbd : ∀ y, ‖heatOp t h y - h y‖ₑ ≤ M := fun y => by
      rw [hM, ← ofReal_norm]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [Real.norm_eq_abs]
      have := abs_torusConv_le (continuous_heatKernelT ht) (fun z => (heatKernelT_pos ht z).le)
        (integral_heatKernelT ht) hB y
      have this : |heatOp t h y| ≤ B := this
      calc |heatOp t h y - h y| ≤ |heatOp t h y| + |h y| := abs_sub _ _
        _ ≤ 2 * B := by linarith [hB y]
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hvm, ← hq]
    refine ENNReal.rpow_le_rpow ?_ (by positivity)
    have h2 : ∫⁻ y, ‖heatOp t h y - h y‖ₑ ^ (2 : ℝ) ∂haar d =
        eLpNorm (fun y => heatOp t h y - h y) 2 (haar d) ^ 2 := by
      have := lintegral_rpow_enorm_eq_rpow_eLpNorm' (μ := haar d)
        (f := fun y => heatOp t h y - h y) (q := 2) (by norm_num)
      rw [this, eLpNorm_eq_eLpNorm' (by norm_num) (by simp) hvm]
      simp
    calc ∫⁻ y, ‖heatOp t h y - h y‖ₑ ^ q ∂haar d
        ≤ ∫⁻ y, M ^ (q - 2) * ‖heatOp t h y - h y‖ₑ ^ (2 : ℝ) ∂haar d := by
          refine lintegral_mono fun y => ?_
          have : ‖heatOp t h y - h y‖ₑ ^ q =
              ‖heatOp t h y - h y‖ₑ ^ (q - 2) * ‖heatOp t h y - h y‖ₑ ^ (2 : ℝ) := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ (by linarith) (by norm_num)]
            congr 1; ring
          rw [this]
          exact mul_le_mul' (ENNReal.rpow_le_rpow (hbd y) (by linarith)) le_rfl
      _ = M ^ (q - 2) * ∫⁻ y, ‖heatOp t h y - h y‖ₑ ^ (2 : ℝ) ∂haar d :=
          lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hMt)
      _ = _ := by rw [h2]

theorem tendsto_eLpNorm_heatOp_sub {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞) {f : Torus d → ℝ}
    (hf : MemLp f p (haar d)) :
    Tendsto (fun t : ℝ => eLpNorm (fun y => heatOp t f y - f y) p (haar d)) (𝓝[>] 0) (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ0, hδε⟩ : ∃ δ : ℝ≥0∞, δ ≠ 0 ∧ δ + δ + δ ≤ ε := by
    rcases eq_or_ne ε ∞ with rfl | hε'
    · exact ⟨1, one_ne_zero, by simp⟩
    refine ⟨ε / 3, (ENNReal.div_pos hε.ne' (by simp)).ne', le_of_eq ?_⟩
    rw [← two_mul, ← add_one_mul]
    norm_num
    exact ENNReal.mul_div_cancel (by norm_num) (by norm_num)
  obtain ⟨h, hfh, hhp⟩ := hf.exists_boundedContinuous_eLpNorm_sub_le hp' hδ0
  have hfi := integrable_of_memLp hp hf
  have hhi := integrable_of_memLp hp hhp
  have hB := tendsto_eLpNorm_heatOp_sub_of_bounded hp hp' h.continuous (B := ‖h‖)
    (fun x => by simpa [Real.norm_eq_abs] using h.norm_coe_le_norm x)
  have hev := (ENNReal.tendsto_nhds_zero.mp hB) δ (pos_iff_ne_zero.mpr hδ0)
  filter_upwards [hev, self_mem_nhdsWithin] with t ht0 ht
  have hsplit : (fun y => heatOp t f y - f y) =
      (fun y => heatOp t (fun z => f z - h z) y) +
        ((fun y => heatOp t h y - h y) + (fun y => h y - f y)) := by
    funext y
    simp only [Pi.add_apply, heatOp, torusConv_sub (continuous_heatKernelT ht) hfi hhi]
    ring
  have hm1 : AEStronglyMeasurable (fun y => heatOp t (fun z => f z - h z) y) (haar d) :=
    (continuous_torusConv (continuous_heatKernelT ht) (hfi.sub hhi)).aestronglyMeasurable
  have hm2 : AEStronglyMeasurable (fun y => heatOp t h y - h y) (haar d) :=
    ((continuous_torusConv (continuous_heatKernelT ht) hhi).sub h.continuous).aestronglyMeasurable
  have hm3 : AEStronglyMeasurable (fun y => h y - f y) (haar d) :=
    hhi.aestronglyMeasurable.sub hfi.aestronglyMeasurable
  rw [hsplit]
  refine (eLpNorm_add_le hp).trans ?_
  refine le_trans ?_ hδε
  rw [add_assoc]
  gcongr
  · calc eLpNorm (fun y => heatOp t (fun z => f z - h z) y) p (haar d)
        ≤ eLpNorm (fun z => f z - h z) p (haar d) := eLpNorm_heatOp_le ht hp hp' (hf.sub hhp)
      _ ≤ δ := hfh
  · refine (eLpNorm_add_le hp).trans (add_le_add ht0 ?_)
    rw [← eLpNorm_neg]
    convert hfh using 2
    funext y
    simp

/-- Semigroup law for the operators, `H_t H_s = H_{t+s}`. -/
theorem heatOp_add {t s : ℝ} (ht : 0 < t) (hs : 0 < s) {f : Torus d → ℝ}
    (hf : Integrable f (haar d)) : heatOp t (heatOp s f) = heatOp (t + s) f := by
  have hc : Continuous (heatOp s f) := continuous_torusConv (continuous_heatKernelT hs) hf
  refine eq_of_fourierCoeff_eq (continuous_torusConv (continuous_heatKernelT ht)
    (integrable_of_continuous_torus hc)) (continuous_torusConv
      (continuous_heatKernelT (add_pos ht hs)) hf) fun k => ?_
  rw [fourierCoeff_heatOp ht (integrable_of_continuous_torus hc), fourierCoeff_heatOp hs hf,
    fourierCoeff_heatOp (add_pos ht hs) hf, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3; ring

/-! ### The `H¹` theory -/

/-- Componentwise heat flow of a vector field. -/
noncomputable def heatGrad (t : ℝ) (g : Torus d → Tangent d) (y : Torus d) : Tangent d :=
  WithLp.toLp 2 fun j => heatOp t (fun z => g z j) y

theorem memLp_heatGrad {t : ℝ} (ht : 0 < t) {g : Torus d → Tangent d} (hg : MemLp g 2 (haar d)) :
    MemLp (heatGrad t g) 2 (haar d) :=
  memLp_piLp_iff.mpr fun j => memLp_heatOp ht one_le_two (by simp) (memLp_coord hg j)

/-- `H_t` commutes with weak gradients: `∇ (H_t u) = H_t (∇ u)` componentwise. -/
theorem IsWeakGradient.heatOp {t : ℝ} (ht : 0 < t) {u : Torus d → ℝ} {g : Torus d → Tangent d}
    (h : IsWeakGradient u g) : IsWeakGradient (DGPS.heatOp t u) (heatGrad t g) := by
  refine isWeakGradient_of_fourierCoeff (memLp_heatOp ht one_le_two (by simp) h.memLp)
    (memLp_heatGrad ht h.memLp_grad) fun j k => ?_
  have hgj := (memLp_coord h.memLp_grad j).integrable one_le_two
  have hu := h.memLp.integrable one_le_two
  show fourierCoeff (DGPS.heatOp t fun z => g z j) k = _
  rw [fourierCoeff_heatOp ht hgj, fourierCoeff_heatOp ht hu, fourierCoeff_weakGradient h j k]
  ring

theorem tendsto_integral_norm_sq_heatGrad_sub {g : Torus d → Tangent d} (hg : MemLp g 2 (haar d)) :
    Tendsto (fun t : ℝ => ∫ x, ‖heatGrad t g x - g x‖ ^ 2 ∂haar d) (𝓝[>] 0) (𝓝 0) := by
  have hj : ∀ t : ℝ, 0 < t → ∫ x, ‖heatGrad t g x - g x‖ ^ 2 ∂haar d =
      ∑ j, ∫ y, (DGPS.heatOp t (fun z => g z j) y - g y j) ^ 2 ∂haar d := by
    intro t ht
    simp_rw [tangent_norm_sq]
    refine integral_finsetSum _ fun j _ => ?_
    exact ((memLp_heatOp ht one_le_two (by simp) (memLp_coord hg j)).sub
      (memLp_coord hg j)).integrable_sq
  have := tendsto_finsetSum (Finset.univ : Finset (Fin d)) fun j _ =>
    tendsto_integral_sq_heatOp_sub (memLp_coord hg j)
  simp only [Finset.sum_const_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (hj t ht).symm

/-- Strong convergence in `H¹`: `H_t u → u` and `∇ H_t u → ∇ u` in `L²`. -/
theorem tendsto_H1_heatOp {u : Torus d → ℝ} {g : Torus d → Tangent d} (h : IsWeakGradient u g) :
    Tendsto (fun t : ℝ => ∫ y, (DGPS.heatOp t u y - u y) ^ 2 ∂haar d +
        ∫ x, ‖heatGrad t g x - g x‖ ^ 2 ∂haar d) (𝓝[>] 0) (𝓝 0) := by
  simpa using (tendsto_integral_sq_heatOp_sub h.memLp).add
    (tendsto_integral_norm_sq_heatGrad_sub h.memLp_grad)

end DGPS

namespace DGPS.Analysis

/-- FOU007 bundle: the periodized Gaussian heat kernel `K_t(x) = ∑ₙ (4πt)^{-d/2} e^{-|x+n|²/(4t)}`
on `𝕋^d` (the kernel `heatKernelT t`, the legacy theta/Poisson carrier, agrees with this sum on the
lift) is positive, smooth periodic, of Haar integral `1`, with Fourier coefficients
`e^{-4π²|k|²t}`, and `K_t ⋆ K_s = K_{t+s}`. The operator `H_t f = K_t ⋆ f` has Fourier multiplier
`e^{-4π²|k|²t}`, is self-adjoint, positivity and mass preserving, `Lᵖ`-contracting
(`1 ≤ p < ∞`), satisfies the semigroup law, converges strongly to the identity in `Lᵖ` as
`t → 0⁺`, commutes with weak gradients and converges strongly in `H¹`. -/
theorem periodized_gaussian_heat_kernel (d : ℕ) :
    (∀ t : ℝ, 0 < t → ∀ x : Fin d → ℝ, heatKernelT t (torusLift x) =
      ∑' n : Fin d → ℤ, (4 * π * t) ^ (-(d : ℝ) / 2) *
        Real.exp (-(∑ j, (x j + (n j : ℝ)) ^ 2) / (4 * t))) ∧
    (∀ t : ℝ, 0 < t → ∀ z : Torus d, 0 < heatKernelT t z) ∧
    (∀ t : ℝ, 0 < t → IsSmoothPeriodic (heatKernelT (d := d) t)) ∧
    (∀ t : ℝ, 0 < t → ∫ z, heatKernelT (d := d) t z ∂haar d = 1) ∧
    (∀ t : ℝ, 0 < t → ∀ k : Fin d → ℤ,
      fourierCoeff (heatKernelT (d := d) t) k = (Real.exp (-(gradWeight k * t)) : ℂ)) ∧
    (∀ t s : ℝ, 0 < t → 0 < s →
      torusConv (heatKernelT (d := d) t) (heatKernelT s) = heatKernelT (t + s)) ∧
    (∀ t : ℝ, 0 < t → ∀ f : Torus d → ℝ, Integrable f (haar d) → ∀ k : Fin d → ℤ,
      fourierCoeff (heatOp t f) k = (Real.exp (-(gradWeight k * t)) : ℂ) * fourierCoeff f k) ∧
    (∀ t : ℝ, 0 < t → ∀ f g : Torus d → ℝ, Integrable f (haar d) → Integrable g (haar d) →
      ∫ y, heatOp t f y * g y ∂haar d = ∫ y, f y * heatOp t g y ∂haar d) ∧
    (∀ t : ℝ, 0 < t → ∀ f : Torus d → ℝ, (∀ᵐ w ∂haar d, 0 ≤ f w) → ∀ y, 0 ≤ heatOp t f y) ∧
    (∀ t : ℝ, 0 < t → ∀ f : Torus d → ℝ, Integrable f (haar d) →
      ∫ y, heatOp t f y ∂haar d = ∫ y, f y ∂haar d) ∧
    (∀ t : ℝ, 0 < t → ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ∞ → ∀ f : Torus d → ℝ, MemLp f p (haar d) →
      MemLp (heatOp t f) p (haar d) ∧
        eLpNorm (heatOp t f) p (haar d) ≤ eLpNorm f p (haar d)) ∧
    (∀ t s : ℝ, 0 < t → 0 < s → ∀ f : Torus d → ℝ, Integrable f (haar d) →
      heatOp t (heatOp s f) = heatOp (t + s) f) ∧
    (∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ∞ → ∀ f : Torus d → ℝ, MemLp f p (haar d) →
      Tendsto (fun t : ℝ => eLpNorm (fun y => heatOp t f y - f y) p (haar d)) (𝓝[>] 0) (𝓝 0)) ∧
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g → ∀ t : ℝ, 0 < t →
      IsWeakGradient (heatOp t u) (heatGrad t g)) ∧
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      Tendsto (fun t : ℝ => ∫ y, (heatOp t u y - u y) ^ 2 ∂haar d +
        ∫ x, ‖heatGrad t g x - g x‖ ^ 2 ∂haar d) (𝓝[>] 0) (𝓝 0)) :=
  ⟨fun t ht x => heatKernelT_torusLift ht x,
    fun t ht z => heatKernelT_pos ht z,
    fun t ht => isSmoothPeriodic_heatKernelT ht,
    fun t ht => integral_heatKernelT ht,
    fun t ht k => fourierCoeff_heatKernelT ht k,
    fun t s ht hs => heatKernelT_conv ht hs,
    fun t ht f hf k => fourierCoeff_heatOp ht hf k,
    fun t ht f g hf hg => integral_torusConv_mul (continuous_heatKernelT ht)
      (heatKernelT_neg ht) hf hg,
    fun t ht f hf y => torusConv_nonneg (fun z => (heatKernelT_pos ht z).le) hf y,
    fun t ht f hf => by
      change ∫ y, torusConv (heatKernelT t) f y ∂haar d = _
      rw [integral_torusConv (continuous_heatKernelT ht) hf, integral_heatKernelT ht, one_mul],
    fun t ht p hp hp' f hf => ⟨memLp_heatOp ht hp hp' hf, eLpNorm_heatOp_le ht hp hp' hf⟩,
    fun t s ht hs f hf => heatOp_add ht hs hf,
    fun p hp hp' f hf => tendsto_eLpNorm_heatOp_sub hp hp' hf,
    fun u g h t ht => h.heatOp ht,
    fun u g h => tendsto_H1_heatOp h⟩

end DGPS.Analysis
