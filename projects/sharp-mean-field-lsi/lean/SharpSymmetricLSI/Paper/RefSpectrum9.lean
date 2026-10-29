import SharpSymmetricLSI.Paper.RefSpectrum8

/-!
# R23 (6.1), part 9: heat smoothing of an eigenfunction

For `e_t = e^{tΔ}e`: `e_t` is smooth, `|e_t| ≤ B` if `|e| ≤ B`, `∂ₖe_t = e^{tΔ}∂ₖe` a.e.,
`Δe_t = -e^{tΔ}g` a.e. (Fourier coefficients), and `∑ₖ|k|²|ê_t(k)| < ∞`. Hence
`‖∂ᵢ∂ⱼe_t‖_P ≤ A‖g‖_P` for `P = 2^{m+1}` (`cz_smooth` and the `L^P` contraction).
-/

open MeasureTheory Filter Topology Complex
open scoped ENNReal Real ContDiff NNReal
open UnitAddTorus

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Fourier coefficients of the classical Laplacian. -/
theorem cf_lap {u : UnitAddTorus ι → ℝ} (hu : ContDiff ℝ 2 (u ∘ liftT)) (k : ι → ℤ) :
    mFourierCoeff (fun y => (lap u y : ℂ)) k = lapSym k * mFourierCoeff (fun y => (u y : ℂ)) k := by
  have hu1 : ContDiff ℝ 1 (u ∘ liftT) := hu.of_le (by norm_num)
  have hdi : ∀ i, ContDiff ℝ 1 (dpart u i ∘ liftT) := fun i => contDiff_dpart (n := 1) hu i
  have hdd : ∀ i j, Continuous (dpart (dpart u i) j) := fun i j =>
    continuous_of_liftT' (contDiff_dpart (n := 0) (hdi i) j).continuous
  have hint : ∀ l, Integrable (fun t => mFourier (-k) t • (dpart (dpart u l) l t : ℂ)) volume :=
    fun l => ((map_continuous (mFourier (-k))).smul
      (Complex.continuous_ofReal.comp (hdd l l))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have e : (fun t => mFourier (-k) t • (lap u t : ℂ)) =
      fun t => ∑ l, mFourier (-k) t • (dpart (dpart u l) l t : ℂ) := by
    funext t; simp only [lap]; push_cast; rw [Finset.smul_sum]
  rw [mFourierCoeff_eq_integral, e, integral_finsetSum _ fun l _ => hint l]
  simp_rw [← mFourierCoeff_eq_integral]
  have h2 : ∀ l, mFourierCoeff (fun y => (dpart (dpart u l) l y : ℂ)) k =
      -(4 * π ^ 2 * (k l : ℂ) ^ 2) * mFourierCoeff (fun y => (u y : ℂ)) k := by
    intro l
    rw [cf_dpart (hdi l) l k, cf_dpart hu1 l k]
    have : (I : ℂ) * I = -1 := I_mul_I
    linear_combination (4 * π ^ 2 * (k l : ℂ) ^ 2 * mFourierCoeff (fun y => (u y : ℂ)) k) * this
  simp_rw [h2, lapSym, ← Finset.sum_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]

/-- `L²` functions with equal Fourier coefficients agree a.e. -/
theorem ae_eq_of_cf_eq {u v : UnitAddTorus ι → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume)
    (h : ∀ k, mFourierCoeff (fun y => (u y : ℂ)) k = mFourierCoeff (fun y => (v y : ℂ)) k) :
    u =ᵐ[volume] v := by
  have huv := hu.sub hv
  have hcf : ∀ k, mFourierCoeff (fun y => ((u - v) y : ℂ)) k = 0 := by
    intro k
    have h' := h k
    rw [mFourierCoeff_eq_integral, mFourierCoeff_eq_integral] at h'
    rw [mFourierCoeff_eq_integral]
    have e : (fun t => mFourier (-k) t • (((u - v) t : ℝ) : ℂ)) =
        fun t => mFourier (-k) t • (u t : ℂ) - mFourier (-k) t • (v t : ℂ) := by
      funext t; simp [mul_sub]
    rw [e, integral_sub (integrable_mFourier_smul' (hu.integrable one_le_two) (-k))
      (integrable_mFourier_smul' (hv.integrable one_le_two) (-k)), h', sub_self]
  have hP := hasSum_sq_mFourierCoeff_real huv
  simp only [hcf, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hP
  have h0 : ∫ y, (u - v) y ^ 2 = 0 := (hasSum_zero.unique hP).symm
  have := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg ((u - v) y))
    huv.integrable_sq).mp h0
  filter_upwards [this] with y hy
  simpa [sub_eq_zero] using hy

/-! ### Smoothing an `L¹` solution of `-Δe = g` -/

section smooth

variable {e g : UnitAddTorus ι → ℝ} (he : MemLp e 2 volume) (hg : MemLp g 2 volume)
  (hcf : ∀ k, mFourierCoeff (fun y => (g y : ℂ)) k =
    4 * π ^ 2 * (∑ j, ((k j : ℂ)) ^ 2) * mFourierCoeff (fun y => (e y : ℂ)) k)
include he

theorem heat_smooth {t : ℝ} (ht : 0 < t) : ContDiff ℝ ∞ (heatT t e ∘ liftT) :=
  isSmoothT_heatT ht (he.integrable one_le_two)

theorem heat_smooth2 {t : ℝ} (ht : 0 < t) : ContDiff ℝ 2 (heatT t e ∘ liftT) :=
  (heat_smooth he ht).of_le (by norm_cast)

theorem heat_summable {t : ℝ} (ht : 0 < t) :
    Summable fun k : ι → ℤ =>
      (∑ i, ((k i : ℝ)) ^ 2) * ‖mFourierCoeff (fun y => (heatT t e y : ℂ)) k‖ := by
  have hi := he.integrable one_le_two
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_sq_heatMult (ι := ι) ht).mul_right (∫ y, |e y|))
  rw [mFourierCoeff_heatT ht hi, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (heatMult_pos t k).le, ← mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_mFourierCoeff_le_integral hi k)
    (mul_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _) (heatMult_pos t k).le)

include hg hcf in
theorem heat_lap {t : ℝ} (ht : 0 < t) :
    lap (heatT t e) =ᵐ[volume] fun y => -heatT t g y := by
  have hei := he.integrable one_le_two
  have hgi := hg.integrable one_le_two
  have hc1 : Continuous (lap (heatT t e)) := by
    have h2 := heat_smooth2 he ht
    have hdi : ∀ i, ContDiff ℝ 1 (dpart (heatT t e) i ∘ liftT) := fun i =>
      contDiff_dpart (n := 1) h2 i
    exact continuous_finset_sum _ fun i _ =>
      continuous_of_liftT' (contDiff_dpart (n := 0) (hdi i) i).continuous
  have hc2 : Continuous fun y => -heatT t g y := (continuous_heatT ht hgi).neg
  refine ae_eq_of_cf_eq (memLp_of_continuous_torus hc1 _) (memLp_of_continuous_torus hc2 _)
    fun k => ?_
  rw [cf_lap (heat_smooth2 he ht) k, mFourierCoeff_heatT ht hei]
  have hneg : mFourierCoeff (fun y => ((-heatT t g y : ℝ) : ℂ)) k =
      -mFourierCoeff (fun y => (heatT t g y : ℂ)) k := by
    rw [mFourierCoeff_eq_integral, mFourierCoeff_eq_integral, ← integral_neg]
    congr 1; funext y; push_cast; simp [smul_neg]
  rw [hneg, mFourierCoeff_heatT ht hgi, hcf k, lapSym]
  ring

theorem heat_grad {t : ℝ} (ht : 0 < t) {G : UnitAddTorus ι → ι → ℝ} (hw : IsWeakGrad e G)
    (hG : ∀ k, Integrable fun y => G y k) (k : ι) :
    dpart (heatT t e) k =ᵐ[volume] heatT t (fun y => G y k) := by
  have h1 := isWeakGrad_heatT ht hw (he.integrable one_le_two) hG
  have h2 := isWeakGrad_of_contDiff ((heat_smooth he ht).of_le (by norm_cast))
  have := weakGrad_ae_unique h2 h1
  filter_upwards [this] with y hy
  exact congrFun hy k

end smooth

theorem lintegral_rpow_le_of_eLpNorm_le {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f h : α → ℝ} (hf : AEStronglyMeasurable f μ) (hh : AEStronglyMeasurable h μ) {P : ℝ}
    (hP : 0 < P) {K : ℝ≥0∞} (hle : eLpNorm f (ENNReal.ofReal P) μ ≤ K * eLpNorm h (ENNReal.ofReal P) μ) :
    ∫⁻ x, ‖f x‖ₑ ^ P ∂μ ≤ K ^ P * ∫⁻ x, ‖h x‖ₑ ^ P ∂μ := by
  have hp0 : ENNReal.ofReal P ≠ 0 := by simpa using hP
  have hpt : ENNReal.ofReal P ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hh, ENNReal.toReal_ofReal hP.le] at hle
  have := ENNReal.rpow_le_rpow hle hP.le
  rw [ENNReal.mul_rpow_of_nonneg _ _ hP.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div,
    inv_mul_cancel₀ hP.ne', ENNReal.rpow_one, ENNReal.rpow_one] at this
  exact this

theorem two_pow_eq_ofReal (m : ℕ) : (2 : ℝ≥0∞) ^ (m + 1) = ENNReal.ofReal ((2 : ℝ) ^ (m + 1)) := by
  rw [ENNReal.ofReal_pow (by norm_num)]; simp

/-- **Second derivatives of the smoothed solution.** -/
theorem heat_d2_bound (m : ℕ) : ∃ A : ℝ, 0 ≤ A ∧ ∀ (e g : UnitAddTorus ι → ℝ),
    MemLp e 2 volume → MemLp g 2 volume →
    (∀ k, mFourierCoeff (fun y => (g y : ℂ)) k =
      4 * π ^ 2 * (∑ j, ((k j : ℂ)) ^ 2) * mFourierCoeff (fun y => (e y : ℂ)) k) →
    ∀ t, 0 < t → ∀ i j, ∫⁻ y, ‖dpart (dpart (heatT t e) i) j y‖ₑ ^ ((2 : ℝ) ^ (m + 1)) ≤
      ENNReal.ofReal A ^ ((2 : ℝ) ^ (m + 1)) * ∫⁻ y, ‖g y‖ₑ ^ ((2 : ℝ) ^ (m + 1)) := by
  obtain ⟨A, hA0, hA⟩ := cz_smooth (ι := ι) m
  refine ⟨A, hA0, fun e g he hg hcf t ht i j => ?_⟩
  set P : ℝ := (2 : ℝ) ^ (m + 1)
  have hP1 : 1 < P := one_lt_pow₀ (by norm_num) (Nat.succ_ne_zero m)
  have hcz := hA (heatT t e) (heat_smooth2 he ht) (heat_summable he ht) i j
  rw [two_pow_eq_ofReal] at hcz
  have hlap := heat_lap he hg hcf ht
  have hgi := hg.integrable one_le_two
  rw [eLpNorm_congr_ae hlap, show (fun y => -heatT t g y) = -(heatT t g) from rfl,
    eLpNorm_neg] at hcz
  have hd2c : Continuous (dpart (dpart (heatT t e) i) j) := by
    have h2 := heat_smooth2 he ht
    exact continuous_of_liftT' (contDiff_dpart (n := 0) (contDiff_dpart (n := 1) h2 i) j).continuous
  have h1 := lintegral_rpow_le_of_eLpNorm_le hd2c.aestronglyMeasurable
    (continuous_heatT ht hgi).aestronglyMeasurable (by linarith) hcz
  exact h1.trans (mul_le_mul' le_rfl (lintegral_heatT_rpow_le ht hgi hP1))

end SharpLSI
