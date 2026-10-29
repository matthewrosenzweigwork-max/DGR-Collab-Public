import LeanResearch.PeriodicAttractiveLogGas.ConvolutionYoung
import LeanResearch.PeriodicAttractiveLogGas.GreenWeakFourier
import LeanResearch.PeriodicAttractiveLogGas.OccupationNearContraction
import Mathlib.Analysis.Real.Pi.Bounds

/-! The actual Green convolution and the L2 spectral coercivity used in
source `eq:occupation-chemical`, lines 1967--1976. The Fourier multiplier
is identified with the genuine Haar convolution before Parseval is
used. Checking history and source correspondence are recorded in
`research/reviews/green-l2-coercivity-development.md`. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators ComplexConjugate Convolution lp

namespace PeriodicAttractiveLogGas.GreenL2Coercivity

theorem frequencySq_one_le {k : Frequency} (hk : k ≠ 0) : 1 ≤ frequencySq k := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, k j ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hk (funext hh)
  have hsq : (1 : ℝ) ≤ (k j : ℝ) ^ 2 := by
    rcases lt_or_gt_of_ne hj with hneg | hpos
    · have hh : (k j : ℝ) ≤ -1 := by exact_mod_cast (by omega : k j ≤ -1)
      nlinarith
    · have hh : (1 : ℝ) ≤ k j := by exact_mod_cast (by omega : 1 ≤ k j)
      nlinarith
  exact hsq.trans (Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ)) (Finset.mem_univ j))

theorem norm_greenFourierCoeff_le (k : Frequency) :
    ‖greenFourierCoeff k‖ ≤ 1 / (2 * Real.pi) := by
  by_cases hk : k = 0
  · subst k
    simp only [greenFourierCoeff_zero, norm_zero]
    positivity
  · rw [greenFourierCoeff_of_ne_zero hk, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) (frequencySq_pos hk)))]
    apply one_div_le_one_div_of_le (mul_pos (by norm_num) Real.pi_pos)
    have hh := mul_le_mul_of_nonneg_left (frequencySq_one_le hk) (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).le
    simpa only [mul_one] using hh

def gap (β₀ : ℝ) : ℝ := 1 - β₀ / (2 * Real.pi)

theorem gap_pos {β₀ : ℝ} (hβ₀ : β₀ < 4) : 0 < gap β₀ := by
  unfold gap
  apply sub_pos.mpr
  apply (div_lt_one (mul_pos (by norm_num) Real.pi_pos)).mpr
  linarith [Real.pi_gt_three]

/-- The actual Haar convolution, with the original normalization. -/
def convolution (f : Torus → ℝ) : Torus → ℝ :=
  regularGreenRepresentative ⋆[ContinuousLinearMap.mul ℝ ℝ, torusMeasure] f

theorem convolution_apply (f : Torus → ℝ) (x : Torus) :
    convolution f x = ∫ y, regularGreenRepresentative y * f (x - y) ∂torusMeasure := rfl

theorem convolution_eq_sub (f : Torus → ℝ) (x : Torus) :
    convolution f x = ∫ y, regularGreenRepresentative (x - y) * f y ∂torusMeasure :=
  convolution_mul_swap

theorem convolution_eq_original (f : Torus → ℝ) (x : Torus) :
    convolution f x = ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure := by
  rw [convolution_eq_sub]
  apply integral_congr_ae
  filter_upwards [(torusMeasure.measurePreserving_sub_left x).quasiMeasurePreserving.ae
    regularGreenRepresentative_ae] with y hy
  rw [hy]

theorem integrable_convolution_integrand {f : Torus → ℝ}
    (hf : MemLp f 2 torusMeasure) (x : Torus) :
    Integrable (fun y ↦ regularGreenRepresentative y * f (x - y)) torusMeasure :=
  regularGreenRepresentative_memLp.integrable_mul
    (hf.comp_measurePreserving (torusMeasure.measurePreserving_sub_left x))

theorem integrable_convolution_integrand_sub {f : Torus → ℝ}
    (hf : MemLp f 2 torusMeasure) (x : Torus) :
    Integrable (fun y ↦ regularGreenRepresentative (x - y) * f y) torusMeasure :=
  (regularGreenRepresentative_memLp.comp_measurePreserving
    (torusMeasure.measurePreserving_sub_left x)).integrable_mul hf

theorem convolution_memLp {f : Torus → ℝ} (hf : MemLp f 2 torusMeasure) :
    MemLp (convolution f) 2 torusMeasure := by
  have hg : MemLp regularGreenRepresentative (ENNReal.ofReal (youngExponent 2)) torusMeasure := by
    simpa only [youngExponent_two, ENNReal.ofReal_one] using
      (memLp_one_iff_integrable.mpr regularGreenRepresentative_integrable)
  have hh := memLp_inner_convolution (r := 2) (E := ℝ) (by norm_num) hg hf
  have he (a b : ℝ) : inner ℝ a b = a * b := by simp [mul_comm]
  change MemLp (fun x ↦ ∫ y, regularGreenRepresentative y * f (x - y) ∂torusMeasure)
    2 torusMeasure
  simpa only [he, ENNReal.ofReal_ofNat] using hh

theorem convolution_integrable {f : Torus → ℝ} (hf : MemLp f 2 torusMeasure) :
    Integrable (convolution f) torusMeasure :=
  (convolution_memLp hf).integrable (by norm_num)

theorem convolution_integral_zero {f : Torus → ℝ} (hf : MemLp f 2 torusMeasure) :
    (∫ x, convolution f x ∂torusMeasure) = 0 := by
  rw [convolution, integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
    regularGreenRepresentative_integrable (hf.integrable (by norm_num)),
    regularGreenRepresentative_integral_zero]
  simp

theorem complex_memLp {p : ℝ≥0∞} {f : Torus → ℝ} (hf : MemLp f p torusMeasure) :
    MemLp (fun x ↦ (f x : ℂ)) p torusMeasure := by
  apply hf.mono (Complex.continuous_ofReal.comp_aestronglyMeasurable hf.aestronglyMeasurable)
  exact Eventually.of_forall fun x ↦ by simp

theorem complex_lpNorm {p : ℝ≥0∞} {f : Torus → ℝ} (hf : AEStronglyMeasurable f torusMeasure) :
    lpNorm (fun x ↦ (f x : ℂ)) p torusMeasure = lpNorm f p torusMeasure := by
  exact congrArg ENNReal.toReal (eLpNorm_congr_norm_ae
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hf) hf
    (Eventually.of_forall fun x ↦ by simp))

local instance circleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩

theorem mFourier_argument_add (k : Frequency) (x y : Torus) :
    UnitAddTorus.mFourier k (x + y) =
      UnitAddTorus.mFourier k x * UnitAddTorus.mFourier k y := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply,
    zsmul_add, AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

theorem norm_mFourier_apply (k : Frequency) (x : Torus) :
    ‖UnitAddTorus.mFourier k x‖ = 1 := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_apply,
    norm_prod, Circle.norm_coe, Finset.prod_const_one]

/-- The actual convolution multiplier identity, proved by integrable
Fubini and Haar translation. No Fourier support restriction is used. -/
theorem mFourierCoeff_convolution {F G : Torus → ℂ}
    (hF : Integrable F torusMeasure) (hG : Integrable G torusMeasure) (k : Frequency) :
    UnitAddTorus.mFourierCoeff
      (F ⋆[ContinuousLinearMap.mul ℂ ℂ, torusMeasure] G) k =
        UnitAddTorus.mFourierCoeff F k * UnitAddTorus.mFourierCoeff G k := by
  let χ : Torus → ℂ := UnitAddTorus.mFourier (-k)
  have hχ : Continuous χ := (UnitAddTorus.mFourier (-k)).continuous
  have hj : Integrable (fun z : Torus × Torus ↦ F z.2 * G (z.1 - z.2))
      (torusMeasure.prod torusMeasure) :=
    hF.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ) hG
  have hw : Integrable (fun z : Torus × Torus ↦ χ z.1 * (F z.2 * G (z.1 - z.2)))
      (torusMeasure.prod torusMeasure) :=
    hj.bdd_mul (hχ.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ (norm_mFourier_apply (-k) z.1).le)
  have harg (x y : Torus) : χ x = χ (x - y) * χ y := by
    dsimp only [χ]
    rw [← mFourier_argument_add, sub_add_cancel]
  rw [torus_mFourierCoeff_eq_integral]
  change (∫ x, χ x * (∫ y, F y * G (x - y) ∂torusMeasure) ∂torusMeasure) = _
  calc
    _ = ∫ x, ∫ y, χ x * (F y * G (x - y)) ∂torusMeasure ∂torusMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x ↦ (integral_const_mul (χ x) _).symm
    _ = ∫ y, ∫ x, χ x * (F y * G (x - y)) ∂torusMeasure ∂torusMeasure :=
      integral_integral_swap hw
    _ = ∫ y, (χ y * F y) * UnitAddTorus.mFourierCoeff G k ∂torusMeasure := by
      apply integral_congr_ae
      filter_upwards with y
      calc
        _ = ∫ x, (χ y * F y) * (χ (x - y) * G (x - y)) ∂torusMeasure := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x ↦ by dsimp only; rw [harg x y]; ring
        _ = (χ y * F y) * (∫ x, χ (x - y) * G (x - y) ∂torusMeasure) :=
          integral_const_mul _ _
        _ = (χ y * F y) * (∫ x, χ x * G x ∂torusMeasure) := by
          congr 1
          exact integral_sub_right_eq_self (fun x ↦ χ x * G x) y
        _ = _ := by rw [torus_mFourierCoeff_eq_integral]
    _ = _ := by
      rw [integral_mul_const, torus_mFourierCoeff_eq_integral F k]

theorem complex_convolution (f : Torus → ℝ) (x : Torus) :
    ((convolution f x : ℝ) : ℂ) =
      ((fun y ↦ (regularGreenRepresentative y : ℂ))
        ⋆[ContinuousLinearMap.mul ℂ ℂ, torusMeasure] (fun y ↦ (f y : ℂ))) x := by
  calc
    _ = ∫ y, ((regularGreenRepresentative y * f (x - y) : ℝ) : ℂ) ∂torusMeasure :=
      integral_ofReal.symm
    _ = _ := by
      change (∫ y, ((regularGreenRepresentative y * f (x - y) : ℝ) : ℂ) ∂torusMeasure) =
        ∫ y, (regularGreenRepresentative y : ℂ) * (f (x - y) : ℂ) ∂torusMeasure
      apply integral_congr_ae
      exact Eventually.of_forall fun y ↦ Complex.ofReal_mul _ _

theorem convolution_fourierCoeff {f : Torus → ℝ} (hf : MemLp f 2 torusMeasure)
    (k : Frequency) :
    UnitAddTorus.mFourierCoeff (fun x ↦ (convolution f x : ℂ)) k =
      greenFourierCoeff k * UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k := by
  have he : (fun x ↦ (convolution f x : ℂ)) =
      (fun y ↦ (regularGreenRepresentative y : ℂ))
        ⋆[ContinuousLinearMap.mul ℂ ℂ, torusMeasure] (fun y ↦ (f y : ℂ)) :=
    funext (complex_convolution f)
  rw [he, mFourierCoeff_convolution
    ((complex_memLp regularGreenRepresentative_memLp).integrable (by norm_num))
    ((complex_memLp hf).integrable (by norm_num)), regularGreenRepresentative_fourierCoeff]

theorem complex_toLp_norm {f : Torus → ℝ} (hf : MemLp f 2 torusMeasure) :
    ‖(complex_memLp hf).toLp (fun x ↦ (f x : ℂ))‖ = lpNorm f 2 torusMeasure := by
  rw [Lp.norm_toLp, toReal_eLpNorm]
  exact complex_lpNorm hf.aestronglyMeasurable

/-- The Fourier Hilbert-basis isometry is Parseval on the full L2 space.
Its actual convolution coefficients give the sharp source constant. -/
theorem convolution_lpNorm_le {f : Torus → ℝ} (hf : MemLp f 2 torusMeasure) :
    lpNorm (convolution f) 2 torusMeasure ≤
      (1 / (2 * Real.pi)) * lpNorm f 2 torusMeasure := by
  let F : Lp ℂ 2 torusMeasure := (complex_memLp hf).toLp (fun x ↦ (f x : ℂ))
  let G : Lp ℂ 2 torusMeasure :=
    (complex_memLp (convolution_memLp hf)).toLp (fun x ↦ (convolution f x : ℂ))
  let c : ℝ := 1 / (2 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hF : (F : Torus → ℂ) =ᵐ[torusMeasure] (fun x ↦ (f x : ℂ)) :=
    (complex_memLp hf).coeFn_toLp
  have hG : (G : Torus → ℂ) =ᵐ[torusMeasure] (fun x ↦ (convolution f x : ℂ)) :=
    (complex_memLp (convolution_memLp hf)).coeFn_toLp
  have hcoeff (k : Frequency) :
      ‖torusFourierBasis.repr G k‖ ≤ ‖(c • torusFourierBasis.repr F) k‖ := by
    change ‖torusFourierBasis.repr G k‖ ≤ ‖c • (torusFourierBasis.repr F k)‖
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc, torusFourierBasis_repr,
      torusFourierBasis_repr, torus_mFourierCoeff_congr hG,
      torus_mFourierCoeff_congr hF, convolution_fourierCoeff hf, norm_mul]
    exact mul_le_mul_of_nonneg_right (norm_greenFourierCoeff_le k) (norm_nonneg _)
  have hh := lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0) hcoeff
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc,
    torusFourierBasis.repr.norm_map, torusFourierBasis.repr.norm_map] at hh
  change ‖G‖ ≤ c * ‖F‖ at hh
  have hFn : ‖F‖ = lpNorm f 2 torusMeasure := complex_toLp_norm hf
  have hGn : ‖G‖ = lpNorm (convolution f) 2 torusMeasure :=
    complex_toLp_norm (convolution_memLp hf)
  rw [hGn, hFn] at hh
  exact hh

theorem residual_memLp {f : Torus → ℝ} (hf : MemLp f 2 torusMeasure) (β : ℝ) :
    MemLp (fun x ↦ f x - β * convolution f x) 2 torusMeasure :=
  hf.sub ((convolution_memLp hf).const_mul β)

/-- The reverse triangle estimate for the genuine integral operator.
It applies to all L2 inputs, and therefore to the source mean-zero space. -/
theorem coercivity {f : Torus → ℝ} (hf : MemLp f 2 torusMeasure)
    {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) :
    gap β₀ * lpNorm f 2 torusMeasure ≤
      lpNorm (fun x ↦ f x - β * convolution f x) 2 torusMeasure := by
  have hb := convolution_lpNorm_le hf
  have hn : lpNorm (fun x ↦ β * convolution f x) 2 torusMeasure =
      β * lpNorm (convolution f) 2 torusMeasure := by
    simpa only [Pi.smul_apply, smul_eq_mul, coe_nnnorm, Real.norm_eq_abs,
      abs_of_nonneg hβ] using! lpNorm_const_smul β (convolution f) torusMeasure (p := 2)
  have ht := lpNorm_add_le (residual_memLp hf β) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    (g := fun x ↦ β * convolution f x)
  have he : (fun x ↦ f x - β * convolution f x) + (fun x ↦ β * convolution f x) = f := by
    funext x
    simp only [Pi.add_apply, sub_add_cancel]
  rw [he, hn] at ht
  have hβb := mul_le_mul_of_nonneg_left hb hβ
  have hβb' := mul_le_mul_of_nonneg_right hβ₀
    (mul_nonneg (by positivity : 0 ≤ 1 / (2 * Real.pi))
      (lpNorm_nonneg (f := f) (p := 2) (μ := torusMeasure)))
  calc
    gap β₀ * lpNorm f 2 torusMeasure = lpNorm f 2 torusMeasure -
        β₀ * (1 / (2 * Real.pi) * lpNorm f 2 torusMeasure) := by unfold gap; ring
    _ ≤ _ := by linarith only [ht, hβb, hβb']

theorem mean_zero_coercivity {f : Torus → ℝ} (hf : MemLp f 2 torusMeasure)
    (hmean : (∫ x, f x ∂torusMeasure) = 0)
    {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) :
    0 < gap β₀ ∧
      (∫ x, convolution f x ∂torusMeasure) = 0 ∧
      (∫ x, (f x - β * convolution f x) ∂torusMeasure) = 0 ∧
      gap β₀ * lpNorm f 2 torusMeasure ≤
        lpNorm (fun x ↦ f x - β * convolution f x) 2 torusMeasure := by
  refine ⟨gap_pos hsub, convolution_integral_zero hf, ?_, coercivity hf hβ hβ₀⟩
  rw [integral_sub (hf.integrable (by norm_num)) ((convolution_integrable hf).const_mul β),
    integral_const_mul, hmean, convolution_integral_zero hf]
  ring

theorem convolution_fourierCoeff_ne_zero {f : Torus → ℝ}
    (hf : MemLp f 2 torusMeasure) {k : Frequency} (hk : k ≠ 0) :
    UnitAddTorus.mFourierCoeff (fun x ↦ (convolution f x : ℂ)) k =
      ((1 / (2 * Real.pi * frequencySq k) : ℝ) : ℂ) *
        UnitAddTorus.mFourierCoeff (fun x ↦ (f x : ℂ)) k := by
  rw [convolution_fourierCoeff hf, greenFourierCoeff_of_ne_zero hk]

/-- An explicit endpoint on the full mean-zero real L2 space. The right
side is finite by `residual_memLp`; no regularity or support assumption
is imposed on the L2 class. -/
theorem mean_zero_L2_coercivity (f : Lp ℝ 2 torusMeasure)
    (hmean : (∫ x, f x ∂torusMeasure) = 0)
    {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4) :
    0 < gap β₀ ∧
      MemLp (fun x ↦ f x - β * convolution f x) 2 torusMeasure ∧
      (∫ x, (f x - β * convolution f x) ∂torusMeasure) = 0 ∧
      gap β₀ * ‖f‖ ≤ lpNorm (fun x ↦ f x - β * convolution f x) 2 torusMeasure := by
  have hh := mean_zero_coercivity (Lp.memLp f) hmean hβ hβ₀ hsub
  have hn : lpNorm f 2 torusMeasure = ‖f‖ := by rw [Lp.norm_def, toReal_eLpNorm]
  rw [hn] at hh
  exact ⟨hh.1, residual_memLp (Lp.memLp f) β, hh.2.2.1, hh.2.2.2⟩

/-- The same estimate written literally with the source representative. -/
theorem original_coercivity {f : Torus → ℝ} (hf : MemLp f 2 torusMeasure)
    {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) :
    gap β₀ * lpNorm f 2 torusMeasure ≤
      lpNorm (fun x ↦ f x - β * (∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure))
        2 torusMeasure := by
  simpa only [convolution_eq_original] using coercivity hf hβ hβ₀

theorem integrable_original_convolution_integrand {f : Torus → ℝ}
    (hf : MemLp f 2 torusMeasure) (x : Torus) :
    Integrable (fun y ↦ greenRealRepresentative (x - y) * f y) torusMeasure := by
  apply (integrable_convolution_integrand_sub hf x).congr
  filter_upwards [(torusMeasure.measurePreserving_sub_left x).quasiMeasurePreserving.ae
    regularGreenRepresentative_ae] with y hy
  rw [hy]

/-- Changing the input on a Haar-null set does not change even a single
value of the actual convolution. Thus the L2-class endpoint is independent
of the selected measurable representative. -/
theorem convolution_congr_ae {f g : Torus → ℝ} (hfg : f =ᵐ[torusMeasure] g) :
    convolution f = convolution g := by
  funext x
  rw [convolution_eq_sub, convolution_eq_sub]
  apply integral_congr_ae
  exact hfg.mono fun y hy ↦ by dsimp only; rw [hy]

theorem convolution_eq_densityPotential (f : Torus → ℝ) :
    convolution f = OccupationNearContraction.densityPotential f := by
  funext x
  rw [convolution_eq_sub]
  unfold OccupationNearContraction.densityPotential
  apply integral_congr_ae
  exact Eventually.of_forall fun y ↦ mul_comm _ _

theorem L4_coercivity {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure)
    {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) :
    gap β₀ * lpNorm f 2 torusMeasure ≤
      lpNorm (fun x ↦ f x - β * OccupationNearContraction.densityPotential f x) 2 torusMeasure := by
  have hf₂ : MemLp f 2 torusMeasure := hf.mono_exponent (by norm_num)
  simpa only [convolution_eq_densityPotential] using coercivity hf₂ hβ hβ₀

theorem centered_memLp {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure) :
    MemLp (fun x ↦ f x - 1) 2 torusMeasure :=
  (hf.sub (memLp_const (1 : ℝ))).mono_exponent (by norm_num)

theorem centered_mean_zero {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure)
    (hmass : (∫ x, f x ∂torusMeasure) = 1) :
    (∫ x, (f x - 1) ∂torusMeasure) = 0 := by
  rw [integral_sub (hf.integrable (by norm_num)) (integrable_const (1 : ℝ)),
    hmass, integral_const, probReal_univ, one_smul, sub_self]

theorem centered_convolution {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure) (x : Torus) :
    convolution (fun y ↦ f y - 1) x = OccupationNearContraction.densityPotential f x := by
  rw [convolution_eq_densityPotential]
  have hh := OccupationNearContraction.densityPotential_sub hf
    (memLp_const (1 : ℝ)) x
  have he : f - (fun _ ↦ (1 : ℝ)) = (fun y ↦ f y - 1) := rfl
  rw [he, OccupationNearContraction.densityPotential_one, sub_zero] at hh
  exact hh

theorem centered_L4_residual_memLp {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure) (β : ℝ) :
    MemLp (fun x ↦ (f x - 1) - β * OccupationNearContraction.densityPotential f x)
      2 torusMeasure := by
  simpa only [centered_convolution hf] using residual_memLp (centered_memLp hf) β

theorem centered_L4_coercivity {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure)
    {β β₀ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) :
    gap β₀ * lpNorm (fun x ↦ f x - 1) 2 torusMeasure ≤
      lpNorm (fun x ↦ (f x - 1) - β * OccupationNearContraction.densityPotential f x)
        2 torusMeasure := by
  simpa only [centered_convolution hf] using coercivity (centered_memLp hf) hβ hβ₀

/-- The actual nearby fixed point supplies the source's `v = μθ - 1`.
Its existence, probability mass and L4 regularity are derived in the
released contraction module, rather than imposed as an analytic premise. -/
theorem nearFixedPoint_coercivity {J : ℕ} (hJ : 0 < J)
    {θ : MeshCells.MeshIndex J → ℝ} {β β₀ : ℝ}
    (h : OccupationNearContraction.NearParameters θ β β₀) (hsub : β₀ < 4) :
    let f := (OccupationNearContraction.nearFixedPoint hJ h).val
    0 < gap β₀ ∧
      MemLp (fun x ↦ f x - 1) 2 torusMeasure ∧
      (∫ x, (f x - 1) ∂torusMeasure) = 0 ∧
      (∀ x, convolution (fun y ↦ f y - 1) x = OccupationNearContraction.densityPotential f x) ∧
      MemLp (fun x ↦ (f x - 1) - β * OccupationNearContraction.densityPotential f x) 2 torusMeasure ∧
      (∫ x, ((f x - 1) - β * OccupationNearContraction.densityPotential f x) ∂torusMeasure) = 0 ∧
      gap β₀ * lpNorm (fun x ↦ f x - 1) 2 torusMeasure ≤
        lpNorm (fun x ↦ (f x - 1) - β * OccupationNearContraction.densityPotential f x)
          2 torusMeasure := by
  let f := (OccupationNearContraction.nearFixedPoint hJ h).val
  have hf : MemLp f 4 torusMeasure := Lp.memLp f
  have hm : (∫ x, f x ∂torusMeasure) = 1 :=
    (OccupationNearContraction.nearFixedPoint hJ h).property.2.1
  refine ⟨gap_pos hsub, centered_memLp hf, centered_mean_zero hf hm,
    centered_convolution hf, centered_L4_residual_memLp hf β, ?_,
    centered_L4_coercivity hf h.beta_nonneg h.beta_le⟩
  have hh := (mean_zero_coercivity (centered_memLp hf) (centered_mean_zero hf hm)
    h.beta_nonneg h.beta_le hsub).2.2.1
  simpa only [centered_convolution hf] using hh

end PeriodicAttractiveLogGas.GreenL2Coercivity
