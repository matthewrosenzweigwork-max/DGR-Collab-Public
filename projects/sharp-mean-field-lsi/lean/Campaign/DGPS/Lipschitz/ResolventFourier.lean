import DGPS.Lipschitz.ResolventSobolev
import DGPS.Lipschitz.DuhamelPotential
import DGPS.Foundations.SobolevFourier
import DGPS.Analysis.PeriodicHeatKernel

/-!
# LIP010c3: the resolvent as a Fourier multiplier and its weak gradient

For `F ∈ L²(𝕋^d)`, with `R F = ∫₀^∞ e^{-t} H_t F dt` and `∇R F = ∫₀^∞ e^{-t} ∇H_t F dt`
(`DGPS.Lipschitz.resolvent`, `resolventGrad`):

* (a) `(R F)^(k) = (1 + 4π²|k|²)⁻¹ F^(k)` (the heat semigroup is `e^{tΔ}`, with multiplier
  `e^{-4π²|k|² t}`, so the resolvent multiplier is `(1 + gradWeight k)⁻¹`);
* (b) `∇R F` is the weak gradient of `R F`;
* (c) `R F` is the unique `H¹` weak solution of `(1 - Δ) u = F`.
-/

open MeasureTheory Set Filter
open scoped ENNReal Real

namespace DGPS.Lipschitz

section Swap

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Joint integrability on `(0,∞) × 𝕋^d` from a slicewise `L¹` bound. -/
theorem integrable_of_slice_bound {Θ : ℝ × Torus d → E} (hΘ : StronglyMeasurable Θ)
    {c : ℝ → ℝ} (hc : IntegrableOn c (Ioi 0))
    (hb : ∀ t : ℝ, 0 < t → ∫⁻ x, ‖Θ (t, x)‖ₑ ∂haar d ≤ ENNReal.ofReal (c t)) :
    Integrable Θ ((volume.restrict (Ioi (0 : ℝ))).prod (haar d)) := by
  refine ⟨hΘ.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_prod _ hΘ.enorm.aemeasurable]
  calc ∫⁻ t, ∫⁻ x, ‖Θ (t, x)‖ₑ ∂haar d ∂(volume.restrict (Ioi (0 : ℝ)))
      ≤ ∫⁻ t, ENNReal.ofReal (c t) ∂(volume.restrict (Ioi (0 : ℝ))) :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).2
          (Filter.Eventually.of_forall hb))
    _ ≤ ∫⁻ t, ‖c t‖ₑ ∂(volume.restrict (Ioi (0 : ℝ))) :=
        lintegral_mono fun t => Real.ofReal_le_enorm _
    _ < ⊤ := hc.2

omit [CompleteSpace E] in
/-- Fubini on `(0,∞) × 𝕋^d`. -/
theorem integral_swap_Ioi {Θ : ℝ × Torus d → E} (hΘ : StronglyMeasurable Θ)
    {c : ℝ → ℝ} (hc : IntegrableOn c (Ioi 0))
    (hb : ∀ t : ℝ, 0 < t → ∫⁻ x, ‖Θ (t, x)‖ₑ ∂haar d ≤ ENNReal.ofReal (c t)) :
    ∫ x, (∫ t in Ioi (0 : ℝ), Θ (t, x)) ∂haar d = ∫ t in Ioi (0 : ℝ), ∫ x, Θ (t, x) ∂haar d :=
  (integral_integral_swap (f := fun t x => Θ (t, x)) (integrable_of_slice_bound hΘ hc hb)).symm

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Domination of a slice `L¹` norm by that of a reference function. -/
theorem slice_bound_of_dom {E' : Type*} [NormedAddCommGroup E'] {Θ : ℝ × Torus d → E}
    {Ξ : ℝ × Torus d → E'} {B c₀ t : ℝ} (hB : 0 ≤ B)
    (hdom : ∀ x, ‖Θ (t, x)‖ ≤ Real.exp (-t) * B * ‖Ξ (t, x)‖)
    (hΞ : ∫⁻ x, ‖Ξ (t, x)‖ₑ ∂haar d ≤ ENNReal.ofReal c₀) :
    ∫⁻ x, ‖Θ (t, x)‖ₑ ∂haar d ≤ ENNReal.ofReal (Real.exp (-t) * B * c₀) := by
  have hp : 0 ≤ Real.exp (-t) * B := by positivity
  calc ∫⁻ x, ‖Θ (t, x)‖ₑ ∂haar d
      ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (-t) * B) * ‖Ξ (t, x)‖ₑ ∂haar d := by
        refine lintegral_mono fun x => ?_
        rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hp]
        exact ENNReal.ofReal_le_ofReal (hdom x)
    _ = ENNReal.ofReal (Real.exp (-t) * B) * ∫⁻ x, ‖Ξ (t, x)‖ₑ ∂haar d :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (-t) * B) * ENNReal.ofReal c₀ := by gcongr
    _ = ENNReal.ofReal (Real.exp (-t) * B * c₀) := (ENNReal.ofReal_mul hp).symm

end Swap

section Slices

variable {d : ℕ}

/-- The `L¹` norm of the heat slice is at most `2^d ‖F‖₁`. -/
theorem lintegral_heatJ_le {F : Torus d → ℝ} (hF : AEStronglyMeasurable F (haar d))
    (hF1 : eLpNorm F 1 (haar d) ≠ ⊤) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, ‖heatJ (hF.mk F) (t, x)‖ₑ ∂haar d ≤
      ENNReal.ofReal (2 ^ d * (eLpNorm F 1 (haar d)).toReal) := by
  have h := eLpNorm_heatOp_le ht (p := 1) (q := 1) le_rfl le_rfl hF
  have e : ∫⁻ x, ‖heatJ (hF.mk F) (t, x)‖ₑ ∂haar d = eLpNorm (heatOp t F) 1 (haar d) := by
    have hm : AEStronglyMeasurable (heatOp t F) (haar d) := by
      have : heatOp t F = fun x => heatJ (hF.mk F) (t, x) := (funext (heatJ_eq hF.ae_eq_mk ht)).symm
      rw [this]
      exact ((stronglyMeasurable_heatJ hF.stronglyMeasurable_mk.measurable).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hm]
    exact lintegral_congr fun x => by rw [heatJ_eq hF.ae_eq_mk ht]
  simp only [inv_one, ENNReal.toReal_one, sub_self, Real.rpow_zero, mul_one] at h
  rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hF1]
  exact h

/-- The `L¹` norm of the gradient slice is at most `2^d (d+1) t^{-1/2} ‖F‖₁`. -/
theorem lintegral_gradJ_le {F : Torus d → ℝ} (hF : AEStronglyMeasurable F (haar d))
    (hF1 : eLpNorm F 1 (haar d) ≠ ⊤) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, ‖gradJ (hF.mk F) (t, x)‖ₑ ∂haar d ≤
      ENNReal.ofReal (2 ^ d * (d + 1) * t ^ (-(1 : ℝ) / 2) * (eLpNorm F 1 (haar d)).toReal) := by
  have h := eLpNorm_kerGrad_le ht (p := 1) (q := 1) le_rfl le_rfl hF
  have e : ∫⁻ x, ‖gradJ (hF.mk F) (t, x)‖ₑ ∂haar d = eLpNorm (kerGrad t F) 1 (haar d) := by
    have hm : AEStronglyMeasurable (kerGrad t F) (haar d) := by
      have : kerGrad t F = fun x => gradJ (hF.mk F) (t, x) := (funext (gradJ_eq hF.ae_eq_mk)).symm
      rw [this]
      exact ((stronglyMeasurable_gradJ hF.stronglyMeasurable_mk.measurable).comp_measurable
        (measurable_const.prodMk measurable_id)).aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hm]
    exact lintegral_congr fun x => by rw [gradJ_eq hF.ae_eq_mk]
  simp only [inv_one, ENNReal.toReal_one, sub_self, Real.rpow_zero, mul_one] at h
  rw [e, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hF1]
  have : 2 ^ d * (d + 1) * t ^ (-(1 : ℝ) / 2) = 2 ^ d * (d + 1) * (t ^ (-(1 : ℝ) / 2)) := rfl
  exact h

theorem integrableOn_exp_const (a : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * a) (Ioi 0) :=
  IntegrableOn.congr_fun ((integrableOn_exp_rpow (b := 0) (by norm_num)).const_mul a)
    (fun t _ => by simp [mul_comm]) measurableSet_Ioi

theorem integrableOn_exp_sqrt (a : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t) * (a * t ^ (-(1 : ℝ) / 2))) (Ioi 0) :=
  IntegrableOn.congr_fun ((integrableOn_exp_rpow (b := -(1 : ℝ) / 2) (by norm_num)).const_mul a)
    (fun t _ => by ring) measurableSet_Ioi

end Slices

section FourierMultiplier

variable {d : ℕ}

theorem memLp_resolvent {F : Torus d → ℝ} (hF : MemLp F 2 (haar d)) :
    MemLp (resolvent F) 2 (haar d) ∧ MemLp (resolventGrad F) 2 (haar d) := by
  have hθ : (d : ℝ) * theta 2 2 < 1 := by simp [theta]
  obtain ⟨h1, h2⟩ := resolvent_Lq_bound (d := d) (p := 2) (q := 2) (by norm_num) le_rfl hθ hF.aestronglyMeasurable
  exact ⟨h1.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.eLpNorm_lt_top),
    h2.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.eLpNorm_lt_top)⟩

theorem integrable_of_memLp_two {F : Torus d → ℝ} (hF : MemLp F 2 (haar d)) :
    Integrable F (haar d) := hF.integrable one_le_two

theorem eLpNorm_one_ne_top {F : Torus d → ℝ} (hF : MemLp F 2 (haar d)) :
    eLpNorm F 1 (haar d) ≠ ⊤ :=
  (memLp_one_iff_integrable.2 (integrable_of_memLp_two hF)).eLpNorm_lt_top.ne

/-- **(a)** The Fourier coefficients of the resolvent: `(R F)^(k) = (1 + 4π²|k|²)⁻¹ F^(k)`. -/
theorem fourierCoeff_resolvent {F : Torus d → ℝ} (hF : MemLp F 2 (haar d))
    (k : Fin d → ℤ) :
    fourierCoeff (resolvent F) k = (((1 + gradWeight k)⁻¹ : ℝ) : ℂ) * fourierCoeff F k := by
  have hFG := hF.aestronglyMeasurable.ae_eq_mk
  have hFi := integrable_of_memLp_two hF
  have hF1 := eLpNorm_one_ne_top hF
  set G := hF.aestronglyMeasurable.mk F with hGdef
  set M := (eLpNorm F 1 (haar d)).toReal with hM
  have hw : 0 ≤ gradWeight k := by unfold gradWeight; positivity
  let Θ : ℝ × Torus d → ℂ := fun p =>
    UnitAddTorus.mFourier (-k) p.2 * ((Real.exp (-p.1) * heatJ G p : ℝ) : ℂ)
  have hΘ : StronglyMeasurable Θ := by
    refine Measurable.stronglyMeasurable ?_
    exact ((UnitAddTorus.mFourier (-k)).continuous.measurable.comp measurable_snd).mul
      (Complex.measurable_ofReal.comp
        (((Real.measurable_exp.comp measurable_neg).comp measurable_fst).mul
          (stronglyMeasurable_heatJ hF.aestronglyMeasurable.stronglyMeasurable_mk.measurable).measurable))
  have hdom : ∀ t x, ‖Θ (t, x)‖ ≤ Real.exp (-t) * 1 * ‖heatJ G (t, x)‖ := by
    intro t x
    simp only [Θ, norm_mul, norm_mFourier_apply, Complex.norm_real,
      Real.norm_eq_abs, Real.abs_exp, one_mul, mul_one]
    exact le_rfl
  have hbound : ∀ t : ℝ, 0 < t → ∫⁻ x, ‖Θ (t, x)‖ₑ ∂haar d ≤
      ENNReal.ofReal (Real.exp (-t) * 1 * (2 ^ d * M)) := fun t ht =>
    slice_bound_of_dom zero_le_one (hdom t) (lintegral_heatJ_le hF.aestronglyMeasurable hF1 ht)
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-t) * 1 * (2 ^ d * M)) (Ioi 0) :=
    IntegrableOn.congr_fun (integrableOn_exp_const (2 ^ d * M)) (fun t _ => by simp)
      measurableSet_Ioi
  have hswap := integral_swap_Ioi hΘ hint hbound
  have hL : ∀ x, ∫ t in Ioi (0 : ℝ), Θ (t, x) =
      UnitAddTorus.mFourier (-k) x * ((resolvent F x : ℝ) : ℂ) := by
    intro x
    simp only [Θ]
    rw [integral_const_mul, integral_complex_ofReal, resolvent_eq hFG x]
    simp only [smul_eq_mul]
  have hR : ∀ t : ℝ, 0 < t → ∫ x, Θ (t, x) ∂haar d =
      ((Real.exp (-t) * Real.exp (-(gradWeight k * t)) : ℝ) : ℂ) * fourierCoeff F k := by
    intro t ht
    have h1 : ∀ x, Θ (t, x) = ((Real.exp (-t) : ℝ) : ℂ) *
        (UnitAddTorus.mFourier (-k) x * ((heatOp t F x : ℝ) : ℂ)) := by
      intro x
      simp only [Θ]
      rw [heatJ_eq hFG ht]
      push_cast
      ring
    simp_rw [h1]
    rw [integral_const_mul, ← mFourierCoeff_ofReal_eq]
    have := fourierCoeff_heatOp ht hFi k
    unfold fourierCoeff at this ⊢
    rw [this]
    push_cast
    ring
  have hlhs : fourierCoeff (resolvent F) k = ∫ x, (∫ t in Ioi (0 : ℝ), Θ (t, x)) ∂haar d := by
    unfold fourierCoeff
    rw [mFourierCoeff_ofReal_eq]
    exact (integral_congr_ae (Filter.Eventually.of_forall hL)).symm
  rw [hlhs, hswap]
  have hneg : -(1 + gradWeight k) < 0 := by linarith
  calc ∫ t in Ioi (0 : ℝ), ∫ x, Θ (t, x) ∂haar d
      = ∫ t in Ioi (0 : ℝ), ((Real.exp (-(1 + gradWeight k) * t) : ℝ) : ℂ) * fourierCoeff F k := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
        rw [hR t ht, ← Real.exp_add]
        congr 3
        ring
    _ = ((∫ t in Ioi (0 : ℝ), Real.exp (-(1 + gradWeight k) * t) : ℝ) : ℂ) * fourierCoeff F k := by
        rw [integral_mul_const, integral_complex_ofReal]
    _ = _ := by
        rw [integral_exp_mul_Ioi hneg]
        congr 2
        simp only [mul_zero, Real.exp_zero]
        field_simp

end FourierMultiplier

section WeakGradient

variable {d : ℕ}

/-- **(b)** The resolvent is in `H¹` with weak gradient `resolventGrad F`. -/
theorem isWeakGradient_resolvent {F : Torus d → ℝ} (hF : MemLp F 2 (haar d)) :
    IsWeakGradient (resolvent F) (resolventGrad F) := by
  obtain ⟨hu, hg⟩ := memLp_resolvent hF
  refine ⟨hu, hg, fun φ hφ j => ?_⟩
  have hFG := hF.aestronglyMeasurable.ae_eq_mk
  have hF1 := eLpNorm_one_ne_top hF
  have hFi := integrable_of_memLp_two hF
  set G := hF.aestronglyMeasurable.mk F with hGdef
  have hGm : Measurable G := hF.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  set M := (eLpNorm F 1 (haar d)).toReal with hM
  have hφc : Continuous φ := hφ.continuous_torus
  have hPc : Continuous (coordPartial j φ) := hφ.continuous_coordPartial j
  obtain ⟨Bφ, hBφ⟩ := (isCompact_univ.exists_bound_of_continuousOn hφc.continuousOn)
  obtain ⟨BP, hBP⟩ := (isCompact_univ.exists_bound_of_continuousOn hPc.continuousOn)
  have hBφ0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 0 (mem_univ _))
  have hBP0 : 0 ≤ BP := (norm_nonneg _).trans (hBP 0 (mem_univ _))
  -- u-side Fubini
  let Θ₁ : ℝ × Torus d → ℝ := fun p => Real.exp (-p.1) * heatJ G p * coordPartial j φ p.2
  have hΘ₁ : StronglyMeasurable Θ₁ := by
    refine Measurable.stronglyMeasurable ?_
    exact (((Real.measurable_exp.comp measurable_neg).comp measurable_fst).mul
      (stronglyMeasurable_heatJ hGm).measurable).mul (hPc.measurable.comp measurable_snd)
  have hint1 : IntegrableOn (fun t : ℝ => Real.exp (-t) * BP * (2 ^ d * M)) (Ioi 0) :=
    IntegrableOn.congr_fun (integrableOn_exp_const (BP * (2 ^ d * M))) (fun t _ => by ring)
      measurableSet_Ioi
  have hb1 : ∀ t : ℝ, 0 < t → ∫⁻ x, ‖Θ₁ (t, x)‖ₑ ∂haar d ≤
      ENNReal.ofReal (Real.exp (-t) * BP * (2 ^ d * M)) := fun t ht =>
    slice_bound_of_dom hBP0 (fun x => by
      simp only [Θ₁, norm_mul, Real.norm_eq_abs, Real.abs_exp]
      have := hBP x (mem_univ _)
      rw [Real.norm_eq_abs] at this
      calc Real.exp (-t) * ‖heatJ G (t, x)‖ * |coordPartial j φ x|
          ≤ Real.exp (-t) * ‖heatJ G (t, x)‖ * BP := by gcongr
        _ = Real.exp (-t) * BP * ‖heatJ G (t, x)‖ := by ring)
      (lintegral_heatJ_le hF.aestronglyMeasurable hF1 ht)
  have hswap1 := integral_swap_Ioi hΘ₁ hint1 hb1
  -- gradient-side Fubini (vector valued, for a.e. integrability)
  let Ξ : ℝ × Torus d → Tangent d := fun p => Real.exp (-p.1) • gradJ G p
  have hΞ : StronglyMeasurable Ξ := by
    refine Measurable.stronglyMeasurable ?_
    exact ((Real.measurable_exp.comp measurable_neg).comp measurable_fst).smul
      (stronglyMeasurable_gradJ hGm).measurable
  have hint2 : IntegrableOn (fun t : ℝ => Real.exp (-t) * 1 * (2 ^ d * (d + 1) * t ^ (-(1 : ℝ) / 2) * M))
      (Ioi 0) :=
    IntegrableOn.congr_fun (integrableOn_exp_sqrt (2 ^ d * (d + 1) * M)) (fun t _ => by ring)
      measurableSet_Ioi
  have hb2 : ∀ t : ℝ, 0 < t → ∫⁻ x, ‖Ξ (t, x)‖ₑ ∂haar d ≤
      ENNReal.ofReal (Real.exp (-t) * 1 * (2 ^ d * (d + 1) * t ^ (-(1 : ℝ) / 2) * M)) := fun t ht =>
    slice_bound_of_dom zero_le_one (fun x => by
      simp only [Ξ, norm_smul, Real.norm_eq_abs, Real.abs_exp, mul_one]; exact le_rfl)
      (lintegral_gradJ_le hF.aestronglyMeasurable hF1 ht)
  have hΞi := integrable_of_slice_bound hΞ hint2 hb2
  have hΞae := hΞi.prod_left_ae
  -- scalar component Θ₂
  let Θ₂ : ℝ × Torus d → ℝ := fun p => Real.exp (-p.1) * gradJ G p j * φ p.2
  have hΘ₂ : StronglyMeasurable Θ₂ := by
    refine Measurable.stronglyMeasurable ?_
    exact (((Real.measurable_exp.comp measurable_neg).comp measurable_fst).mul
      ((EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).continuous.measurable.comp
        (stronglyMeasurable_gradJ hGm).measurable)).mul (hφc.measurable.comp measurable_snd)
  have hint3 : IntegrableOn (fun t : ℝ => Real.exp (-t) * Bφ * (2 ^ d * (d + 1) * t ^ (-(1 : ℝ) / 2) * M))
      (Ioi 0) :=
    IntegrableOn.congr_fun (integrableOn_exp_sqrt (Bφ * (2 ^ d * (d + 1) * M))) (fun t _ => by ring)
      measurableSet_Ioi
  have hb3 : ∀ t : ℝ, 0 < t → ∫⁻ x, ‖Θ₂ (t, x)‖ₑ ∂haar d ≤
      ENNReal.ofReal (Real.exp (-t) * Bφ * (2 ^ d * (d + 1) * t ^ (-(1 : ℝ) / 2) * M)) := fun t ht =>
    slice_bound_of_dom hBφ0 (fun x => by
      simp only [Θ₂, norm_mul, Real.norm_eq_abs, Real.abs_exp]
      have h1 := hBφ x (mem_univ _)
      rw [Real.norm_eq_abs] at h1
      have h2 : |gradJ G (t, x) j| ≤ ‖gradJ G (t, x)‖ := by
        simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (gradJ G (t, x)) j
      calc Real.exp (-t) * |gradJ G (t, x) j| * |φ x|
          ≤ Real.exp (-t) * ‖gradJ G (t, x)‖ * Bφ := by gcongr
        _ = Real.exp (-t) * Bφ * ‖gradJ G (t, x)‖ := by ring)
      (lintegral_gradJ_le hF.aestronglyMeasurable hF1 ht)
  have hswap2 := integral_swap_Ioi hΘ₂ hint3 hb3
  -- pointwise t-integrals
  have hL1 : ∀ x, ∫ t in Ioi (0 : ℝ), Θ₁ (t, x) = resolvent F x * coordPartial j φ x := by
    intro x
    simp only [Θ₁]
    rw [integral_mul_const, resolvent_eq hFG x]
    simp only [smul_eq_mul]
  have hL2 : ∀ᵐ x ∂haar d, ∫ t in Ioi (0 : ℝ), Θ₂ (t, x) = resolventGrad F x j * φ x := by
    filter_upwards [hΞae] with x hx
    simp only [Θ₂]
    rw [integral_mul_const, resolventGrad_eq hFG x]
    congr 1
    have hc := (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).integral_comp_comm hx
    have hΞx : (fun t : ℝ => Ξ (t, x)) = fun t => Real.exp (-t) • gradJ G (t, x) := rfl
    rw [hΞx] at hc
    simp only [EuclideanSpace.coe_proj] at hc
    exact hc
  -- slice identities
  have hS1 : ∀ t ∈ Ioi (0 : ℝ), ∫ x, Θ₁ (t, x) ∂haar d =
      Real.exp (-t) * (-∫ x, kerGrad t F x j * φ x ∂haar d) := by
    intro t ht
    rw [← slice_ibp ht hFi hφ j, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Θ₁]
    rw [heatJ_eq hFG ht]
    ring
  have hS2 : ∀ t ∈ Ioi (0 : ℝ), ∫ x, Θ₂ (t, x) ∂haar d =
      Real.exp (-t) * ∫ x, kerGrad t F x j * φ x ∂haar d := by
    intro t ht
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Θ₂]
    rw [gradJ_eq hFG]
    ring
  have e1 : ∫ x, resolvent F x * coordPartial j φ x ∂haar d =
      ∫ t in Ioi (0 : ℝ), Real.exp (-t) * (-∫ x, kerGrad t F x j * φ x ∂haar d) := by
    rw [← integral_congr_ae (Filter.Eventually.of_forall hL1), hswap1]
    exact setIntegral_congr_fun measurableSet_Ioi hS1
  have e2 : ∫ x, resolventGrad F x j * φ x ∂haar d =
      ∫ t in Ioi (0 : ℝ), Real.exp (-t) * ∫ x, kerGrad t F x j * φ x ∂haar d := by
    rw [← integral_congr_ae hL2, hswap2]
    exact setIntegral_congr_fun measurableSet_Ioi hS2
  rw [e1, e2, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only
  ring

end WeakGradient

section WeakSolution

variable {d : ℕ}

theorem integrable_mul_of_memLp_two' {f h : Torus d → ℝ} (hf : MemLp f 2 (haar d))
    (hh : MemLp h 2 (haar d)) : Integrable (fun x => f x * h x) (haar d) :=
  hf.integrable_mul hh

theorem fourierCoeff_sub'' {f h : Torus d → ℝ} (hf : MemLp f 2 (haar d)) (hh : MemLp h 2 (haar d))
    (k : Fin d → ℤ) :
    fourierCoeff (fun x => f x - h x) k = fourierCoeff f k - fourierCoeff h k :=
  SharpLSI.cf_sub (hf.integrable one_le_two) (hh.integrable one_le_two) k

theorem fourierCoeff_add' {f h : Torus d → ℝ} (hf : MemLp f 2 (haar d)) (hh : MemLp h 2 (haar d))
    (k : Fin d → ℤ) :
    fourierCoeff (fun x => f x + h x) k = fourierCoeff f k + fourierCoeff h k := by
  have hn : fourierCoeff (fun x => -h x) k = -fourierCoeff h k := by
    unfold fourierCoeff
    rw [mFourierCoeff_ofReal_eq, mFourierCoeff_ofReal_eq, ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp
  have := fourierCoeff_sub'' (h := fun x => -h x) hf hh.neg k
  simp only [sub_neg_eq_add] at this
  rw [this, hn]
  ring

/-- Parseval pairing of two `L²` functions (polarisation). -/
theorem hasSum_pairing {f h : Torus d → ℝ} (hf : MemLp f 2 (haar d)) (hh : MemLp h 2 (haar d)) :
    HasSum (fun k => (fourierCoeff f k * (starRingEnd ℂ) (fourierCoeff h k)).re)
      (∫ x, f x * h x ∂haar d) := by
  have hp : MemLp (fun x => f x + h x) 2 (haar d) := hf.add hh
  have hm : MemLp (fun x => f x - h x) 2 (haar d) := hf.sub hh
  have h1 := hasSum_sq_fourierCoeff hp
  have h2 := hasSum_sq_fourierCoeff hm
  have h3 := (h1.sub h2).div_const 4
  convert h3 using 1
  · funext k
    rw [fourierCoeff_add' hf hh, fourierCoeff_sub'' hf hh]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.sub_re,
      Complex.add_im, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  · have i1 : Integrable (fun x => (f x + h x) ^ 2) (haar d) := hp.integrable_sq
    have i2 : Integrable (fun x => (f x - h x) ^ 2) (haar d) := hm.integrable_sq
    rw [← integral_sub i1 i2, eq_div_iff (by norm_num : (4 : ℝ) ≠ 0), ← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring

theorem integrable_dot {g G : Torus d → Tangent d} (hg : MemLp g 2 (haar d))
    (hG : MemLp G 2 (haar d)) : Integrable (fun x => ∑ j, g x j * G x j) (haar d) :=
  integrable_finsetSum _ fun j _ =>
    integrable_mul_of_memLp_two' (memLp_coord hg j) (memLp_coord hG j)

/-- Parseval pairing of the weak gradients: `∫ ∇u·∇φ = Σ_k |2πk|² Re(û conj φ̂)`. -/
theorem hasSum_gradPairing {u φ : Torus d → ℝ} {g G : Torus d → Tangent d}
    (hu : IsWeakGradient u g) (hφ : IsWeakGradient φ G) :
    HasSum (fun k => gradWeight k * (fourierCoeff u k * (starRingEnd ℂ) (fourierCoeff φ k)).re)
      (∫ x, ∑ j, g x j * G x j ∂haar d) := by
  have hj : ∀ j : Fin d, HasSum (fun k => (fourierCoeff (fun y => g y j) k *
      (starRingEnd ℂ) (fourierCoeff (fun y => G y j) k)).re) (∫ x, g x j * G x j ∂haar d) :=
    fun j => hasSum_pairing (memLp_coord hu.memLp_grad j) (memLp_coord hφ.memLp_grad j)
  have hs := hasSum_sum (s := Finset.univ) (fun j _ => hj j)
  rw [← integral_finsetSum _ fun j _ =>
    integrable_mul_of_memLp_two' (memLp_coord hu.memLp_grad j) (memLp_coord hφ.memLp_grad j)]
    at hs
  convert hs using 1
  funext k
  have : ∀ j : Fin d, (fourierCoeff (fun y => g y j) k *
      (starRingEnd ℂ) (fourierCoeff (fun y => G y j) k)).re =
      (4 * π ^ 2 * ((k j : ℤ) : ℝ) ^ 2) * (fourierCoeff u k * (starRingEnd ℂ) (fourierCoeff φ k)).re := by
    intro j
    rw [fourierCoeff_weakGradient hu j k, fourierCoeff_weakGradient hφ j k]
    have e : 2 * (π : ℂ) * Complex.I * (k j : ℂ) * fourierCoeff u k *
        (starRingEnd ℂ) (2 * (π : ℂ) * Complex.I * (k j : ℂ) * fourierCoeff φ k) =
        ((4 * π ^ 2 * ((k j : ℤ) : ℝ) ^ 2 : ℝ) : ℂ) *
          (fourierCoeff u k * (starRingEnd ℂ) (fourierCoeff φ k)) := by
      simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast, map_ofNat]
      push_cast
      have := Complex.I_mul_I
      linear_combination (4 * (π : ℂ) ^ 2 * (k j : ℂ) ^ 2 * fourierCoeff u k *
        (starRingEnd ℂ) (fourierCoeff φ k)) * (-this)
    rw [e, Complex.re_ofReal_mul]
  simp_rw [this]
  unfold gradWeight
  rw [← Finset.sum_mul, Finset.mul_sum]

/-- **(c, identity)** For every `H¹` test `φ` with weak gradient `Gφ`,
`∫ u φ + ∫ ∇u·Gφ = ∫ F φ` for `u = R F`. -/
theorem resolvent_weak_identity {F : Torus d → ℝ} (hF : MemLp F 2 (haar d))
    {φ : Torus d → ℝ} {G : Torus d → Tangent d} (hφ : IsWeakGradient φ G) :
    ∫ x, resolvent F x * φ x ∂haar d + ∫ x, ∑ j, resolventGrad F x j * G x j ∂haar d =
      ∫ x, F x * φ x ∂haar d := by
  have hR := isWeakGradient_resolvent hF
  have h1 := hasSum_pairing hR.memLp hφ.memLp
  have h2 := hasSum_gradPairing hR hφ
  have h3 := hasSum_pairing hF hφ.memLp
  refine (h1.add h2).unique ?_
  convert h3 using 1
  funext k
  rw [fourierCoeff_resolvent hF k]
  have hw : 0 ≤ gradWeight k := by unfold gradWeight; positivity
  have hne : (1 + gradWeight k) ≠ 0 := by linarith
  rw [mul_assoc, Complex.re_ofReal_mul]
  field_simp

/-- **(c, uniqueness, energy form)** An `H¹` weak solution of `(1 - Δ)u = F` tested against all
`H¹` functions equals `R F` a.e. -/
theorem eq_resolvent_of_weak_solution {F : Torus d → ℝ} (hF : MemLp F 2 (haar d))
    {u : Torus d → ℝ} {g : Torus d → Tangent d} (hu : IsWeakGradient u g)
    (hsol : ∀ (φ : Torus d → ℝ) (G : Torus d → Tangent d), IsWeakGradient φ G →
      ∫ x, u x * φ x ∂haar d + ∫ x, ∑ j, g x j * G x j ∂haar d = ∫ x, F x * φ x ∂haar d) :
    u =ᵐ[haar d] resolvent F := by
  have hR := isWeakGradient_resolvent hF
  have hv : IsWeakGradient (fun x => u x + (-1) * resolvent F x)
      (fun x => g x + (-1 : ℝ) • resolventGrad F x) := hu.add (hR.smul (-1))
  have e1 := hsol _ _ hv
  have e2 := resolvent_weak_identity hF hv
  set v : Torus d → ℝ := fun x => u x + (-1) * resolvent F x with hvdef
  set gv : Torus d → Tangent d := fun x => g x + (-1 : ℝ) • resolventGrad F x with hgvdef
  have a1 := integrable_mul_of_memLp_two' hu.memLp hv.memLp
  have a2 := integrable_mul_of_memLp_two' hR.memLp hv.memLp
  have b1 := integrable_dot hu.memLp_grad hv.memLp_grad
  have b2 := integrable_dot hR.memLp_grad hv.memLp_grad
  have c1 : ∫ x, v x * v x ∂haar d =
      ∫ x, u x * v x ∂haar d - ∫ x, resolvent F x * v x ∂haar d := by
    rw [← integral_sub a1 a2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hvdef]; ring
  have c2 : ∫ x, ∑ j, gv x j * gv x j ∂haar d =
      ∫ x, ∑ j, g x j * gv x j ∂haar d - ∫ x, ∑ j, resolventGrad F x j * gv x j ∂haar d := by
    rw [← integral_sub b1 b2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hgvdef, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
  have n1 : 0 ≤ ∫ x, v x * v x ∂haar d := integral_nonneg fun x => mul_self_nonneg _
  have n2 : 0 ≤ ∫ x, ∑ j, gv x j * gv x j ∂haar d :=
    integral_nonneg fun x => Finset.sum_nonneg fun j _ => mul_self_nonneg _
  have h0 : ∫ x, v x * v x ∂haar d = 0 := by linarith
  have hint : Integrable (fun x => v x * v x) (haar d) :=
    integrable_mul_of_memLp_two' hv.memLp hv.memLp
  have := (integral_eq_zero_iff_of_nonneg (fun x => mul_self_nonneg (v x)) hint).mp h0
  filter_upwards [this] with x hx
  have : v x = 0 := mul_self_eq_zero.mp hx
  simp only [hvdef] at this
  linarith

/-- **(c, uniqueness via Fourier coefficients)** An `L²` function with the coefficients
`(1 + 4π²|k|²)⁻¹ F^(k)` is `R F` a.e. -/
theorem eq_resolvent_of_fourierCoeff {F : Torus d → ℝ} (hF : MemLp F 2 (haar d))
    {u : Torus d → ℝ} (hu : MemLp u 2 (haar d))
    (hcoef : ∀ k, fourierCoeff u k = (((1 + gradWeight k)⁻¹ : ℝ) : ℂ) * fourierCoeff F k) :
    u =ᵐ[haar d] resolvent F := by
  have hR := (memLp_resolvent hF).1
  have hd : MemLp (fun x => u x - resolvent F x) 2 (haar d) := hu.sub hR
  have h0 := ae_eq_zero_of_mFourierCoeff_eq_zero hd fun k => by
    have := fourierCoeff_sub'' hu hR k
    change fourierCoeff (fun x => u x - resolvent F x) k = 0
    rw [this, hcoef k, fourierCoeff_resolvent hF k, sub_self]
  filter_upwards [h0] with x hx
  simpa [sub_eq_zero] using hx

end WeakSolution

/-- **LIP010c3.** For `F ∈ L²(𝕋^d)`, with `R F = ∫₀^∞ e^{-t} H_t F dt` (`H_t = e^{tΔ}`, whose
Fourier multiplier is `exp(-4π²|k|² t)`):
(a) `(R F)^(k) = (1 + 4π²|k|²)⁻¹ F^(k)`;
(b) `R F ∈ H¹` with weak gradient `∇R F = ∫₀^∞ e^{-t} ∇H_t F dt`;
(c) `R F` is the unique `H¹` weak solution of `(1 - Δ)u = F`, tested against all `H¹` functions, and
the unique `L²` function with the Fourier coefficients in (a). -/
theorem lip010c3_resolvent_fourier {d : ℕ} {F : Torus d → ℝ} (hF : MemLp F 2 (haar d)) :
    (∀ k, fourierCoeff (resolvent F) k = (((1 + gradWeight k)⁻¹ : ℝ) : ℂ) * fourierCoeff F k) ∧
    IsWeakGradient (resolvent F) (resolventGrad F) ∧
    (∀ (φ : Torus d → ℝ) (G : Torus d → Tangent d), IsWeakGradient φ G →
      ∫ x, resolvent F x * φ x ∂haar d + ∫ x, ∑ j, resolventGrad F x j * G x j ∂haar d =
        ∫ x, F x * φ x ∂haar d) ∧
    (∀ (u : Torus d → ℝ) (g : Torus d → Tangent d), IsWeakGradient u g →
      (∀ (φ : Torus d → ℝ) (G : Torus d → Tangent d), IsWeakGradient φ G →
        ∫ x, u x * φ x ∂haar d + ∫ x, ∑ j, g x j * G x j ∂haar d = ∫ x, F x * φ x ∂haar d) →
      u =ᵐ[haar d] resolvent F) ∧
    (∀ u : Torus d → ℝ, MemLp u 2 (haar d) →
      (∀ k, fourierCoeff u k = (((1 + gradWeight k)⁻¹ : ℝ) : ℂ) * fourierCoeff F k) →
      u =ᵐ[haar d] resolvent F) :=
  ⟨fourierCoeff_resolvent hF, isWeakGradient_resolvent hF,
    fun _ _ hφ => resolvent_weak_identity hF hφ,
    fun _ _ hu hsol => eq_resolvent_of_weak_solution hF hu hsol,
    fun _ hu hcoef => eq_resolvent_of_fourierCoeff hF hu hcoef⟩

end DGPS.Lipschitz
