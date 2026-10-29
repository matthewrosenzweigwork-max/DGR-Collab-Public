import SharpSymmetricLSI.Paper.CosineMeanField
import SharpSymmetricLSI.Paper.CosineCalculus

/-!
# Section 3.4: expansions along `ρ_ε` and the upper bound on `r_{*,κ}` (Phase 3, lane C)

For a mode `h` (continuous, `|h| ≤ 1`, `∫ h = 0`) and `ρ = 1 + εh`:
`H(ρ|m)/ε² → (∫h²)/2` (`tendsto_kl_mode`). The dissipations of `1 + ε cos(2πx)` and
`1 + ε cos(4πx)` are `ε² Φ(ε)` with `Φ` continuous at `0` (dominated convergence).
-/

open MeasureTheory InformationTheory Set Filter Topology
open scoped ENNReal Real ContDiff

namespace SharpLSI

/-! ### Trigonometric integrals on the circle -/

theorem integral_fun_gCos_sCos (P : ℝ → ℝ → ℝ) :
    ∫ y : Torus 1, P (gCos y) (sCos y) =
      ∫ s in (0 : ℝ)..1, P (Real.cos (2 * π * s)) (Real.sin (2 * π * s)) := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have := integral_torus1 (fun t => P (fourier 1 t).re (fourier 1 t).im)
  calc ∫ y : Torus 1, P (gCos y) (sCos y) =
        ∫ y : Torus 1, P ((fourier 1) (y 0)).re ((fourier 1) (y 0)).im := rfl
    _ = ∫ t in Ioc (0 : ℝ) 1, P ((fourier 1) (t : UnitAddCircle)).re
          ((fourier 1) (t : UnitAddCircle)).im := this
    _ = _ := by
      congr 1; funext t
      rw [show (fourier 1 (t : UnitAddCircle)).re = gCos (fun _ => (t : UnitAddCircle)) from rfl,
        gCos_coe _ t rfl,
        show (fourier 1 (t : UnitAddCircle)).im = sCos (fun _ => (t : UnitAddCircle)) from rfl,
        sCos, expT_im_coe _ t rfl]

theorem intervalIntegral_cos_pow_two_pi (n : ℕ) :
    ∫ s in (0 : ℝ)..1, Real.cos (2 * π * s) ^ n =
      (2 * π)⁻¹ * ∫ x in (0 : ℝ)..(2 * π), Real.cos x ^ n := by
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ n) (by positivity)]
  simp

theorem integral_gCos_pow3 : ∫ y, gCos y ^ 3 ∂haar 1 = 0 := by
  have := integral_fun_gCos (fun s => s ^ 3)
  rw [this, intervalIntegral_cos_pow_two_pi, integral_cos_pow (n := 1)]
  simp [integral_cos]

theorem integral_gCos_pow4 : ∫ y, gCos y ^ 4 ∂haar 1 = 3 / 8 := by
  have := integral_fun_gCos (fun s => s ^ 4)
  rw [this, intervalIntegral_cos_pow_two_pi, integral_cos_pow (n := 2), integral_cos_sq]
  simp
  field_simp
  ring

theorem integral_sCos_gCos : ∫ y, sCos y * gCos y ∂haar 1 = 0 := by
  have := integral_fun_gCos_sCos (fun c s => s * c)
  rw [this]
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s => Real.sin (2 * π * s) ^ 2 / (4 * π))
      (Real.sin (2 * π * s) * Real.cos (2 * π * s)) s := by
    intro s _
    have := ((((hasDerivAt_id s).const_mul (2 * π)).sin).pow 2).div_const (4 * π)
    convert this using 1
    · funext x; simp only [id, Pi.pow_apply]
    · simp only [id]; norm_num; field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp [Real.sin_two_pi]

theorem integral_sCos_gCos_sq : ∫ y, sCos y * gCos y ^ 2 ∂haar 1 = 0 := by
  have := integral_fun_gCos_sCos (fun c s => s * c ^ 2)
  rw [this]
  have hd : ∀ s ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s => -(Real.cos (2 * π * s) ^ 3 / (6 * π)))
      (Real.sin (2 * π * s) * Real.cos (2 * π * s) ^ 2) s := by
    intro s _
    have := (((((hasDerivAt_id s).const_mul (2 * π)).cos).pow 3).div_const (6 * π)).neg
    convert this using 1
    · funext x; simp only [id, Pi.pow_apply, Pi.neg_apply]
    · simp only [id]; norm_num; field_simp; ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp [Real.cos_two_pi]

theorem integral_sCos_sq : ∫ y, sCos y ^ 2 ∂haar 1 = 1 / 2 := by
  have h : ∀ y, sCos y ^ 2 = 1 - gCos y ^ 2 := fun y => by
    obtain ⟨s, hs⟩ := exists_coe y
    rw [sCos, expT_im_coe _ _ hs, gCos_coe _ _ hs]
    linarith [Real.sin_sq_add_cos_sq (2 * π * s)]
  simp_rw [h]
  rw [integral_sub (f := fun _ => (1 : ℝ)) (g := fun y => gCos y ^ 2) (integrable_const 1)
    (integrable_bdd (continuous_gCos.pow 2)),
    integral_gCos_sq]
  simp; norm_num

/-! ### Entropy of `1 + εh` -/

section Mode

variable {h : Torus 1 → ℝ}

theorem one_add_mul_nonneg (hb : ∀ x, |h x| ≤ 1) {ε : ℝ} (hε : |ε| ≤ 1) (x : Torus 1) :
    0 ≤ 1 + ε * h x := by
  have : |ε * h x| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg ε, abs_nonneg (h x), hb x]
  linarith [neg_abs_le (ε * h x)]

theorem integral_mode (hc : Continuous h) (h0 : ∫ x, h x ∂haar 1 = 0) (ε : ℝ) :
    ∫ x, 1 + ε * h x ∂haar 1 = 1 := by
  rw [integral_add (f := fun _ => (1 : ℝ)) (g := fun x => ε * h x) (integrable_const 1)
    ((integrable_bdd hc).const_mul ε), integral_const_mul, h0]
  simp

theorem continuous_klFun : Continuous klFun := by
  have : klFun = fun x => x * Real.log x + 1 - x := funext klFun_apply
  rw [this]
  exact (Real.continuous_mul_log.add continuous_const).sub continuous_id

theorem klDiv_mode (hc : Continuous h) (hb : ∀ x, |h x| ≤ 1) (h0 : ∫ x, h x ∂haar 1 = 0)
    {ε : ℝ} (hε : |ε| ≤ 1) :
    klDiv (densMeasure (fun x => 1 + ε * h x)) (haar 1) =
      ENNReal.ofReal (∫ x, klFun (1 + ε * h x) ∂haar 1) := by
  rw [klDiv_densMeasure (one_add_mul_nonneg hb hε) (integral_mode hc h0 ε)]
  exact (ofReal_integral_eq_lintegral_ofReal (integrable_bdd (continuous_klFun.comp
    (continuous_const.add (continuous_const.mul hc))))
    (Eventually.of_forall fun x => klFun_nonneg (one_add_mul_nonneg hb hε x))).symm

theorem kl_mode_bounds (hc : Continuous h) (hb : ∀ x, |h x| ≤ 1)
    (h0 : ∫ x, h x ∂haar 1 = 0) {ε : ℝ} (hε : |ε| < 1) :
    ε ^ 2 * (∫ x, h x ^ 2 ∂haar 1) / (2 * (1 + |ε|)) ≤ ∫ x, klFun (1 + ε * h x) ∂haar 1 ∧
      ∫ x, klFun (1 + ε * h x) ∂haar 1 ≤ ε ^ 2 * (∫ x, h x ^ 2 ∂haar 1) / (2 * (1 - |ε|)) := by
  have ht : ∀ x, |ε * h x| ≤ |ε| := fun x => by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg ε) (hb x)
  have hk : ∀ x, klFun (1 + ε * h x) =
      (1 + ε * h x) * Real.log (1 + ε * h x) - ε * h x := fun x => by
    rw [klFun_apply]; ring
  have iK : Integrable (fun x => klFun (1 + ε * h x)) (haar 1) :=
    integrable_bdd (continuous_klFun.comp (continuous_const.add (continuous_const.mul hc)))
  have iH : Integrable (fun x => h x ^ 2) (haar 1) := integrable_bdd (hc.pow 2)
  have hδ1 : 0 < 1 + |ε| := by positivity
  have hδ2 : 0 < 1 - |ε| := by linarith
  constructor
  · rw [show ε ^ 2 * (∫ x, h x ^ 2 ∂haar 1) / (2 * (1 + |ε|)) =
        ∫ x, (ε * h x) ^ 2 / (2 * (1 + |ε|)) ∂haar 1 by
      rw [integral_div, ← integral_const_mul]; congr 1; congr 1; funext x; ring]
    refine integral_mono ((iH.const_mul (ε ^ 2)).div_const (2 * (1 + |ε|)) |>.congr
      (Eventually.of_forall fun x => by simp only; ring)) iK fun x => ?_
    have := (mul_log_taylor_bounds (by linarith) (ht x)).1
    simp only
    rw [hk]; linarith
  · rw [show ε ^ 2 * (∫ x, h x ^ 2 ∂haar 1) / (2 * (1 - |ε|)) =
        ∫ x, (ε * h x) ^ 2 / (2 * (1 - |ε|)) ∂haar 1 by
      rw [integral_div, ← integral_const_mul]; congr 1; congr 1; funext x; ring]
    refine integral_mono iK ((iH.const_mul (ε ^ 2)).div_const (2 * (1 - |ε|)) |>.congr
      (Eventually.of_forall fun x => by simp only; ring)) fun x => ?_
    have := (mul_log_taylor_bounds (by linarith) (ht x)).2
    simp only
    rw [hk]; linarith

theorem tendsto_kl_mode (hc : Continuous h) (hb : ∀ x, |h x| ≤ 1)
    (h0 : ∫ x, h x ∂haar 1 = 0) :
    Tendsto (fun ε : ℝ => (∫ x, klFun (1 + ε * h x) ∂haar 1) / ε ^ 2) (𝓝[≠] 0)
      (𝓝 ((∫ x, h x ^ 2 ∂haar 1) / 2)) := by
  set m := ∫ x, h x ^ 2 ∂haar 1
  have hsmall : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |ε| < 1 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((continuous_abs.tendsto (0 : ℝ)).eventually (gt_mem_nhds (by norm_num)))
  have hne : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ε ≠ 0 := self_mem_nhdsWithin
  have hl : ∀ c : ℝ, Tendsto (fun ε : ℝ => m / (2 * (1 + c * |ε|))) (𝓝[≠] 0) (𝓝 (m / 2)) := by
    intro c
    have hca : ContinuousAt (fun ε : ℝ => m / (2 * (1 + c * |ε|))) 0 :=
      continuousAt_const.div (continuousAt_const.mul (continuousAt_const.add
        (continuousAt_const.mul continuous_abs.continuousAt))) (by simp)
    have := hca.tendsto
    simp only [abs_zero, mul_zero, add_zero, mul_one] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hl 1) (hl (-1)) ?_ ?_
  · filter_upwards [hsmall, hne] with ε h1 h2
    have hε2 : 0 < ε ^ 2 := by positivity
    have hb := (kl_mode_bounds hc hb h0 h1).1
    rw [le_div_iff₀ hε2]
    calc m / (2 * (1 + 1 * |ε|)) * ε ^ 2 = ε ^ 2 * m / (2 * (1 + |ε|)) := by ring
      _ ≤ _ := hb
  · filter_upwards [hsmall, hne] with ε h1 h2
    have hε2 : 0 < ε ^ 2 := by positivity
    have hb := (kl_mode_bounds hc hb h0 h1).2
    rw [div_le_iff₀ hε2]
    calc _ ≤ ε ^ 2 * m / (2 * (1 - |ε|)) := hb
      _ = m / (2 * (1 + -1 * |ε|)) * ε ^ 2 := by ring

end Mode

/-! ### Smooth periodic functions are in `H¹` -/

theorem memH1_of_contDiff {ι : Type*} [Fintype ι] [DecidableEq ι] {f : UnitAddTorus ι → ℝ}
    (hf : ContDiff ℝ ∞ (f ∘ liftT)) : MemH1 volume f := by
  have hf1 : ContDiff ℝ 1 (f ∘ liftT) := hf.of_le (by simp)
  have hw := isWeakGrad_of_contDiff hf1
  have hfs : ∀ y, f y = (f ∘ liftT) (secT y) := fun y => by simp [liftT_secT]
  obtain ⟨C, hC⟩ := periodic_bounded hf.continuous (lift_periodic f)
  have hfm : AEStronglyMeasurable f volume := by
    have : f = fun y => (f ∘ liftT) (secT y) := funext hfs
    rw [this]
    exact hf.continuous.comp_aestronglyMeasurable measurable_secT.aestronglyMeasurable
  refine ⟨⟨_, hw⟩, MemLp.of_bound hfm C (Eventually.of_forall fun y => by rw [hfs]; exact hC _), ?_⟩
  set Φ : (ι → ℝ) → ℝ := fun x => Real.sqrt (sqNorm (fun k => fderiv ℝ (f ∘ liftT) x
    (Pi.single k 1))) with hΦ
  have hΦc : Continuous Φ := Real.continuous_sqrt.comp (continuous_finset_sum _ fun k _ =>
    (((hf1.continuous_fderiv one_ne_zero).clm_apply continuous_const)).pow 2)
  have hΦp : ∀ (m : ι → ℤ) x, Φ (x + intVec m) = Φ x := fun m x => by
    simp only [hΦ, fderiv_lift_periodic f m x]
  obtain ⟨D, hD⟩ := periodic_bounded hΦc hΦp
  have h1 : MemLp (fun y => Φ (secT y)) 2 volume :=
    MemLp.of_bound (hΦc.comp_aestronglyMeasurable measurable_secT.aestronglyMeasurable) D
      (Eventually.of_forall fun y => hD _)
  refine h1.ae_eq ?_
  filter_upwards [weakGrad_ae_eq_of_contDiff hf1] with y hy
  rw [hy]

/-! ### `√(1 + εh)` -/

section SqrtMode

variable {h : Torus 1 → ℝ}

theorem one_add_mul_pos (hb : ∀ x, |h x| ≤ 1) {ε : ℝ} (hε : |ε| < 1) (x : Torus 1) :
    0 < 1 + ε * h x := by
  have : |ε * h x| < 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg ε, abs_nonneg (h x), hb x]
  linarith [neg_abs_le (ε * h x)]

theorem lift_bound (hb : ∀ x, |h x| ≤ 1) (z : Fin 1 → ℝ) : |(h ∘ liftT) z| ≤ 1 := hb _

theorem contDiff_sqrt_mode (hH : ContDiff ℝ ∞ (h ∘ liftT)) (hb : ∀ x, |h x| ≤ 1) {ε : ℝ}
    (hε : |ε| < 1) : ContDiff ℝ ∞ ((fun x => Real.sqrt (1 + ε * h x)) ∘ liftT) :=
  (contDiff_const.add (contDiff_const.mul hH)).sqrt fun z =>
    (one_add_mul_pos hb hε (liftT z)).ne'

theorem fderiv_sqrt_mode (hH : ContDiff ℝ ∞ (h ∘ liftT)) (hb : ∀ x, |h x| ≤ 1) {ε : ℝ}
    (hε : |ε| < 1) (z : Fin 1 → ℝ) :
    fderiv ℝ ((fun x => Real.sqrt (1 + ε * h x)) ∘ liftT) z (Pi.single 0 1) =
      ε * fderiv ℝ (h ∘ liftT) z (Pi.single 0 1) / (2 * Real.sqrt (1 + ε * h (liftT z))) := by
  have hd := ((hH.differentiable (by simp)) z).hasFDerivAt
  have h2 := ((hd.const_mul ε).const_add 1).sqrt (one_add_mul_pos hb hε (liftT z)).ne'
  rw [show ((fun x => Real.sqrt (1 + ε * h x)) ∘ liftT) =
    fun z => Real.sqrt (1 + ε * (h ∘ liftT) z) from rfl, h2.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Function.comp_apply]
  field_simp

theorem memH1_sqrt_mode (hH : ContDiff ℝ ∞ (h ∘ liftT)) (hb : ∀ x, |h x| ≤ 1) {ε : ℝ}
    (hε : |ε| < 1) : MemH1 (haar 1) (fun x => Real.sqrt (1 + ε * h x)) :=
  memH1_of_contDiff (contDiff_sqrt_mode hH hb hε)

end SqrtMode

/-! ### Mode 1: `ρ_ε = 1 + ε cos(2πx)` -/

theorem gCos_lift : gCos ∘ liftT = fun z : Fin 1 → ℝ => Real.cos (2 * π * z 0) := by
  funext z; exact gCos_coe (liftT z) (z 0) rfl

theorem gCos_secT (y : Torus 1) : gCos y = Real.cos (2 * π * secT y 0) := by
  conv_lhs => rw [← liftT_secT y]
  exact congrFun gCos_lift (secT y)

theorem contDiff_gCos_lift : ContDiff ℝ ∞ (gCos ∘ liftT) := by
  rw [gCos_lift]
  exact (Real.contDiff_cos.comp (contDiff_const.mul (contDiff_apply ℝ ℝ 0))).of_le le_top

theorem fderiv_gCos_lift (z : Fin 1 → ℝ) :
    fderiv ℝ (gCos ∘ liftT) z (Pi.single 0 1) = -(2 * π) * Real.sin (2 * π * z 0) := by
  refine fderiv_apply_of_line ((contDiff_gCos_lift.differentiable (by simp)) z) ?_
  rw [gCos_lift]
  have := (((hasDerivAt_id (0 : ℝ)).const_add (z 0)).const_mul (2 * π)).cos
  convert this using 1
  · funext t; simp
  · simp; ring

theorem abs_gCos_le' : ∀ x, |gCos x| ≤ 1 := abs_gCos_le

theorem integral_gCos_rho (ε : ℝ) : ∫ y, gCos y * (1 + ε * gCos y) ∂haar 1 = ε / 2 := by
  have e : ∀ y, gCos y * (1 + ε * gCos y) = gCos y + ε * gCos y ^ 2 := fun y => by ring
  simp_rw [e]
  rw [integral_add (f := gCos) (g := fun y => ε * gCos y ^ 2)
    (integrable_bdd continuous_gCos) ((integrable_bdd (continuous_gCos.pow 2)).const_mul ε),
    integral_const_mul, integral_gCos, integral_gCos_sq]
  ring

theorem integral_sCos_rho (ε : ℝ) : ∫ y, sCos y * (1 + ε * gCos y) ∂haar 1 = 0 := by
  have e : ∀ y, sCos y * (1 + ε * gCos y) = sCos y + ε * (sCos y * gCos y) := fun y => by ring
  simp_rw [e]
  rw [integral_add (f := sCos) (g := fun y => ε * (sCos y * gCos y))
    (integrable_bdd continuous_sCos)
    ((integrable_bdd (continuous_sCos.mul continuous_gCos)).const_mul ε),
    integral_const_mul, integral_sCos, integral_sCos_gCos]
  ring

theorem gConv_rho1 (ε : ℝ) :
    gConv (fun x => 1 + ε * gCos x) = fun x => ε / 2 * gCos x := by
  funext x
  have h1 := integral_mode continuous_gCos integral_gCos ε
  rw [gConv_eq h1]
  have e1 : ∫ y, gCos y * (1 + ε * gCos y) ∂haar 1 = ε / 2 := integral_gCos_rho ε
  have e2 : ∫ y, sCos y * (1 + ε * gCos y) ∂haar 1 = 0 := integral_sCos_rho ε
  rw [e1, e2]; ring

theorem firstMode_eq {ρ : Torus 1 → ℝ} (hi : Integrable ρ (haar 1)) :
    firstMode ρ = (∫ y, gCos y * ρ y ∂haar 1) ^ 2 + (∫ y, sCos y * ρ y ∂haar 1) ^ 2 := by
  have hie : Integrable (fun x => expT x * (ρ x : ℂ)) (haar 1) := by
    refine Integrable.mono' hi.norm (continuous_expT.aestronglyMeasurable.mul
      hi.ofReal.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    have h1 : ‖expT x‖ = 1 := by simp [expT, fourier_apply]
    rw [norm_mul, h1, one_mul, Complex.norm_real]
  rw [firstMode, Complex.normSq_apply]
  have hr := integral_re hie
  have hm := integral_im hie
  simp only [RCLike.re_to_complex, RCLike.im_to_complex] at hr hm
  rw [← hr, ← hm]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, add_zero, gCos, sCos]
  ring

theorem firstMode_rho1 (ε : ℝ) : firstMode (fun x => 1 + ε * gCos x) = ε ^ 2 / 4 := by
  rw [firstMode_eq (ρ := fun x => 1 + ε * gCos x)
    (integrable_bdd (continuous_const.add (continuous_const.mul continuous_gCos))),
    integral_gCos_rho, integral_sCos_rho]
  ring

/-- The mode-1 dissipation density. -/
noncomputable def F1 (κ ε : ℝ) (y : Torus 1) : ℝ :=
  π ^ 2 * (1 - gCos y ^ 2) * (2 + κ * (1 + ε * gCos y)) ^ 2 / (1 + ε * gCos y)

theorem F1_nonneg (κ : ℝ) {ε : ℝ} (hε : |ε| < 1) (y : Torus 1) : 0 ≤ F1 κ ε y := by
  have h1 := one_add_mul_pos abs_gCos_le hε y
  have h2 : 0 ≤ 1 - gCos y ^ 2 := by
    have := abs_gCos_le y; nlinarith [abs_nonneg (gCos y), sq_abs (gCos y)]
  unfold F1; positivity

theorem continuous_F1 (κ : ℝ) {ε : ℝ} (hε : |ε| < 1) : Continuous (F1 κ ε) := by
  unfold F1
  exact (continuous_const.mul (continuous_const.sub (continuous_gCos.pow 2))).mul
    ((continuous_const.add (continuous_const.mul (continuous_const.add (continuous_const.mul
      continuous_gCos)))).pow 2) |>.div (continuous_const.add (continuous_const.mul continuous_gCos))
      fun y => (one_add_mul_pos abs_gCos_le hε y).ne'

theorem dissipation_rho1 (κ : ℝ) {ε : ℝ} (hε : |ε| < 1) :
    dissipation cosV (cosW κ) (fun x => 1 + ε * gCos x) =
      ENNReal.ofReal (ε ^ 2 * ∫ y, F1 κ ε y ∂haar 1) := by
  have hρ1 := integral_mode continuous_gCos integral_gCos ε
  rw [dissipation_cos κ hρ1 (memH1_sqrt_mode contDiff_gCos_lift abs_gCos_le hε), gConv_rho1]
  have hu1 : ContDiff ℝ 1 ((fun x => Real.sqrt (1 + ε * gCos x)) ∘ liftT) :=
    (contDiff_sqrt_mode contDiff_gCos_lift abs_gCos_le hε).of_le (by simp)
  have hG1 : ContDiff ℝ 1 ((fun x => ε / 2 * gCos x) ∘ liftT) :=
    (contDiff_const.mul contDiff_gCos_lift).of_le (by simp)
  have hint : Integrable (fun y => ε ^ 2 * F1 κ ε y) (haar 1) :=
    (integrable_bdd (continuous_F1 κ hε)).const_mul _
  rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (F1_nonneg κ hε y))]
  refine lintegral_congr_ae ?_
  filter_upwards [weakGrad_ae_eq_of_contDiff hu1, weakGrad_ae_eq_of_contDiff hG1] with x h1 h2
  rw [h1, h2]
  simp only
  rw [fderiv_sqrt_mode contDiff_gCos_lift abs_gCos_le hε,
    show ((fun x => ε / 2 * gCos x) ∘ liftT) = fun z => ε / 2 * (gCos ∘ liftT) z from rfl,
    fderiv_const_mul ((contDiff_gCos_lift.differentiable (by simp)) (secT x))]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, fderiv_gCos_lift, liftT_secT]
  congr 1
  set c := gCos x with hc
  set r := Real.sqrt (1 + ε * c) with hr
  set sn := Real.sin (2 * π * secT x 0) with hsn
  have hpos := one_add_mul_pos abs_gCos_le hε x
  have hr2 : r ^ 2 = 1 + ε * c := Real.sq_sqrt hpos.le
  have hr0 : 0 < r := Real.sqrt_pos.mpr hpos
  have hs : sn ^ 2 = 1 - c ^ 2 := by
    rw [hc, gCos_secT, hsn]; linarith [Real.sin_sq_add_cos_sq (2 * π * secT x 0)]
  have key : (2 * (ε * (-(2 * π) * sn) / (2 * r)) + κ * r * (ε / 2 * (-(2 * π) * sn))) ^ 2 =
      π ^ 2 * ε ^ 2 * sn ^ 2 * (2 + κ * r ^ 2) ^ 2 / r ^ 2 := by
    field_simp; ring
  rw [key, hs, hr2]
  unfold F1
  rw [← hc]
  field_simp

theorem small_eventually : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < 1 / 2 :=
  (continuous_abs.tendsto (0 : ℝ)).eventually (gt_mem_nhds (by norm_num))

theorem continuousAt_integral_F1 (κ : ℝ) :
    ContinuousAt (fun ε => ∫ y, F1 κ ε y ∂haar 1) 0 := by
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => 2 * π ^ 2 * (2 + 2 * |κ|) ^ 2)
    ?_ ?_ (integrable_const _) ?_
  · filter_upwards [small_eventually] with ε hε
    exact (continuous_F1 κ (by linarith)).aestronglyMeasurable
  · filter_upwards [small_eventually] with ε hε
    refine Eventually.of_forall fun y => ?_
    have hc := abs_gCos_le y
    have hd : 1 / 2 ≤ 1 + ε * gCos y := by
      have : |ε * gCos y| ≤ 1 / 2 := by
        rw [abs_mul]; nlinarith [abs_nonneg ε, abs_nonneg (gCos y)]
      linarith [neg_abs_le (ε * gCos y)]
    have h1 : 0 ≤ 1 - gCos y ^ 2 := by nlinarith [abs_nonneg (gCos y), sq_abs (gCos y)]
    have h1' : 1 - gCos y ^ 2 ≤ 1 := by nlinarith [sq_nonneg (gCos y)]
    have h2 : |2 + κ * (1 + ε * gCos y)| ≤ 2 + 2 * |κ| := by
      have : |1 + ε * gCos y| ≤ 2 := by
        have : |ε * gCos y| ≤ 1 / 2 := by
          rw [abs_mul]; nlinarith [abs_nonneg ε, abs_nonneg (gCos y)]
        calc |1 + ε * gCos y| ≤ |1| + |ε * gCos y| := abs_add_le _ _
          _ ≤ 2 := by rw [abs_one]; linarith
      calc |2 + κ * (1 + ε * gCos y)| ≤ |2| + |κ * (1 + ε * gCos y)| := abs_add_le _ _
        _ = 2 + |κ| * |1 + ε * gCos y| := by rw [abs_mul]; norm_num
        _ ≤ 2 + |κ| * 2 := by gcongr
        _ = 2 + 2 * |κ| := by ring
    have h3 : (2 + κ * (1 + ε * gCos y)) ^ 2 ≤ (2 + 2 * |κ|) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
    rw [Real.norm_eq_abs, abs_of_nonneg (F1_nonneg κ (by linarith) y)]
    unfold F1
    rw [div_le_iff₀ (by linarith)]
    calc π ^ 2 * (1 - gCos y ^ 2) * (2 + κ * (1 + ε * gCos y)) ^ 2
        ≤ π ^ 2 * 1 * (2 + 2 * |κ|) ^ 2 := by gcongr
      _ = 2 * π ^ 2 * (2 + 2 * |κ|) ^ 2 * (1 / 2) := by ring
      _ ≤ 2 * π ^ 2 * (2 + 2 * |κ|) ^ 2 * (1 + ε * gCos y) := by gcongr
  · refine Eventually.of_forall fun y => ?_
    unfold F1
    refine ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)

theorem integral_F1_zero (κ : ℝ) : ∫ y, F1 κ 0 y ∂haar 1 = π ^ 2 * (2 + κ) ^ 2 / 2 := by
  have e : ∀ y, F1 κ 0 y = π ^ 2 * (2 + κ) ^ 2 * (1 - gCos y ^ 2) := fun y => by
    unfold F1; ring
  simp_rw [e]
  rw [integral_const_mul, integral_sub (f := fun _ => (1 : ℝ)) (g := fun y => gCos y ^ 2)
    (integrable_const 1) (integrable_bdd (continuous_gCos.pow 2)), integral_gCos_sq]
  simp; ring

theorem gap_rho_toReal {κ : ℝ} (hκ : 0 < κ) {h : Torus 1 → ℝ} (hc : Continuous h)
    (hb : ∀ x, |h x| ≤ 1) (h0 : ∫ x, h x ∂haar 1 = 0) {ε : ℝ} (hε : |ε| ≤ 1) :
    (gap cosV (cosW κ) (densMeasure (fun x => 1 + ε * h x))).toReal =
      (∫ x, klFun (1 + ε * h x) ∂haar 1) + κ / 2 * firstMode (fun x => 1 + ε * h x) := by
  rw [(cosine_free_energy_aux hκ).2.2.2.1 _ (one_add_mul_nonneg hb hε) (integral_mode hc h0 ε),
    klDiv_mode hc hb h0 hε, EReal.coe_ennreal_ofReal,
    max_eq_left (integral_nonneg fun x => klFun_nonneg (one_add_mul_nonneg hb hε x)),
    ← EReal.coe_add, EReal.toReal_coe]

theorem tendsto_gap_rho1 {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun ε : ℝ => (gap cosV (cosW κ) (densMeasure (fun x => 1 + ε * gCos x))).toReal /
        ε ^ 2) (𝓝[≠] 0) (𝓝 ((1 + κ / 2) / 4)) := by
  have hk := tendsto_kl_mode continuous_gCos abs_gCos_le integral_gCos
  rw [integral_gCos_sq] at hk
  have h2 := hk.add (tendsto_const_nhds (x := κ / 8))
  rw [show 1 / 2 / 2 + κ / 8 = (1 + κ / 2) / 4 by ring] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds small_eventually, self_mem_nhdsWithin]
    with ε hε hne
  have hne' : ε ≠ 0 := hne
  rw [gap_rho_toReal hκ continuous_gCos abs_gCos_le integral_gCos (by linarith), firstMode_rho1]
  field_simp
  ring

theorem tendsto_dissipation_rho1 {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun ε : ℝ => (dissipation cosV (cosW κ) (fun x => 1 + ε * gCos x)).toReal / ε ^ 2)
        (𝓝[≠] 0) (𝓝 (aCos / 2 * (1 + κ / 2) ^ 2)) := by
  have hc := (continuousAt_integral_F1 κ).tendsto
  rw [integral_F1_zero] at hc
  rw [show aCos / 2 * (1 + κ / 2) ^ 2 = π ^ 2 * (2 + κ) ^ 2 / 2 by unfold aCos; ring]
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds small_eventually, self_mem_nhdsWithin]
    with ε hε hne
  have hne' : ε ≠ 0 := hne
  rw [dissipation_rho1 κ (by linarith), ENNReal.toReal_ofReal (mul_nonneg (sq_nonneg _)
    (integral_nonneg fun y => F1_nonneg κ (by linarith) y))]
  field_simp

/-! ### Mode 2: `1 + ε cos(4πx)` -/

theorem gCos_two_smul (y : Torus 1) : gCos (2 • y) = 2 * gCos y ^ 2 - 1 := by
  obtain ⟨s, hs⟩ := exists_coe y
  have h2 : (2 • y) 0 = ((2 * s : ℝ) : UnitAddCircle) := by
    rw [Pi.smul_apply, hs, show (2 : ℝ) * s = (2 : ℕ) • s by simp, AddCircle.coe_nsmul]
  rw [gCos_coe _ _ h2, gCos_coe _ _ hs, show 2 * π * (2 * s) = 2 * (2 * π * s) by ring,
    Real.cos_two_mul]

/-- `cos(4πx)`. -/
noncomputable abbrev c2 (y : Torus 1) : ℝ := gCos (2 • y)

theorem c2_eq : c2 = fun y => 2 * gCos y ^ 2 - 1 := funext gCos_two_smul

theorem c2_apply (y : Torus 1) : c2 y = 2 * gCos y ^ 2 - 1 := gCos_two_smul y

theorem continuous_c2 : Continuous c2 := by
  rw [c2_eq]; exact (continuous_const.mul (continuous_gCos.pow 2)).sub continuous_const

theorem abs_c2_le (y : Torus 1) : |c2 y| ≤ 1 := by
  rw [c2_eq]
  have := abs_gCos_le y
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg (gCos y), sq_abs (gCos y), sq_nonneg (gCos y)]

theorem integral_c2 : ∫ y, c2 y ∂haar 1 = 0 := by
  rw [c2_eq, integral_sub (f := fun y => 2 * gCos y ^ 2) (g := fun _ => (1 : ℝ))
    ((integrable_bdd (continuous_gCos.pow 2)).const_mul 2) (integrable_const 1),
    integral_const_mul, integral_gCos_sq]
  simp

theorem integral_c2_sq : ∫ y, c2 y ^ 2 ∂haar 1 = 1 / 2 := by
  have e : ∀ y, c2 y ^ 2 = 4 * gCos y ^ 4 - 4 * gCos y ^ 2 + 1 := fun y => by
    rw [c2_apply]; ring
  simp_rw [e]
  rw [integral_add (f := fun y => 4 * gCos y ^ 4 - 4 * gCos y ^ 2) (g := fun _ => (1 : ℝ))
    (((integrable_bdd (continuous_gCos.pow 4)).const_mul 4).sub
      ((integrable_bdd (continuous_gCos.pow 2)).const_mul 4)) (integrable_const 1),
    integral_sub (f := fun y => 4 * gCos y ^ 4) (g := fun y => 4 * gCos y ^ 2)
      ((integrable_bdd (continuous_gCos.pow 4)).const_mul 4)
      ((integrable_bdd (continuous_gCos.pow 2)).const_mul 4),
    integral_const_mul, integral_const_mul, integral_gCos_pow4, integral_gCos_sq]
  simp; norm_num

theorem integral_gCos_rho2 (ε : ℝ) : ∫ y, gCos y * (1 + ε * c2 y) ∂haar 1 = 0 := by
  have e : ∀ y, gCos y * (1 + ε * c2 y) = (1 - ε) * gCos y + 2 * ε * gCos y ^ 3 := fun y => by
    rw [c2_apply]; ring
  simp_rw [e]
  rw [integral_add (f := fun y => (1 - ε) * gCos y) (g := fun y => 2 * ε * gCos y ^ 3)
    ((integrable_bdd continuous_gCos).const_mul _)
    ((integrable_bdd (continuous_gCos.pow 3)).const_mul _), integral_const_mul,
    integral_const_mul, integral_gCos, integral_gCos_pow3]
  ring

theorem integral_sCos_rho2 (ε : ℝ) : ∫ y, sCos y * (1 + ε * c2 y) ∂haar 1 = 0 := by
  have e : ∀ y, sCos y * (1 + ε * c2 y) = (1 - ε) * sCos y + 2 * ε * (sCos y * gCos y ^ 2) :=
    fun y => by rw [c2_apply]; ring
  simp_rw [e]
  rw [integral_add (f := fun y => (1 - ε) * sCos y)
    (g := fun y => 2 * ε * (sCos y * gCos y ^ 2))
    ((integrable_bdd continuous_sCos).const_mul _)
    ((integrable_bdd (continuous_sCos.mul (continuous_gCos.pow 2))).const_mul _),
    integral_const_mul, integral_const_mul, integral_sCos, integral_sCos_gCos_sq]
  ring

theorem gConv_rho2 (ε : ℝ) : gConv (fun x => 1 + ε * c2 x) = fun _ => 0 := by
  funext x
  rw [gConv_eq (integral_mode continuous_c2 integral_c2 ε), integral_gCos_rho2,
    integral_sCos_rho2]
  ring

theorem firstMode_rho2 (ε : ℝ) : firstMode (fun x => 1 + ε * c2 x) = 0 := by
  rw [firstMode_eq (ρ := fun x => 1 + ε * c2 x)
    (integrable_bdd (continuous_const.add (continuous_const.mul continuous_c2))),
    integral_gCos_rho2, integral_sCos_rho2]
  ring

theorem c2_lift : c2 ∘ liftT = fun z : Fin 1 → ℝ => 2 * Real.cos (2 * π * z 0) ^ 2 - 1 := by
  funext z
  simp only [Function.comp_apply, gCos_two_smul]
  rw [show gCos (liftT z) = (gCos ∘ liftT) z from rfl, gCos_lift]

theorem contDiff_c2_lift : ContDiff ℝ ∞ (c2 ∘ liftT) := by
  rw [c2_lift]
  exact ((contDiff_const.mul ((Real.contDiff_cos.comp (contDiff_const.mul
    (contDiff_apply ℝ ℝ 0))).pow 2)).sub contDiff_const).of_le le_top

theorem fderiv_c2_lift (z : Fin 1 → ℝ) :
    fderiv ℝ (c2 ∘ liftT) z (Pi.single 0 1) =
      -(8 * π) * Real.cos (2 * π * z 0) * Real.sin (2 * π * z 0) := by
  refine fderiv_apply_of_line ((contDiff_c2_lift.differentiable (by simp)) z) ?_
  rw [c2_lift]
  have := ((((((hasDerivAt_id (0 : ℝ)).const_add (z 0)).const_mul (2 * π)).cos).pow 2).const_mul
    2).sub_const 1
  convert this using 1
  · funext t; simp
  · simp; ring

/-- The mode-2 dissipation density. -/
noncomputable def F2 (ε : ℝ) (y : Torus 1) : ℝ := 16 * π ^ 2 * (1 - c2 y ^ 2) / (1 + ε * c2 y)

theorem F2_nonneg {ε : ℝ} (hε : |ε| < 1) (y : Torus 1) : 0 ≤ F2 ε y := by
  have h1 := one_add_mul_pos abs_c2_le hε y
  have h2 : 0 ≤ 1 - c2 y ^ 2 := by
    have := abs_c2_le y; nlinarith [abs_nonneg (c2 y), sq_abs (c2 y)]
  unfold F2; positivity

theorem continuous_F2 {ε : ℝ} (hε : |ε| < 1) : Continuous (F2 ε) := by
  unfold F2
  exact (continuous_const.mul (continuous_const.sub (continuous_c2.pow 2))).div
    (continuous_const.add (continuous_const.mul continuous_c2))
    fun y => (one_add_mul_pos abs_c2_le hε y).ne'

theorem dissipation_rho2 (κ : ℝ) {ε : ℝ} (hε : |ε| < 1) :
    dissipation cosV (cosW κ) (fun x => 1 + ε * c2 x) =
      ENNReal.ofReal (ε ^ 2 * ∫ y, F2 ε y ∂haar 1) := by
  have hρ1 := integral_mode continuous_c2 integral_c2 ε
  rw [dissipation_cos κ hρ1 (memH1_sqrt_mode contDiff_c2_lift abs_c2_le hε), gConv_rho2]
  have hu1 : ContDiff ℝ 1 ((fun x => Real.sqrt (1 + ε * c2 x)) ∘ liftT) :=
    (contDiff_sqrt_mode contDiff_c2_lift abs_c2_le hε).of_le (by simp)
  have hG1 : ContDiff ℝ 1 ((fun _ : Torus 1 => (0 : ℝ)) ∘ liftT) := contDiff_const
  have hint : Integrable (fun y => ε ^ 2 * F2 ε y) (haar 1) :=
    (integrable_bdd (continuous_F2 hε)).const_mul _
  rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (F2_nonneg hε y))]
  refine lintegral_congr_ae ?_
  filter_upwards [weakGrad_ae_eq_of_contDiff hu1, weakGrad_ae_eq_of_contDiff hG1] with x h1 h2
  rw [h1, h2]
  simp only
  rw [fderiv_sqrt_mode contDiff_c2_lift abs_c2_le hε, fderiv_c2_lift, liftT_secT,
    show ((fun _ : Torus 1 => (0 : ℝ)) ∘ liftT) = fun _ => 0 from rfl, fderiv_const_apply]
  simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, mul_zero, add_zero]
  congr 1
  set c := Real.cos (2 * π * secT x 0) with hc
  set sn := Real.sin (2 * π * secT x 0) with hsn
  have hcx : c2 x = 2 * c ^ 2 - 1 := by rw [c2_apply, gCos_secT]
  set r := Real.sqrt (1 + ε * c2 x) with hr
  have hpos := one_add_mul_pos abs_c2_le hε x
  have hr2 : r ^ 2 = 1 + ε * c2 x := Real.sq_sqrt hpos.le
  have hr0 : 0 < r := Real.sqrt_pos.mpr hpos
  have hs : sn ^ 2 = 1 - c ^ 2 := by linarith [Real.sin_sq_add_cos_sq (2 * π * secT x 0)]
  have key : (2 * (ε * (-(8 * π) * c * sn) / (2 * r))) ^ 2 =
      64 * π ^ 2 * ε ^ 2 * c ^ 2 * sn ^ 2 / r ^ 2 := by
    field_simp; ring
  rw [key, hs, hr2]
  unfold F2
  rw [hcx]
  field_simp
  ring

theorem continuousAt_integral_F2 : ContinuousAt (fun ε => ∫ y, F2 ε y ∂haar 1) 0 := by
  refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => 32 * π ^ 2)
    ?_ ?_ (integrable_const _) ?_
  · filter_upwards [small_eventually] with ε hε
    exact (continuous_F2 (by linarith)).aestronglyMeasurable
  · filter_upwards [small_eventually] with ε hε
    refine Eventually.of_forall fun y => ?_
    have hc := abs_c2_le y
    have hd : 1 / 2 ≤ 1 + ε * c2 y := by
      have : |ε * c2 y| ≤ 1 / 2 := by
        rw [abs_mul]; nlinarith [abs_nonneg ε, abs_nonneg (c2 y)]
      linarith [neg_abs_le (ε * c2 y)]
    have h1' : 1 - c2 y ^ 2 ≤ 1 := by nlinarith [sq_nonneg (c2 y)]
    have h1 : 0 ≤ 1 - c2 y ^ 2 := by nlinarith [abs_nonneg (c2 y), sq_abs (c2 y)]
    rw [Real.norm_eq_abs, abs_of_nonneg (F2_nonneg (by linarith) y)]
    unfold F2
    rw [div_le_iff₀ (by linarith)]
    calc 16 * π ^ 2 * (1 - c2 y ^ 2) ≤ 16 * π ^ 2 * 1 := by gcongr
      _ = 32 * π ^ 2 * (1 / 2) := by ring
      _ ≤ 32 * π ^ 2 * (1 + ε * c2 y) := by gcongr
  · refine Eventually.of_forall fun y => ?_
    unfold F2
    exact ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)

theorem integral_F2_zero : ∫ y, F2 0 y ∂haar 1 = 8 * π ^ 2 := by
  have e : ∀ y, F2 0 y = 16 * π ^ 2 * (1 - c2 y ^ 2) := fun y => by unfold F2; ring
  simp_rw [e]
  rw [integral_const_mul, integral_sub (f := fun _ => (1 : ℝ)) (g := fun y => c2 y ^ 2)
    (integrable_const 1) (integrable_bdd (continuous_c2.pow 2)), integral_c2_sq]
  simp; ring

/-! ### The quotients and the upper bound on `r_{*,κ}` -/

theorem gap_rho_eq {κ : ℝ} (hκ : 0 < κ) {h : Torus 1 → ℝ} (hc : Continuous h)
    (hb : ∀ x, |h x| ≤ 1) (h0 : ∫ x, h x ∂haar 1 = 0) {ε : ℝ} (hε : |ε| ≤ 1) :
    gap cosV (cosW κ) (densMeasure (fun x => 1 + ε * h x)) =
      ((ENNReal.ofReal ((∫ x, klFun (1 + ε * h x) ∂haar 1) +
        κ / 2 * firstMode (fun x => 1 + ε * h x)) : ℝ≥0∞) : EReal) := by
  have hk : 0 ≤ ∫ x, klFun (1 + ε * h x) ∂haar 1 :=
    integral_nonneg fun x => klFun_nonneg (one_add_mul_nonneg hb hε x)
  have hQ : 0 ≤ firstMode (fun x => 1 + ε * h x) := Complex.normSq_nonneg _
  rw [(cosine_free_energy_aux hκ).2.2.2.1 _ (one_add_mul_nonneg hb hε) (integral_mode hc h0 ε),
    klDiv_mode hc hb h0 hε, EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal, max_eq_left hk,
    max_eq_left (by positivity), EReal.coe_add]

theorem kl_mode_pos {h : Torus 1 → ℝ} (hc : Continuous h) (hb : ∀ x, |h x| ≤ 1)
    (h0 : ∫ x, h x ∂haar 1 = 0) (hm : 0 < ∫ x, h x ^ 2 ∂haar 1) {ε : ℝ} (hε : |ε| < 1)
    (hne : ε ≠ 0) : 0 < ∫ x, klFun (1 + ε * h x) ∂haar 1 := by
  refine lt_of_lt_of_le ?_ (kl_mode_bounds hc hb h0 hε).1
  have : 0 < ε ^ 2 := by positivity
  positivity

theorem admissible_rho {κ : ℝ} (hκ : 0 < κ) {h : Torus 1 → ℝ} (hc : Continuous h)
    (hH : ContDiff ℝ ∞ (h ∘ liftT)) (hb : ∀ x, |h x| ≤ 1) (h0 : ∫ x, h x ∂haar 1 = 0)
    (hm : 0 < ∫ x, h x ^ 2 ∂haar 1) {ε : ℝ} (hε : |ε| < 1) (hne : ε ≠ 0) :
    Admissible cosV (cosW κ) (fun x => 1 + ε * h x) := by
  refine ⟨one_add_mul_nonneg hb hε.le, integral_mode hc h0 ε, memH1_sqrt_mode hH hb hε, ?_⟩
  rw [gap_rho_eq hκ hc hb h0 hε.le]
  have hk := kl_mode_pos hc hb h0 hm hε hne
  have hQ : 0 ≤ firstMode (fun x => 1 + ε * h x) := Complex.normSq_nonneg _
  exact EReal.coe_ennreal_pos.mpr (ENNReal.ofReal_pos.mpr (by positivity))

theorem quotient_eq {D K : ℝ} (hD : 0 ≤ D) (hK : 0 < K) :
    ENNReal.ofReal D / (2 * ENNReal.ofReal K) = ENNReal.ofReal (D / (2 * K)) := by
  rw [show (2 : ℝ≥0∞) * ENNReal.ofReal K = ENNReal.ofReal (2 * K) by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp, ENNReal.ofReal_div_of_pos (by positivity)]

theorem integral_gCos_sq_pos : 0 < ∫ x, gCos x ^ 2 ∂haar 1 := by rw [integral_gCos_sq]; norm_num

theorem integral_c2_sq_pos : 0 < ∫ x, c2 x ^ 2 ∂haar 1 := by rw [integral_c2_sq]; norm_num

/-- The mode-1 quotient `D/(2G) → a(1 + κ/2)`. -/
theorem tendsto_quotient_rho1 {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun ε : ℝ => dissipation cosV (cosW κ) (fun x => 1 + ε * gCos x) /
        (2 * (gap cosV (cosW κ) (densMeasure (fun x => 1 + ε * gCos x))).toENNReal))
      (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (aCos * (1 + κ / 2)))) := by
  have hΦ := ((continuousAt_integral_F1 κ).tendsto).mono_left
    (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
  rw [integral_F1_zero] at hΦ
  have hk := tendsto_kl_mode continuous_gCos abs_gCos_le integral_gCos
  rw [integral_gCos_sq] at hk
  have hden := (hk.add (tendsto_const_nhds (x := κ / 8))).const_mul 2
  have hq := hΦ.div hden (by positivity)
  have hval : π ^ 2 * (2 + κ) ^ 2 / 2 / (2 * (1 / 2 / 2 + κ / 8)) = aCos * (1 + κ / 2) := by
    unfold aCos; field_simp; ring
  rw [hval] at hq
  refine (ENNReal.tendsto_ofReal hq).congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds small_eventually, self_mem_nhdsWithin]
    with ε hε hne
  have hne' : ε ≠ 0 := hne
  have hε1 : |ε| < 1 := by linarith
  have hkp := kl_mode_pos continuous_gCos abs_gCos_le integral_gCos integral_gCos_sq_pos hε1 hne'
  rw [dissipation_rho1 κ hε1, gap_rho_eq hκ continuous_gCos abs_gCos_le integral_gCos hε1.le,
    EReal.toENNReal_coe, firstMode_rho1, quotient_eq (mul_nonneg (sq_nonneg _)
      (integral_nonneg fun y => F1_nonneg κ hε1 y)) (by positivity)]
  congr 1
  simp only [Pi.div_apply]
  field_simp
  ring

/-- The mode-2 quotient `D/(2G) → 4a`. -/
theorem tendsto_quotient_rho2 {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun ε : ℝ => dissipation cosV (cosW κ) (fun x => 1 + ε * gCos (2 • x)) /
        (2 * (gap cosV (cosW κ) (densMeasure (fun x => 1 + ε * gCos (2 • x)))).toENNReal))
      (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (4 * aCos))) := by
  have hΦ := (continuousAt_integral_F2.tendsto).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
  rw [integral_F2_zero] at hΦ
  have hk := tendsto_kl_mode continuous_c2 abs_c2_le integral_c2
  rw [integral_c2_sq] at hk
  have hq := hΦ.div (hk.const_mul 2) (by norm_num)
  have hval : 8 * π ^ 2 / (2 * (1 / 2 / 2)) = 4 * aCos := by unfold aCos; ring
  rw [hval] at hq
  refine (ENNReal.tendsto_ofReal hq).congr' ?_
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds small_eventually, self_mem_nhdsWithin]
    with ε hε hne
  have hne' : ε ≠ 0 := hne
  have hε1 : |ε| < 1 := by linarith
  have hkp := kl_mode_pos continuous_c2 abs_c2_le integral_c2 integral_c2_sq_pos hε1 hne'
  show _ = dissipation cosV (cosW κ) (fun x => 1 + ε * c2 x) /
    (2 * (gap cosV (cosW κ) (densMeasure (fun x => 1 + ε * c2 x))).toENNReal)
  rw [dissipation_rho2 κ hε1, gap_rho_eq hκ continuous_c2 abs_c2_le integral_c2 hε1.le,
    EReal.toENNReal_coe, firstMode_rho2, mul_zero, add_zero,
    quotient_eq (mul_nonneg (sq_nonneg _) (integral_nonneg fun y => F2_nonneg hε1 y)) hkp]
  congr 1
  simp only [Pi.div_apply]
  field_simp

/-- The expansions along `ρ_ε` and the second-mode quotient. -/
theorem cosine_rho_eps_expansions_aux {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun ε : ℝ => (gap cosV (cosW κ) (densMeasure (fun x => 1 + ε * gCos x))).toReal /
        ε ^ 2) (𝓝[≠] 0) (𝓝 ((1 + κ / 2) / 4)) ∧
    Tendsto (fun ε : ℝ => (dissipation cosV (cosW κ) (fun x => 1 + ε * gCos x)).toReal / ε ^ 2)
        (𝓝[≠] 0) (𝓝 (aCos / 2 * (1 + κ / 2) ^ 2)) ∧
    Tendsto (fun ε : ℝ => dissipation cosV (cosW κ) (fun x => 1 + ε * gCos (2 • x)) /
        (2 * (gap cosV (cosW κ) (densMeasure (fun x => 1 + ε * gCos (2 • x)))).toENNReal))
        (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (4 * aCos))) :=
  ⟨tendsto_gap_rho1 hκ, tendsto_dissipation_rho1 hκ, tendsto_quotient_rho2 hκ⟩

/-- `r_{*,κ} ≤ a min{1 + κ/2, 4}`. -/
theorem cosine_rStar_le_aux {κ : ℝ} (hκ : 0 < κ) :
    rStar cosV (cosW κ) ≤ ENNReal.ofReal (aCos * min (1 + κ / 2) 4) := by
  have hev : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |ε| < 1 ∧ ε ≠ 0 := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds small_eventually,
      self_mem_nhdsWithin] with ε hε hne
    exact ⟨by linarith, hne⟩
  have h1 : rStar cosV (cosW κ) ≤ ENNReal.ofReal (aCos * (1 + κ / 2)) := by
    refine ge_of_tendsto (tendsto_quotient_rho1 hκ) ?_
    filter_upwards [hev] with ε hε
    exact iInf₂_le _ (admissible_rho hκ continuous_gCos contDiff_gCos_lift abs_gCos_le
      integral_gCos integral_gCos_sq_pos hε.1 hε.2)
  have h2 : rStar cosV (cosW κ) ≤ ENNReal.ofReal (4 * aCos) := by
    refine ge_of_tendsto (tendsto_quotient_rho2 hκ) ?_
    filter_upwards [hev] with ε hε
    exact iInf₂_le (fun x => 1 + ε * c2 x) (admissible_rho hκ continuous_c2 contDiff_c2_lift
      abs_c2_le integral_c2 integral_c2_sq_pos hε.1 hε.2)
  have ha : 0 ≤ aCos := by unfold aCos; positivity
  rw [mul_min_of_nonneg _ _ ha, ENNReal.ofReal_min]
  exact le_min h1 (by rw [mul_comm]; exact h2)

end SharpLSI
