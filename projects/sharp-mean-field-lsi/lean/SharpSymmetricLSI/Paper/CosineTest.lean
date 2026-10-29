import SharpSymmetricLSI.Defs.D12_Cosine
import SharpSymmetricLSI.Infra.SmoothWeakGrad
import SharpSymmetricLSI.Infra.Calculus

/-!
# R9: the one-coordinate test `h_ε = 1 + ε cos 2πx` (Phase 1)

Manuscript Section 3.2, display after (3.9): `2∫|h_ε'|² dm = aε²` (`dirichlet_hEps`, via the
classical derivative and `weakGrad_ae_eq_of_contDiff`) and `Ent_m(h_ε²) = ε² + O(|ε|³)`
(`entHEps_approx`, second-order Taylor bounds for `s log s`), hence the quotient tends to `a`
(`cosine_test_quotient_aux`).
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace SharpLSI

/-- Integrals over `𝕋 = 𝕋^1` of functions of the single coordinate, as integrals over `(0,1]`. -/
theorem integral_torus1 (g : UnitAddCircle → ℝ) :
    ∫ y : Torus 1, g (y 0) = ∫ t in Ioc (0 : ℝ) 1, g t := by
  have h := (volume_preserving_funUnique (Fin 1) UnitAddCircle).integral_comp'
    (g := g)
  simp only [MeasurableEquiv.funUnique_apply] at h
  calc ∫ y : Torus 1, g (y 0) = ∫ y : UnitAddCircle, g y := h
    _ = _ := by rw [← UnitAddCircle.integral_preimage 0 g, zero_add]

theorem gCos_coe (y : Torus 1) (s : ℝ) (hs : y 0 = (s : UnitAddCircle)) :
    gCos y = Real.cos (2 * π * s) := by
  rw [gCos, expT, hs, fourier_coe_apply]
  push_cast
  rw [show (2 * (π : ℂ) * Complex.I * 1 * s / 1) = ((2 * π * s : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_re]

theorem expT_im_coe (y : Torus 1) (s : ℝ) (hs : y 0 = (s : UnitAddCircle)) :
    (expT y).im = Real.sin (2 * π * s) := by
  rw [expT, hs, fourier_coe_apply]
  push_cast
  rw [show (2 * (π : ℂ) * Complex.I * 1 * s / 1) = ((2 * π * s : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_im]

@[fun_prop] theorem continuous_expT : Continuous expT :=
  (fourier 1).continuous.comp (continuous_apply 0)

@[fun_prop] theorem continuous_gCos : Continuous gCos :=
  Complex.continuous_re.comp continuous_expT

theorem abs_gCos_le (y : Torus 1) : |gCos y| ≤ 1 := by
  have h1 : ‖expT y‖ = 1 := by simp [expT, fourier_apply]
  calc |gCos y| = |(expT y).re| := rfl
    _ ≤ ‖expT y‖ := Complex.abs_re_le_norm _
    _ = 1 := h1

theorem integrable_of_continuous_torus1 {F : Torus 1 → ℝ} (hF : Continuous F) :
    Integrable F (haar 1) :=
  (BoundedContinuousFunction.mkOfCompact ⟨F, hF⟩).integrable _

theorem intervalIntegral_cos_two_pi : ∫ s in (0 : ℝ)..1, Real.cos (2 * π * s) = 0 := by
  rw [intervalIntegral.integral_comp_mul_left (fun s => Real.cos s) (by positivity), integral_cos]
  simp

theorem intervalIntegral_cos_sq_two_pi : ∫ s in (0 : ℝ)..1, Real.cos (2 * π * s) ^ 2 = 1 / 2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun s => Real.cos s ^ 2) (by positivity),
    integral_cos_sq]
  simp; field_simp

theorem intervalIntegral_sin_sq_two_pi : ∫ s in (0 : ℝ)..1, Real.sin (2 * π * s) ^ 2 = 1 / 2 := by
  rw [intervalIntegral.integral_comp_mul_left (fun s => Real.sin s ^ 2) (by positivity),
    integral_sin_sq]
  simp; field_simp

/-- `∫_𝕋 F(gCos) dm = ∫_0^1 F(cos 2πs) ds`. -/
theorem integral_fun_gCos (F : ℝ → ℝ) :
    ∫ y : Torus 1, F (gCos y) = ∫ s in (0 : ℝ)..1, F (Real.cos (2 * π * s)) := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have := integral_torus1 (fun t => F (fourier 1 t).re)
  calc ∫ y : Torus 1, F (gCos y) = ∫ y : Torus 1, F ((fourier 1) (y 0)).re := rfl
    _ = ∫ t in Ioc (0 : ℝ) 1, F ((fourier 1) (t : UnitAddCircle)).re := this
    _ = _ := by
      congr 1; funext t
      rw [show (fourier 1 (t : UnitAddCircle)).re = gCos (fun _ => (t : UnitAddCircle)) from rfl,
        gCos_coe _ t rfl]

theorem integral_fun_expT_im (F : ℝ → ℝ) :
    ∫ y : Torus 1, F (expT y).im = ∫ s in (0 : ℝ)..1, F (Real.sin (2 * π * s)) := by
  rw [intervalIntegral.integral_of_le zero_le_one]
  have := integral_torus1 (fun t => F (fourier 1 t).im)
  calc ∫ y : Torus 1, F (expT y).im = ∫ y : Torus 1, F ((fourier 1) (y 0)).im := rfl
    _ = ∫ t in Ioc (0 : ℝ) 1, F ((fourier 1) (t : UnitAddCircle)).im := this
    _ = _ := by
      congr 1; funext t
      rw [show (fourier 1 (t : UnitAddCircle)).im = (expT (fun _ => (t : UnitAddCircle))).im
        from rfl, expT_im_coe _ t rfl]

/-! ### The Dirichlet energy of `h_ε = 1 + ε cos 2πx` -/

theorem dirichlet_hEps (ε : ℝ) :
    dirichlet (haar 1) (fun x => 1 + ε * gCos x) = ENNReal.ofReal (aCos * ε ^ 2 / 2) := by
  set h : Torus 1 → ℝ := fun x => 1 + ε * gCos x with hh
  have hlift : h ∘ liftT = fun z : Fin 1 → ℝ => 1 + ε * Real.cos (2 * π * z 0) := by
    funext z; simp only [Function.comp, hh]; rw [gCos_coe (liftT z) (z 0) rfl]
  have hcd : ContDiff ℝ 1 (h ∘ liftT) := by rw [hlift]; fun_prop
  have hderiv : ∀ z : Fin 1 → ℝ, fderiv ℝ (h ∘ liftT) z (Pi.single 0 1) =
      -(ε * (2 * π) * Real.sin (2 * π * z 0)) := by
    intro z
    rw [hlift]
    have hG : HasDerivAt (fun t : ℝ => 1 + ε * Real.cos (2 * π * t))
        (-(ε * (2 * π) * Real.sin (2 * π * z 0))) (z 0) := by
      have := (((hasDerivAt_id' (z 0)).const_mul (2 * π)).cos.const_mul ε).const_add 1
      convert this using 1; ring
    have hP : HasFDerivAt (fun z : Fin 1 → ℝ => z 0)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0) z :=
      hasFDerivAt_apply 0 z
    have hc := hG.comp_hasFDerivAt z hP
    rw [show (fun z : Fin 1 → ℝ => 1 + ε * Real.cos (2 * π * z 0)) =
      (fun t : ℝ => 1 + ε * Real.cos (2 * π * t)) ∘ (fun z : Fin 1 → ℝ => z 0) from rfl, hc.fderiv]
    simp
  unfold dirichlet
  have hae : ∀ᵐ y ∂(haar 1), ENNReal.ofReal (sqNorm (weakGrad h y)) =
      ENNReal.ofReal ((ε * (2 * π)) ^ 2 * (expT y).im ^ 2) := by
    filter_upwards [weakGrad_ae_eq_of_contDiff hcd] with y hy
    rw [hy]
    congr 1
    simp only [sqNorm, Fin.sum_univ_one]
    rw [hderiv, expT_im_coe y (secT y 0) (congrFun (liftT_secT y) 0).symm]
    ring
  rw [lintegral_congr_ae hae]
  have hcont : Continuous fun y : Torus 1 => (ε * (2 * π)) ^ 2 * (expT y).im ^ 2 :=
    continuous_const.mul ((Complex.continuous_im.comp continuous_expT).pow 2)
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_of_continuous_torus1 hcont)
    (Filter.Eventually.of_forall fun y => by simp only [Pi.zero_apply]; positivity)]
  congr 1
  rw [integral_fun_expT_im (fun s => (ε * (2 * π)) ^ 2 * s ^ 2),
    intervalIntegral.integral_const_mul, intervalIntegral_sin_sq_two_pi, aCos]
  ring

/-! ### The entropy of `h_ε²` -/

/-- Taylor bounds for `φ(s) = s log s` at `1`. -/
theorem mul_log_taylor_bounds {t δ : ℝ} (hδ : δ < 1) (ht : |t| ≤ δ) :
    t + t ^ 2 / (2 * (1 + δ)) ≤ (1 + t) * Real.log (1 + t) ∧
      (1 + t) * Real.log (1 + t) ≤ t + t ^ 2 / (2 * (1 - δ)) := by
  have hδ0 : 0 ≤ δ := le_trans (abs_nonneg t) ht
  have hseg : ∀ y ∈ Set.uIcc 1 (1 + t), 1 - δ ≤ y ∧ y ≤ 1 + δ := by
    intro y hy
    have := abs_le.mp ht
    rcases Set.mem_uIcc.mp hy with h | h <;> constructor <;> linarith [h.1, h.2]
  have hpos : ∀ y ∈ Set.uIcc 1 (1 + t), 0 < y := fun y hy => by linarith [(hseg y hy).1]
  have hd1 : ∀ y ∈ Set.uIcc 1 (1 + t), HasDerivAt (fun s => s * Real.log s) (Real.log y + 1) y :=
    fun y hy => Real.hasDerivAt_mul_log (hpos y hy).ne'
  have hd2 : ∀ y ∈ Set.uIcc 1 (1 + t), HasDerivAt (fun s => Real.log s + 1) y⁻¹ y :=
    fun y hy => (Real.hasDerivAt_log (hpos y hy).ne').add_const 1
  constructor
  · have := taylor2 (f := fun s => -(s * Real.log s)) (f' := fun s => -(Real.log s + 1))
      (f'' := fun s => -s⁻¹) (x₀ := 1) (x := 1 + t) (K := -(1 + δ)⁻¹)
      (fun y hy => (hd1 y hy).neg) (fun y hy => (hd2 y hy).neg)
      (fun y hy => by
        simp only [neg_le_neg_iff]
        exact inv_anti₀ (hpos y hy) (hseg y hy).2)
    simp only [Real.log_one, mul_zero, neg_zero, zero_add, add_sub_cancel_left] at this
    have e : -(1 + δ)⁻¹ / 2 * t ^ 2 = -(t ^ 2 / (2 * (1 + δ))) := by field_simp
    linarith
  · have := taylor2 (f := fun s => s * Real.log s) (f' := fun s => Real.log s + 1)
      (f'' := fun s => s⁻¹) (x₀ := 1) (x := 1 + t) (K := (1 - δ)⁻¹)
      hd1 hd2 (fun y hy => inv_anti₀ (by linarith) (hseg y hy).1)
    simp only [Real.log_one, mul_zero, zero_add, add_sub_cancel_left, one_mul, sub_zero] at this
    have e : (1 - δ)⁻¹ / 2 * t ^ 2 = t ^ 2 / (2 * (1 - δ)) := by field_simp
    linarith

theorem integral_gCos : ∫ y, gCos y ∂haar 1 = 0 := by
  have := integral_fun_gCos (fun s => s)
  simpa [intervalIntegral_cos_two_pi] using this

theorem integral_gCos_sq : ∫ y, gCos y ^ 2 ∂haar 1 = 1 / 2 := by
  have := integral_fun_gCos (fun s => s ^ 2)
  simpa [intervalIntegral_cos_sq_two_pi] using this

/-- `Ent_m(h_ε²)` as a real number (manuscript (1.3)). -/
noncomputable def entHEps (ε : ℝ) : ℝ :=
  ∫ y, (1 + ε * gCos y) ^ 2 * Real.log ((1 + ε * gCos y) ^ 2) ∂haar 1 -
    (∫ y, (1 + ε * gCos y) ^ 2 ∂haar 1) * Real.log (∫ y, (1 + ε * gCos y) ^ 2 ∂haar 1)

theorem ent_hEps (ε : ℝ) :
    ent (haar 1) (fun x => (1 + ε * gCos x) ^ 2) = ENNReal.ofReal (entHEps ε) := by
  have hc : Continuous fun x => (1 + ε * gCos x) ^ 2 :=
    (continuous_const.add (continuous_const.mul continuous_gCos)).pow 2
  exact ent_eq_formula (haar 1) _ (fun x => sq_nonneg _) (integrable_of_continuous_torus1 hc)
    (integrable_of_continuous_torus1 (Real.continuous_mul_log.comp hc))

theorem integral_hEps_sq (ε : ℝ) : ∫ y, (1 + ε * gCos y) ^ 2 ∂haar 1 = 1 + ε ^ 2 / 2 := by
  have e : (fun y => (1 + ε * gCos y) ^ 2) =
      fun y => (1 + 2 * ε * gCos y) + ε ^ 2 * gCos y ^ 2 := by funext y; ring
  have i1 : Integrable (fun y => 2 * ε * gCos y) (haar 1) :=
    (integrable_of_continuous_torus1 continuous_gCos).const_mul _
  have i2 : Integrable (fun y => ε ^ 2 * gCos y ^ 2) (haar 1) :=
    (integrable_of_continuous_torus1 (continuous_gCos.pow 2)).const_mul _
  have i3 : Integrable (fun y => 1 + 2 * ε * gCos y) (haar 1) := (integrable_const 1).add i1
  rw [e, integral_add i3 i2, integral_add (integrable_const 1) i1, integral_const_mul,
    integral_const_mul, integral_gCos, integral_gCos_sq]
  simp; ring

theorem entHEps_approx {ε : ℝ} (hε : |ε| ≤ 1 / 8) : |entHEps ε - ε ^ 2| ≤ 20 * |ε| ^ 3 := by
  set e := |ε| with he
  have he0 : 0 ≤ e := abs_nonneg ε
  have he2 : ε ^ 2 = e ^ 2 := (sq_abs ε).symm
  have hcpt : ∀ y, |gCos y| ≤ 1 := abs_gCos_le
  set t : Torus 1 → ℝ := fun y => 2 * ε * gCos y + ε ^ 2 * gCos y ^ 2 with htdef
  set δ := 3 * e with hδ
  have hδ1 : δ < 1 := by rw [hδ]; linarith
  have ht : ∀ y, |t y| ≤ δ := by
    intro y
    have hc := hcpt y
    have hc2 : gCos y ^ 2 ≤ 1 := by nlinarith [abs_nonneg (gCos y), sq_abs (gCos y)]
    have a1 : |2 * ε * gCos y| ≤ 2 * e := by
      rw [abs_mul, abs_mul, abs_two]
      exact mul_le_of_le_one_right (by positivity) hc
    have a2 : |ε ^ 2 * gCos y ^ 2| ≤ e ^ 2 := by
      rw [abs_mul, abs_pow, abs_pow]
      exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (abs_nonneg _) hc)
    calc |t y| ≤ |2 * ε * gCos y| + |ε ^ 2 * gCos y ^ 2| := abs_add_le _ _
      _ ≤ 2 * e + e ^ 2 := add_le_add a1 a2
      _ ≤ δ := by rw [hδ]; nlinarith
  have hu : ∀ y, (1 + ε * gCos y) ^ 2 = 1 + t y := fun y => by simp only [htdef]; ring
  have hct : Continuous t := by
    simp only [htdef]; fun_prop
  have hctl : Continuous fun y => (1 + t y) * Real.log (1 + t y) :=
    Real.continuous_mul_log.comp (continuous_const.add hct)
  have iT := integrable_of_continuous_torus1 hct
  have iT2 := integrable_of_continuous_torus1 (hct.pow 2)
  have iL := integrable_of_continuous_torus1 hctl
  -- `∫ t = ε²/2`
  have hint_t : ∫ y, t y ∂haar 1 = ε ^ 2 / 2 := by
    have := integral_hEps_sq ε
    simp_rw [hu] at this
    rw [integral_add (integrable_const 1) iT] at this
    simp at this; linarith
  -- `∫ t² = 2ε² + R`, `|R| ≤ 5|ε|³`
  obtain ⟨T2, hT2⟩ : ∃ T2, T2 = ∫ y, t y ^ 2 ∂haar 1 := ⟨_, rfl⟩
  have hT2b : |T2 - 2 * ε ^ 2| ≤ 5 * e ^ 3 := by
    have e1 : (fun y => t y ^ 2) = fun y => 4 * ε ^ 2 * gCos y ^ 2 +
        (4 * ε ^ 3 * gCos y ^ 3 + ε ^ 4 * gCos y ^ 4) := by funext y; simp only [htdef]; ring
    have iR := integrable_of_continuous_torus1 (show Continuous fun y =>
      4 * ε ^ 3 * gCos y ^ 3 + ε ^ 4 * gCos y ^ 4 by fun_prop)
    have i2 : Integrable (fun y => 4 * ε ^ 2 * gCos y ^ 2) (haar 1) :=
      (integrable_of_continuous_torus1 (continuous_gCos.pow 2)).const_mul _
    rw [hT2, e1, integral_add i2 iR, integral_const_mul, integral_gCos_sq]
    have hR : ‖∫ y, (4 * ε ^ 3 * gCos y ^ 3 + ε ^ 4 * gCos y ^ 4) ∂haar 1‖ ≤ 5 * e ^ 3 * 1 := by
      have := norm_integral_le_of_norm_le_const (μ := haar 1) (C := 5 * e ^ 3)
        (f := fun y => 4 * ε ^ 3 * gCos y ^ 3 + ε ^ 4 * gCos y ^ 4)
        (Filter.Eventually.of_forall fun y => by
          have hc := hcpt y
          have hc0 := abs_nonneg (gCos y)
          rw [Real.norm_eq_abs]
          calc |4 * ε ^ 3 * gCos y ^ 3 + ε ^ 4 * gCos y ^ 4|
              ≤ |4 * ε ^ 3 * gCos y ^ 3| + |ε ^ 4 * gCos y ^ 4| := abs_add_le _ _
            _ = 4 * e ^ 3 * |gCos y| ^ 3 + e ^ 4 * |gCos y| ^ 4 := by
                simp only [abs_mul, abs_pow, he]; norm_num
            _ ≤ 4 * e ^ 3 * 1 + e ^ 4 * 1 := by gcongr <;> exact pow_le_one₀ hc0 hc
            _ ≤ 5 * e ^ 3 := by nlinarith [pow_nonneg he0 3])
      simpa using this
    rw [Real.norm_eq_abs] at hR
    have : 4 * ε ^ 2 * (1 / 2) + ∫ y, (4 * ε ^ 3 * gCos y ^ 3 + ε ^ 4 * gCos y ^ 4) ∂haar 1 -
        2 * ε ^ 2 = ∫ y, (4 * ε ^ 3 * gCos y ^ 3 + ε ^ 4 * gCos y ^ 4) ∂haar 1 := by ring
    rw [this]; linarith
  -- integrated Taylor bounds
  have hlow : ∫ y, t y ∂haar 1 + T2 / (2 * (1 + δ)) ≤
      ∫ y, (1 + t y) * Real.log (1 + t y) ∂haar 1 := by
    have iD : Integrable (fun y => t y ^ 2 / (2 * (1 + δ))) (haar 1) := iT2.div_const _
    rw [hT2, ← integral_div, ← integral_add iT iD]
    exact integral_mono (iT.add iD) iL fun y => (mul_log_taylor_bounds hδ1 (ht y)).1
  have hup : ∫ y, (1 + t y) * Real.log (1 + t y) ∂haar 1 ≤
      ∫ y, t y ∂haar 1 + T2 / (2 * (1 - δ)) := by
    have iD : Integrable (fun y => t y ^ 2 / (2 * (1 - δ))) (haar 1) := iT2.div_const _
    rw [hT2, ← integral_div, ← integral_add iT iD]
    exact integral_mono iL (iT.add iD) fun y => (mul_log_taylor_bounds hδ1 (ht y)).2
  have hτ : |ε ^ 2 / 2| ≤ δ := by
    rw [abs_of_nonneg (by positivity), he2, hδ]; nlinarith
  have hmean := mul_log_taylor_bounds hδ1 hτ
  have hE : entHEps ε = ∫ y, (1 + t y) * Real.log (1 + t y) ∂haar 1 -
      (1 + ε ^ 2 / 2) * Real.log (1 + ε ^ 2 / 2) := by
    rw [entHEps, integral_hEps_sq]; simp_rw [hu]
  rw [hE]
  rw [hint_t] at hlow hup
  have hT2u : T2 ≤ 2 * e ^ 2 + 5 * e ^ 3 := by rw [he2] at hT2b; linarith [(abs_le.mp hT2b).2]
  have hT2l : 2 * e ^ 2 - 5 * e ^ 3 ≤ T2 := by rw [he2] at hT2b; linarith [(abs_le.mp hT2b).1]
  have h1δ : (5 : ℝ) / 8 ≤ 1 - δ := by rw [hδ]; linarith
  -- upper bound `E ≤ e² + 20e³`
  have hU : T2 / (2 * (1 - δ)) ≤ e ^ 2 + 20 * e ^ 3 := by
    rw [div_le_iff₀ (by linarith), hδ]
    nlinarith [pow_nonneg he0 3, pow_nonneg he0 4, mul_nonneg (pow_nonneg he0 3) he0]
  -- lower bound `E ≥ e² - 20e³`
  have hL1 : e ^ 2 - 10 * e ^ 3 ≤ T2 / (2 * (1 + δ)) := by
    rw [le_div_iff₀ (by rw [hδ]; linarith), hδ]
    nlinarith [pow_nonneg he0 3, pow_nonneg he0 4]
  have hL2 : (ε ^ 2 / 2) ^ 2 / (2 * (1 - δ)) ≤ e ^ 3 := by
    rw [div_le_iff₀ (by linarith), he2]
    nlinarith [pow_nonneg he0 3, pow_nonneg he0 4, mul_nonneg (pow_nonneg he0 3) he0]
  have hX : 0 ≤ (ε ^ 2 / 2) ^ 2 / (2 * (1 + δ)) :=
    div_nonneg (sq_nonneg _) (by rw [hδ]; linarith)
  have he3 : 0 ≤ e ^ 3 := pow_nonneg he0 3
  rw [abs_le]
  constructor <;> linarith [hmean.1, hmean.2]

/-- Unnumbered display after (3.9): `2∫|h_ε'|²/Ent_m(h_ε²) → a` as `ε → 0`. -/
theorem cosine_test_quotient_aux :
    Tendsto (fun ε : ℝ => 2 * dirichlet (haar 1) (fun x => 1 + ε * gCos x) /
        ent (haar 1) (fun x => (1 + ε * gCos x) ^ 2)) (𝓝[≠] 0) (𝓝 (ENNReal.ofReal aCos)) := by
  have ha : 0 < aCos := by unfold aCos; positivity
  have hsmall : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), |ε| < 1 / 40 :=
    eventually_nhdsWithin_of_eventually_nhds
      ((continuous_abs.tendsto (0 : ℝ)).eventually (gt_mem_nhds (by norm_num)))
  have hne : ∀ᶠ ε in 𝓝[≠] (0 : ℝ), ε ≠ 0 := self_mem_nhdsWithin
  -- `E/ε² → 1`
  have hbounds : ∀ᶠ ε in 𝓝[≠] (0 : ℝ),
      1 - 20 * |ε| ≤ entHEps ε / ε ^ 2 ∧ entHEps ε / ε ^ 2 ≤ 1 + 20 * |ε| := by
    filter_upwards [hsmall, hne] with ε h1 h2
    have hε2 : 0 < ε ^ 2 := by positivity
    have hb := abs_le.mp (entHEps_approx (ε := ε) (by linarith))
    have e3 : |ε| ^ 3 = |ε| * ε ^ 2 := by rw [pow_succ, sq_abs]; ring
    rw [e3] at hb
    constructor
    · rw [le_div_iff₀ hε2]; linarith [hb.1]
    · rw [div_le_iff₀ hε2]; linarith [hb.2]
  have hlim : ∀ c : ℝ, Tendsto (fun ε : ℝ => 1 + c * |ε|) (𝓝[≠] 0) (𝓝 1) := fun c => by
    have : Tendsto (fun ε : ℝ => 1 + c * |ε|) (𝓝 0) (𝓝 (1 + c * |(0:ℝ)|)) :=
      (continuous_const.add (continuous_const.mul continuous_abs)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hq : Tendsto (fun ε => entHEps ε / ε ^ 2) (𝓝[≠] 0) (𝓝 1) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' ?_ (hlim 20)
      (hbounds.mono fun _ h => h.1) (hbounds.mono fun _ h => h.2)
    simpa [sub_eq_add_neg, neg_mul] using hlim (-20)
  have hreal : Tendsto (fun ε => aCos / (entHEps ε / ε ^ 2)) (𝓝[≠] 0) (𝓝 aCos) := by
    have h := (tendsto_const_nhds (x := aCos)).div hq one_ne_zero
    rw [div_one] at h
    exact h
  refine (ENNReal.tendsto_ofReal hreal).congr' ?_
  filter_upwards [hbounds, hsmall, hne] with ε hb h1 h2
  have hε2 : 0 < ε ^ 2 := by positivity
  have hq0 : 0 < entHEps ε / ε ^ 2 := by linarith [hb.1]
  have hE : 0 < entHEps ε := by
    have := mul_pos hq0 hε2; rwa [div_mul_cancel₀ _ hε2.ne'] at this
  rw [dirichlet_hEps, ent_hEps, ← ENNReal.ofReal_ofNat 2,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_div_of_pos hE]
  congr 1
  field_simp

end SharpLSI
