import DGPS.Circle.HeatInformation

/-!
# FIN042: optional direct planar Poincare inequality

For a rotational probability measure `nu = (angleLaw ⊗ sigma).map polar` on the plane
(`sigma` the law of the signed radius) with radial Poincare inverse constant `P` and
`R2 = ∫ r^2 dsigma < ∞`, every smooth planar `F` of finite energy satisfies
`Var_nu(F) ≤ max P R2 * ∫ |∇F|^2 dnu`.  The proof decomposes the variance by angle, applies the
radial inequality for fixed angle, and bounds the variance of the angular mean `M(θ)` by
Cauchy-Schwarz and the Wirtinger inequality; truncation in the radius (with Fatou in the limit)
replaces an origin cutoff.
-/


open MeasureTheory Set Filter Topology
open scoped ContDiff Real ENNReal

namespace DGPS.FiniteN.Tools.PlanarPoincare

/-- Partial derivative in the first variable. -/
noncomputable def d1 (G : ℝ × ℝ → ℝ) : ℝ × ℝ → ℝ := fun p => fderiv ℝ G p (1, 0)

lemma contDiff_d1 {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) : ContDiff ℝ ∞ (d1 G) :=
  (hG.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const

lemma hasDerivAt_d1 {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (θ r : ℝ) :
    HasDerivAt (fun t => G (t, r)) (d1 G (θ, r)) θ := by
  have h1 : HasFDerivAt G (fderiv ℝ G (θ, r)) (θ, r) :=
    ((hG.differentiable (by simp)) (θ, r)).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => (t, r)) ((1 : ℝ), (0 : ℝ)) θ :=
    (hasDerivAt_id θ).prodMk (hasDerivAt_const θ r)
  exact h1.comp_hasDerivAt θ h2

lemma hasDerivAt_param_integral {μ : Measure ℝ} [IsFiniteMeasure μ] {K : ℝ}
    (hK : ∀ᵐ r ∂μ, r ∈ Icc (-K) K) {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (θ0 : ℝ) :
    HasDerivAt (fun θ => ∫ r, G (θ, r) ∂μ) (∫ r, d1 G (θ0, r) ∂μ) θ0 := by
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc :
    IsCompact (Icc (θ0 - 1) (θ0 + 1) ×ˢ Icc (-K) K)).exists_bound_of_continuousOn
      (contDiff_d1 hG).continuous.continuousOn
  have hGc : Continuous G := hG.continuous
  have hdc : Continuous (d1 G) := (contDiff_d1 hG).continuous
  have hmeas : ∀ θ, AEStronglyMeasurable (fun r => G (θ, r)) μ := fun θ =>
    (hGc.comp (Continuous.prodMk_right θ)).aestronglyMeasurable
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun θ r => G (θ, r)) (F' := fun θ r => d1 G (θ, r)) (x₀ := θ0)
    (bound := fun _ => C) (s := Metric.ball θ0 1) (Metric.ball_mem_nhds θ0 one_pos)
    (Eventually.of_forall hmeas)
    (by
      obtain ⟨C2, hC2⟩ := (isCompact_Icc (a := -K) (b := K)).exists_bound_of_continuousOn
        (hGc.comp (Continuous.prodMk_right θ0)).continuousOn
      refine (integrable_const C2).mono' (hmeas θ0) ?_
      filter_upwards [hK] with r hr using hC2 r hr)
    ((hdc.comp (Continuous.prodMk_right θ0)).aestronglyMeasurable)
    (by
      filter_upwards [hK] with r hr θ hθ
      refine hC (θ, r) ⟨?_, hr⟩
      rw [Metric.mem_ball, Real.dist_eq] at hθ
      have := abs_lt.mp hθ
      constructor <;> simp only <;> linarith [this.1, this.2])
    (integrable_const C)
    (Eventually.of_forall fun r θ _ => hasDerivAt_d1 hG θ r)
  exact this.2

lemma contDiff_param_integral_nat {μ : Measure ℝ} [IsFiniteMeasure μ] {K : ℝ}
    (hK : ∀ᵐ r ∂μ, r ∈ Icc (-K) K) (n : ℕ) :
    ∀ {G : ℝ × ℝ → ℝ}, ContDiff ℝ ∞ G → ContDiff ℝ n (fun θ => ∫ r, G (θ, r) ∂μ) := by
  induction n with
  | zero =>
    intro G hG
    refine contDiff_zero.2 ?_
    exact continuous_iff_continuousAt.2 fun θ => (hasDerivAt_param_integral hK hG θ).continuousAt
  | succ n ih =>
    intro G hG
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by push_cast; rfl, contDiff_succ_iff_deriv]
    refine ⟨fun θ => (hasDerivAt_param_integral hK hG θ).differentiableAt, by simp, ?_⟩
    have : deriv (fun θ => ∫ r, G (θ, r) ∂μ) = fun θ => ∫ r, d1 G (θ, r) ∂μ :=
      funext fun θ => (hasDerivAt_param_integral hK hG θ).deriv
    rw [this]
    exact ih (contDiff_d1 hG)

lemma contDiff_param_integral {μ : Measure ℝ} [IsFiniteMeasure μ] {K : ℝ}
    (hK : ∀ᵐ r ∂μ, r ∈ Icc (-K) K) {G : ℝ × ℝ → ℝ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun θ => ∫ r, G (θ, r) ∂μ) :=
  contDiff_infty.2 fun n => contDiff_param_integral_nat hK n hG

/-- Uniform probability law of the angle on `(0, 2π]`. -/
noncomputable def angleLaw : Measure ℝ :=
  ENNReal.ofReal (2 * π)⁻¹ • volume.restrict (Ioc 0 (2 * π))

instance : IsProbabilityMeasure angleLaw := by
  refine ⟨?_⟩
  rw [angleLaw, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioc, sub_zero, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity),
    inv_mul_cancel₀ Real.two_pi_pos.ne', ENNReal.ofReal_one]

lemma integral_angleLaw (h : ℝ → ℝ) :
    ∫ x, h x ∂angleLaw = (2 * π)⁻¹ * ∫ x in (0:ℝ)..(2 * π), h x := by
  rw [angleLaw, integral_smul_measure, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    ENNReal.toReal_ofReal (by positivity)]
  rfl

/-- Wirtinger's inequality for the period `2π`. -/
lemma wirtinger_two_pi {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (hper : Function.Periodic h (2 * π))
    (c : ℝ) (hc : c = (2 * π)⁻¹ * ∫ x in (0:ℝ)..(2 * π), h x) :
    ∫ x in (0:ℝ)..(2 * π), (h x - c) ^ 2 ≤ ∫ x in (0:ℝ)..(2 * π), deriv h x ^ 2 := by
  have hpi : (2 * π) ≠ 0 := Real.two_pi_pos.ne'
  set g : ℝ → ℝ := fun x => h (2 * π * x) - c with hg
  have hgs : ContDiff ℝ ∞ g :=
    (hh.comp (contDiff_const.mul contDiff_id)).sub contDiff_const
  have hgp : Function.Periodic g 1 := fun x => by
    simp only [hg]
    have := hper (2 * π * x)
    rw [mul_add, mul_one]; rw [this]
  have hgd : ∀ x, deriv g x = 2 * π * deriv h (2 * π * x) := by
    intro x
    have h1 : HasDerivAt h (deriv h (2 * π * x)) (2 * π * x) :=
      ((hh.differentiable (by simp)) _).hasDerivAt
    have h2 := (h1.comp x ((hasDerivAt_id x).const_mul (2 * π))).sub_const c
    simpa [hg, mul_comm] using h2.deriv
  have hcont : Continuous h := hh.continuous
  have hdcont : Continuous (deriv h) := (contDiff_infty_iff_deriv.mp hh).2.continuous
  have hmean : ∫ x in (0:ℝ)..1, g x = 0 := by
    simp only [hg]
    rw [intervalIntegral.integral_sub, intervalIntegral.integral_comp_mul_left (fun y => h y) hpi]
    · simp only [mul_zero, mul_one, smul_eq_mul, intervalIntegral.integral_const, sub_zero]
      rw [hc]; ring
    · exact (hcont.comp (continuous_const.mul continuous_id)).intervalIntegrable _ _
    · exact intervalIntegrable_const
  have hw := DGPS.Circle.HeatInformation.wirtinger hgs hgp hmean
  have e1 : ∫ x in (0:ℝ)..1, g x ^ 2 = (2 * π)⁻¹ * ∫ x in (0:ℝ)..(2 * π), (h x - c) ^ 2 := by
    have := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
      (fun y => (h y - c) ^ 2) hpi
    simpa [hg] using this
  have e2 : ∫ x in (0:ℝ)..1, deriv g x ^ 2
      = 4 * π ^ 2 * ((2 * π)⁻¹ * ∫ x in (0:ℝ)..(2 * π), deriv h x ^ 2) := by
    have := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
      (fun y => deriv h y ^ 2) hpi
    simp only [hgd, mul_pow]
    rw [intervalIntegral.integral_const_mul]
    simp only [mul_zero, mul_one, smul_eq_mul] at this
    rw [this]; ring
  rw [e1, e2] at hw
  have hp : 0 < π := Real.pi_pos
  have : (2 * π)⁻¹ * ∫ x in (0:ℝ)..(2 * π), (h x - c) ^ 2
      ≤ (2 * π)⁻¹ * ∫ x in (0:ℝ)..(2 * π), deriv h x ^ 2 := by
    have h4 : 0 < 4 * π ^ 2 := by positivity
    nlinarith
  exact le_of_mul_le_mul_left this (by positivity)

lemma cs_integral {μ : Measure ℝ} {a b : ℝ → ℝ} (ham : AEStronglyMeasurable a μ)
    (hbm : AEStronglyMeasurable b μ) (ha : Integrable (fun r => a r ^ 2) μ)
    (hb : Integrable (fun r => b r ^ 2) μ) :
    (∫ r, a r * b r ∂μ) ^ 2 ≤ (∫ r, a r ^ 2 ∂μ) * ∫ r, b r ^ 2 ∂μ := by
  have hab : Integrable (fun r => a r * b r) μ := by
    refine ((ha.add hb).div_const 2).mono' (ham.mul hbm) (Eventually.of_forall fun r => ?_)
    simp only [Pi.add_apply, Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|a r| - |b r|), sq_abs (a r), sq_abs (b r), abs_nonneg (a r),
      abs_nonneg (b r)]
  have key : ∀ x : ℝ, 0 ≤ (∫ r, a r ^ 2 ∂μ) * (x * x) + (-2 * ∫ r, a r * b r ∂μ) * x
      + ∫ r, b r ^ 2 ∂μ := by
    intro x
    have h0 : 0 ≤ ∫ r, (x * a r - b r) ^ 2 ∂μ := integral_nonneg fun r => sq_nonneg _
    have h1 : ∫ r, (x * a r - b r) ^ 2 ∂μ
        = x * x * ∫ r, a r ^ 2 ∂μ - 2 * x * ∫ r, a r * b r ∂μ + ∫ r, b r ^ 2 ∂μ := by
      have : (fun r => (x * a r - b r) ^ 2)
          = fun r => (x * x) * a r ^ 2 - (2 * x) * (a r * b r) + b r ^ 2 := by
        funext r; ring
      have i1 : Integrable (fun r => x * x * a r ^ 2 - 2 * x * (a r * b r)) μ :=
        (ha.const_mul _).sub (hab.const_mul _)
      rw [this, integral_add i1 hb, integral_sub (ha.const_mul _) (hab.const_mul _),
        integral_const_mul, integral_const_mul]
    nlinarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

section Angular

variable {σ : Measure ℝ} [IsProbabilityMeasure σ]

lemma trunc_bound {R2 : ℝ} (hR2i : Integrable (fun r : ℝ => r ^ 2) σ)
    (hR2 : ∫ r, r ^ 2 ∂σ = R2) {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : ∀ θ r, f (θ + 2 * π, r) = f (θ, r))
    (hgc : Continuous g) (hd : ∀ θ r, d1 f (θ, r) = r * g (θ, r))
    (hgi : Integrable (fun p : ℝ × ℝ => g p ^ 2) (angleLaw.prod σ)) (K : ℝ) :
    ∫ θ, (∫ r, f (θ, r) ∂(σ.restrict (Icc (-K) K))
        - ∫ θ', ∫ r, f (θ', r) ∂(σ.restrict (Icc (-K) K)) ∂angleLaw) ^ 2 ∂angleLaw
      ≤ R2 * ∫ p, g p ^ 2 ∂(angleLaw.prod σ) := by
  set μ := σ.restrict (Icc (-K) K) with hμ
  have hK : ∀ᵐ r ∂μ, r ∈ Icc (-K) K := ae_restrict_mem measurableSet_Icc
  set Mk : ℝ → ℝ := fun θ => ∫ r, f (θ, r) ∂μ with hMk
  have hs : ContDiff ℝ ∞ Mk := contDiff_param_integral hK hf
  have hp : Function.Periodic Mk (2 * π) := fun θ => by simp only [hMk, hper]
  set c : ℝ := ∫ θ, Mk θ ∂angleLaw with hcdef
  have hc : c = (2 * π)⁻¹ * ∫ x in (0:ℝ)..(2 * π), Mk x := integral_angleLaw Mk
  have hw := wirtinger_two_pi hs hp c hc
  have hl : ∫ θ, (Mk θ - c) ^ 2 ∂angleLaw
      ≤ ∫ θ, deriv Mk θ ^ 2 ∂angleLaw := by
    rw [integral_angleLaw, integral_angleLaw]
    exact mul_le_mul_of_nonneg_left hw (by positivity)
  have hder : ∀ θ, deriv Mk θ = ∫ r, r * g (θ, r) ∂μ := fun θ => by
    rw [(hasDerivAt_param_integral hK hf θ).deriv]; simp only [hd]
  have hR2nn : 0 ≤ R2 := hR2 ▸ integral_nonneg fun r => sq_nonneg r
  have hgae := hgi.prod_right_ae
  have hpt : ∀ᵐ θ ∂angleLaw, deriv Mk θ ^ 2 ≤ R2 * ∫ r, g (θ, r) ^ 2 ∂σ := by
    filter_upwards [hgae] with θ hθ
    have hgθ : Continuous (fun r => g (θ, r)) := hgc.comp (Continuous.prodMk_right θ)
    have h1 := cs_integral (μ := μ) (a := fun r => r) (b := fun r => g (θ, r))
      continuous_id.aestronglyMeasurable hgθ.aestronglyMeasurable
      (hR2i.restrict) (hθ.restrict)
    rw [hder θ]
    have h2 : ∫ r, r ^ 2 ∂μ ≤ R2 := hR2 ▸ setIntegral_le_integral hR2i
      (Eventually.of_forall fun r => sq_nonneg r)
    have h3 : ∫ r, g (θ, r) ^ 2 ∂μ ≤ ∫ r, g (θ, r) ^ 2 ∂σ :=
      setIntegral_le_integral hθ (Eventually.of_forall fun r => sq_nonneg _)
    have h4 : 0 ≤ ∫ r, r ^ 2 ∂μ := integral_nonneg fun r => sq_nonneg r
    have h5 : 0 ≤ ∫ r, g (θ, r) ^ 2 ∂μ := integral_nonneg fun r => sq_nonneg _
    exact h1.trans (mul_le_mul h2 h3 h5 hR2nn)
  have hGi : Integrable (fun θ => ∫ r, g (θ, r) ^ 2 ∂σ) angleLaw := hgi.integral_prod_left
  have hint := integral_mono_of_nonneg (μ := angleLaw) (f := fun θ => deriv Mk θ ^ 2)
    (Eventually.of_forall fun θ => sq_nonneg _) (hGi.const_mul R2) hpt
  rw [integral_const_mul, ← integral_prod (fun p : ℝ × ℝ => g p ^ 2) hgi] at hint
  exact hl.trans hint

lemma integrable_angleLaw_of_continuous {h : ℝ → ℝ} (hh : Continuous h) :
    Integrable h angleLaw := by
  unfold angleLaw
  exact (hh.integrableOn_Ioc (a := 0) (b := 2 * π)).smul_measure ENNReal.ofReal_ne_top

lemma angular_bound {R2 : ℝ} (hR2i : Integrable (fun r : ℝ => r ^ 2) σ)
    (hR2 : ∫ r, r ^ 2 ∂σ = R2) {f g : ℝ × ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hper : ∀ θ r, f (θ + 2 * π, r) = f (θ, r))
    (hgc : Continuous g) (hd : ∀ θ r, d1 f (θ, r) = r * g (θ, r))
    (hgi : Integrable (fun p : ℝ × ℝ => g p ^ 2) (angleLaw.prod σ))
    (hfi : Integrable f (angleLaw.prod σ)) :
    ∫ θ, (∫ r, f (θ, r) ∂σ - ∫ θ', ∫ r, f (θ', r) ∂σ ∂angleLaw) ^ 2 ∂angleLaw
      ≤ R2 * ∫ p, g p ^ 2 ∂(angleLaw.prod σ) := by
  have hR2nn : 0 ≤ R2 := hR2 ▸ integral_nonneg fun r => sq_nonneg r
  set B := R2 * ∫ p, g p ^ 2 ∂(angleLaw.prod σ) with hB
  have hB0 : 0 ≤ B := mul_nonneg hR2nn (integral_nonneg fun p => sq_nonneg _)
  have hfc : Continuous f := hf.continuous
  set M : ℝ → ℝ := fun θ => ∫ r, f (θ, r) ∂σ with hM
  set Mk : ℕ → ℝ → ℝ := fun K θ => ∫ r, f (θ, r) ∂(σ.restrict (Icc (-(K : ℝ)) K)) with hMk
  set c : ℝ := ∫ θ, M θ ∂angleLaw with hc
  set ck : ℕ → ℝ := fun K => ∫ θ, Mk K θ ∂angleLaw with hck
  have hae := hfi.prod_right_ae
  -- pointwise convergence of the truncated means
  have tend1 : ∀ᵐ θ ∂angleLaw, Tendsto (fun K : ℕ => Mk K θ) atTop (𝓝 (M θ)) := by
    filter_upwards [hae] with θ hθ
    have hmeas : ∀ K : ℕ, AEStronglyMeasurable
        ((Icc (-(K : ℝ)) K).indicator fun r => f (θ, r)) σ := fun K =>
      (hθ.aestronglyMeasurable).indicator measurableSet_Icc
    have := tendsto_integral_of_dominated_convergence (μ := σ)
      (F := fun (K : ℕ) r => (Icc (-(K : ℝ)) K).indicator (fun r => f (θ, r)) r)
      (f := fun r => f (θ, r)) (bound := fun r => ‖f (θ, r)‖) hmeas hθ.norm
      (fun K => Eventually.of_forall fun r => norm_indicator_le_norm_self _ _)
      (Eventually.of_forall fun r => by
        obtain ⟨N, hN⟩ := exists_nat_ge |r|
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
        rw [indicator_of_mem]
        have := abs_le.mp (hN.trans hn')
        exact ⟨by linarith [this.1], by linarith [this.2]⟩)
    refine this.congr fun K => ?_
    simp only [hMk]
    rw [integral_indicator measurableSet_Icc]
  -- convergence of the truncated means of means
  have tend2 : Tendsto ck atTop (𝓝 c) := by
    have hJ : ∀ K : ℕ, Integrable
        ((Prod.snd ⁻¹' Icc (-(K : ℝ)) K).indicator f) (angleLaw.prod σ) := fun K =>
      hfi.indicator (measurable_snd measurableSet_Icc)
    have h1 := tendsto_integral_of_dominated_convergence (μ := angleLaw.prod σ)
      (F := fun (K : ℕ) p => (Prod.snd ⁻¹' Icc (-(K : ℝ)) K).indicator f p) (f := f)
      (bound := fun p => ‖f p‖) (fun K => (hJ K).aestronglyMeasurable) hfi.norm
      (fun K => Eventually.of_forall fun p => norm_indicator_le_norm_self _ _)
      (Eventually.of_forall fun p => by
        obtain ⟨N, hN⟩ := exists_nat_ge |p.2|
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [eventually_ge_atTop N] with n hn
        have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
        rw [indicator_of_mem]
        have := abs_le.mp (hN.trans hn')
        exact ⟨by linarith [this.1], by linarith [this.2]⟩)
    have e1 : ∀ K : ℕ, ∫ p, (Prod.snd ⁻¹' Icc (-(K : ℝ)) K).indicator f p ∂(angleLaw.prod σ) = ck K := by
      intro K
      rw [integral_prod _ (hJ K)]
      refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only [hMk]
      rw [← integral_indicator measurableSet_Icc]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      by_cases hr : r ∈ Icc (-(K : ℝ)) K <;> simp [indicator, hr]
    have e2 : ∫ p, f p ∂(angleLaw.prod σ) = c := integral_prod _ hfi
    simp only [e1, e2] at h1
    exact h1
  -- Fatou
  set h : ℕ → ℝ → ℝ≥0∞ := fun K θ => ENNReal.ofReal ((Mk K θ - ck K) ^ 2) with hh
  have hMkc : ∀ K : ℕ, Continuous (Mk K) := fun K =>
    (contDiff_param_integral (μ := σ.restrict (Icc (-(K : ℝ)) K)) (K := K)
      (ae_restrict_mem measurableSet_Icc) hf).continuous
  have hhm : ∀ K, Measurable (h K) := fun K =>
    (((hMkc K).sub continuous_const).pow 2).measurable.ennreal_ofReal
  have hbd : ∀ K : ℕ, ∫⁻ θ, h K θ ∂angleLaw ≤ ENNReal.ofReal B := by
    intro K
    have hi : Integrable (fun θ => (Mk K θ - ck K) ^ 2) angleLaw :=
      integrable_angleLaw_of_continuous (((hMkc K).sub continuous_const).pow 2)
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun θ => sq_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (trunc_bound hR2i hR2 hf hper hgc hd hgi K)
  have hlim : ∀ᵐ θ ∂angleLaw, Tendsto (fun K : ℕ => h K θ) atTop
      (𝓝 (ENNReal.ofReal ((M θ - c) ^ 2))) := by
    filter_upwards [tend1] with θ hθ
    exact (ENNReal.continuous_ofReal.tendsto _).comp (((hθ.sub tend2).pow 2))
  have hfat : ∫⁻ θ, ENNReal.ofReal ((M θ - c) ^ 2) ∂angleLaw ≤ ENNReal.ofReal B := by
    calc ∫⁻ θ, ENNReal.ofReal ((M θ - c) ^ 2) ∂angleLaw
        = ∫⁻ θ, liminf (fun K : ℕ => h K θ) atTop ∂angleLaw :=
          lintegral_congr_ae (by filter_upwards [hlim] with θ hθ using hθ.liminf_eq.symm)
      _ ≤ liminf (fun K : ℕ => ∫⁻ θ, h K θ ∂angleLaw) atTop := lintegral_liminf_le hhm
      _ ≤ ENNReal.ofReal B :=
          liminf_le_of_frequently_le' (Eventually.of_forall hbd).frequently
  have hMm : StronglyMeasurable M := hfc.stronglyMeasurable.integral_prod_right'
  show ∫ θ, (M θ - c) ^ 2 ∂angleLaw ≤ B
  have hm2 : AEStronglyMeasurable (fun θ => (M θ - c) ^ 2) angleLaw :=
    ((hMm.sub stronglyMeasurable_const).pow 2).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun θ => sq_nonneg _) hm2]
  exact ENNReal.toReal_le_of_le_ofReal hB0 hfat

end Angular

/-- Polar coordinates `(θ, r) ↦ (r cos θ, r sin θ)`. -/
noncomputable def polar (p : ℝ × ℝ) : ℝ × ℝ := (p.2 * Real.cos p.1, p.2 * Real.sin p.1)

/-- The rotational probability measure on the plane with radial law `σ` and uniform angle. -/
noncomputable def rotationalMeasure (σ : Measure ℝ) : Measure (ℝ × ℝ) :=
  (angleLaw.prod σ).map polar

/-- Squared Euclidean gradient norm of a planar function. -/
noncomputable def gradSq (F : ℝ × ℝ → ℝ) (x : ℝ × ℝ) : ℝ :=
  (fderiv ℝ F x (1, 0)) ^ 2 + (fderiv ℝ F x (0, 1)) ^ 2

lemma contDiff_polar : ContDiff ℝ ∞ polar :=
  (contDiff_snd.mul (Real.contDiff_cos.comp contDiff_fst)).prodMk
    (contDiff_snd.mul (Real.contDiff_sin.comp contDiff_fst))

lemma continuous_polar : Continuous polar := contDiff_polar.continuous

lemma fderiv_pair (L : ℝ × ℝ →L[ℝ] ℝ) (a b : ℝ) : L (a, b) = a * L (1, 0) + b * L (0, 1) := by
  have : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [this, map_add, map_smul, map_smul]
  simp

/-- Radial derivative of the polar pull-back. -/
noncomputable def radDer (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  Real.cos p.1 * fderiv ℝ F (polar p) (1, 0) + Real.sin p.1 * fderiv ℝ F (polar p) (0, 1)

/-- Tangential derivative (divided by `r`) of the polar pull-back. -/
noncomputable def tanDer (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -Real.sin p.1 * fderiv ℝ F (polar p) (1, 0) + Real.cos p.1 * fderiv ℝ F (polar p) (0, 1)

lemma radDer_sq_add_tanDer_sq (F : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
    radDer F p ^ 2 + tanDer F p ^ 2 = gradSq F (polar p) := by
  unfold radDer tanDer gradSq
  have := Real.sin_sq_add_cos_sq p.1
  nlinarith [this]

lemma continuous_radDer {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : Continuous (radDer F) := by
  have h1 : Continuous fun x => fderiv ℝ F x (1, 0) :=
    ((hF.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).continuous
  have h2 : Continuous fun x => fderiv ℝ F x (0, 1) :=
    ((hF.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).continuous
  unfold radDer
  have := continuous_polar
  fun_prop

lemma continuous_tanDer {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : Continuous (tanDer F) := by
  have h1 : Continuous fun x => fderiv ℝ F x (1, 0) :=
    ((hF.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).continuous
  have h2 : Continuous fun x => fderiv ℝ F x (0, 1) :=
    ((hF.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).continuous
  unfold tanDer
  have := continuous_polar
  fun_prop

lemma hasDerivAt_radial {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (θ r : ℝ) :
    HasDerivAt (fun s => F (polar (θ, s))) (radDer F (θ, r)) r := by
  have h1 : HasFDerivAt F (fderiv ℝ F (polar (θ, r))) (polar (θ, r)) :=
    ((hF.differentiable (by simp)) _).hasFDerivAt
  have h2 : HasDerivAt (fun s : ℝ => polar (θ, s)) (Real.cos θ, Real.sin θ) r :=
    by simpa [polar] using
      ((hasDerivAt_id r).mul_const (Real.cos θ)).prodMk ((hasDerivAt_id r).mul_const (Real.sin θ))
  have := h1.comp_hasDerivAt r h2
  rw [fderiv_pair] at this
  exact this

lemma hasDerivAt_tangential {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (θ r : ℝ) :
    HasDerivAt (fun t => F (polar (t, r))) (r * tanDer F (θ, r)) θ := by
  have h1 : HasFDerivAt F (fderiv ℝ F (polar (θ, r))) (polar (θ, r)) :=
    ((hF.differentiable (by simp)) _).hasFDerivAt
  have h2 : HasDerivAt (fun t : ℝ => polar (t, r)) (r * -Real.sin θ, r * Real.cos θ) θ :=
    ((Real.hasDerivAt_cos θ).const_mul r).prodMk ((Real.hasDerivAt_sin θ).const_mul r)
  have := h1.comp_hasDerivAt θ h2
  rw [fderiv_pair] at this
  unfold tanDer
  convert this using 1
  · ext t; simp [polar]
  · ring

lemma integrable_of_sq {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {u : α → ℝ} (hm : AEStronglyMeasurable u μ) (h2 : Integrable (fun x => u x ^ 2) μ) :
    Integrable u μ := by
  refine (h2.add (integrable_const (1 : ℝ))).mono' hm (Eventually.of_forall fun x => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [sq_abs (u x), abs_nonneg (u x), sq_nonneg (|u x| - 1)]

lemma integral_sq_sub {μ : Measure ℝ} [IsProbabilityMeasure μ] {u : ℝ → ℝ}
    (hu1 : Integrable u μ) (hu2 : Integrable (fun r => u r ^ 2) μ) (a : ℝ) :
    ∫ r, (u r - a) ^ 2 ∂μ = ∫ r, u r ^ 2 ∂μ - 2 * a * ∫ r, u r ∂μ + a ^ 2 := by
  have : (fun r => (u r - a) ^ 2) = fun r => u r ^ 2 - (2 * a) * u r + a ^ 2 := by
    funext r; ring
  have i1 : Integrable (fun r => u r ^ 2 - 2 * a * u r) μ := hu2.sub (hu1.const_mul _)
  rw [this, integral_add i1 (integrable_const _),
    integral_sub hu2 (hu1.const_mul _), integral_const_mul]
  simp

lemma var_decomp {μ : Measure ℝ} [IsProbabilityMeasure μ] {u : ℝ → ℝ}
    (hu1 : Integrable u μ) (hu2 : Integrable (fun r => u r ^ 2) μ) (c : ℝ) :
    ∫ r, (u r - c) ^ 2 ∂μ
      = ∫ r, (u r - ∫ s, u s ∂μ) ^ 2 ∂μ + (∫ s, u s ∂μ - c) ^ 2 := by
  rw [integral_sq_sub hu1 hu2, integral_sq_sub hu1 hu2]
  ring

lemma continuous_fderiv_apply {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) (v : ℝ × ℝ) :
    Continuous fun x => fderiv ℝ F x v :=
  ((hF.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const).continuous

lemma continuous_gradSq {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F) : Continuous (gradSq F) := by
  have h1 := continuous_fderiv_apply hF (1, 0)
  have h2 := continuous_fderiv_apply hF (0, 1)
  unfold gradSq
  fun_prop

/-- FIN042 (optional direct planar Poincaré inequality).  A rotational probability measure `ν`
is the image of `(uniform angle) ⊗ σ` under polar coordinates.  If `σ` has radial Poincaré
inverse constant `P` (tested on smooth `u`) and `R2 = ∫ r² dσ < ∞`, then
`Var_ν(F) ≤ max P R2 ∫ |∇F|² dν` for smooth planar `F`. -/
theorem optional_direct_planar_poincare_main {σ : Measure ℝ} [IsProbabilityMeasure σ] {P R2 : ℝ}
    (hR2i : Integrable (fun r : ℝ => r ^ 2) σ) (hR2 : ∫ r, r ^ 2 ∂σ = R2)
    (hP : ∀ u : ℝ → ℝ, ContDiff ℝ ∞ u → Integrable (fun r => u r ^ 2) σ →
      Integrable (fun r => deriv u r ^ 2) σ →
      ∫ r, (u r - ∫ s, u s ∂σ) ^ 2 ∂σ ≤ P * ∫ r, deriv u r ^ 2 ∂σ)
    {F : ℝ × ℝ → ℝ} (hF : ContDiff ℝ ∞ F)
    (hFi : Integrable (fun x => F x ^ 2) (rotationalMeasure σ))
    (hGi : Integrable (gradSq F) (rotationalMeasure σ)) :
    ∫ x, (F x - ∫ y, F y ∂(rotationalMeasure σ)) ^ 2 ∂(rotationalMeasure σ)
      ≤ max P R2 * ∫ x, gradSq F x ∂(rotationalMeasure σ) := by
  set ρ := angleLaw.prod σ with hρ
  have hFc : Continuous F := hF.continuous
  have hgc := continuous_gradSq hF
  have hmap : ∀ G : ℝ × ℝ → ℝ, Continuous G →
      ∫ x, G x ∂(rotationalMeasure σ) = ∫ p, G (polar p) ∂ρ := fun G hG =>
    integral_map continuous_polar.aemeasurable hG.aestronglyMeasurable
  have hint : ∀ G : ℝ × ℝ → ℝ, Continuous G →
      Integrable G (rotationalMeasure σ) → Integrable (fun p => G (polar p)) ρ := fun G hG h =>
    (integrable_map_measure hG.aestronglyMeasurable continuous_polar.aemeasurable).1 h
  set f : ℝ × ℝ → ℝ := fun p => F (polar p) with hf
  have hfs : ContDiff ℝ ∞ f := hF.comp contDiff_polar
  have hfc : Continuous f := hfs.continuous
  have hf2 : Integrable (fun p => f p ^ 2) ρ := hint (fun x => F x ^ 2) (hFc.pow 2) hFi
  have hGρ : Integrable (fun p => gradSq F (polar p)) ρ := hint _ hgc hGi
  have hfi : Integrable f ρ := integrable_of_sq hfc.aestronglyMeasurable hf2
  set c : ℝ := ∫ p, f p ∂ρ with hc
  have e1 : ∫ y, F y ∂(rotationalMeasure σ) = c := hmap F hFc
  rw [e1, hmap (fun x => (F x - c) ^ 2) (by fun_prop), hmap (gradSq F) hgc]
  have hAc := continuous_radDer hF
  have hTc := continuous_tanDer hF
  have hsum : ∀ p, gradSq F (polar p) = radDer F p ^ 2 + tanDer F p ^ 2 := fun p =>
    (radDer_sq_add_tanDer_sq F p).symm
  have hA2 : Integrable (fun p => radDer F p ^ 2) ρ := by
    refine hGρ.mono' (hAc.pow 2).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hsum p]
    nlinarith [sq_nonneg (tanDer F p)]
  have hT2 : Integrable (fun p => tanDer F p ^ 2) ρ := by
    refine hGρ.mono' (hTc.pow 2).aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hsum p]
    nlinarith [sq_nonneg (radDer F p)]
  set EA := ∫ p, radDer F p ^ 2 ∂ρ with hEA
  set ET := ∫ p, tanDer F p ^ 2 ∂ρ with hET
  have hEA0 : 0 ≤ EA := integral_nonneg fun p => sq_nonneg _
  have hET0 : 0 ≤ ET := integral_nonneg fun p => sq_nonneg _
  have hsumint : ∫ p, gradSq F (polar p) ∂ρ = EA + ET := by
    rw [hEA, hET, ← integral_add hA2 hT2]
    exact integral_congr_ae (Eventually.of_forall hsum)
  rw [hsumint]
  -- angular part
  have hd : ∀ θ r, d1 f (θ, r) = r * tanDer F (θ, r) := fun θ r =>
    (hasDerivAt_d1 hfs θ r).unique (hasDerivAt_tangential hF θ r)
  have hper : ∀ θ r, f (θ + 2 * π, r) = f (θ, r) := fun θ r => by
    simp [hf, polar, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have hang := angular_bound hR2i hR2 hfs hper hTc hd hT2 hfi
  have e2 : ∫ θ', ∫ r, f (θ', r) ∂σ ∂angleLaw = c := (integral_prod _ hfi).symm
  rw [e2] at hang
  -- decomposition
  set M : ℝ → ℝ := fun θ => ∫ r, f (θ, r) ∂σ with hM
  have hMm : StronglyMeasurable M := hfc.stronglyMeasurable.integral_prod_right'
  set φ : ℝ → ℝ := fun θ => ∫ r, (f (θ, r) - M θ) ^ 2 ∂σ with hφ
  set ψ : ℝ → ℝ := fun θ => (M θ - c) ^ 2 with hψ
  have hφm : StronglyMeasurable φ :=
    ((hfc.stronglyMeasurable.sub (hMm.comp_measurable measurable_fst)).pow 2).integral_prod_right'
  have hψm : StronglyMeasurable ψ := (hMm.sub stronglyMeasurable_const).pow 2
  have hint2 : Integrable (fun p => (f p - c) ^ 2) ρ := by
    have : (fun p => (f p - c) ^ 2) = fun p => f p ^ 2 - 2 * c * f p + c ^ 2 := by
      funext p; ring
    rw [this]
    exact (hf2.sub (hfi.const_mul _)).add (integrable_const _)
  have hVfub : ∫ p, (f p - c) ^ 2 ∂ρ = ∫ θ, ∫ r, (f (θ, r) - c) ^ 2 ∂σ ∂angleLaw :=
    integral_prod _ hint2
  have hinner : Integrable (fun θ => ∫ r, (f (θ, r) - c) ^ 2 ∂σ) angleLaw :=
    hint2.integral_prod_left
  have hae1 : ∀ᵐ θ ∂angleLaw, Integrable (fun r => f (θ, r) ^ 2) σ := hf2.prod_right_ae
  have hae2 : ∀ᵐ θ ∂angleLaw, Integrable (fun r => radDer F (θ, r) ^ 2) σ := hA2.prod_right_ae
  have hdec : ∀ᵐ θ ∂angleLaw, ∫ r, (f (θ, r) - c) ^ 2 ∂σ = φ θ + ψ θ := by
    filter_upwards [hae1] with θ hθ
    have hcθ : Continuous (fun r => f (θ, r)) := hfc.comp (Continuous.prodMk_right θ)
    exact var_decomp (integrable_of_sq hcθ.aestronglyMeasurable hθ) hθ c
  have hφ0 : ∀ θ, 0 ≤ φ θ := fun θ => integral_nonneg fun r => sq_nonneg _
  have hψ0 : ∀ θ, 0 ≤ ψ θ := fun θ => sq_nonneg _
  have hφi : Integrable φ angleLaw := by
    refine hinner.mono' hφm.aestronglyMeasurable ?_
    filter_upwards [hdec] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (hφ0 θ), hθ]
    linarith [hψ0 θ]
  have hψi : Integrable ψ angleLaw := by
    refine hinner.mono' hψm.aestronglyMeasurable ?_
    filter_upwards [hdec] with θ hθ
    rw [Real.norm_eq_abs, abs_of_nonneg (hψ0 θ), hθ]
    linarith [hφ0 θ]
  have hV : ∫ p, (f p - c) ^ 2 ∂ρ = ∫ θ, φ θ ∂angleLaw + ∫ θ, ψ θ ∂angleLaw := by
    rw [hVfub, ← integral_add hφi hψi]
    exact integral_congr_ae hdec
  -- radial part
  have hrad : ∀ᵐ θ ∂angleLaw, φ θ ≤ P * ∫ r, radDer F (θ, r) ^ 2 ∂σ := by
    filter_upwards [hae1, hae2] with θ h1 h2
    have hu : ContDiff ℝ ∞ (fun r => f (θ, r)) :=
      hfs.comp (contDiff_const.prodMk contDiff_id)
    have hder : deriv (fun r => f (θ, r)) = fun r => radDer F (θ, r) :=
      funext fun r => (hasDerivAt_radial hF θ r).deriv
    have := hP (fun r => f (θ, r)) hu h1 (by rw [hder]; exact h2)
    rw [hder] at this
    exact this
  have hGi' : Integrable (fun θ => ∫ r, radDer F (θ, r) ^ 2 ∂σ) angleLaw :=
    hA2.integral_prod_left
  have hradint : ∫ θ, φ θ ∂angleLaw ≤ P * EA := by
    have := integral_mono_of_nonneg (μ := angleLaw) (Eventually.of_forall hφ0)
      (hGi'.const_mul P) hrad
    rw [integral_const_mul, ← integral_prod (fun p : ℝ × ℝ => radDer F p ^ 2) hA2] at this
    exact this
  have hang' : ∫ θ, ψ θ ∂angleLaw ≤ R2 * ET := hang
  rw [hV]
  have hmx1 : P * EA ≤ max P R2 * EA := mul_le_mul_of_nonneg_right (le_max_left _ _) hEA0
  have hmx2 : R2 * ET ≤ max P R2 * ET := mul_le_mul_of_nonneg_right (le_max_right _ _) hET0
  nlinarith

end DGPS.FiniteN.Tools.PlanarPoincare

namespace DGPS.FiniteN

alias optional_direct_planar_poincare :=
  DGPS.FiniteN.Tools.PlanarPoincare.optional_direct_planar_poincare_main

end DGPS.FiniteN
