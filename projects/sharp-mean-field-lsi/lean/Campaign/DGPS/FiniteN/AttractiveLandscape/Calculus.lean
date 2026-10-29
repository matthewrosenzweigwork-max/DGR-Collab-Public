import DGPS.Foundations.Torus

open MeasureTheory
open scoped RealInnerProductSpace ContDiff

namespace DGPS.FiniteN.AttractiveLandscape

universe u

variable {d r : ℕ}

/-- The feature space `ℝ^r`. -/
abbrev Feature (r : ℕ) := EuclideanSpace ℝ (Fin r)

/-- The unnormalised tilted integral `z ↦ ∫ e^{⟨z,Φ⟩ - U} • T dm`. -/
noncomputable def tiltedIntegral {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : Torus d → ℝ) (Φ : Torus d → Feature r) (T : Torus d → F) (z : Feature r) : F :=
  ∫ x, Real.exp (⟪z, Φ x⟫ - U x) • T x ∂(haar d)

theorem exists_bound_of_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {F : Type*} [NormedAddCommGroup F] {f : X → F} (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  exact ⟨|C|, abs_nonneg _, fun x => (hC x (Set.mem_univ x)).trans (le_abs_self C)⟩

section

variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {U : Torus d → ℝ} {Φ : Torus d → Feature r} {T : Torus d → F}

theorem continuous_integrand (hU : Continuous U) (hΦ : Continuous Φ) (hT : Continuous T)
    (z : Feature r) : Continuous fun x => Real.exp (⟪z, Φ x⟫ - U x) • T x :=
  ((Real.continuous_exp.comp ((continuous_const.inner hΦ).sub hU))).smul hT

theorem integrable_integrand (hU : Continuous U) (hΦ : Continuous Φ) (hT : Continuous T)
    (z : Feature r) : Integrable (fun x => Real.exp (⟪z, Φ x⟫ - U x) • T x) (haar d) :=
  (continuous_integrand hU hΦ hT z).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- The derivative field of the integrand. -/
noncomputable def derivT (Φ : Torus d → Feature r) (T : Torus d → F) (x : Torus d) :
    Feature r →L[ℝ] F :=
  (innerSL ℝ (Φ x)).smulRight (T x)

theorem continuous_derivT (hΦ : Continuous Φ) (hT : Continuous T) :
    Continuous (derivT Φ T) := by
  have h1 : Continuous fun x => innerSL ℝ (Φ x) := (innerSL ℝ).continuous.comp hΦ
  exact (ContinuousLinearMap.smulRightL ℝ (Feature r) F).continuous₂.comp₂ h1 hT

theorem norm_derivT_le (x : Torus d) : ‖derivT Φ T x‖ ≤ ‖Φ x‖ * ‖T x‖ := by
  unfold derivT
  rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm]

theorem hasFDerivAt_exponent (Φ : Torus d → Feature r) (U : Torus d → ℝ) (x : Torus d)
    (z : Feature r) :
    HasFDerivAt (fun z : Feature r => Real.exp (⟪z, Φ x⟫ - U x))
      (Real.exp (⟪z, Φ x⟫ - U x) • innerSL ℝ (Φ x)) z := by
  have h1 : HasFDerivAt (fun z : Feature r => ⟪z, Φ x⟫) (innerSL ℝ (Φ x)) z := by
    have := (innerSL ℝ (Φ x)).hasFDerivAt (x := z)
    refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    simp [real_inner_comm]
  exact (h1.sub_const (U x)).exp

theorem hasFDerivAt_tiltedIntegral (hU : Continuous U) (hΦ : Continuous Φ) (hT : Continuous T)
    [CompleteSpace F] (z : Feature r) :
    HasFDerivAt (tiltedIntegral U Φ T) (tiltedIntegral U Φ (derivT Φ T) z) z := by
  obtain ⟨L, hL0, hL⟩ := exists_bound_of_continuous hΦ
  obtain ⟨CU, hCU0, hCU⟩ := exists_bound_of_continuous hU
  obtain ⟨CT, hCT0, hCT⟩ := exists_bound_of_continuous hT
  set R : ℝ := ‖z‖ + 1 with hR
  let bound : Torus d → ℝ := fun _ => Real.exp (R * L + CU) * (L * CT)
  have hbound : ∀ x, ∀ y ∈ Metric.ball z 1,
      ‖Real.exp (⟪y, Φ x⟫ - U x) • derivT Φ T x‖ ≤ bound x := by
    intro x y hy
    have hy' : ‖y‖ ≤ R := by
      have := (Metric.mem_ball.1 hy)
      rw [dist_eq_norm] at this
      calc ‖y‖ = ‖z + (y - z)‖ := by abel_nf
        _ ≤ ‖z‖ + ‖y - z‖ := norm_add_le _ _
        _ ≤ R := by rw [hR]; linarith
    have h1 : ⟪y, Φ x⟫ - U x ≤ R * L + CU := by
      have : ⟪y, Φ x⟫ ≤ ‖y‖ * ‖Φ x‖ := real_inner_le_norm _ _
      have h2 : ‖y‖ * ‖Φ x‖ ≤ R * L := mul_le_mul hy' (hL x) (norm_nonneg _) (by positivity)
      have h3 : -U x ≤ CU := by
        have := hCU x
        rw [Real.norm_eq_abs] at this
        linarith [neg_abs_le (U x), abs_nonneg (U x)]
      linarith
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (⟪y, Φ x⟫ - U x) * ‖derivT Φ T x‖
        ≤ Real.exp (R * L + CU) * (L * CT) := by
          refine mul_le_mul (Real.exp_le_exp.2 h1) ?_ (norm_nonneg _) (Real.exp_pos _).le
          exact (norm_derivT_le x).trans (mul_le_mul (hL x) (hCT x) (norm_nonneg _) hL0)
      _ = bound x := rfl
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (F := fun z x => Real.exp (⟪z, Φ x⟫ - U x) • T x)
    (F' := fun z x => Real.exp (⟪z, Φ x⟫ - U x) • derivT Φ T x)
    (s := Metric.ball z 1) (bound := bound) (Metric.ball_mem_nhds z one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun y =>
      (continuous_integrand hU hΦ hT y).aestronglyMeasurable
  · exact integrable_integrand hU hΦ hT z
  · exact (continuous_integrand hU hΦ (continuous_derivT hΦ hT) z).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun x y hy => hbound x y hy
  · exact integrable_const _
  · refine Filter.Eventually.of_forall fun x y _ => ?_
    have := (hasFDerivAt_exponent Φ U x y).smul_const (T x)
    convert this using 1
    ext v
    simp [derivT, smul_smul]

theorem fderiv_tiltedIntegral (hU : Continuous U) (hΦ : Continuous Φ) (hT : Continuous T)
    [CompleteSpace F] :
    fderiv ℝ (tiltedIntegral U Φ T) = tiltedIntegral U Φ (derivT Φ T) :=
  funext fun z => (hasFDerivAt_tiltedIntegral hU hΦ hT z).fderiv

theorem continuous_tiltedIntegral_derivT (hU : Continuous U) (hΦ : Continuous Φ)
    (hT : Continuous T) [CompleteSpace F] : Continuous (tiltedIntegral U Φ T) :=
  continuous_iff_continuousAt.2 fun z => (hasFDerivAt_tiltedIntegral hU hΦ hT z).continuousAt

end

theorem contDiff_tiltedIntegral {U : Torus d → ℝ} {Φ : Torus d → Feature r}
    (hU : Continuous U) (hΦ : Continuous Φ) :
    ∀ (n : ℕ) {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (T : Torus d → F), Continuous T → ContDiff ℝ n (tiltedIntegral U Φ T)
  | 0, F, _, _, _, T, hT => by
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_tiltedIntegral_derivT hU hΦ hT
  | n + 1, F, _, _, _, T, hT => by
      rw [Nat.cast_succ, contDiff_succ_iff_fderiv]
      refine ⟨fun z => (hasFDerivAt_tiltedIntegral hU hΦ hT z).differentiableAt, ?_, ?_⟩
      · intro h
        exact absurd h (by exact_mod_cast WithTop.coe_ne_top)
      · rw [fderiv_tiltedIntegral hU hΦ hT]
        exact contDiff_tiltedIntegral hU hΦ n _ (continuous_derivT hΦ hT)

/-! ### The partition function and the auxiliary landscape -/

section Model

variable (U : Torus d → ℝ) (Φ : Torus d → Feature r)

/-- The partition function `ζ(z) = ∫ e^{⟨z,Φ⟩ - U} dm`. -/
noncomputable def zeta (z : Feature r) : ℝ :=
  ∫ x, Real.exp (⟪z, Φ x⟫ - U x) ∂(haar d)

/-- The auxiliary potential `ψ(z) = |z|²/2 - log ζ(z)`. -/
noncomputable def psi (z : Feature r) : ℝ :=
  ‖z‖ ^ 2 / 2 - Real.log (zeta U Φ z)

/-- The tilted probability measure `q_z ∝ e^{⟨z,Φ⟩ - U} dm`. -/
noncomputable def gibbs (z : Feature r) : Measure (Torus d) :=
  (haar d).tilted fun x => ⟪z, Φ x⟫ - U x

/-- The `q_z`-mean of the feature map. -/
noncomputable def featureMean (z : Feature r) : Feature r :=
  ∫ x, Φ x ∂(gibbs U Φ z)

/-- The covariance form `Cov_{q_z}(⟨v,Φ⟩, ⟨w,Φ⟩)`. -/
noncomputable def featureCov (z : Feature r) (v w : Feature r) : ℝ :=
  ∫ x, ⟪v, Φ x - featureMean U Φ z⟫ * ⟪w, Φ x - featureMean U Φ z⟫ ∂(gibbs U Φ z)

variable {U Φ}

theorem zeta_eq_tiltedIntegral :
    zeta U Φ = tiltedIntegral U Φ (fun _ : Torus d => (1 : ℝ)) := by
  funext z; simp [zeta, tiltedIntegral]

theorem zeta_pos (hU : Continuous U) (hΦ : Continuous Φ) (z : Feature r) : 0 < zeta U Φ z := by
  have := integrable_integrand hU hΦ (T := fun _ : Torus d => (1 : ℝ)) continuous_const z
  simp only [smul_eq_mul, mul_one] at this
  exact integral_exp_pos this

theorem contDiff_zeta (hU : Continuous U) (hΦ : Continuous Φ) (n : ℕ) :
    ContDiff ℝ n (zeta U Φ) := by
  rw [zeta_eq_tiltedIntegral]
  exact contDiff_tiltedIntegral hU hΦ n _ continuous_const

theorem contDiff_moment (hU : Continuous U) (hΦ : Continuous Φ) (n : ℕ) :
    ContDiff ℝ n (tiltedIntegral U Φ Φ) :=
  contDiff_tiltedIntegral hU hΦ n _ hΦ

theorem hasFDerivAt_zeta (hU : Continuous U) (hΦ : Continuous Φ) (z : Feature r) :
    HasFDerivAt (zeta U Φ) (innerSL ℝ (tiltedIntegral U Φ Φ z)) z := by
  have h := hasFDerivAt_tiltedIntegral hU hΦ (T := fun _ : Torus d => (1 : ℝ)) continuous_const z
  rw [← zeta_eq_tiltedIntegral] at h
  convert h using 1
  ext v
  have hi : Integrable (fun x => Real.exp (⟪z, Φ x⟫ - U x) • (innerSL ℝ (Φ x)).smulRight (1 : ℝ))
      (haar d) := integrable_integrand hU hΦ (continuous_derivT hΦ continuous_const) z
  simp only [tiltedIntegral, derivT]
  rw [ContinuousLinearMap.integral_apply hi]
  have hΦi : Integrable (fun x => Real.exp (⟪z, Φ x⟫ - U x) • Φ x) (haar d) :=
    integrable_integrand hU hΦ hΦ z
  rw [innerSL_apply_apply, real_inner_comm, ← integral_inner hΦi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [real_inner_comm, inner_smul_right]

/-- `innerSL` as a real bilinear continuous map. -/
noncomputable def innerR : Feature r →L[ℝ] Feature r →L[ℝ] ℝ := innerSL ℝ

@[simp] theorem innerR_apply (v w : Feature r) : innerR v w = ⟪v, w⟫ := rfl

theorem isProbabilityMeasure_gibbs (hU : Continuous U) (hΦ : Continuous Φ) (z : Feature r) :
    IsProbabilityMeasure (gibbs U Φ z) := by
  have := integrable_integrand hU hΦ (T := fun _ : Torus d => (1 : ℝ)) continuous_const z
  simp only [smul_eq_mul, mul_one] at this
  exact isProbabilityMeasure_tilted this

theorem integral_gibbs {F : Type u}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (g : Torus d → F) (z : Feature r) :
    ∫ x, g x ∂(gibbs U Φ z) =
      (zeta U Φ z)⁻¹ • ∫ x, Real.exp (⟪z, Φ x⟫ - U x) • g x ∂(haar d) := by
  unfold gibbs
  rw [integral_tilted, ← integral_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [zeta, smul_smul, div_eq_inv_mul]

theorem featureMean_eq (z : Feature r) :
    featureMean U Φ z = (zeta U Φ z)⁻¹ • tiltedIntegral U Φ Φ z :=
  integral_gibbs Φ z

theorem hasFDerivAt_psi (hU : Continuous U) (hΦ : Continuous Φ) (z : Feature r) :
    HasFDerivAt (psi U Φ) (innerR (z - featureMean U Φ z)) z := by
  have h1 : HasFDerivAt (fun y : Feature r => ‖y‖ ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have h2 := (hasFDerivAt_zeta hU hΦ z).log (zeta_pos hU hΦ z).ne'
  have h3 := (h1.const_smul (1 / 2 : ℝ)).sub h2
  have hf : psi U Φ = ((1 / 2 : ℝ) • fun y : Feature r => ‖y‖ ^ 2) - fun x => Real.log (zeta U Φ x) := by
    funext y; simp [psi]; ring
  rw [hf]
  refine h3.congr_fderiv ?_
  ext v
  rw [featureMean_eq]
  have hi : ∀ a b : Feature r, (innerSL ℝ a) b = ⟪a, b⟫ := fun a b => rfl
  simp only [hi, innerR, sub_apply, smul_apply, inner_sub_right, inner_smul_right, smul_eq_mul,
    nsmul_eq_mul, real_inner_comm v]
  push_cast
  ring

theorem integrable_gibbs (hU : Continuous U) (hΦ : Continuous Φ) {g : Torus d → ℝ}
    (hg : Continuous g) (z : Feature r) : Integrable g (gibbs U Φ z) := by
  have := isProbabilityMeasure_gibbs hU hΦ z
  exact hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

theorem integrable_gibbs_feature (hU : Continuous U) (hΦ : Continuous Φ) (z : Feature r) :
    Integrable Φ (gibbs U Φ z) := by
  have := isProbabilityMeasure_gibbs hU hΦ z
  exact hΦ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace Φ)

theorem featureCov_eq_gibbs (hU : Continuous U) (hΦ : Continuous Φ) (z v w : Feature r) :
    featureCov U Φ z v w = ∫ x, ⟪v, Φ x⟫ * ⟪w, Φ x⟫ ∂(gibbs U Φ z) -
        ⟪v, featureMean U Φ z⟫ * ⟪w, featureMean U Φ z⟫ := by
  have := isProbabilityMeasure_gibbs hU hΦ z
  set m := featureMean U Φ z with hm
  have ha : Continuous fun x => ⟪v, Φ x⟫ := continuous_const.inner hΦ
  have hb : Continuous fun x => ⟪w, Φ x⟫ := continuous_const.inner hΦ
  have hav : ∫ x, ⟪v, Φ x⟫ ∂(gibbs U Φ z) = ⟪v, m⟫ := by
    rw [hm, featureMean, integral_inner (integrable_gibbs_feature hU hΦ z)]
  have hbw : ∫ x, ⟪w, Φ x⟫ ∂(gibbs U Φ z) = ⟪w, m⟫ := by
    rw [hm, featureMean, integral_inner (integrable_gibbs_feature hU hΦ z)]
  have key : ∀ x, ⟪v, Φ x - m⟫ * ⟪w, Φ x - m⟫ =
      ⟪v, Φ x⟫ * ⟪w, Φ x⟫ - ⟪v, m⟫ * ⟪w, Φ x⟫ - ⟪w, m⟫ * ⟪v, Φ x⟫ + ⟪v, m⟫ * ⟪w, m⟫ := by
    intro x; rw [inner_sub_right, inner_sub_right]; ring
  have i1 : Integrable (fun x => ⟪v, Φ x⟫ * ⟪w, Φ x⟫) (gibbs U Φ z) :=
    integrable_gibbs hU hΦ (ha.mul hb) z
  have i2 : Integrable (fun x => ⟪w, Φ x⟫) (gibbs U Φ z) := integrable_gibbs hU hΦ hb z
  have i3 : Integrable (fun x => ⟪v, Φ x⟫) (gibbs U Φ z) := integrable_gibbs hU hΦ ha z
  unfold featureCov
  simp_rw [← hm, key]
  have i4 : Integrable (fun x => ⟪v, Φ x⟫ * ⟪w, Φ x⟫ - ⟪v, m⟫ * ⟪w, Φ x⟫) (gibbs U Φ z) :=
    i1.sub (i2.const_mul _)
  have i5 : Integrable (fun x => ⟪v, Φ x⟫ * ⟪w, Φ x⟫ - ⟪v, m⟫ * ⟪w, Φ x⟫ - ⟪w, m⟫ * ⟪v, Φ x⟫)
      (gibbs U Φ z) := i4.sub (i3.const_mul _)
  rw [integral_add i5 (integrable_const _), integral_sub i4 (i3.const_mul _),
    integral_sub i1 (i2.const_mul _), integral_const_mul, integral_const_mul, hav, hbw]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

theorem featureCov_eq (hU : Continuous U) (hΦ : Continuous Φ) (z v w : Feature r) :
    featureCov U Φ z v w =
      (zeta U Φ z)⁻¹ * ∫ x, Real.exp (⟪z, Φ x⟫ - U x) * (⟪v, Φ x⟫ * ⟪w, Φ x⟫) ∂(haar d) -
        ⟪v, featureMean U Φ z⟫ * ⟪w, featureMean U Φ z⟫ := by
  rw [featureCov_eq_gibbs hU hΦ, integral_gibbs (g := fun x => ⟪v, Φ x⟫ * ⟪w, Φ x⟫)]
  rfl

theorem inner_momentDeriv (hU : Continuous U) (hΦ : Continuous Φ) (z v w : Feature r) :
    ⟪tiltedIntegral U Φ (derivT Φ Φ) z v, w⟫ =
      ∫ x, Real.exp (⟪z, Φ x⟫ - U x) * (⟪v, Φ x⟫ * ⟪w, Φ x⟫) ∂(haar d) := by
  have hi : Integrable (fun x => Real.exp (⟪z, Φ x⟫ - U x) • derivT Φ Φ x) (haar d) :=
    integrable_integrand hU hΦ (continuous_derivT hΦ hΦ) z
  have hΦi : Integrable (fun x => Real.exp (⟪z, Φ x⟫ - U x) • (⟪Φ x, v⟫ • Φ x)) (haar d) := by
    have := integrable_integrand hU hΦ (T := fun x => ⟪Φ x, v⟫ • Φ x)
      (by fun_prop : Continuous fun x => ⟪Φ x, v⟫ • Φ x) z
    exact this
  simp only [tiltedIntegral]
  rw [ContinuousLinearMap.integral_apply hi, real_inner_comm]
  have : (fun x => (Real.exp (⟪z, Φ x⟫ - U x) • derivT Φ Φ x) v) =
      fun x => Real.exp (⟪z, Φ x⟫ - U x) • (⟪Φ x, v⟫ • Φ x) := by
    funext x; simp [derivT]
  rw [this, ← integral_inner hΦi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [real_inner_comm, inner_smul_right]

theorem exists_hasFDerivAt_featureMean (hU : Continuous U) (hΦ : Continuous Φ) (z : Feature r) :
    ∃ D : Feature r →L[ℝ] Feature r, HasFDerivAt (featureMean U Φ) D z ∧
      ∀ v w, ⟪D v, w⟫ = featureCov U Φ z v w := by
  have hζ := hasFDerivAt_zeta hU hΦ z
  have hinv : HasFDerivAt (fun y => (zeta U Φ y)⁻¹)
      ((-((zeta U Φ z) ^ 2)⁻¹) • innerSL ℝ (tiltedIntegral U Φ Φ z)) z :=
    (hasDerivAt_inv (zeta_pos hU hΦ z).ne').comp_hasFDerivAt z hζ
  have hG := hasFDerivAt_tiltedIntegral hU hΦ hΦ z
  have h := hinv.smul hG
  have hfun : featureMean U Φ = fun y => (zeta U Φ y)⁻¹ • tiltedIntegral U Φ Φ y :=
    funext fun y => featureMean_eq y
  rw [hfun]
  refine ⟨_, h, fun v w => ?_⟩
  rw [featureCov_eq hU hΦ, ← inner_momentDeriv hU hΦ z v w, featureMean_eq]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, inner_add_left, inner_smul_left, inner_smul_right,
    innerSL_apply_apply, RCLike.conj_to_real, smul_eq_mul]
  have hζ0 := (zeta_pos hU hΦ z).ne'
  simp only [real_inner_comm v, real_inner_comm w]
  field_simp
  ring


theorem fderiv_psi (hU : Continuous U) (hΦ : Continuous Φ) :
    fderiv ℝ (psi U Φ) = fun z => innerR (z - featureMean U Φ z) :=
  funext fun z => (hasFDerivAt_psi hU hΦ z).fderiv

theorem gradient_psi (hU : Continuous U) (hΦ : Continuous Φ) (z : Feature r) :
    gradient (psi U Φ) z = z - featureMean U Φ z := by
  rw [gradient, fderiv_psi hU hΦ]
  apply (InnerProductSpace.toDual ℝ (Feature r)).injective
  ext v
  simp [InnerProductSpace.toDual_apply_apply]

theorem contDiff_psi (hU : Continuous U) (hΦ : Continuous Φ) (n : ℕ) :
    ContDiff ℝ n (psi U Φ) := by
  have h1 : ContDiff ℝ n fun y : Feature r => ‖y‖ ^ 2 / 2 := (contDiff_norm_sq ℝ).div_const 2
  have h2 : ContDiff ℝ n fun y => Real.log (zeta U Φ y) :=
    (contDiff_zeta hU hΦ n).log fun y => (zeta_pos hU hΦ y).ne'
  exact h1.sub h2

theorem contDiff_psi_infty (hU : Continuous U) (hΦ : Continuous Φ) :
    ContDiff ℝ ∞ (psi U Φ) :=
  contDiff_infty.2 fun n => contDiff_psi hU hΦ n

theorem hessian_psi (hU : Continuous U) (hΦ : Continuous Φ) (z v w : Feature r) :
    fderiv ℝ (fderiv ℝ (psi U Φ)) z v w = ⟪v, w⟫ - featureCov U Φ z v w := by
  obtain ⟨D, hD, hDv⟩ := exists_hasFDerivAt_featureMean hU hΦ z
  have hg := (hasFDerivAt_id z).sub hD
  have h : HasFDerivAt (fderiv ℝ (psi U Φ))
      (innerR.comp (ContinuousLinearMap.id ℝ (Feature r) - D)) z := by
    rw [fderiv_psi hU hΦ]; exact innerR.hasFDerivAt.comp z hg
  rw [h.fderiv]
  simp only [ContinuousLinearMap.comp_apply, sub_apply, ContinuousLinearMap.id_apply, innerR_apply,
    inner_sub_left, hDv]

/-! ### Bounds -/

theorem norm_featureMean_le (hU : Continuous U) (hΦ : Continuous Φ) {L : ℝ}
    (hL : ∀ x, ‖Φ x‖ ≤ L) (z : Feature r) : ‖featureMean U Φ z‖ ≤ L := by
  have := isProbabilityMeasure_gibbs hU hΦ z
  have h := norm_integral_le_of_norm_le_const (μ := gibbs U Φ z) (f := Φ) (C := L)
    (Filter.Eventually.of_forall hL)
  simpa [featureMean, probReal_univ] using h

theorem norm_sub_le_norm_gradient_psi (hU : Continuous U) (hΦ : Continuous Φ) {L : ℝ}
    (hL : ∀ x, ‖Φ x‖ ≤ L) (z : Feature r) : ‖z‖ - L ≤ ‖gradient (psi U Φ) z‖ := by
  rw [gradient_psi hU hΦ]
  have h1 := norm_sub_norm_le z (featureMean U Φ z)
  have h2 := norm_featureMean_le hU hΦ hL z
  linarith

theorem integrable_exp_integrand (hU : Continuous U) (hΦ : Continuous Φ) (z : Feature r) :
    Integrable (fun x => Real.exp (⟪z, Φ x⟫ - U x)) (haar d) := by
  have := integrable_integrand hU hΦ (T := fun _ : Torus d => (1 : ℝ)) continuous_const z
  simpa using this

theorem zeta_le (hU : Continuous U) (hΦ : Continuous Φ) {L : ℝ} (hL : ∀ x, ‖Φ x‖ ≤ L)
    (z : Feature r) : zeta U Φ z ≤ Real.exp (L * ‖z‖) * zeta U Φ 0 := by
  unfold zeta
  rw [← integral_const_mul]
  refine integral_mono (integrable_exp_integrand hU hΦ z)
    ((integrable_exp_integrand hU hΦ 0).const_mul _) fun x => ?_
  simp only [inner_zero_left, zero_sub]
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h1 : ⟪z, Φ x⟫ ≤ ‖z‖ * ‖Φ x‖ := real_inner_le_norm z (Φ x)
  have h2 : ‖z‖ * ‖Φ x‖ ≤ ‖z‖ * L := mul_le_mul_of_nonneg_left (hL x) (norm_nonneg z)
  nlinarith

theorem psi_lower_bound (hU : Continuous U) (hΦ : Continuous Φ) {L : ℝ}
    (hL : ∀ x, ‖Φ x‖ ≤ L) (z : Feature r) :
    ‖z‖ ^ 2 / 2 - L * ‖z‖ - Real.log (zeta U Φ 0) ≤ psi U Φ z := by
  have h0 := zeta_pos hU hΦ 0
  have hz := zeta_pos hU hΦ z
  have h := Real.log_le_log hz (zeta_le hU hΦ hL z)
  rw [Real.log_mul (Real.exp_pos _).ne' h0.ne', Real.log_exp] at h
  unfold psi
  linarith

theorem featureCov_self_nonneg (z v : Feature r) : 0 ≤ featureCov U Φ z v v :=
  integral_nonneg fun _ => mul_self_nonneg _

theorem integral_sq_gibbs_le (hU : Continuous U) (hΦ : Continuous Φ) {L : ℝ}
    (hL : ∀ x, ‖Φ x‖ ≤ L) (z v : Feature r) :
    ∫ x, ⟪v, Φ x⟫ * ⟪v, Φ x⟫ ∂(gibbs U Φ z) ≤ L ^ 2 * ‖v‖ ^ 2 := by
  have := isProbabilityMeasure_gibbs hU hΦ z
  have ha : Continuous fun x => ⟪v, Φ x⟫ := continuous_const.inner hΦ
  have hi : Integrable (fun x => ⟪v, Φ x⟫ * ⟪v, Φ x⟫) (gibbs U Φ z) :=
    integrable_gibbs hU hΦ (ha.mul ha) z
  have h := integral_mono hi (integrable_const (L ^ 2 * ‖v‖ ^ 2)) (μ := gibbs U Φ z)
    (g := fun _ => L ^ 2 * ‖v‖ ^ 2) fun x => by
      have h1 : |⟪v, Φ x⟫| ≤ ‖v‖ * L :=
        (abs_real_inner_le_norm v (Φ x)).trans (mul_le_mul_of_nonneg_left (hL x) (norm_nonneg v))
      have h2 : ⟪v, Φ x⟫ * ⟪v, Φ x⟫ = |⟪v, Φ x⟫| ^ 2 := by rw [sq_abs]; ring
      rw [h2]
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      nlinarith
  simpa [probReal_univ] using h

theorem featureCov_self_le (hU : Continuous U) (hΦ : Continuous Φ) {L : ℝ}
    (hL : ∀ x, ‖Φ x‖ ≤ L) (z v : Feature r) : featureCov U Φ z v v ≤ L ^ 2 * ‖v‖ ^ 2 := by
  rw [featureCov_eq_gibbs hU hΦ]
  have := integral_sq_gibbs_le hU hΦ hL z v
  nlinarith [mul_self_nonneg ⟪v, featureMean U Φ z⟫]


theorem laplacian_psi_bounds (hU : Continuous U) (hΦ : Continuous Φ) {L : ℝ}
    (hL : ∀ x, ‖Φ x‖ ≤ L) (z : Feature r) :
    (r : ℝ) - L ^ 2 ≤ Laplacian.laplacian (psi U Φ) z ∧
      Laplacian.laplacian (psi U Φ) z ≤ r := by
  have := isProbabilityMeasure_gibbs hU hΦ z
  set b := EuclideanSpace.basisFun (Fin r) ℝ with hb
  have hlap : Laplacian.laplacian (psi U Φ) z =
      (r : ℝ) - ∑ i, featureCov U Φ z (b i) (b i) := by
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (psi U Φ) b]
    simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      hessian_psi hU hΦ, Finset.sum_sub_distrib]
    simp
  have hnn : 0 ≤ ∑ i, featureCov U Φ z (b i) (b i) :=
    Finset.sum_nonneg fun i _ => featureCov_self_nonneg z (b i)
  have hsum : ∑ i, featureCov U Φ z (b i) (b i) ≤ L ^ 2 := by
    have hle : ∀ i, featureCov U Φ z (b i) (b i) ≤
        ∫ x, ⟪b i, Φ x⟫ * ⟪b i, Φ x⟫ ∂(gibbs U Φ z) := fun i => by
      rw [featureCov_eq_gibbs hU hΦ]
      nlinarith [mul_self_nonneg ⟪b i, featureMean U Φ z⟫]
    refine (Finset.sum_le_sum fun i _ => hle i).trans ?_
    have hint : ∀ i ∈ Finset.univ, Integrable (fun x => ⟪b i, Φ x⟫ * ⟪b i, Φ x⟫) (gibbs U Φ z) :=
      fun i _ => integrable_gibbs hU hΦ
        ((continuous_const.inner hΦ).mul (continuous_const.inner hΦ)) z
    rw [← integral_finsetSum _ hint]
    have hpt : ∀ x, ∑ i, ⟪b i, Φ x⟫ * ⟪b i, Φ x⟫ = ‖Φ x‖ ^ 2 := fun x => by
      rw [← b.sum_sq_norm_inner_right (Φ x)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Real.norm_eq_abs, sq_abs]; ring
    have hi2 : Integrable (fun x => ∑ i, ⟪b i, Φ x⟫ * ⟪b i, Φ x⟫) (gibbs U Φ z) :=
      integrable_finsetSum _ hint
    have h := integral_mono hi2 (integrable_const (L ^ 2)) (μ := gibbs U Φ z)
      (g := fun _ => L ^ 2) fun x => by
        rw [hpt]
        exact pow_le_pow_left₀ (norm_nonneg _) (hL x) 2
    simpa [probReal_univ] using h
  rw [hlap]
  constructor <;> linarith


end Model

end DGPS.FiniteN.AttractiveLandscape
