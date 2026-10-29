import DGPS.Basic.HeatKernelBounds
import DGPS.Foundations.PeriodicSmoothing

/-!
# Heat-regularized functions as `H¹` test functions (LIP026a)

For `ε > 0` and `ψ ∈ L²(m)`, the heat regularization `heatOp ε ψ` is `C¹` (its lift to `ℝ^d` is
`C¹`), has the classical gradient `heatOpGrad ε ψ` as its weak gradient, and
`‖∇ heatOp ε ψ‖_{L²} ≤ √(d/2) ε^{-1/2} ‖ψ‖_{L²}`.  Also: integration by parts against smooth
periodic tests extends from smooth to `C¹` periodic functions.
-/

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace DGPS.Lipschitz.ParabolicChainRule

open DGPS

variable {d : ℕ}

/-- `v : 𝕋^d → ℝ` is `C¹` periodic: its periodic lift is `C¹` on `ℝ^d`. -/
def IsC1Periodic (v : Torus d → ℝ) : Prop := ContDiff ℝ 1 (v ∘ torusLift)

theorem IsC1Periodic.continuous_torus {v : Torus d → ℝ} (hv : IsC1Periodic v) : Continuous v :=
  continuous_of_comp_torusLift hv.continuous

theorem IsC1Periodic.continuous_coordPartial {v : Torus d → ℝ} (hv : IsC1Periodic v) (j : Fin d) :
    Continuous (coordPartial j v) := by
  refine continuous_of_comp_torusLift ?_
  rw [coordPartial_comp_torusLift]
  exact (hv.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem isC1Periodic_of_smooth {v : Torus d → ℝ} (hv : IsSmoothPeriodic v) :
    IsC1Periodic v := ContDiff.of_le (n := ∞) hv (by exact_mod_cast le_top)

/-- Integration by parts for a `C¹` periodic function against a smooth periodic test. -/
theorem integral_mul_coordPartial_of_c1 {v φ : Torus d → ℝ} (hv : IsC1Periodic v)
    (hφ : IsSmoothPeriodic φ) (j : Fin d) :
    ∫ x, v x * coordPartial j φ x ∂haar d = -∫ x, coordPartial j v x * φ x ∂haar d := by
  have hW : ContDiff ℝ 1 ((fun x => v x * φ x) ∘ SharpLSI.liftT) :=
    ContDiff.mul hv (isC1Periodic_of_smooth hφ)
  have h0 := SharpLSI.integral_fderiv_torus_eq_zero hW (Pi.single j 1)
  have hpt : ∀ y : Torus d,
      fderiv ℝ ((fun x => v x * φ x) ∘ SharpLSI.liftT) (SharpLSI.secT y) (Pi.single j 1)
        = v y * coordPartial j φ y + coordPartial j v y * φ y := by
    intro y
    have hv1 : DifferentiableAt ℝ (v ∘ SharpLSI.liftT) (SharpLSI.secT y) :=
      (hv.differentiable one_ne_zero) _
    have hφ1 : DifferentiableAt ℝ (φ ∘ SharpLSI.liftT) (SharpLSI.secT y) :=
      (hφ.differentiable (by simp)) _
    have : ((fun x => v x * φ x) ∘ SharpLSI.liftT) =
        fun x => (v ∘ SharpLSI.liftT) x * (φ ∘ SharpLSI.liftT) x := rfl
    rw [this, fderiv_fun_mul hv1 hφ1]
    simp only [add_apply, smul_apply, smul_eq_mul,
      Function.comp_apply, SharpLSI.liftT_secT, DGPS.coordPartial]
    ring
  simp_rw [hpt] at h0
  have i1 : Integrable (fun x => v x * coordPartial j φ x) (haar d) :=
    integrable_of_continuous_torus (hv.continuous_torus.mul (hφ.continuous_coordPartial j))
  have i2 : Integrable (fun x => coordPartial j v x * φ x) (haar d) :=
    integrable_of_continuous_torus ((hv.continuous_coordPartial j).mul hφ.continuous_torus)
  have h3 := integral_add i1 i2
  have h4 : ∫ x, (v x * coordPartial j φ x + coordPartial j v x * φ x) ∂haar d = 0 := h0
  linarith


/-- The classical gradient of a (`C¹`) periodic function, as a tangent vector. -/
noncomputable def heatOpGrad (ε : ℝ) (ψ : Torus d → ℝ) : Torus d → Tangent d :=
  smoothGrad (heatOp ε ψ)

theorem heatOpGrad_apply (ε : ℝ) (ψ : Torus d → ℝ) (y : Torus d) (j : Fin d) :
    heatOpGrad ε ψ y j = coordPartial j (heatOp ε ψ) y := rfl

/-- A `C¹` periodic function is in `H¹` with its classical gradient. -/
theorem IsC1Periodic.isWeakGradient {v : Torus d → ℝ} (hv : IsC1Periodic v) :
    IsWeakGradient v (smoothGrad v) where
  memLp := memLp_two_of_continuous hv.continuous_torus
  memLp_grad := by
    have hc : Continuous (smoothGrad v) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi fun j => hv.continuous_coordPartial j)
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hc.continuousOn
    exact (memLp_top_of_bound hc.aestronglyMeasurable C
      (Eventually.of_forall fun x => hC x (Set.mem_univ x))).mono_exponent le_top
  ibp φ hφ j := integral_mul_coordPartial_of_c1 hv hφ j

theorem IsC1Periodic.memH1 {v : Torus d → ℝ} (hv : IsC1Periodic v) : MemH1 v :=
  ⟨_, hv.isWeakGradient⟩

/-- A global bound for the gradient of the lifted heat kernel. -/
theorem exists_norm_fderiv_Kh_le {t : ℝ} (ht : 0 < t) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : Tangent d, ‖fderiv ℝ (Kh t) u‖ ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_le_of_continuous' (continuous_Psi (d := d) ht)
  refine ⟨M, hM0, fun u => ?_⟩
  have h := Psi_torusLift (d := d) t u.ofLp
  have hu : (WithLp.toLp 2 u.ofLp : Tangent d) = u := rfl
  rw [hu] at h
  rw [← h]
  exact (le_abs_self _).trans (hM _)

/-- The lifted heat regularization of an integrable function is `C¹`. -/
theorem contDiff_Hl {t : ℝ} (ht : 0 < t) {f : Torus d → ℝ} (hf : Integrable f (haar d)) :
    ContDiff ℝ 1 (Hl t f) := by
  rw [contDiff_one_iff_fderiv]
  refine ⟨fun v => (hasFDerivAt_Hl ht hf v).differentiableAt, ?_⟩
  have hfun : fderiv ℝ (Hl t f) =
      fun v => ∫ w, f w • fderiv ℝ (Kh t) (v - secE w) ∂haar d :=
    funext fun v => (hasFDerivAt_Hl ht hf v).fderiv
  rw [hfun]
  obtain ⟨M, hM0, hM⟩ := exists_norm_fderiv_Kh_le (d := d) ht
  have hKd : Continuous (fderiv ℝ (Kh (d := d) t)) :=
    (contDiff_Kh ht).continuous_fderiv (by simp)
  refine continuous_of_dominated (bound := fun w => ‖f w‖ * M) (fun v => ?_) (fun v => ?_)
    (hf.norm.mul_const M) ?_
  · exact hf.aestronglyMeasurable.smul
      ((hKd.measurable.comp (measurable_const.sub measurable_secE)).aestronglyMeasurable)
  · refine Eventually.of_forall fun w => ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  · refine Eventually.of_forall fun w => ?_
    exact (hKd.comp (continuous_id.sub continuous_const)).const_smul (f w)

theorem isC1Periodic_heatOp {ε : ℝ} (hε : 0 < ε) {ψ : Torus d → ℝ} (hψ : Integrable ψ (haar d)) :
    IsC1Periodic (heatOp ε ψ) :=
  (contDiff_Hl hε hψ).comp (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.contDiff


theorem continuous_heatOpGrad {ε : ℝ} (hε : 0 < ε) {ψ : Torus d → ℝ} (hψ : Integrable ψ (haar d)) :
    Continuous (heatOpGrad ε ψ) :=
  (PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun j => (isC1Periodic_heatOp hε hψ).continuous_coordPartial j)

/-- Pointwise gradient bound: `|∇ H_ε ψ| ≤ Ψ_ε ⋆ |ψ|`. -/
theorem norm_heatOpGrad_le {ε : ℝ} (hε : 0 < ε) {ψ : Torus d → ℝ} (hψ : Integrable ψ (haar d))
    (y : Torus d) :
    ‖heatOpGrad ε ψ y‖ ≤ torusConv (Psi ε) (fun w => ‖ψ w‖) y := by
  set G := heatOpGrad ε ψ y with hG
  set L : Tangent d →L[ℝ] ℝ := ∫ w, ψ w • fderiv ℝ (Kh ε) (secE y - secE w) ∂haar d with hL
  have hLa : ∀ a : Tangent d, L a = ∫ w, ψ w * fderiv ℝ (Kh ε) (secE y - secE w) a ∂haar d := by
    intro a
    rw [hL, ContinuousLinearMap.integral_apply (integrable_smul_dKh hε hψ (secE y)) a]
    simp only [smul_apply, smul_eq_mul]
  have hGj : ∀ j, G j = L (EuclideanSpace.single j 1) := fun j => by
    rw [hLa, hG, heatOpGrad_apply, coordPartial_heatOp hε hψ]
  have hnorm : ‖G‖ ^ 2 = L G := by
    have e : G = ∑ j, G j • (EuclideanSpace.single j (1 : ℝ) : Tangent d) := by
      ext i; simp [Pi.single_apply]
    conv_rhs => rw [e]
    rw [tangent_norm_sq, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, ← hGj]; ring
  have hLn : ‖L‖ ≤ torusConv (Psi ε) (fun w => ‖ψ w‖) y := by
    rw [hL]
    refine norm_integral_le_of_norm_le (integrable_conv_integrand (continuous_Psi hε) hψ.norm y)
      (Eventually.of_forall fun w => ?_)
    rw [norm_smul, ← norm_fderiv_Kh_sub, mul_comm]
  refine le_trans ?_ hLn
  rcases (norm_nonneg G).eq_or_lt with h0 | hpos
  · rw [← h0]; exact norm_nonneg _
  · have : ‖G‖ ^ 2 ≤ ‖L‖ * ‖G‖ := by
      rw [hnorm]; exact (le_abs_self _).trans (L.le_opNorm G)
    nlinarith

/-- **Quantitative `L²` gradient bound** for the heat regularization:
`‖∇ H_ε ψ‖_{L²} ≤ √(d/2) ε^{-1/2} ‖ψ‖_{L²}`. -/
theorem eLpNorm_heatOpGrad_le {ε : ℝ} (hε : 0 < ε) {ψ : Torus d → ℝ} (hψ : MemLp ψ 2 (haar d)) :
    eLpNorm (heatOpGrad ε ψ) 2 (haar d) ≤
      ENNReal.ofReal (Real.sqrt (d / 2) * ε ^ (-(1 : ℝ) / 2)) * eLpNorm ψ 2 (haar d) := by
  have hψ1 : Integrable ψ (haar d) := hψ.integrable one_le_two
  rcases Nat.eq_zero_or_pos d with h0 | hd
  · subst h0
    have : heatOpGrad ε ψ = 0 := funext fun y => Subsingleton.elim _ _
    rw [this]
    simp
  rw [← sqrt_const_eq hε]
  obtain ⟨K, hKc, hK0, hK1, hKP⟩ := exists_dom_kernel hε hd
  set c0 := Real.sqrt (2 * ε * d) / (2 * ε) with hc0
  have hc0pos : 0 < c0 := by
    have : 0 < Real.sqrt (2 * ε * d) := Real.sqrt_pos.2 (by positivity)
    positivity
  have hpt : ∀ y, ‖heatOpGrad ε ψ y‖ ≤ c0 * torusConv K (fun w => ‖ψ w‖) y := fun y => by
    refine (norm_heatOpGrad_le hε hψ1 y).trans ?_
    unfold torusConv
    rw [← integral_const_mul]
    refine integral_mono (integrable_conv_integrand (continuous_Psi hε) hψ1.norm y)
      ((integrable_conv_integrand hKc hψ1.norm y).const_mul _) fun w => ?_
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hKP _) (norm_nonneg _)
  have hg : MemLp (fun w => ‖ψ w‖) 2 (haar d) := hψ.norm
  calc eLpNorm (heatOpGrad ε ψ) 2 (haar d)
      ≤ eLpNorm (fun y => c0 * torusConv K (fun w => ‖ψ w‖) y) 2 (haar d) := by
        refine eLpNorm_mono (continuous_heatOpGrad hε hψ1).aestronglyMeasurable fun y => ?_
        refine (hpt y).trans ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc0pos.le
          (torusConv_nonneg hK0 (Eventually.of_forall fun w => norm_nonneg _) y))]
    _ = ENNReal.ofReal c0 * eLpNorm (torusConv K (fun w => ‖ψ w‖)) 2 (haar d) := by
        have := eLpNorm_const_smul (μ := haar d) (p := 2) c0 (torusConv K (fun w => ‖ψ w‖))
        rw [Real.enorm_eq_ofReal hc0pos.le] at this
        exact this
    _ ≤ ENNReal.ofReal c0 * eLpNorm (fun w => ‖ψ w‖) 2 (haar d) :=
        mul_le_mul_right (eLpNorm_torusConv_le hKc hK0 hK1 one_le_two (by simp) hg) _
    _ = _ := by rw [eLpNorm_norm ψ hψ.aestronglyMeasurable]

/-- **LIP026a headline.** For `ε > 0` and `ψ ∈ L²(m)`, the heat regularization `H_ε ψ` is a `C¹`
periodic function whose classical gradient is its `L²` weak gradient (in particular
`H_ε ψ ∈ H¹`), with `‖∇ H_ε ψ‖_{L²} ≤ √(d/2) ε^{-1/2} ‖ψ‖_{L²}`. -/
theorem heatOp_isWeakGradient_of_memL2 {ε : ℝ} (hε : 0 < ε) {ψ : Torus d → ℝ}
    (hψ : MemLp ψ 2 (haar d)) :
    IsC1Periodic (heatOp ε ψ) ∧ IsWeakGradient (heatOp ε ψ) (heatOpGrad ε ψ) ∧
      eLpNorm (heatOpGrad ε ψ) 2 (haar d) ≤
        ENNReal.ofReal (Real.sqrt (d / 2) * ε ^ (-(1 : ℝ) / 2)) * eLpNorm ψ 2 (haar d) :=
  ⟨isC1Periodic_heatOp hε (hψ.integrable one_le_two),
    (isC1Periodic_heatOp hε (hψ.integrable one_le_two)).isWeakGradient,
    eLpNorm_heatOpGrad_le hε hψ⟩

theorem heatOp_memH1 {ε : ℝ} (hε : 0 < ε) {ψ : Torus d → ℝ} (hψ : MemLp ψ 2 (haar d)) :
    MemH1 (heatOp ε ψ) :=
  ⟨_, (heatOp_isWeakGradient_of_memL2 hε hψ).2.1⟩

end DGPS.Lipschitz.ParabolicChainRule
