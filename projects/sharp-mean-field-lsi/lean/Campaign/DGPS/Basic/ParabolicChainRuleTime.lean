import DGPS.Basic.ParabolicChainRule

/-!
# Parabolic chain rule, time layer at fixed heat regularization (LIP026b)
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal ContDiff RealInnerProductSpace

namespace DGPS.Lipschitz.ParabolicChainRule

open DGPS

variable {d : ℕ}

/-- The kernel-gradient coefficient: `∂ⱼ K_ε (x - w)` in the variable `x`. -/
noncomputable def lip026b_kern (ε : ℝ) (j : Fin d) (x w : Torus d) : ℝ :=
  fderiv ℝ (Kh ε) (secE x - secE w) (EuclideanSpace.single j 1)

/-- The smooth periodic test function `w ↦ K_ε (x - w)`. -/
noncomputable def lip026b_phiX (ε : ℝ) (x : Torus d) : Torus d → ℝ :=
  fun w => heatKernelT ε (x - w)

theorem lip026b_phiX_comp_lift (ε : ℝ) (x : Torus d) (p : Fin d → ℝ) :
    lip026b_phiX ε x (torusLift p) = Kh ε (secE x - WithLp.toLp 2 p) := by
  unfold lip026b_phiX Kh
  have : x - torusLift p = torusLift (SharpLSI.secT x - p) := by
    simp only [torusLift, SharpLSI.liftT_sub, SharpLSI.liftT_secT]
  rw [this]
  exact SharpLSI.heatP_liftT ε _

theorem lip026b_isSmoothPeriodic_phiX {ε : ℝ} (hε : 0 < ε) (x : Torus d) :
    IsSmoothPeriodic (lip026b_phiX ε x) := by
  unfold IsSmoothPeriodic
  have : (lip026b_phiX ε x ∘ torusLift) = fun p => Kh ε (secE x - WithLp.toLp 2 p) :=
    funext (lip026b_phiX_comp_lift ε x)
  rw [this]
  exact (contDiff_Kh hε).comp
    (contDiff_const.sub (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.contDiff)

theorem lip026b_coordPartial_phiX {ε : ℝ} (hε : 0 < ε) (x w : Torus d) (j : Fin d) :
    coordPartial j (lip026b_phiX ε x) w = -lip026b_kern ε j x w := by
  unfold coordPartial
  have hfun : (lip026b_phiX ε x ∘ torusLift) = fun p => Kh ε (secE x - WithLp.toLp 2 p) :=
    funext (lip026b_phiX_comp_lift ε x)
  rw [hfun]
  have hm : HasFDerivAt (fun p : Fin d → ℝ => secE x - (WithLp.toLp 2 p : Tangent d))
      (-((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm : (Fin d → ℝ) →L[ℝ] Tangent d))
      (SharpLSI.secT w) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.hasFDerivAt.const_sub (secE x)
  have hK : HasFDerivAt (Kh ε) (fderiv ℝ (Kh ε) (secE x - WithLp.toLp 2 (SharpLSI.secT w)))
      (secE x - WithLp.toLp 2 (SharpLSI.secT w)) :=
    (((contDiff_Kh hε).differentiable (by simp)) _).hasFDerivAt
  have hc := hK.comp (SharpLSI.secT w) hm
  rw [show (fun p : Fin d → ℝ => Kh ε (secE x - WithLp.toLp 2 p)) =
    Kh ε ∘ (fun p : Fin d → ℝ => secE x - (WithLp.toLp 2 p : Tangent d)) from rfl, hc.fderiv]
  simp only [lip026b_kern, ContinuousLinearMap.comp_apply, neg_apply,
    map_neg]
  rfl

theorem lip026b_kern_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (j : Fin d) (x w : Torus d), |lip026b_kern ε j x w| ≤ M := by
  obtain ⟨M, hM0, hM⟩ := exists_norm_fderiv_Kh_le (d := d) hε
  refine ⟨M, hM0, fun j x w => ?_⟩
  unfold lip026b_kern
  have h1 := (fderiv ℝ (Kh ε) (secE x - secE w)).le_opNorm (EuclideanSpace.single j (1 : ℝ))
  have h2 : ‖(EuclideanSpace.single j (1 : ℝ) : Tangent d)‖ = 1 := by simp
  rw [h2, mul_one] at h1
  exact (Real.norm_eq_abs _ ▸ h1).trans (hM _)

theorem lip026b_measurable_kern {ε : ℝ} (hε : 0 < ε) (j : Fin d) :
    Measurable (fun p : Torus d × Torus d => lip026b_kern ε j p.1 p.2) := by
  have hKd : Continuous (fderiv ℝ (Kh (d := d) ε)) :=
    (contDiff_Kh hε).continuous_fderiv (by simp)
  have hc : Continuous (fun A : Tangent d →L[ℝ] ℝ => A (EuclideanSpace.single j 1)) :=
    (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single j (1 : ℝ) : Tangent d)).continuous
  exact (hc.comp hKd).measurable.comp
    ((measurable_secE.comp measurable_fst).sub (measurable_secE.comp measurable_snd))

theorem lip026b_coordPartial_heatOp {ε : ℝ} (hε : 0 < ε) {f : Torus d → ℝ}
    (hf : Integrable f (haar d)) (j : Fin d) (x : Torus d) :
    coordPartial j (heatOp ε f) x = ∫ w, f w * lip026b_kern ε j x w ∂haar d := by
  have hH := hasFDerivAt_Hl hε hf (secE x)
  have hfun : (heatOp ε f ∘ torusLift) = Hl ε f ∘ (fun p : Fin d → ℝ => (WithLp.toLp 2 p : Tangent d)) :=
    rfl
  have hm := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm.hasFDerivAt
    (x := SharpLSI.secT x)
  have hc := hH.comp (SharpLSI.secT x) hm
  unfold coordPartial
  rw [hfun, hc.fderiv]
  obtain ⟨M, hM0, hM⟩ := exists_norm_fderiv_Kh_le (d := d) hε
  have hKd : Continuous (fderiv ℝ (Kh (d := d) ε)) :=
    (contDiff_Kh hε).continuous_fderiv (by simp)
  have hint : Integrable (fun w => f w • fderiv ℝ (Kh ε) (secE x - secE w)) (haar d) := by
    refine Integrable.mono' (hf.norm.mul_const M)
      (hf.aestronglyMeasurable.smul
        ((hKd.measurable.comp (measurable_const.sub measurable_secE)).aestronglyMeasurable))
      (Eventually.of_forall fun w => ?_)
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
  simp only [ContinuousLinearMap.comp_apply]
  have := (ContinuousLinearMap.apply ℝ ℝ
    (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm : (Fin d → ℝ) →L[ℝ] Tangent d)
      (Pi.single j 1))).integral_comp_comm hint
  simp only [ContinuousLinearMap.apply_apply] at this
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only [smul_apply, smul_eq_mul, lip026b_kern]
  rfl

/-- One-dimensional chain rule for a primitive of an interval-integrable function. -/
theorem lip026b_chain_1d0 {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {G : ℝ → ℝ} {s t : ℝ} (hst : s ≤ t)
    (hG : IntervalIntegrable G volume s t) :
    h (∫ r in s..t, G r) - h 0 = ∫ r in s..t, deriv h (∫ r' in s..r, G r') * G r := by
  have hFac : AbsolutelyContinuousOnInterval (fun r => ∫ v in s..r, G v) s t :=
    hG.absolutelyContinuousOnInterval_intervalIntegral (by simp [hst])
  have hK : IsCompact ((fun r => ∫ v in s..r, G v) '' uIcc s t) :=
    isCompact_uIcc.image_of_continuousOn hFac.continuousOn
  obtain ⟨L, hL⟩ := hh.locallyLipschitz.locallyLipschitzOn.exists_lipschitzOnWith_of_compact hK
  have hAC := hL.comp_absolutelyContinuousOnInterval (Set.mapsTo_image _ _) hFac
  have key := hAC.integral_deriv_eq_sub
  simp only [Function.comp_apply, intervalIntegral.integral_same] at key
  rw [← key]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hG.ae_hasDerivAt_integral] with r hr hrmem
  have hrm : r ∈ uIcc s t := Set.uIoc_subset_uIcc hrmem
  have h1 := hr hrm s (by simp [hst])
  have h2 := ((hh.differentiable one_ne_zero) (∫ v in s..r, G v)).hasDerivAt.comp r h1
  exact h2.deriv

theorem lip026b_chain_1d {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) {G U : ℝ → ℝ} {s t : ℝ}
    (hst : s ≤ t) (hG : IntervalIntegrable G volume s t)
    (hU : ∀ r ∈ Set.Icc s t, U r = U s + ∫ r' in s..r, G r') :
    h (U t) - h (U s) = ∫ r in s..t, deriv h (U r) * G r := by
  have hha : ContDiff ℝ 1 (fun y => h (U s + y)) := hh.comp (contDiff_const.add contDiff_id)
  have key := lip026b_chain_1d0 hha hst hG
  simp only [add_zero] at key
  rw [hU t ⟨hst, le_rfl⟩]
  rw [key]
  refine intervalIntegral.integral_congr fun r hr => ?_
  have hr' : r ∈ Set.Icc s t := by simpa [Set.uIcc_of_le hst] using hr
  rw [hU r hr', deriv_comp_const_add]

/-- **Weak time derivative `∂ₜ u = div J` on `[0,T]` (integrated form).**  For `φ` smooth periodic
and `0 ≤ s ≤ t ≤ T`:
`∫ u_t φ - ∫ u_s φ = -∫_s^t ∫ J_r · ∇φ dm dr`, with each `u_t` integrable and the flux `J`
jointly measurable and integrable on `[0,T] × 𝕋^d`. -/
structure IsWeakTimeDivergence (T : ℝ) (u : ℝ → Torus d → ℝ) (J : ℝ → Torus d → Tangent d) :
    Prop where
  integrable_u : ∀ t ∈ Set.Icc 0 T, Integrable (u t) (haar d)
  measurable_J : Measurable (fun p : ℝ × Torus d => J p.1 p.2)
  integrable_J : Integrable (fun p : ℝ × Torus d => J p.1 p.2)
    ((volume.restrict (Set.Icc 0 T)).prod (haar d))
  weak : ∀ φ : Torus d → ℝ, IsSmoothPeriodic φ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
    ∫ x, u t x * φ x ∂haar d - ∫ x, u s x * φ x ∂haar d =
      -∫ r in s..t, ∫ w, ∑ j, J r w j * coordPartial j φ w ∂haar d

/-- The divergence of the heat-regularized vector field `J^ε = heatGrad ε V` (componentwise
`H_ε V^j`): `div J^ε (x) = ∑ⱼ ∂ⱼ (H_ε V^j) (x)`. -/
noncomputable def heatDiv (ε : ℝ) (V : Torus d → Tangent d) (x : Torus d) : ℝ :=
  ∑ j, coordPartial j (fun y => heatGrad ε V y j) x

/-- The kernel form of `heatDiv`. -/
noncomputable def lip026b_Gt (ε : ℝ) (J : ℝ → Torus d → Tangent d) (r : ℝ) (x : Torus d) : ℝ :=
  ∑ j, ∫ w, J r w j * lip026b_kern ε j x w ∂haar d

theorem lip026b_measurable_Gt {ε : ℝ} (hε : 0 < ε) {J : ℝ → Torus d → Tangent d}
    (hJ : Measurable (fun p : ℝ × Torus d => J p.1 p.2)) :
    Measurable (fun p : ℝ × Torus d => lip026b_Gt ε J p.1 p.2) := by
  unfold lip026b_Gt
  refine Finset.measurable_sum _ fun j _ => ?_
  have hproj : Measurable (fun v : Tangent d => v j) :=
    (EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).continuous.measurable
  have hf : Measurable (fun q : (ℝ × Torus d) × Torus d =>
      J q.1.1 q.2 j * lip026b_kern ε j q.1.2 q.2) := by
    refine Measurable.mul (hproj.comp ?_) ?_
    · exact hJ.comp (measurable_fst.comp measurable_fst |>.prodMk measurable_snd)
    · exact (lip026b_measurable_kern hε j).comp ((measurable_snd.comp measurable_fst).prodMk
        measurable_snd)
  exact (hf.stronglyMeasurable.integral_prod_right').measurable

theorem lip026b_measurable_slice {J : ℝ → Torus d → Tangent d}
    (hJ : Measurable (fun p : ℝ × Torus d => J p.1 p.2)) (r : ℝ) : Measurable (J r) :=
  hJ.comp measurable_prodMk_left

/-- For a.e. `r ∈ [0,T]` the slice `J_r` is integrable. -/
theorem lip026b_ae_slice {T : ℝ} {J : ℝ → Torus d → Tangent d}
    (hJ : Integrable (fun p : ℝ × Torus d => J p.1 p.2)
      ((volume.restrict (Set.Icc 0 T)).prod (haar d))) :
    ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Integrable (fun w => ‖J r w‖) (haar d) := by
  filter_upwards [hJ.prod_right_ae] with r hr using hr.norm

theorem lip026b_integrable_comp {J : ℝ → Torus d → Tangent d} {r : ℝ}
    (hm : Measurable (J r)) (hn : Integrable (fun w => ‖J r w‖) (haar d)) (j : Fin d) :
    Integrable (fun w => J r w j) (haar d) := by
  refine Integrable.mono' hn ?_ (Eventually.of_forall fun w => ?_)
  · exact ((EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).continuous.measurable.comp
      hm).aestronglyMeasurable
  · simpa using PiLp.norm_apply_le (J r w) j

theorem lip026b_heatDiv_eq {ε : ℝ} (hε : 0 < ε) {J : ℝ → Torus d → Tangent d} {r : ℝ}
    (hm : Measurable (J r)) (hn : Integrable (fun w => ‖J r w‖) (haar d)) (x : Torus d) :
    heatDiv ε (J r) x = lip026b_Gt ε J r x := by
  unfold heatDiv lip026b_Gt
  refine Finset.sum_congr rfl fun j _ => ?_
  exact lip026b_coordPartial_heatOp hε (lip026b_integrable_comp hm hn j) j x

theorem lip026b_Gt_bound {ε M : ℝ} (hM : ∀ (j : Fin d) (x w : Torus d), |lip026b_kern ε j x w| ≤ M)
    {J : ℝ → Torus d → Tangent d} {r : ℝ}
    (hn : Integrable (fun w => ‖J r w‖) (haar d)) (x : Torus d) :
    |lip026b_Gt ε J r x| ≤ d * M * ∫ w, ‖J r w‖ ∂haar d := by
  unfold lip026b_Gt
  have hj : ∀ j : Fin d, |∫ w, J r w j * lip026b_kern ε j x w ∂haar d| ≤
      M * ∫ w, ‖J r w‖ ∂haar d := by
    intro j
    have h1 := norm_integral_le_of_norm_le (hn.mul_const M)
      (Eventually.of_forall fun w => ?_) (f := fun w => J r w j * lip026b_kern ε j x w)
    · rw [Real.norm_eq_abs] at h1
      rw [integral_mul_const] at h1
      linarith
    · rw [norm_mul]
      exact mul_le_mul (by simpa using PiLp.norm_apply_le (J r w) j)
        (by simpa using hM j x w) (norm_nonneg _) (norm_nonneg _)
  calc |∑ j, ∫ w, J r w j * lip026b_kern ε j x w ∂haar d|
      ≤ ∑ j : Fin d, |∫ w, J r w j * lip026b_kern ε j x w ∂haar d| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, M * ∫ w, ‖J r w‖ ∂haar d := Finset.sum_le_sum fun j _ => hj j
    _ = d * M * ∫ w, ‖J r w‖ ∂haar d := by simp [Finset.sum_const]; ring

theorem lip026b_integrable_mul_kern {ε M : ℝ} (hε : 0 < ε)
    (hM : ∀ (j : Fin d) (x w : Torus d), |lip026b_kern ε j x w| ≤ M)
    {J : ℝ → Torus d → Tangent d} {r : ℝ}
    (hm : Measurable (J r)) (hn : Integrable (fun w => ‖J r w‖) (haar d)) (j : Fin d)
    (x : Torus d) : Integrable (fun w => J r w j * lip026b_kern ε j x w) (haar d) := by
  have hk : Measurable (fun w => lip026b_kern ε j x w) :=
    (lip026b_measurable_kern hε j).comp (measurable_prodMk_left : Measurable fun w : Torus d => (x, w))
  refine Integrable.mono' ((lip026b_integrable_comp hm hn j).norm.mul_const M) ?_
    (Eventually.of_forall fun w => ?_)
  · exact (((EuclideanSpace.proj j : Tangent d →L[ℝ] ℝ).continuous.measurable.comp hm).mul
      hk).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (by simpa using hM j x w) (norm_nonneg _)

theorem lip026b_integral_phiX_mul (ε : ℝ) (f : Torus d → ℝ) (x : Torus d) :
    ∫ w, f w * lip026b_phiX ε x w ∂haar d = heatOp ε f x := by
  unfold heatOp torusConv lip026b_phiX
  exact integral_congr_ae (Eventually.of_forall fun w => mul_comm _ _)

theorem lip026b_inner_flux {ε M : ℝ} (hε : 0 < ε)
    (hM : ∀ (j : Fin d) (x w : Torus d), |lip026b_kern ε j x w| ≤ M)
    {J : ℝ → Torus d → Tangent d} {r : ℝ}
    (hm : Measurable (J r)) (hn : Integrable (fun w => ‖J r w‖) (haar d)) (x : Torus d) :
    ∫ w, ∑ j, J r w j * coordPartial j (lip026b_phiX ε x) w ∂haar d = -lip026b_Gt ε J r x := by
  unfold lip026b_Gt
  have : ∀ w, ∑ j, J r w j * coordPartial j (lip026b_phiX ε x) w =
      -∑ j, J r w j * lip026b_kern ε j x w := by
    intro w
    simp only [lip026b_coordPartial_phiX hε, mul_neg, Finset.sum_neg_distrib]
  simp_rw [this]
  rw [integral_neg, integral_finsetSum _ fun j _ => lip026b_integrable_mul_kern hε hM hm hn j x]

theorem lip026b_Gt_integrableOn {ε M : ℝ} (hε : 0 < ε)
    (hM : ∀ (j : Fin d) (x w : Torus d), |lip026b_kern ε j x w| ≤ M) {T : ℝ}
    {u : ℝ → Torus d → ℝ} {J : ℝ → Torus d → Tangent d} (h : IsWeakTimeDivergence T u J)
    (x : Torus d) : IntegrableOn (fun r => lip026b_Gt ε J r x) (Set.Icc 0 T) := by
  have hN := h.integrable_J.integral_norm_prod_left
  refine Integrable.mono' (hN.const_mul (d * M)) ?_ ?_
  · exact ((lip026b_measurable_Gt hε h.measurable_J).comp
      (measurable_prodMk_right (y := x))).aestronglyMeasurable
  · filter_upwards [lip026b_ae_slice h.integrable_J] with r hr
    rw [Real.norm_eq_abs]
    exact lip026b_Gt_bound hM hr x

/-- **(i) LIP026b, time derivative of the heat-regularized curve.**  If `∂ₜ u = div J` weakly on
`[0,T]` (`IsWeakTimeDivergence`), then for fixed `ε > 0` and every `x`, `r ↦ div J^ε_r (x)` is
integrable on `[0,T]` and `u^ε_t(x) - u^ε_s(x) = ∫_s^t div J^ε_r (x) dr`
(with `u^ε_t = heatOp ε (u t)` and `J^ε_r = heatGrad ε (J r)`); i.e. `t ↦ u^ε_t(x)` is
absolutely continuous with a.e. derivative `div J^ε_t (x)`. -/
theorem heatOp_timeIncrement {ε : ℝ} (hε : 0 < ε) {T : ℝ} {u : ℝ → Torus d → ℝ}
    {J : ℝ → Torus d → Tangent d} (h : IsWeakTimeDivergence T u J) (x : Torus d) :
    IntegrableOn (fun r => heatDiv ε (J r) x) (Set.Icc 0 T) ∧
      ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
        heatOp ε (u t) x - heatOp ε (u s) x = ∫ r in s..t, heatDiv ε (J r) x := by
  obtain ⟨M, hM0, hM⟩ := lip026b_kern_bound (d := d) hε
  have hae : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      heatDiv ε (J r) x = lip026b_Gt ε J r x := by
    filter_upwards [lip026b_ae_slice h.integrable_J] with r hr
    exact lip026b_heatDiv_eq hε (lip026b_measurable_slice h.measurable_J r) hr x
  have hae' : ∀ᵐ r, r ∈ Set.Icc (0 : ℝ) T → heatDiv ε (J r) x = lip026b_Gt ε J r x :=
    (ae_restrict_iff' measurableSet_Icc).1 hae
  refine ⟨(lip026b_Gt_integrableOn hε hM h x).congr (by
    filter_upwards [hae] with r hr using hr.symm), ?_⟩
  intro s t hs hst ht
  have hw := h.weak (lip026b_phiX ε x) (lip026b_isSmoothPeriodic_phiX hε x) s t hs hst ht
  have hu : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫ w, u r w * lip026b_phiX ε x w ∂haar d = heatOp ε (u r) x :=
    fun r _ => lip026b_integral_phiX_mul ε (u r) x
  rw [hu t ⟨hs.trans hst, ht⟩, hu s ⟨hs, hst.trans ht⟩] at hw
  rw [hw]
  have hsub : Set.uIoc s t ⊆ Set.Icc 0 T := by
    rw [Set.uIoc_of_le hst]
    exact fun r hr => ⟨hs.trans hr.1.le, hr.2.trans ht⟩
  have h2 : ∫ r in s..t, ∫ w, ∑ j, J r w j * coordPartial j (lip026b_phiX ε x) w ∂haar d =
      -∫ r in s..t, heatDiv ε (J r) x := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr_ae ?_
    have hae2 : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Integrable (fun w => ‖J r w‖) (haar d) :=
      lip026b_ae_slice h.integrable_J
    have hae3 := (ae_restrict_iff' measurableSet_Icc).1 hae2
    filter_upwards [hae3, hae'] with r h3 h4 hr
    rw [lip026b_inner_flux hε hM (lip026b_measurable_slice h.measurable_J r) (h3 (hsub hr)) x,
      h4 (hsub hr)]
  rw [h2, neg_neg]

/-- Integration by parts for two `C¹` periodic functions. -/
theorem lip026b_ibp_c1 {v w : Torus d → ℝ} (hv : IsC1Periodic v) (hw : IsC1Periodic w)
    (j : Fin d) :
    ∫ x, v x * coordPartial j w x ∂haar d = -∫ x, coordPartial j v x * w x ∂haar d := by
  have hW : ContDiff ℝ 1 ((fun x => v x * w x) ∘ SharpLSI.liftT) := ContDiff.mul hv hw
  have h0 := SharpLSI.integral_fderiv_torus_eq_zero hW (Pi.single j 1)
  have hpt : ∀ y : Torus d,
      fderiv ℝ ((fun x => v x * w x) ∘ SharpLSI.liftT) (SharpLSI.secT y) (Pi.single j 1)
        = v y * coordPartial j w y + coordPartial j v y * w y := by
    intro y
    have hv1 : DifferentiableAt ℝ (v ∘ SharpLSI.liftT) (SharpLSI.secT y) :=
      (hv.differentiable one_ne_zero) _
    have hw1 : DifferentiableAt ℝ (w ∘ SharpLSI.liftT) (SharpLSI.secT y) :=
      (hw.differentiable one_ne_zero) _
    have : ((fun x => v x * w x) ∘ SharpLSI.liftT) =
        fun x => (v ∘ SharpLSI.liftT) x * (w ∘ SharpLSI.liftT) x := rfl
    rw [this, fderiv_fun_mul hv1 hw1]
    simp only [add_apply, smul_apply, smul_eq_mul,
      Function.comp_apply, SharpLSI.liftT_secT, DGPS.coordPartial]
    ring
  simp_rw [hpt] at h0
  have i1 : Integrable (fun x => v x * coordPartial j w x) (haar d) :=
    integrable_of_continuous_torus (hv.continuous_torus.mul (hw.continuous_coordPartial j))
  have i2 : Integrable (fun x => coordPartial j v x * w x) (haar d) :=
    integrable_of_continuous_torus ((hv.continuous_coordPartial j).mul hw.continuous_torus)
  have h3 := integral_add i1 i2
  have h4 : ∫ x, (v x * coordPartial j w x + coordPartial j v x * w x) ∂haar d = 0 := h0
  linarith

/-- Chain rule for `coordPartial` along a `C¹` periodic function. -/
theorem lip026b_coordPartial_comp {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {f : Torus d → ℝ}
    (hf : IsC1Periodic f) (j : Fin d) (x : Torus d) :
    coordPartial j (fun y => g (f y)) x = deriv g (f x) * coordPartial j f x := by
  unfold coordPartial
  have hf1 : DifferentiableAt ℝ (f ∘ torusLift) (SharpLSI.secT x) :=
    (hf.differentiable one_ne_zero) _
  have hfx : (f ∘ torusLift) (SharpLSI.secT x) = f x := by
    simp [Function.comp_apply, torusLift, SharpLSI.liftT_secT]
  have hg1 : HasDerivAt g (deriv g (f x)) (f x) :=
    ((hg.differentiable one_ne_zero) (f x)).hasDerivAt
  have hg2 : HasDerivAt g (deriv g ((f ∘ torusLift) (SharpLSI.secT x)))
      ((f ∘ torusLift) (SharpLSI.secT x)) := by rwa [hfx]
  have hc := hg2.comp_hasFDerivAt (SharpLSI.secT x) hf1.hasFDerivAt
  have e : ((fun y => g (f y)) ∘ torusLift) = g ∘ (f ∘ torusLift) := rfl
  rw [e, hc.fderiv]
  simp only [smul_apply, smul_eq_mul, hfx]

theorem lip026b_isC1Periodic_comp {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {f : Torus d → ℝ}
    (hf : IsC1Periodic f) : IsC1Periodic (fun y => g (f y)) :=
  hg.comp hf

theorem lip026b_deriv_contDiff {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H) : ContDiff ℝ 1 (deriv H) :=
  (contDiff_succ_iff_deriv.mp (by
    rw [show ((1 : WithTop ℕ∞) + 1) = 2 by norm_num]; exact hH)).2.2

/-- Spatial integration by parts at a fixed time: the heart of the second step. -/
theorem lip026b_ibp_step {ε : ℝ} (hε : 0 < ε)
    {J : ℝ → Torus d → Tangent d} {r : ℝ}
    (hm : Measurable (J r)) (hn : Integrable (fun w => ‖J r w‖) (haar d))
    {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H) {ψ : Torus d → ℝ} (hψ : IsC1Periodic ψ) :
    ∫ x, deriv H (ψ x) * lip026b_Gt ε J r x ∂haar d =
      -∫ x, deriv (deriv H) (ψ x) * ⟪smoothGrad ψ x, heatGrad ε (J r) x⟫ ∂haar d := by
  have hH1 : ContDiff ℝ 1 (deriv H) := lip026b_deriv_contDiff hH
  have hv : IsC1Periodic (fun x => deriv H (ψ x)) := lip026b_isC1Periodic_comp hH1 hψ
  have hw : ∀ j : Fin d, IsC1Periodic (fun y => heatGrad ε (J r) y j) := fun j =>
    isC1Periodic_heatOp hε (lip026b_integrable_comp hm hn j)
  have e1 : ∀ x, lip026b_Gt ε J r x = ∑ j, coordPartial j (fun y => heatGrad ε (J r) y j) x :=
    fun x => (lip026b_heatDiv_eq hε hm hn x).symm
  have e2 : ∀ x, ⟪smoothGrad ψ x, heatGrad ε (J r) x⟫ =
      ∑ j, coordPartial j ψ x * heatGrad ε (J r) x j := by
    intro x
    simp [PiLp.inner_apply, mul_comm]
  have i1 : ∀ j : Fin d, Integrable (fun x => deriv H (ψ x) *
      coordPartial j (fun y => heatGrad ε (J r) y j) x) (haar d) := fun j =>
    integrable_of_continuous_torus
      (hv.continuous_torus.mul ((hw j).continuous_coordPartial j))
  have i2 : ∀ j : Fin d, Integrable (fun x => deriv (deriv H) (ψ x) *
      (coordPartial j ψ x * heatGrad ε (J r) x j)) (haar d) := fun j =>
    integrable_of_continuous_torus
      (((hH1.continuous_deriv le_rfl).comp hψ.continuous_torus).mul
        ((hψ.continuous_coordPartial j).mul (hw j).continuous_torus))
  simp_rw [e1, e2, Finset.mul_sum]
  rw [integral_finsetSum _ fun j _ => i1 j, integral_finsetSum _ fun j _ => i2 j,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [lip026b_ibp_c1 hv (hw j) j]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [lip026b_coordPartial_comp hH1 hψ j x, mul_assoc]

/-- Time clamp to `[0,T]`. -/
def lip026b_clamp (T r : ℝ) : ℝ := max 0 (min r T)

theorem lip026b_continuous_clamp (T : ℝ) : Continuous (lip026b_clamp T) := by
  unfold lip026b_clamp; fun_prop

theorem lip026b_clamp_mem {T : ℝ} (hT : 0 ≤ T) (r : ℝ) : lip026b_clamp T r ∈ Set.Icc 0 T :=
  ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

theorem lip026b_clamp_of_mem {T r : ℝ} (hr : r ∈ Set.Icc 0 T) : lip026b_clamp T r = r := by
  unfold lip026b_clamp
  rw [min_eq_left hr.2, max_eq_right hr.1]

/-- The increment identity (i) with the kernel form of the divergence. -/
theorem lip026b_increment_Gt {ε : ℝ} (hε : 0 < ε) {T : ℝ} {u : ℝ → Torus d → ℝ}
    {J : ℝ → Torus d → Tangent d} (h : IsWeakTimeDivergence T u J) (x : Torus d)
    {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) (hr : r ≤ T) :
    heatOp ε (u r) x - heatOp ε (u s) x = ∫ r' in s..r, lip026b_Gt ε J r' x := by
  rw [(heatOp_timeIncrement hε h x).2 s r hs hsr hr]
  have hae : ∀ᵐ r' ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      heatDiv ε (J r') x = lip026b_Gt ε J r' x := by
    filter_upwards [lip026b_ae_slice h.integrable_J] with r' hr'
    exact lip026b_heatDiv_eq hε (lip026b_measurable_slice h.measurable_J r') hr' x
  have hae' := (ae_restrict_iff' measurableSet_Icc).1 hae
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hae'] with r' h4 hr'
  rw [Set.uIoc_of_le hsr] at hr'
  exact h4 ⟨hs.trans hr'.1.le, hr'.2.trans hr⟩

theorem lip026b_continuous_U {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 0 ≤ T) {u : ℝ → Torus d → ℝ}
    {J : ℝ → Torus d → Tangent d} (h : IsWeakTimeDivergence T u J) (x : Torus d) :
    Continuous (fun r => heatOp ε (u (lip026b_clamp T r)) x) := by
  obtain ⟨M, hM0, hM⟩ := lip026b_kern_bound (d := d) hε
  set f : ℝ → ℝ := Set.indicator (Set.Icc 0 T) (fun r => lip026b_Gt ε J r x) with hf
  have hfi : Integrable f := by
    rw [hf, integrable_indicator_iff measurableSet_Icc]
    exact lip026b_Gt_integrableOn hε hM h x
  have hcont : Continuous (fun y => ∫ r in (0 : ℝ)..y, f r) :=
    intervalIntegral.continuous_primitive (fun a b => hfi.intervalIntegrable) 0
  have heq : ∀ r, heatOp ε (u (lip026b_clamp T r)) x =
      heatOp ε (u 0) x + ∫ r' in (0 : ℝ)..(lip026b_clamp T r), f r' := by
    intro r
    have hm := lip026b_clamp_mem hT r
    have := lip026b_increment_Gt hε h x le_rfl hm.1 hm.2
    have hint : ∫ r' in (0 : ℝ)..(lip026b_clamp T r), lip026b_Gt ε J r' x =
        ∫ r' in (0 : ℝ)..(lip026b_clamp T r), f r' := by
      refine intervalIntegral.integral_congr fun r' hr' => ?_
      rw [Set.uIcc_of_le hm.1] at hr'
      exact (Set.indicator_of_mem (s := Set.Icc 0 T) (f := fun r => lip026b_Gt ε J r x)
        (⟨hr'.1, hr'.2.trans hm.2⟩ : r' ∈ Set.Icc 0 T)).symm
    rw [← hint]
    linarith
  simp_rw [heq]
  exact continuous_const.add (hcont.comp (lip026b_continuous_clamp T))

theorem lip026b_continuous_heatOp_u {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 0 ≤ T)
    {u : ℝ → Torus d → ℝ} {J : ℝ → Torus d → Tangent d} (h : IsWeakTimeDivergence T u J)
    (r : ℝ) : Continuous (heatOp ε (u (lip026b_clamp T r))) :=
  (isC1Periodic_heatOp hε (h.integrable_u _ (lip026b_clamp_mem hT r))).continuous_torus

theorem lip026b_measurable_U {ε : ℝ} (hε : 0 < ε) {T : ℝ} (hT : 0 ≤ T)
    {u : ℝ → Torus d → ℝ} {J : ℝ → Torus d → Tangent d} (h : IsWeakTimeDivergence T u J) :
    Measurable (fun p : ℝ × Torus d => heatOp ε (u (lip026b_clamp T p.1)) p.2) :=
  measurable_uncurry_of_continuous_of_measurable
    (u := fun r x => heatOp ε (u (lip026b_clamp T r)) x)
    (fun x => lip026b_continuous_U hε hT h x)
    (fun r => (lip026b_continuous_heatOp_u hε hT h r).measurable)

theorem lip026b_bound_U {ε M : ℝ} (hε : 0 < ε) (hM0 : 0 ≤ M)
    (hM : ∀ (j : Fin d) (x w : Torus d), |lip026b_kern ε j x w| ≤ M)
    {T : ℝ} (hT : 0 ≤ T) {u : ℝ → Torus d → ℝ} {J : ℝ → Torus d → Tangent d}
    (h : IsWeakTimeDivergence T u J) :
    ∃ B : ℝ, ∀ r x, |heatOp ε (u (lip026b_clamp T r)) x| ≤ B := by
  obtain ⟨A, hA0, hA⟩ := exists_abs_le_of_continuous'
    (isC1Periodic_heatOp hε (h.integrable_u 0 ⟨le_rfl, hT⟩)).continuous_torus
  have hN := h.integrable_J.integral_norm_prod_left
  have hg : IntegrableOn (fun r => d * M * ∫ w, ‖J r w‖ ∂haar d) (Set.Icc 0 T) :=
    hN.const_mul (d * M)
  refine ⟨A + ∫ r in Set.Icc 0 T, d * M * ∫ w, ‖J r w‖ ∂haar d, fun r x => ?_⟩
  have hm := lip026b_clamp_mem hT r
  have h1 := lip026b_increment_Gt hε h x le_rfl hm.1 hm.2
  have hae := lip026b_ae_slice h.integrable_J
  have hae' := (ae_restrict_iff' measurableSet_Icc).1 hae
  have h2 : |∫ r' in (0 : ℝ)..(lip026b_clamp T r), lip026b_Gt ε J r' x| ≤
      ∫ r' in (0 : ℝ)..(lip026b_clamp T r), d * M * ∫ w, ‖J r' w‖ ∂haar d := by
    have := intervalIntegral.norm_integral_le_of_norm_le (a := 0) (b := lip026b_clamp T r)
      (μ := volume) (f := fun r' => lip026b_Gt ε J r' x)
      (g := fun r' => d * M * ∫ w, ‖J r' w‖ ∂haar d) hm.1 ?_ ?_
    · simpa using this
    · filter_upwards [hae'] with r' h3 hr'
      rw [Real.norm_eq_abs]
      exact lip026b_Gt_bound hM (h3 ⟨hr'.1.le, hr'.2.trans hm.2⟩) x
    · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hm.1]
      exact hg.mono_set (fun r' hr' => ⟨hr'.1.le, hr'.2.trans hm.2⟩)
  have h3 : ∫ r' in (0 : ℝ)..(lip026b_clamp T r), d * M * ∫ w, ‖J r' w‖ ∂haar d ≤
      ∫ r in Set.Icc 0 T, d * M * ∫ w, ‖J r w‖ ∂haar d := by
    rw [intervalIntegral.integral_of_le hm.1]
    refine setIntegral_mono_set hg ?_ ?_
    · refine Eventually.of_forall fun r' => ?_
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hM0) (integral_nonneg fun w => norm_nonneg _)
    · exact Eventually.of_forall (fun r' hr' => ⟨hr'.1.le, hr'.2.trans hm.2⟩)
  have h4 := hA x
  calc |heatOp ε (u (lip026b_clamp T r)) x|
      = |(heatOp ε (u (lip026b_clamp T r)) x - heatOp ε (u 0) x) + heatOp ε (u 0) x| := by ring_nf
    _ ≤ |heatOp ε (u (lip026b_clamp T r)) x - heatOp ε (u 0) x| + |heatOp ε (u 0) x| :=
        abs_add_le _ _
    _ ≤ _ := by rw [h1]; linarith

/-- **Integrated chain rule** (ii).  For fixed `ε > 0`, a weak solution `∂ₜu = div J` in the sense
of `IsWeakTimeDivergence`, and `H ∈ C²`, the heat-regularised `u^ε_t = heatOp ε (u t)` satisfies
`∫ H(u^ε_t) - ∫ H(u^ε_s) = -∫_s^t ∫ H''(u^ε_r) ∇u^ε_r · J^ε_r dm dr`
with `J^ε_r = heatGrad ε (J r)` (componentwise heat regularisation of the flux). -/
theorem heatOp_chain_rule_integrated {ε : ℝ} (hε : 0 < ε) {T : ℝ} {u : ℝ → Torus d → ℝ}
    {J : ℝ → Torus d → Tangent d} (h : IsWeakTimeDivergence T u J) {H : ℝ → ℝ}
    (hH : ContDiff ℝ 2 H) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    ∫ x, H (heatOp ε (u t) x) ∂haar d - ∫ x, H (heatOp ε (u s) x) ∂haar d =
      -∫ r in s..t, ∫ x, deriv (deriv H) (heatOp ε (u r) x) *
          ⟪heatOpGrad ε (u r) x, heatGrad ε (J r) x⟫ ∂haar d := by
  have hT : 0 ≤ T := hs.trans (hst.trans ht)
  have hsub : Set.Icc s t ⊆ Set.Icc 0 T := Set.Icc_subset_Icc hs ht
  have hsub' : Set.Ioc s t ⊆ Set.Icc 0 T := fun r hr => ⟨hs.trans hr.1.le, hr.2.trans ht⟩
  obtain ⟨M, hM0, hM⟩ := lip026b_kern_bound (d := d) hε
  obtain ⟨B, hB⟩ := lip026b_bound_U hε hM0 hM hT h
  have hH1 : ContDiff ℝ 1 H := hH.of_le (by norm_num)
  have hdc : Continuous (deriv H) := hH1.continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := -B) (b := B)).exists_bound_of_continuousOn
    hdc.continuousOn
  obtain ⟨Ut, hUt⟩ : ∃ Ut : ℝ → Torus d → ℝ,
      ∀ r x, Ut r x = heatOp ε (u (lip026b_clamp T r)) x := ⟨_, fun _ _ => rfl⟩
  have hpt : ∀ x, H (heatOp ε (u t) x) - H (heatOp ε (u s) x) =
      ∫ r in s..t, deriv H (Ut r x) * lip026b_Gt ε J r x := by
    intro x
    have hIG : IntervalIntegrable (fun r => lip026b_Gt ε J r x) volume s t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hst).2
        ((lip026b_Gt_integrableOn hε hM h x).mono_set hsub)
    have key := lip026b_chain_1d (U := fun r => heatOp ε (u r) x) hH1 hst hIG
      (fun r hr => by
        have := lip026b_increment_Gt hε h x hs hr.1 (hr.2.trans ht)
        linarith)
    rw [key]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hst] at hr
    simp only [hUt, lip026b_clamp_of_mem (hsub hr)]
  have hmeas : Measurable (fun p : ℝ × Torus d =>
      deriv H (Ut p.1 p.2) * lip026b_Gt ε J p.1 p.2) := by
    have hU : Measurable (fun p : ℝ × Torus d => Ut p.1 p.2) := by
      have := lip026b_measurable_U hε hT h
      simpa only [hUt] using this
    exact (hdc.measurable.comp hU).mul (lip026b_measurable_Gt hε h.measurable_J)
  have hN := h.integrable_J.integral_norm_prod_left
  have hNμ : Integrable (fun r => ∫ w, ‖J r w‖ ∂haar d) (volume.restrict (Set.Ioc s t)) :=
    hN.mono_measure (Measure.restrict_mono hsub' le_rfl)
  have hbound : Integrable (fun p : ℝ × Torus d =>
      (C * (d * M) * ∫ w, ‖J p.1 w‖ ∂haar d) * (1 : ℝ))
      ((volume.restrict (Set.Ioc s t)).prod (haar d)) :=
    (hNμ.const_mul (C * (d * M))).mul_prod
      (integrable_const (1 : ℝ) : Integrable (fun _ : Torus d => (1 : ℝ)) (haar d))
  have hae1 : ∀ᵐ r ∂(volume.restrict (Set.Ioc s t)), Integrable (fun w => ‖J r w‖) (haar d) := by
    have := (ae_restrict_iff' measurableSet_Icc).1 (lip026b_ae_slice h.integrable_J)
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [this] with r hr hrm using hr (hsub' hrm)
  have hFint : Integrable (fun p : ℝ × Torus d =>
      deriv H (Ut p.1 p.2) * lip026b_Gt ε J p.1 p.2)
      ((volume.restrict (Set.Ioc s t)).prod (haar d)) := by
    refine Integrable.mono' hbound hmeas.aestronglyMeasurable ?_
    have hq := Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Ioc s t))
      (ν := haar d)
    filter_upwards [hq.ae hae1] with p hp
    have hp' : Integrable (fun w => ‖J p.1 w‖) (haar d) := hp
    have h1 : ‖deriv H (Ut p.1 p.2)‖ ≤ C := by
      apply hC
      rw [hUt]
      exact abs_le.1 (hB _ _)
    have h2 : ‖lip026b_Gt ε J p.1 p.2‖ ≤ d * M * ∫ w, ‖J p.1 w‖ ∂haar d := by
      rw [Real.norm_eq_abs]
      exact lip026b_Gt_bound hM hp' p.2
    rw [norm_mul]
    calc ‖deriv H (Ut p.1 p.2)‖ * ‖lip026b_Gt ε J p.1 p.2‖
        ≤ C * (d * M * ∫ w, ‖J p.1 w‖ ∂haar d) :=
          mul_le_mul h1 h2 (norm_nonneg _) ((norm_nonneg _).trans h1)
      _ = _ := by ring
  have step2 : ∫ r, ∫ x, deriv H (Ut r x) * lip026b_Gt ε J r x ∂haar d
        ∂(volume.restrict (Set.Ioc s t)) =
      ∫ x, ∫ r, deriv H (Ut r x) * lip026b_Gt ε J r x ∂(volume.restrict (Set.Ioc s t))
        ∂haar d :=
    integral_integral_swap (f := fun r x => deriv H (Ut r x) * lip026b_Gt ε J r x) hFint
  have hL : ∫ x, H (heatOp ε (u t) x) ∂haar d - ∫ x, H (heatOp ε (u s) x) ∂haar d =
      ∫ x, (H (heatOp ε (u t) x) - H (heatOp ε (u s) x)) ∂haar d := by
    rw [integral_sub]
    · exact integrable_of_continuous_torus (hH1.continuous.comp
        (isC1Periodic_heatOp hε (h.integrable_u t ⟨hs.trans hst, ht⟩)).continuous_torus)
    · exact integrable_of_continuous_torus (hH1.continuous.comp
        (isC1Periodic_heatOp hε (h.integrable_u s ⟨hs, hst.trans ht⟩)).continuous_torus)
  have step1 : ∫ x, (H (heatOp ε (u t) x) - H (heatOp ε (u s) x)) ∂haar d =
      ∫ x, ∫ r, deriv H (Ut r x) * lip026b_Gt ε J r x ∂(volume.restrict (Set.Ioc s t))
        ∂haar d := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [hpt x, intervalIntegral.integral_of_le hst]
  rw [hL, step1, ← step2, intervalIntegral.integral_of_le hst, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hae1, ae_restrict_mem measurableSet_Ioc] with r hr hrm
  have hrI : r ∈ Set.Icc 0 T := hsub' hrm
  have key := lip026b_ibp_step hε (lip026b_measurable_slice h.measurable_J r) hr hH
    (ψ := heatOp ε (u r)) (isC1Periodic_heatOp hε (h.integrable_u r hrI))
  simp only [hUt, lip026b_clamp_of_mem hrI]
  exact key

end DGPS.Lipschitz.ParabolicChainRule
