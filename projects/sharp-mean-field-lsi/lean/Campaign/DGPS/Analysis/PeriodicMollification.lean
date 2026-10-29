import DGPS.Foundations.Torus
import DGPS.Foundations.PeriodicSmoothing
import SharpSymmetricLSI.Infra.Mollify

/-!
# Periodic mollifier construction (SEM002) and strong Sobolev mollification (SEM004)

Lemma-DAG node SEM002 (`DGPS.Analysis.PeriodicMollification.periodic_mollifier_construction`).

One fixed nonnegative `C^∞` bump `phi : ℝ → ℝ` of integral one supported in `[-1, 1]` is chosen
once and for all; for `h > 0` its rescaling is `phiH h x = h⁻¹ φ(x / h)` (support in `[-h, h]`,
integral one). For a function `g` on the circle `Torus 1`, the mollification is

  `mollify h g y = ∫ s : ℝ, phiH h s * g (y - pt s)`,

i.e. convolution with the periodization of `phiH h` (realised, as in FOU002, through the periodic
lift; for `h < 1/4` the periodization has no overlap).  For a vector-valued periodic feature
`G : Torus 1 → (Fin m → ℝ)` the mollification `mollifyVec h G` is componentwise.

Lemma-DAG node SEM004 (`strong_sobolev_mollification_including_p_equals_one`): for `g` with an
`Lᵖ` weak gradient `G` (`DGPS.IsWeakGradientLp`, `1 ≤ p < ∞`, including `p = 1`), `g_h` has the weak
gradient `φ_h * G₀` (`coordPartial_mollify_of_ibp`, `isWeakGradientLp_mollify`), `‖g_h' - g'‖_p` is
bounded by the `Lᵖ` translation modulus `transModulus` (Jensen/Tonelli, `eLpNorm_mollify_sub_le`),
`‖g_h - g‖_p ≤ h ‖g'‖_p` (FTC along translations for smooth functions plus FOU002 smoothing,
`eLpNorm_translate_sub_le_weakGradient`), the modulus tends to `0` (`tendsto_transModulus`), and
hence `g_{h_j} → g` in `W^{1,p}` along any `h_j ↓ 0`, simultaneously for all `p`.

R5 notes (SEM004): the result is proved for all `1 ≤ p < ∞` (the spec asks for `1 ≤ p < 2`); the
zeroth-order bound goes through the smooth approximations `SharpLSI.moll n g` instead of an
absolutely continuous primitive; the `W^{1,p}` gradient is the scalar component `G x 0` of the
tangent vector in `Tangent 1`, and `mollifyGrad h G` is the corresponding mollified vector.

Main results:
* `phiH_nonneg`, `phiH_support`, `integral_phiH`, `contDiff_phiH`: kernel facts;
* `mollify_eq_integral_fin1`: the same integral over `ℝ^1`, as used by the legacy `SharpLSI.moll`;
* `isSmoothPeriodic_mollify`: `mollify h g` is smooth periodic for integrable `g`;
* `mollify_const`: constants are fixed (mass one);
* `periodic_mollifier_construction`: the SEM002 bundle (kernel facts, scalar smoothness for
  `0 < h < 1/4`, componentwise smoothing of continuous periodic vector features).

R5 note: FOU002's `SharpLSI.moll n` is indexed by `n` with a *different* bump at each scale
(radius `2/(n+2)`), so it is not the dilation family `h⁻¹φ(·/h)` of one fixed `φ` required here
(and SEM003 uses the exact scaling and support `[-h, h]`); only the periodic-lift conventions
and the smoothness proof pattern are reused.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff Convolution

namespace DGPS.Analysis.PeriodicMollification

/-! ### The fixed bump and its dilations -/

/-- The fixed bump: `ContDiffBump` with `rIn = 1/2`, `rOut = 1`. -/
noncomputable def bump : ContDiffBump (0 : ℝ) where
  rIn := 1 / 2
  rOut := 1
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- The fixed mollifier `φ`: nonnegative, `C^∞`, integral one, supported in `[-1, 1]`. -/
noncomputable def phi : ℝ → ℝ := bump.normed volume

theorem phi_nonneg (x : ℝ) : 0 ≤ phi x := ContDiffBump.nonneg_normed _ x

theorem integral_phi : ∫ x, phi x = 1 := ContDiffBump.integral_normed _

theorem contDiff_phi : ContDiff ℝ ∞ phi := ContDiffBump.contDiff_normed _

theorem support_phi : Function.support phi ⊆ Icc (-1 : ℝ) 1 := by
  have : Function.support phi = Metric.ball 0 1 := ContDiffBump.support_normed_eq _
  rw [this]
  intro x hx
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hx
  exact abs_lt.mp hx |>.imp (fun a => a.le) (fun b => b.le)

theorem hasCompactSupport_phi : HasCompactSupport phi := ContDiffBump.hasCompactSupport_normed _

/-- The dilation `φ_h(x) = h⁻¹ φ(x / h)`. -/
noncomputable def phiH (h : ℝ) (x : ℝ) : ℝ := h⁻¹ * phi (x / h)

theorem phiH_nonneg {h : ℝ} (hh : 0 < h) (x : ℝ) : 0 ≤ phiH h x :=
  mul_nonneg (inv_nonneg.mpr hh.le) (phi_nonneg _)

theorem contDiff_phiH {h : ℝ} (_hh : 0 < h) : ContDiff ℝ ∞ (phiH h) :=
  contDiff_const.mul (contDiff_phi.comp (contDiff_id.div_const h))

theorem phiH_support {h : ℝ} (hh : 0 < h) : Function.support (phiH h) ⊆ Icc (-h) h := by
  intro x hx
  have hx' : phi (x / h) ≠ 0 := fun e => hx (by simp [phiH, e])
  have := support_phi hx'
  rw [mem_Icc, le_div_iff₀ hh, div_le_iff₀ hh] at this
  exact ⟨by linarith [this.1], by linarith [this.2]⟩

theorem hasCompactSupport_phiH {h : ℝ} (hh : 0 < h) : HasCompactSupport (phiH h) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -h) (b := h)) ?_
  exact phiH_support hh

theorem integral_phiH {h : ℝ} (hh : 0 < h) : ∫ x, phiH h x = 1 := by
  unfold phiH
  rw [integral_const_mul, Measure.integral_comp_div, abs_of_pos hh, smul_eq_mul, integral_phi]
  field_simp

/-! ### Mollification on the circle -/

/-- The point of `Torus 1` with coordinate `x`. -/
abbrev pt (x : ℝ) : Torus 1 := DGPS.torusLift (fun _ => x)

/-- Periodic mollification `g_h = φ_h * g` of a function on the circle. -/
noncomputable def mollify (h : ℝ) (g : Torus 1 → ℝ) (y : Torus 1) : ℝ :=
  ∫ s : ℝ, phiH h s * g (y - pt s)

/-- Componentwise mollification of a vector feature `G : 𝕋 → ℝ^m`. -/
noncomputable def mollifyVec {m : ℕ} (h : ℝ) (G : Torus 1 → Fin m → ℝ) (y : Torus 1) :
    Fin m → ℝ :=
  fun i => mollify h (fun x => G x i) y

/-- The kernel as a function on `ℝ^1`. -/
noncomputable def psi (h : ℝ) (s : Fin 1 → ℝ) : ℝ := phiH h (s 0)

theorem integral_fin1 (f : ℝ → ℝ) : ∫ s : Fin 1 → ℝ, f (s 0) = ∫ t : ℝ, f t := by
  have := (volume_preserving_funUnique (Fin 1) ℝ).integral_comp' (g := f)
  simp only [MeasurableEquiv.funUnique_apply] at this
  exact this

theorem mollify_eq_integral_fin1 (h : ℝ) (g : Torus 1 → ℝ) (y : Torus 1) :
    mollify h g y = ∫ s : Fin 1 → ℝ, psi h s * g (y - DGPS.torusLift s) := by
  have key := integral_fin1 (fun t => phiH h t * g (y - pt t))
  unfold mollify psi
  rw [← key]
  congr 1
  funext s
  congr 3
  funext i
  fin_cases i
  rfl

theorem hasCompactSupport_psi {h : ℝ} (hh : 0 < h) : HasCompactSupport (psi h) :=
  (hasCompactSupport_phiH hh).comp_homeomorph (Homeomorph.funUnique (Fin 1) ℝ)

theorem contDiff_psi {h : ℝ} (hh : 0 < h) : ContDiff ℝ ∞ (psi h) :=
  (contDiff_phiH hh).comp (contDiff_apply ℝ ℝ (0 : Fin 1))

/-- Mollification, read on the periodic lift, is a convolution on `ℝ^1` with the compactly
supported smooth kernel `psi h`. -/
theorem mollify_comp_lift (h : ℝ) (g : Torus 1 → ℝ) :
    mollify h g ∘ DGPS.torusLift =
      fun x => ((g ∘ DGPS.torusLift) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] psi h) x := by
  funext x
  simp only [Function.comp, mollify_eq_integral_fin1, convolution_def,
    ContinuousLinearMap.mul_apply']
  rw [← integral_sub_left_eq_self (fun t => (g (DGPS.torusLift t)) * psi h (x - t)) volume x]
  simp only [sub_sub_cancel]
  congr 1
  funext s
  rw [show DGPS.torusLift (x - s) = DGPS.torusLift x - DGPS.torusLift s from
    SharpLSI.liftT_sub x s]
  ring

/-- `g_h` is smooth and periodic for integrable `g`. -/
theorem isSmoothPeriodic_mollify {h : ℝ} (hh : 0 < h) {g : Torus 1 → ℝ}
    (hg : Integrable g (DGPS.haar 1)) : DGPS.IsSmoothPeriodic (mollify h g) := by
  unfold DGPS.IsSmoothPeriodic
  rw [mollify_comp_lift]
  exact (hasCompactSupport_psi hh).contDiff_convolution_right _
    (SharpLSI.locallyIntegrable_comp_liftT hg) (contDiff_psi hh)

/-- Smooth periodic, for continuous `g`. -/
theorem isSmoothPeriodic_mollify_of_continuous {h : ℝ} (hh : 0 < h) {g : Torus 1 → ℝ}
    (hg : Continuous g) : DGPS.IsSmoothPeriodic (mollify h g) :=
  isSmoothPeriodic_mollify hh
    (hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

/-- Mollification fixes constants (the kernel has mass one). -/
theorem mollify_const {h : ℝ} (hh : 0 < h) (c : ℝ) (y : Torus 1) :
    mollify h (fun _ => c) y = c := by
  unfold mollify
  simp_rw [mul_comm (phiH h _) c]
  rw [integral_const_mul, integral_phiH hh, mul_one]

/-- Componentwise smoothness of the mollified vector feature (as a map on the periodic lift). -/
theorem contDiff_mollifyVec {m : ℕ} {h : ℝ} (hh : 0 < h) {G : Torus 1 → Fin m → ℝ}
    (hG : Continuous G) : ContDiff ℝ ∞ (mollifyVec h G ∘ DGPS.torusLift) := by
  refine contDiff_pi.mpr fun i => ?_
  exact isSmoothPeriodic_mollify_of_continuous hh
    ((continuous_apply i).comp hG)

/-! ### The SEM002 bundle -/

/-- **SEM002.** The fixed mollifier `φ` is a nonnegative `C^∞` function of integral one supported
in `[-1, 1]`; for every `0 < h < 1/4` the rescaling `φ_h = h⁻¹ φ(·/h)` is nonnegative, `C^∞`,
supported in `[-h, h]` with integral one; `g_h = φ_h * g` (`mollify h g`) is a smooth periodic
real function for every integrable (in particular continuous) periodic `g`, fixes constants, and
the componentwise mollification of any continuous periodic vector feature is smooth in each
component (indeed a `C^∞` map on the periodic lift). -/
theorem periodic_mollifier_construction :
    ((∀ x, 0 ≤ phi x) ∧ ContDiff ℝ ∞ phi ∧ Function.support phi ⊆ Icc (-1 : ℝ) 1 ∧
      ∫ x, phi x = 1) ∧
    ∀ h : ℝ, 0 < h → h < 1 / 4 →
      ((∀ x, 0 ≤ phiH h x) ∧ ContDiff ℝ ∞ (phiH h) ∧ Function.support (phiH h) ⊆ Icc (-h) h ∧
        ∫ x, phiH h x = 1) ∧
      (∀ g : Torus 1 → ℝ, Integrable g (DGPS.haar 1) → DGPS.IsSmoothPeriodic (mollify h g)) ∧
      (∀ g : Torus 1 → ℝ, Continuous g → DGPS.IsSmoothPeriodic (mollify h g)) ∧
      (∀ c : ℝ, ∀ y, mollify h (fun _ => c) y = c) ∧
      (∀ {m : ℕ} (G : Torus 1 → Fin m → ℝ), Continuous G →
        ∀ i, DGPS.IsSmoothPeriodic (fun y => mollifyVec h G y i)) ∧
      (∀ {m : ℕ} (G : Torus 1 → Fin m → ℝ), Continuous G →
        ContDiff ℝ ∞ (mollifyVec h G ∘ DGPS.torusLift)) := by
  refine ⟨⟨phi_nonneg, contDiff_phi, support_phi, integral_phi⟩, fun h hh _ => ?_⟩
  refine ⟨⟨phiH_nonneg hh, contDiff_phiH hh, phiH_support hh, integral_phiH hh⟩,
    fun g hg => isSmoothPeriodic_mollify hh hg,
    fun g hg => isSmoothPeriodic_mollify_of_continuous hh hg,
    mollify_const hh, ?_, ?_⟩
  · intro m G hG i
    exact isSmoothPeriodic_mollify_of_continuous hh ((continuous_apply i).comp hG)
  · intro m G hG
    exact contDiff_mollifyVec hh hG

/-! ### Translations on the circle -/

theorem pt_sub (x y : ℝ) : pt (x - y) = pt x - pt y := by
  funext i; simp [pt, DGPS.torusLift, SharpLSI.liftT]

theorem pt_add (x y : ℝ) : pt (x + y) = pt x + pt y := by
  funext i; simp [pt, DGPS.torusLift, SharpLSI.liftT]

theorem pt_zero : pt 0 = 0 := by
  funext i; simp [pt, DGPS.torusLift, SharpLSI.liftT]

theorem continuous_pt : Continuous pt :=
  SharpLSI.continuous_liftT.comp (continuous_pi fun _ => continuous_id)

theorem measurable_pt : Measurable pt := continuous_pt.measurable

theorem measurePreserving_sub_pt (a : ℝ) :
    MeasurePreserving (fun y : Torus 1 => y - pt a) (DGPS.haar 1) (DGPS.haar 1) :=
  measurePreserving_sub_right _ _

/-- Translation is an `Lᵖ` isometry. -/
theorem eLpNorm_translate {E : Type*} [NormedAddCommGroup E] (p : ℝ≥0∞) {f : Torus 1 → E}
    (hf : AEStronglyMeasurable f (DGPS.haar 1)) (a : ℝ) :
    eLpNorm (fun y => f (y - pt a)) p (DGPS.haar 1) = eLpNorm f p (DGPS.haar 1) :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_sub_pt a)

theorem aestronglyMeasurable_translate {E : Type*} [NormedAddCommGroup E] {f : Torus 1 → E}
    (hf : AEStronglyMeasurable f (DGPS.haar 1)) (a : ℝ) :
    AEStronglyMeasurable (fun y => f (y - pt a)) (DGPS.haar 1) :=
  hf.comp_measurePreserving (measurePreserving_sub_pt a)

theorem translate_congr_ae {E : Type*} {f f' : Torus 1 → E} (hf : f =ᵐ[DGPS.haar 1] f') (a : ℝ) :
    (fun y => f (y - pt a)) =ᵐ[DGPS.haar 1] fun y => f' (y - pt a) :=
  (measurePreserving_sub_pt a).quasiMeasurePreserving.ae_eq_comp hf

theorem integrable_translate {f : Torus 1 → ℝ} (hf : Integrable f (DGPS.haar 1)) (a : ℝ) :
    Integrable (fun y => f (y - pt a)) (DGPS.haar 1) :=
  (measurePreserving_sub_pt a).integrable_comp_of_integrable hf

theorem integrable_psi_mul {h : ℝ} (hh : 0 < h) {f : Torus 1 → ℝ}
    (hf : Integrable f (DGPS.haar 1)) (y : Torus 1) :
    Integrable (fun s : Fin 1 → ℝ => psi h s * f (y - DGPS.torusLift s)) := by
  have hc := (hasCompactSupport_psi hh).convolutionExists_right
    (ContinuousLinearMap.mul ℝ ℝ) (SharpLSI.locallyIntegrable_comp_liftT hf)
    (contDiff_psi hh).continuous (SharpLSI.secT y)
  have := hc.comp_sub_left (SharpLSI.secT y)
  refine this.congr (Eventually.of_forall fun s => ?_)
  simp only [ContinuousLinearMap.mul_apply', Function.comp, sub_sub_cancel]
  rw [mul_comm, SharpLSI.liftT_sub, SharpLSI.liftT_secT]


theorem integrable_phiH_mul {h : ℝ} (hh : 0 < h) {f : Torus 1 → ℝ}
    (hf : Integrable f (DGPS.haar 1)) (y : Torus 1) :
    Integrable (fun s : ℝ => phiH h s * f (y - pt s)) := by
  have := integrable_psi_mul hh hf y
  have hmp := volume_preserving_funUnique (Fin 1) ℝ
  have h2 := (hmp.integrable_comp_emb (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
    (g := fun s : ℝ => phiH h s * f (y - pt s))).mpr
  refine (hmp.integrable_comp_emb (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
    (g := fun s : ℝ => phiH h s * f (y - pt s))).mp ?_
  refine this.congr (Eventually.of_forall fun s => ?_)
  simp only [Function.comp, MeasurableEquiv.funUnique_apply, psi, pt]
  congr 3
  funext i; fin_cases i; rfl

theorem integrable_phiH {h : ℝ} (hh : 0 < h) : Integrable (phiH h) :=
  (contDiff_phiH hh).continuous.integrable_of_hasCompactSupport (hasCompactSupport_phiH hh)

theorem lintegral_ofReal_phiH {h : ℝ} (hh : 0 < h) : ∫⁻ s, ENNReal.ofReal (phiH h s) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_phiH hh)
    (Eventually.of_forall (phiH_nonneg hh)), integral_phiH hh, ENNReal.ofReal_one]

theorem mollify_congr_ae {h : ℝ} {f f' : Torus 1 → ℝ} (hf : f =ᵐ[DGPS.haar 1] f') :
    mollify h f = mollify h f' := by
  funext y
  rw [mollify_eq_integral_fin1, mollify_eq_integral_fin1]
  refine integral_congr_ae ?_
  have : (DGPS.haar 1).IsNegInvariant := Pi.isNegInvariant_volume
  have h1 : (fun x : Torus 1 => f (y - x)) =ᵐ[DGPS.haar 1] fun x => f' (y - x) :=
    ((DGPS.haar 1).measurePreserving_sub_left y).quasiMeasurePreserving.ae_eq_comp hf
  filter_upwards [SharpLSI.ae_liftT_of_ae (by exact h1)] with s hs
  try simp only at hs
  rw [hs]


theorem mollify_sub_eq {h : ℝ} (hh : 0 < h) {f : Torus 1 → ℝ} (hf : Integrable f (DGPS.haar 1))
    (y : Torus 1) :
    mollify h f y - f y = ∫ s : ℝ, phiH h s * (f (y - pt s) - f y) := by
  have h1 := integrable_phiH_mul hh hf y
  have h2 : Integrable (fun s : ℝ => phiH h s * f y) := (integrable_phiH hh).mul_const _
  have : (fun s : ℝ => phiH h s * (f (y - pt s) - f y)) =
      fun s => phiH h s * f (y - pt s) - phiH h s * f y := by funext s; ring
  rw [this, integral_sub h1 h2, integral_mul_const, integral_phiH hh, one_mul]
  rfl

/-- Jensen estimate for the mollification defect (measurable case). -/
theorem lintegral_mollify_sub_rpow_le {h : ℝ} (hh : 0 < h) {q : ℝ} (hq : 1 ≤ q)
    {f : Torus 1 → ℝ} (hfm : Measurable f) (hf : Integrable f (DGPS.haar 1)) :
    ∫⁻ y, ‖mollify h f y - f y‖ₑ ^ q ∂DGPS.haar 1 ≤
      ∫⁻ s : ℝ, ENNReal.ofReal (phiH h s) *
        ∫⁻ y, ‖f (y - pt s) - f y‖ₑ ^ q ∂DGPS.haar 1 := by
  have hφm : Measurable fun s : ℝ => ENNReal.ofReal (phiH h s) :=
    ENNReal.measurable_ofReal.comp (contDiff_phiH hh).continuous.measurable
  have hmeas : Measurable (Function.uncurry fun (y : Torus 1) (s : ℝ) =>
      ENNReal.ofReal (phiH h s) * ‖f (y - pt s) - f y‖ₑ ^ q) :=
    (hφm.comp measurable_snd).mul
      (((hfm.comp (measurable_fst.sub (measurable_pt.comp measurable_snd))).sub
        (hfm.comp measurable_fst)).enorm.pow_const q)
  calc ∫⁻ y, ‖mollify h f y - f y‖ₑ ^ q ∂DGPS.haar 1
      ≤ ∫⁻ y, (∫⁻ s : ℝ, ENNReal.ofReal (phiH h s) * ‖f (y - pt s) - f y‖ₑ ^ q) ∂DGPS.haar 1 := by
        refine lintegral_mono fun y => ?_
        rw [mollify_sub_eq hh hf]
        calc ‖∫ s : ℝ, phiH h s * (f (y - pt s) - f y)‖ₑ ^ q
            ≤ (∫⁻ s, ENNReal.ofReal (phiH h s) * ‖f (y - pt s) - f y‖ₑ) ^ q := by
              refine ENNReal.rpow_le_rpow ?_ (by linarith)
              refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
              refine lintegral_congr fun s => ?_
              rw [enorm_mul, Real.enorm_of_nonneg (phiH_nonneg hh s)]
          _ ≤ _ := DGPS.rpow_lintegral_le hq hφm.aemeasurable
              (((hfm.comp (measurable_const.sub measurable_pt)).sub
                measurable_const).enorm.aemeasurable) (lintegral_ofReal_phiH hh)
    _ = ∫⁻ s : ℝ, ∫⁻ y, ENNReal.ofReal (phiH h s) * ‖f (y - pt s) - f y‖ₑ ^ q ∂DGPS.haar 1 :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = _ := by
        refine lintegral_congr fun s => ?_
        rw [lintegral_const_mul]
        exact ((hfm.comp (measurable_id.sub measurable_const)).sub hfm).enorm.pow_const q


theorem lintegral_rpow_eq_eLpNorm_rpow {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp' : p ≠ (⊤ : ℝ≥0∞)) {E : Type*}
    [NormedAddCommGroup E] {u : Torus 1 → E} (hu : AEStronglyMeasurable u (DGPS.haar 1)) :
    ∫⁻ y, ‖u y‖ₑ ^ p.toReal ∂DGPS.haar 1 = eLpNorm u p (DGPS.haar 1) ^ p.toReal := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 hp'
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hu, ← ENNReal.rpow_mul,
    one_div_mul_cancel hq.ne', ENNReal.rpow_one]

/-- The mollification defect is controlled by the translation modulus on `[-h, h]`. -/
theorem eLpNorm_mollify_sub_le {h : ℝ} (hh : 0 < h) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ (⊤ : ℝ≥0∞))
    {f : Torus 1 → ℝ} (hf : MemLp f p (DGPS.haar 1)) {B : ℝ≥0∞}
    (hB : ∀ z : ℝ, |z| ≤ h → eLpNorm (fun y => f (y - pt z) - f y) p (DGPS.haar 1) ≤ B) :
    eLpNorm (fun y => mollify h f y - f y) p (DGPS.haar 1) ≤ B := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hp' hp
  have hq0 : 0 < p.toReal := zero_lt_one.trans_le hq
  have hfi : Integrable f (DGPS.haar 1) := hf.integrable hp
  set f' := hf.aestronglyMeasurable.mk f with hf'
  have hm : f =ᵐ[DGPS.haar 1] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hf'm : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfi' : Integrable f' (DGPS.haar 1) := hfi.congr hm
  have e1 : eLpNorm (fun y => mollify h f y - f y) p (DGPS.haar 1) =
      eLpNorm (fun y => mollify h f' y - f' y) p (DGPS.haar 1) := by
    rw [mollify_congr_ae hm]
    exact eLpNorm_congr_ae (hm.mono fun y hy => by simp [hy])
  have e2 : ∀ z : ℝ, eLpNorm (fun y => f' (y - pt z) - f' y) p (DGPS.haar 1) =
      eLpNorm (fun y => f (y - pt z) - f y) p (DGPS.haar 1) := fun z =>
    eLpNorm_congr_ae (((translate_congr_ae hm z).symm).sub hm.symm)
  rw [e1]
  have key := lintegral_mollify_sub_rpow_le hh hq hf'm hfi'
  have hbound : ∫⁻ s : ℝ, ENNReal.ofReal (phiH h s) *
        ∫⁻ y, ‖f' (y - pt s) - f' y‖ₑ ^ p.toReal ∂DGPS.haar 1 ≤ B ^ p.toReal := by
    calc _ ≤ ∫⁻ s : ℝ, ENNReal.ofReal (phiH h s) * B ^ p.toReal := by
          refine lintegral_mono fun s => ?_
          by_cases h0 : phiH h s = 0
          · simp [h0]
          · gcongr
            have hs : |s| ≤ h := by
              have := phiH_support hh (Function.mem_support.mpr h0)
              exact abs_le.mpr this
            have hmz : AEStronglyMeasurable (fun y => f' (y - pt s) - f' y) (DGPS.haar 1) :=
              ((hf'm.comp (measurable_id.sub measurable_const)).sub hf'm).aestronglyMeasurable
            rw [lintegral_rpow_eq_eLpNorm_rpow hp0 hp' hmz, e2]
            exact ENNReal.rpow_le_rpow (hB s hs) hq0.le
      _ = B ^ p.toReal := by
          rw [lintegral_mul_const (f := fun s => ENNReal.ofReal (phiH h s)) _ (ENNReal.measurable_ofReal.comp
            (contDiff_phiH hh).continuous.measurable), lintegral_ofReal_phiH hh, one_mul]
  have h3 := key.trans hbound
  have hmm : Measurable (fun y => mollify h f' y) := by
    unfold mollify
    have : Measurable (Function.uncurry fun (y : Torus 1) (s : ℝ) => phiH h s * f' (y - pt s)) := by
      have h1 : Measurable fun q : Torus 1 × ℝ => phiH h q.2 :=
        (contDiff_phiH hh).continuous.measurable.comp measurable_snd
      have h2 : Measurable fun q : Torus 1 × ℝ => f' (q.1 - pt q.2) :=
        hf'm.comp (measurable_fst.sub (measurable_pt.comp measurable_snd))
      exact h1.mul h2
    exact this.stronglyMeasurable.integral_prod_right'.measurable
  have hmeas : AEStronglyMeasurable (fun y => mollify h f' y - f' y) (DGPS.haar 1) :=
    (hmm.sub hf'm).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp' hmeas]
  calc (∫⁻ y, ‖mollify h f' y - f' y‖ₑ ^ p.toReal ∂DGPS.haar 1) ^ (1 / p.toReal)
      ≤ (B ^ p.toReal) ^ (1 / p.toReal) := ENNReal.rpow_le_rpow h3 (by positivity)
    _ = B := by rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]


/-! ### Fundamental theorem of calculus along translations -/

theorem hasDerivAt_translate {u : Torus 1 → ℝ} (hu : DGPS.IsSmoothPeriodic u) (y : Torus 1) (t : ℝ) :
    HasDerivAt (fun s : ℝ => u (y - pt s)) (-(DGPS.coordPartial 0 u (y - pt t))) t := by
  set x0 := SharpLSI.secT y with hx0
  have hv : Differentiable ℝ (u ∘ DGPS.torusLift) := hu.differentiable (by simp)
  have e1 : (fun s : ℝ => u (y - pt s)) = fun s => (u ∘ DGPS.torusLift) (x0 - fun _ : Fin 1 => s) := by
    funext s
    simp only [Function.comp, DGPS.torusLift, SharpLSI.liftT_sub, hx0, SharpLSI.liftT_secT, pt]
  have hd : HasDerivAt (fun s : ℝ => x0 - fun _ : Fin 1 => s) (0 - fun _ : Fin 1 => (1 : ℝ)) t :=
    (hasDerivAt_const t x0).sub (hasDerivAt_pi.2 fun i => hasDerivAt_id t)
  have h2 := (hv (x0 - fun _ : Fin 1 => t)).hasFDerivAt.comp_hasDerivAt t hd
  rw [e1]
  have e3 : (0 - fun _ : Fin 1 => (1 : ℝ)) = -(Pi.single (0 : Fin 1) (1 : ℝ)) := by
    funext i; fin_cases i; simp
  have e4 : DGPS.coordPartial 0 u (y - pt t) =
      fderiv ℝ (u ∘ DGPS.torusLift) (x0 - fun _ : Fin 1 => t) (Pi.single 0 1) := by
    have := congrFun (DGPS.coordPartial_comp_torusLift (0 : Fin 1) u) (x0 - fun _ : Fin 1 => t)
    simp only [Function.comp, DGPS.torusLift, SharpLSI.liftT_sub, hx0, SharpLSI.liftT_secT, pt] at this ⊢
    exact this
  rw [e4]
  rw [e3, map_neg] at h2
  exact h2

theorem continuous_coordPartial_translate {u : Torus 1 → ℝ} (hu : DGPS.IsSmoothPeriodic u) (y : Torus 1) :
    Continuous fun t : ℝ => DGPS.coordPartial 0 u (y - pt t) :=
  (hu.continuous_coordPartial 0).comp (continuous_const.sub continuous_pt)

theorem translate_sub_eq {u : Torus 1 → ℝ} (hu : DGPS.IsSmoothPeriodic u) (y : Torus 1) (z : ℝ) :
    u (y - pt z) - u y = -(z * ∫ t in Set.Ioc (0:ℝ) 1, DGPS.coordPartial 0 u (y - pt (z * t))) := by
  have h1 : ∫ t in (0:ℝ)..z, -(DGPS.coordPartial 0 u (y - pt t)) = u (y - pt z) - u (y - pt 0) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_translate hu y t)
      ((continuous_coordPartial_translate hu y).neg.intervalIntegrable _ _)
  have h2 : ∫ t in (0:ℝ)..z, DGPS.coordPartial 0 u (y - pt t) =
      z * ∫ t in (0:ℝ)..1, DGPS.coordPartial 0 u (y - pt (z * t)) := by
    have := intervalIntegral.smul_integral_comp_mul_left (a := (0:ℝ)) (b := 1)
      (fun t => DGPS.coordPartial 0 u (y - pt t)) z
    simp only [smul_eq_mul, mul_zero, mul_one] at this
    exact this.symm
  rw [intervalIntegral.integral_neg, pt_zero, sub_zero] at h1
  rw [intervalIntegral.integral_of_le zero_le_one] at h2
  rw [h2] at h1
  linarith

/-- Zeroth-order Jensen/FTC bound for smooth periodic functions. -/
theorem lintegral_translate_sub_rpow_le_smooth {u : Torus 1 → ℝ} (hu : DGPS.IsSmoothPeriodic u)
    {q : ℝ} (hq : 1 ≤ q) (z : ℝ) :
    ∫⁻ y, ‖u (y - pt z) - u y‖ₑ ^ q ∂DGPS.haar 1 ≤
      ENNReal.ofReal |z| ^ q * ∫⁻ y, ‖DGPS.coordPartial 0 u y‖ₑ ^ q ∂DGPS.haar 1 := by
  set μ : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) 1) with hμ
  have hμ1 : ∫⁻ _t, (1 : ℝ≥0∞) ∂μ = 1 := by simp [hμ]
  have hc : Continuous fun p : Torus 1 × ℝ => DGPS.coordPartial 0 u (p.1 - pt (z * p.2)) :=
    (hu.continuous_coordPartial 0).comp
      (continuous_fst.sub (continuous_pt.comp (continuous_const.mul continuous_snd)))
  have hmeas : Measurable (Function.uncurry fun (y : Torus 1) (t : ℝ) =>
      ‖DGPS.coordPartial 0 u (y - pt (z * t))‖ₑ ^ q) :=
    hc.measurable.enorm.pow_const q
  calc ∫⁻ y, ‖u (y - pt z) - u y‖ₑ ^ q ∂DGPS.haar 1
      ≤ ∫⁻ y, ENNReal.ofReal |z| ^ q * ∫⁻ t, ‖DGPS.coordPartial 0 u (y - pt (z * t))‖ₑ ^ q ∂μ
          ∂DGPS.haar 1 := by
        refine lintegral_mono fun y => ?_
        rw [translate_sub_eq hu y z, enorm_neg, enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by linarith),
          Real.enorm_eq_ofReal_abs]
        refine mul_le_mul' le_rfl ?_
        calc ‖∫ t in Set.Ioc (0:ℝ) 1, DGPS.coordPartial 0 u (y - pt (z * t))‖ₑ ^ q
            ≤ (∫⁻ t, ‖DGPS.coordPartial 0 u (y - pt (z * t))‖ₑ ∂μ) ^ q :=
              ENNReal.rpow_le_rpow (enorm_integral_le_lintegral_enorm _) (by linarith)
          _ = (∫⁻ t, 1 * ‖DGPS.coordPartial 0 u (y - pt (z * t))‖ₑ ∂μ) ^ q := by simp
          _ ≤ ∫⁻ t, 1 * ‖DGPS.coordPartial 0 u (y - pt (z * t))‖ₑ ^ q ∂μ :=
              DGPS.rpow_lintegral_le hq aemeasurable_const
                (((hu.continuous_coordPartial 0).comp
                  (continuous_const.sub (continuous_pt.comp
                    (continuous_const.mul continuous_id)))).measurable.enorm.aemeasurable) hμ1
          _ = _ := by simp
    _ = ENNReal.ofReal |z| ^ q * ∫⁻ y, ∫⁻ t, ‖DGPS.coordPartial 0 u (y - pt (z * t))‖ₑ ^ q ∂μ
          ∂DGPS.haar 1 := by
        rw [lintegral_const_mul]
        exact (hmeas.lintegral_prod_right')
    _ = ENNReal.ofReal |z| ^ q * ∫⁻ t, ∫⁻ y, ‖DGPS.coordPartial 0 u (y - pt (z * t))‖ₑ ^ q
          ∂DGPS.haar 1 ∂μ := by
        rw [lintegral_lintegral_swap hmeas.aemeasurable]
    _ = ENNReal.ofReal |z| ^ q * ∫⁻ t, ∫⁻ y, ‖DGPS.coordPartial 0 u y‖ₑ ^ q ∂DGPS.haar 1 ∂μ := by
        congr 1
        refine lintegral_congr fun t => ?_
        exact lintegral_sub_right_eq_self (μ := DGPS.haar 1)
          (fun y => ‖DGPS.coordPartial 0 u y‖ₑ ^ q) (pt (z * t))
    _ = _ := by
        rw [lintegral_const]; simp [hμ]

theorem eLpNorm_translate_sub_le_smooth {u : Torus 1 → ℝ} (hu : DGPS.IsSmoothPeriodic u)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) (z : ℝ) :
    eLpNorm (fun y => u (y - pt z) - u y) p (DGPS.haar 1) ≤
      ENNReal.ofReal |z| * eLpNorm (DGPS.coordPartial 0 u) p (DGPS.haar 1) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hq : 1 ≤ p.toReal := by
    rw [← ENNReal.toReal_one]; exact ENNReal.toReal_mono hp' hp
  have hq0 : 0 < p.toReal := zero_lt_one.trans_le hq
  have hc := hu.continuous_torus
  have hc' := hu.continuous_coordPartial 0
  have hmz : AEStronglyMeasurable (fun y => u (y - pt z) - u y) (DGPS.haar 1) :=
    ((hc.comp (continuous_id.sub continuous_const)).sub hc).aestronglyMeasurable
  have key := lintegral_translate_sub_rpow_le_smooth hu hq z
  rw [lintegral_rpow_eq_eLpNorm_rpow hp0 hp' hmz,
    lintegral_rpow_eq_eLpNorm_rpow hp0 hp' hc'.aestronglyMeasurable, ← ENNReal.mul_rpow_of_nonneg _ _ hq0.le] at key
  exact (ENNReal.rpow_le_rpow_iff hq0).mp key

theorem eLpNorm_translate_sub_le_add {p : ℝ≥0∞} (hp : 1 ≤ p) {f u : Torus 1 → ℝ}
    (hf : MemLp f p (DGPS.haar 1)) (hu : MemLp u p (DGPS.haar 1)) (z : ℝ) :
    eLpNorm (fun y => f (y - pt z) - f y) p (DGPS.haar 1) ≤
      eLpNorm (fun y => u (y - pt z) - u y) p (DGPS.haar 1) +
        2 * eLpNorm (fun y => u y - f y) p (DGPS.haar 1) := by
  have hd : MemLp (fun y => u y - f y) p (DGPS.haar 1) := hu.sub hf
  have hdt : AEStronglyMeasurable (fun y => u (y - pt z) - f (y - pt z)) (DGPS.haar 1) :=
    aestronglyMeasurable_translate hd.aestronglyMeasurable z
  have hut : AEStronglyMeasurable (fun y => u (y - pt z) - u y) (DGPS.haar 1) :=
    (aestronglyMeasurable_translate hu.aestronglyMeasurable z).sub hu.aestronglyMeasurable
  have e : (fun y => f (y - pt z) - f y) = fun y =>
      (u (y - pt z) - u y) - ((u (y - pt z) - f (y - pt z)) - (u y - f y)) := by
    funext y; ring
  rw [e]
  refine (eLpNorm_sub_le (f := fun y => u (y - pt z) - u y) hp).trans ?_
  gcongr
  refine (eLpNorm_sub_le hp).trans ?_
  rw [eLpNorm_translate p hd.aestronglyMeasurable z, two_mul]

theorem eLpNorm_translate_sub_le_weakGradient {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {g : Torus 1 → ℝ} {G : Torus 1 → DGPS.Tangent 1} (hg : DGPS.IsWeakGradientLp p g G) (z : ℝ) :
    eLpNorm (fun y => g (y - pt z) - g y) p (DGPS.haar 1) ≤
      ENNReal.ofReal |z| * eLpNorm (fun x => G x 0) p (DGPS.haar 1) := by
  have hG0 : MemLp (fun x => G x 0) p (DGPS.haar 1) := DGPS.memLp_coord_of_memLp hg.memLp_grad 0
  have hT := DGPS.tendsto_moll_W1p hp hp' hg
  have h1 := hT.1
  have h2 := hT.2 0
  have hg1 : Integrable g (DGPS.haar 1) := hg.memLp.integrable hp
  have hsm : ∀ n, DGPS.IsSmoothPeriodic (SharpLSI.moll n g) := fun n => DGPS.isSmoothPeriodic_moll n hg1
  have hmem : ∀ n, MemLp (SharpLSI.moll n g) p (DGPS.haar 1) := fun n =>
    ((hsm n).continuous_torus.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hbd : ∀ n, eLpNorm (fun y => g (y - pt z) - g y) p (DGPS.haar 1) ≤
      ENNReal.ofReal |z| * (eLpNorm (fun x => G x 0) p (DGPS.haar 1) +
        eLpNorm (fun x => coordPartial 0 (SharpLSI.moll n g) x - G x 0) p (DGPS.haar 1)) +
      2 * eLpNorm (fun y => SharpLSI.moll n g y - g y) p (DGPS.haar 1) := by
    intro n
    refine (eLpNorm_translate_sub_le_add hp hg.memLp (hmem n) z).trans ?_
    gcongr
    refine (eLpNorm_translate_sub_le_smooth (hsm n) hp hp' z).trans ?_
    gcongr
    have hc' : AEStronglyMeasurable (coordPartial 0 (SharpLSI.moll n g)) (DGPS.haar 1) :=
      ((hsm n).continuous_coordPartial 0).aestronglyMeasurable
    calc eLpNorm (coordPartial 0 (SharpLSI.moll n g)) p (DGPS.haar 1)
        = eLpNorm (fun x => (coordPartial 0 (SharpLSI.moll n g) x - G x 0) + G x 0) p (DGPS.haar 1) := by
          congr 1; funext x; ring
      _ ≤ eLpNorm (fun x => coordPartial 0 (SharpLSI.moll n g) x - G x 0) p (DGPS.haar 1) +
          eLpNorm (fun x => G x 0) p (DGPS.haar 1) :=
          eLpNorm_add_le hp
      _ = _ := add_comm _ _
  have hlim : Tendsto (fun n => ENNReal.ofReal |z| * (eLpNorm (fun x => G x 0) p (DGPS.haar 1) +
        eLpNorm (fun x => coordPartial 0 (SharpLSI.moll n g) x - G x 0) p (DGPS.haar 1)) +
      2 * eLpNorm (fun y => SharpLSI.moll n g y - g y) p (DGPS.haar 1)) atTop
      (𝓝 (ENNReal.ofReal |z| * (eLpNorm (fun x => G x 0) p (DGPS.haar 1) + 0) + 2 * 0)) := by
    refine Tendsto.add ?_ ?_
    · exact ENNReal.Tendsto.const_mul (tendsto_const_nhds.add h2) (Or.inr ENNReal.ofReal_ne_top)
    · exact ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofNat_ne_top)
  simpa using ge_of_tendsto' hlim hbd

/-! ### Continuity of translation in `Lᵖ` -/

theorem exists_real_le {ε : ℝ≥0∞} (hε : 0 < ε) : ∃ r : ℝ, 0 < r ∧ ENNReal.ofReal r ≤ ε := by
  rcases eq_or_ne ε ⊤ with rfl | h
  · exact ⟨1, one_pos, le_top⟩
  · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' h, by simp [ENNReal.ofReal_toReal h]⟩

theorem tendsto_eLpNorm_translate_sub_continuous {u : Torus 1 → ℝ} (hu : Continuous u)
    (p : ℝ≥0∞) :
    Tendsto (fun z : ℝ => eLpNorm (fun y => u (y - pt z) - u y) p (DGPS.haar 1)) (𝓝 0) (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  obtain ⟨r, hr0, hr⟩ := exists_real_le hε
  have huc : UniformContinuous u := CompactSpace.uniformContinuous_of_continuous hu
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuous_iff.1 huc (r / 2) (by positivity)
  have hpt : ∀ᶠ z : ℝ in 𝓝 0, dist (pt z) 0 < δ := by
    have := continuous_pt.tendsto 0
    rw [pt_zero] at this
    exact this (Metric.ball_mem_nhds _ hδ)
  filter_upwards [hpt] with z hz
  refine le_trans ?_ hr
  have hb : ∀ᵐ y ∂DGPS.haar 1, ‖u (y - pt z) - u y‖ ≤ r / 2 := by
    refine Eventually.of_forall fun y => ?_
    have := hδu (a := y - pt z) (b := y) (by
      rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
      simpa [dist_eq_norm] using hz)
    rw [← dist_eq_norm]; exact this.le
  have hm : AEStronglyMeasurable (fun y => u (y - pt z) - u y) (DGPS.haar 1) :=
    ((hu.comp (continuous_id.sub continuous_const)).sub hu).aestronglyMeasurable
  refine (eLpNorm_le_of_ae_bound hm hb).trans ?_
  simp only [measure_univ, ENNReal.one_rpow, one_mul]
  exact ENNReal.ofReal_le_ofReal (by linarith)

theorem tendsto_eLpNorm_translate_sub {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) {f : Torus 1 → ℝ}
    (hf : MemLp f p (DGPS.haar 1)) :
    Tendsto (fun z : ℝ => eLpNorm (fun y => f (y - pt z) - f y) p (DGPS.haar 1)) (𝓝 0) (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have h3 : 0 < ε / 3 := ENNReal.div_pos hε.ne' (by norm_num)
  have h1 := DGPS.tendsto_eLpNorm_moll_sub hp hp' hf
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.1 h1 (ε / 3) h3).exists
  have hg1 : Integrable f (DGPS.haar 1) := hf.integrable hp
  have hsm := DGPS.isSmoothPeriodic_moll n hg1
  have hmem : MemLp (SharpLSI.moll n f) p (DGPS.haar 1) :=
    hsm.continuous_torus.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  filter_upwards [ENNReal.tendsto_nhds_zero.1
    (tendsto_eLpNorm_translate_sub_continuous hsm.continuous_torus p) (ε / 3) h3] with z hz
  refine (eLpNorm_translate_sub_le_add hp hf hmem z).trans ?_
  calc _ ≤ ε / 3 + 2 * (ε / 3) := by gcongr
    _ = 3 * (ε / 3) := by ring
    _ = ε := ENNReal.mul_div_cancel (by norm_num) (by norm_num)

/-- The `Lᵖ` modulus of continuity of translations on `[-h, h]`. -/
noncomputable def transModulus (p : ℝ≥0∞) (f : Torus 1 → ℝ) (h : ℝ) : ℝ≥0∞ :=
  ⨆ z : ℝ, ⨆ _ : |z| ≤ h, eLpNorm (fun y => f (y - pt z) - f y) p (DGPS.haar 1)

theorem le_transModulus {p : ℝ≥0∞} {f : Torus 1 → ℝ} {h z : ℝ} (hz : |z| ≤ h) :
    eLpNorm (fun y => f (y - pt z) - f y) p (DGPS.haar 1) ≤ transModulus p f h :=
  le_iSup₂ (f := fun z (_ : |z| ≤ h) => eLpNorm (fun y => f (y - pt z) - f y) p (DGPS.haar 1)) z hz

theorem tendsto_transModulus {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤) {f : Torus 1 → ℝ}
    (hf : MemLp f p (DGPS.haar 1)) :
    Tendsto (transModulus p f) (𝓝[>] 0) (𝓝 0) := by
  refine ENNReal.tendsto_nhds_zero.2 fun ε hε => ?_
  have := ENNReal.tendsto_nhds_zero.1 (tendsto_eLpNorm_translate_sub hp hp' hf) ε hε
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 this
  have : Set.Ioo (0:ℝ) δ ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT hδ
  filter_upwards [this] with h hh
  refine iSup₂_le fun z hz => hδ' ?_
  rw [Real.dist_eq, sub_zero]
  exact lt_of_le_of_lt hz hh.2

/-! ### Derivatives commute with the mollification (Fourier route, as in FOU002) -/

/-- Fourier coefficients of the mollifier kernel. -/
noncomputable def kernelCoeffH (h : ℝ) (k : Fin 1 → ℤ) : ℂ :=
  ∫ s : ℝ, (phiH h s : ℂ) * UnitAddTorus.mFourier (-k) (pt s)

theorem mFourierCoeff_mollify_of_stronglyMeasurable {h : ℝ} (hh : 0 < h) {f : Torus 1 → ℝ}
    (hf : Integrable f (DGPS.haar 1)) (hfm : StronglyMeasurable f) (k : Fin 1 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun y => (mollify h f y : ℂ)) k =
      kernelCoeffH h k * UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ)) k := by
  rw [DGPS.mFourierCoeff_ofReal_eq, DGPS.mFourierCoeff_ofReal_eq]
  set e := UnitAddTorus.mFourier (-k)
  set φ := phiH h
  set F : Torus 1 → ℝ → ℂ := fun y s => (φ s : ℂ) * (e y * (f (y - pt s) : ℂ))
  have hcont : Continuous fun p : Torus 1 × ℝ => p.1 - pt p.2 :=
    continuous_fst.sub (continuous_pt.comp continuous_snd)
  have hFm : AEStronglyMeasurable (Function.uncurry F) ((DGPS.haar 1).prod volume) := by
    have h1 : StronglyMeasurable fun p : Torus 1 × ℝ => f (p.1 - pt p.2) :=
      hfm.comp_measurable hcont.measurable
    have h2 : Continuous fun p : Torus 1 × ℝ => ((φ p.2 : ℂ) * e p.1) :=
      (Complex.continuous_ofReal.comp ((contDiff_phiH hh).continuous.comp continuous_snd)).mul
        (e.continuous.comp continuous_fst)
    have := (h2.aestronglyMeasurable (μ := (DGPS.haar 1).prod volume)).mul
      (Complex.continuous_ofReal.comp_stronglyMeasurable h1).aestronglyMeasurable
    refine this.congr (Eventually.of_forall fun p => ?_)
    obtain ⟨y, s⟩ := p
    simp only [Pi.mul_apply, Function.uncurry_apply_pair, F]
    ring
  have hslice : ∀ s, Integrable (fun y => e y * (f (y - pt s) : ℂ)) (DGPS.haar 1) := fun s =>
    DGPS.integrable_mFourier_mul (hf.comp_sub_right (pt s)) (-k)
  have hnorm : ∀ s, ∫ y, ‖F y s‖ ∂DGPS.haar 1 = φ s * ∫ y, |f y| ∂DGPS.haar 1 := fun s => by
    have : ∀ y, ‖F y s‖ = φ s * |f (y - pt s)| := fun y => by
      have he : ‖e y‖ = 1 := DGPS.norm_mFourier_apply _ y
      simp [F, he, abs_of_nonneg (phiH_nonneg hh s), φ]
    simp_rw [this]
    rw [integral_const_mul, integral_sub_right_eq_self (fun y => |f y|)]
  have hF : Integrable (Function.uncurry F) ((DGPS.haar 1).prod volume) := by
    rw [integrable_prod_iff' hFm]
    refine ⟨Eventually.of_forall fun s =>
      (show Integrable (fun y => F y s) (DGPS.haar 1) from (hslice s).const_mul _), ?_⟩
    simp only [Function.uncurry_apply_pair]
    simp_rw [hnorm]
    exact (integrable_phiH hh).mul_const _
  have hinner : ∀ s, ∫ y, e y * (f (y - pt s) : ℂ) ∂DGPS.haar 1 =
      e (pt s) * ∫ y, e y * (f y : ℂ) ∂DGPS.haar 1 := fun s => by
    have := integral_sub_right_eq_self
      (μ := DGPS.haar 1) (fun y => e (y + pt s) * (f y : ℂ)) (pt s)
    simp only [sub_add_cancel] at this
    rw [this, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [e, DGPS.mFourier_add_pt]; ring
  calc ∫ y, e y * (mollify h f y : ℂ) ∂DGPS.haar 1
      = ∫ y, (∫ s, F y s) ∂DGPS.haar 1 := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [mollify, F]
        rw [← integral_complex_ofReal, ← integral_const_mul]
        congr 1; funext s; push_cast; ring
    _ = ∫ s, ∫ y, F y s ∂DGPS.haar 1 := integral_integral_swap hF
    _ = ∫ s, (φ s : ℂ) * e (pt s) * ∫ y, e y * (f y : ℂ) ∂DGPS.haar 1 := by
        congr 1; funext s
        simp only [F]
        rw [integral_const_mul, hinner, mul_assoc]
    _ = kernelCoeffH h k * ∫ y, e y * (f y : ℂ) ∂DGPS.haar 1 := by
        rw [integral_mul_const]; rfl

theorem mFourierCoeff_mollify {h : ℝ} (hh : 0 < h) {f : Torus 1 → ℝ}
    (hf : Integrable f (DGPS.haar 1)) (k : Fin 1 → ℤ) :
    UnitAddTorus.mFourierCoeff (fun y => (mollify h f y : ℂ)) k =
      kernelCoeffH h k * UnitAddTorus.mFourierCoeff (fun y => (f y : ℂ)) k := by
  have hae := hf.1.ae_eq_mk
  have h1 : mollify h f = mollify h (hf.1.mk f) := mollify_congr_ae hae
  have h2 := mFourierCoeff_mollify_of_stronglyMeasurable hh (hf.congr hae)
    hf.1.stronglyMeasurable_mk k
  rw [h1, h2, DGPS.mFourierCoeff_ofReal_eq, DGPS.mFourierCoeff_ofReal_eq f]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx]

theorem coordPartial_mollify_of_ibp {h : ℝ} (hh : 0 < h) {u gj : Torus 1 → ℝ}
    (hu1 : Integrable u (DGPS.haar 1)) (hg1 : Integrable gj (DGPS.haar 1))
    (H : ∀ φ, DGPS.IsSmoothPeriodic φ →
      ∫ x, u x * DGPS.coordPartial 0 φ x ∂DGPS.haar 1 = -∫ x, gj x * φ x ∂DGPS.haar 1) :
    DGPS.coordPartial 0 (mollify h u) = mollify h gj := by
  have hS := isSmoothPeriodic_mollify hh hu1
  have hT := isSmoothPeriodic_mollify hh hg1
  have hc1 := hS.continuous_coordPartial 0
  have hc2 := hT.continuous_torus
  have hi1 : Integrable (DGPS.coordPartial 0 (mollify h u)) (DGPS.haar 1) :=
    hc1.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (mollify h gj) (DGPS.haar 1) :=
    hc2.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hcoef : ∀ k, UnitAddTorus.mFourierCoeff (fun x =>
      ((DGPS.coordPartial 0 (mollify h u) x - mollify h gj x : ℝ) : ℂ)) k = 0 := by
    intro k
    have e1 := DGPS.mFourierCoeff_of_ibp (hS.continuous_torus.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)) hi1 0
      (fun φ hφ => DGPS.integral_mul_coordPartial_of_smooth hS hφ 0) k
    have e2 := DGPS.mFourierCoeff_of_ibp hu1 hg1 0 H k
    rw [mFourierCoeff_mollify hh hu1] at e1
    have e3 := mFourierCoeff_mollify hh hg1 k
    have hsplit : UnitAddTorus.mFourierCoeff (fun x =>
        ((DGPS.coordPartial 0 (mollify h u) x - mollify h gj x : ℝ) : ℂ)) k
        = UnitAddTorus.mFourierCoeff (fun x => (DGPS.coordPartial 0 (mollify h u) x : ℂ)) k -
          UnitAddTorus.mFourierCoeff (fun x => (mollify h gj x : ℂ)) k := by
      rw [DGPS.mFourierCoeff_ofReal_eq, DGPS.mFourierCoeff_ofReal_eq, DGPS.mFourierCoeff_ofReal_eq,
        ← integral_sub (DGPS.integrable_mFourier_mul hi1 _) (DGPS.integrable_mFourier_mul hi2 _)]
      congr 1; funext x; push_cast; ring
    rw [hsplit, e1, e3, e2]
    ring
  have hae := DGPS.ae_eq_zero_of_mFourierCoeff_eq_zero
    (DGPS.memLp_two_of_continuous (hc1.sub hc2)) hcoef
  have := (hc1.sub hc2).ae_eq_iff_eq (μ := DGPS.haar 1) continuous_const |>.mp hae
  funext x
  exact sub_eq_zero.mp (congrFun this x)

/-! ### The mollified gradient and the SEM004 bundle -/

/-- The gradient of the mollification, as a tangent vector: `φ_h * g'` in the unique coordinate. -/
noncomputable def mollifyGrad (h : ℝ) (G : Torus 1 → DGPS.Tangent 1) (y : Torus 1) :
    DGPS.Tangent 1 :=
  WithLp.toLp 2 fun _ => mollify h (fun x => G x 0) y

@[simp] theorem mollifyGrad_apply (h : ℝ) (G : Torus 1 → DGPS.Tangent 1) (y : Torus 1) (j : Fin 1) :
    mollifyGrad h G y j = mollify h (fun x => G x 0) y := rfl

theorem isWeakGradientLp_mollify {h : ℝ} (hh : 0 < h) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {g : Torus 1 → ℝ} {G : Torus 1 → DGPS.Tangent 1} (hg : DGPS.IsWeakGradientLp p g G) :
    DGPS.coordPartial 0 (mollify h g) = mollify h (fun x => G x 0) ∧
      DGPS.IsWeakGradientLp p (mollify h g) (mollifyGrad h G) := by
  have hg1 : Integrable g (DGPS.haar 1) := hg.memLp.integrable hp
  have hG1 : Integrable (fun x => G x 0) (DGPS.haar 1) :=
    (DGPS.memLp_coord_of_memLp hg.memLp_grad 0).integrable hp
  have hS := isSmoothPeriodic_mollify hh hg1
  have hT := isSmoothPeriodic_mollify hh hG1
  have hder := coordPartial_mollify_of_ibp hh hg1 hG1 (fun φ hφ => hg.ibp φ hφ 0)
  refine ⟨hder, ?_, ?_, ?_⟩
  · exact hS.continuous_torus.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · have hc : Continuous (mollifyGrad h G) :=
      (PiLp.continuous_toLp 2 _).comp (continuous_pi fun _ => hT.continuous_torus)
    exact hc.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · intro φ hφ j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    rw [DGPS.integral_mul_coordPartial_of_smooth hS hφ 0, hder]
    simp

theorem mollify_estimates {h : ℝ} (hh : 0 < h) {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ⊤)
    {g : Torus 1 → ℝ} {G : Torus 1 → DGPS.Tangent 1} (hg : DGPS.IsWeakGradientLp p g G) :
    eLpNorm (fun y => mollifyGrad h G y 0 - G y 0) p (DGPS.haar 1) ≤
          transModulus p (fun x => G x 0) h ∧
        eLpNorm (fun y => mollify h g y - g y) p (DGPS.haar 1) ≤
          ENNReal.ofReal h * eLpNorm (fun x => G x 0) p (DGPS.haar 1) := by
  have hG0 : MemLp (fun x => G x 0) p (DGPS.haar 1) := DGPS.memLp_coord_of_memLp hg.memLp_grad 0
  refine ⟨?_, ?_⟩
  · simpa only [mollifyGrad_apply] using
      eLpNorm_mollify_sub_le hh hp hp' hG0 (fun z hz => le_transModulus (f := fun x => G x 0) hz)
  · refine eLpNorm_mollify_sub_le hh hp hp' hg.memLp (fun z hz => ?_)
    refine (eLpNorm_translate_sub_le_weakGradient hp hp' hg z).trans ?_
    gcongr

/-- **SEM004.**  Strong `W^{1,p}` mollification, `1 ≤ p < ∞` (in particular `p = 1` and `1 ≤ p < 2`),
on `𝕋¹`.  Let `g` have weak gradient `G` in `Lᵖ` (`IsWeakGradientLp`), and write `g' = G · 0`.
(1) For `h > 0`, `g_h = mollify h g` is smooth periodic, `∂₀ g_h = φ_h * g'` and `g_h` has the weak
gradient `φ_h * g'`, in `Lᵖ`.
(2) `‖g_h' − g'‖_p ≤ sup_{|z| ≤ h} ‖τ_z g' − g'‖_p` and `‖g_h − g‖_p ≤ h ‖g'‖_p`.
(3) the `Lᵖ` translation modulus tends to `0` as `h → 0⁺` (continuity of translation in `Lᵖ`).
(4) Hence for *any* sequence `h_j ↓ 0` (one sequence serves all `p` simultaneously)
`g_{h_j} → g` and `g_{h_j}' → g'` in `Lᵖ`, i.e. `g_{h_j} → g` strongly in `W^{1,p}`. -/
theorem strong_sobolev_mollification_including_p_equals_one :
    (∀ (h : ℝ), 0 < h → ∀ (p : ℝ≥0∞), 1 ≤ p → ∀ (g : Torus 1 → ℝ) (G : Torus 1 → DGPS.Tangent 1),
      DGPS.IsWeakGradientLp p g G →
        DGPS.IsSmoothPeriodic (mollify h g) ∧
        DGPS.coordPartial 0 (mollify h g) = mollify h (fun x => G x 0) ∧
        DGPS.IsWeakGradientLp p (mollify h g) (mollifyGrad h G)) ∧
    (∀ (h : ℝ), 0 < h → ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ → ∀ (g : Torus 1 → ℝ)
      (G : Torus 1 → DGPS.Tangent 1), DGPS.IsWeakGradientLp p g G →
        eLpNorm (fun y => mollifyGrad h G y 0 - G y 0) p (DGPS.haar 1) ≤
          transModulus p (fun x => G x 0) h ∧
        eLpNorm (fun y => mollify h g y - g y) p (DGPS.haar 1) ≤
          ENNReal.ofReal h * eLpNorm (fun x => G x 0) p (DGPS.haar 1)) ∧
    (∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ → ∀ (f : Torus 1 → ℝ), MemLp f p (DGPS.haar 1) →
      Tendsto (transModulus p f) (𝓝[>] 0) (𝓝 0)) ∧
    (∀ (hs : ℕ → ℝ), (∀ j, 0 < hs j) → Tendsto hs atTop (𝓝 0) →
      ∀ (p : ℝ≥0∞), 1 ≤ p → p ≠ ⊤ → ∀ (g : Torus 1 → ℝ) (G : Torus 1 → DGPS.Tangent 1),
        DGPS.IsWeakGradientLp p g G →
          Tendsto (fun j => eLpNorm (fun y => mollify (hs j) g y - g y) p (DGPS.haar 1))
            atTop (𝓝 0) ∧
          Tendsto (fun j => eLpNorm (fun y => mollifyGrad (hs j) G y 0 - G y 0) p (DGPS.haar 1))
            atTop (𝓝 0)) := by
  refine ⟨fun h hh p hp g G hg => ?_, fun h hh p hp hp' g G hg => ?_, fun p hp hp' f hf =>
    tendsto_transModulus hp hp' hf, fun hs hpos hlim p hp hp' g G hg => ?_⟩
  · have hg1 : Integrable g (DGPS.haar 1) := hg.memLp.integrable hp
    obtain ⟨h1, h2⟩ := isWeakGradientLp_mollify hh hp hg
    exact ⟨isSmoothPeriodic_mollify hh hg1, h1, h2⟩
  · exact mollify_estimates hh hp hp' hg
  · have hG0 : MemLp (fun x => G x 0) p (DGPS.haar 1) := DGPS.memLp_coord_of_memLp hg.memLp_grad 0
    have hev : ∀ᶠ j in atTop, 0 < hs j := Eventually.of_forall hpos
    have hlim' : Tendsto hs atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.2 ⟨hlim, hev⟩
    have hmod := (tendsto_transModulus hp hp' hG0).comp hlim'
    have hlin : Tendsto (fun j => ENNReal.ofReal (hs j) * eLpNorm (fun x => G x 0) p (DGPS.haar 1))
        atTop (𝓝 0) := by
      have h0 : Tendsto (fun j => ENNReal.ofReal (hs j)) atTop (𝓝 0) := by
        simpa using ENNReal.tendsto_ofReal hlim
      have := ENNReal.Tendsto.mul_const h0 (Or.inr hG0.eLpNorm_ne_top)
      simpa using this
    refine ⟨?_, ?_⟩
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlin
        (fun _ => bot_le) (fun j => ?_)
      exact ((mollify_estimates (hpos j) hp hp' hg)).2
    · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hmod
        (fun _ => bot_le) (fun j => ?_)
      exact ((mollify_estimates (hpos j) hp hp' hg)).1

end DGPS.Analysis.PeriodicMollification
