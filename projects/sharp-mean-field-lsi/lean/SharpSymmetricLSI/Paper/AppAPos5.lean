import SharpSymmetricLSI.Paper.AppAPos4

/-!
# Positivity (5): classical derivatives and the integration by parts

* `dpart_appA v j`: the classical partial derivative `∂ⱼv` of a smooth periodic function.
* `lapHeat ε f = ∑ⱼ ∂ⱼ∂ⱼ e^{εΔ}f` and `∇·e^{εΔ}F = ∑ⱼ ∂ⱼ e^{εΔ}Fⱼ` almost everywhere (equal Fourier
  coefficients).
* `ibp_energy`: `∫ G'(φ)(∂ⱼ∂ⱼφ + ∂ⱼψ) = -∫ G''(φ) ∂ⱼφ (∂ⱼφ + ψ)` for smooth periodic `φ, ψ`.
-/

open MeasureTheory Set Filter Topology Complex UnitAddTorus
open scoped Real ENNReal ContDiff

namespace SharpLSI

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The classical partial derivative of a function on the torus (through the lift). -/
noncomputable def dpart_appA (v : UnitAddTorus ι → ℝ) (j : ι) (y : UnitAddTorus ι) : ℝ :=
  fderiv ℝ (v ∘ liftT) (secT y) (Pi.single j 1)

theorem dpart_comp_liftT_appA (v : UnitAddTorus ι → ℝ) (j : ι) :
    dpart_appA v j ∘ liftT = fun x => fderiv ℝ (v ∘ liftT) x (Pi.single j 1) := by
  funext x; simp only [Function.comp, dpart_appA, fderiv_lift_secT]

theorem isSmoothT_dpart {v : UnitAddTorus ι → ℝ} (hv : IsSmoothT v) (j : ι) :
    IsSmoothT (dpart_appA v j) := by
  unfold IsSmoothT
  rw [dpart_comp_liftT_appA]
  exact (hv.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

omit [DecidableEq ι] in
theorem continuous_of_isSmoothT {v : UnitAddTorus ι → ℝ} (hv : IsSmoothT v) : Continuous v :=
  (IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk).continuous_comp_iff.mp
    (show ContDiff ℝ ∞ (v ∘ liftT) from hv).continuous

theorem cf_dpart_appA {v : UnitAddTorus ι → ℝ} (hv : IsSmoothT v) (j : ι) (n : ι → ℤ) :
    cf (dpart_appA v j) n = 2 * π * I * n j * cf v n :=
  mFourierCoeff_grad_of_contDiff (hv.of_le (by simp)) n j

theorem memLp_of_continuous {v : UnitAddTorus ι → ℝ} (hv : Continuous v) (p : ℝ≥0∞) :
    MemLp v p volume := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hv.continuousOn
  exact MemLp.of_bound hv.aestronglyMeasurable C (Eventually.of_forall fun x => hC x (mem_univ x))

theorem memLp_of_abs_le {v : UnitAddTorus ι → ℝ} (hv : Measurable v) {C : ℝ}
    (hC : ∀ x, |v x| ≤ C) (p : ℝ≥0∞) : MemLp v p volume :=
  MemLp.of_bound hv.aestronglyMeasurable C (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hC x)

/-- `Δe^{εΔ}f` is the classical Laplacian a.e. -/
theorem lapHeat_ae_eq {ε : ℝ} (hε : 0 < ε) {f : UnitAddTorus ι → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ x, |f x| ≤ B) :
    lapHeat ε f =ᵐ[volume] fun y => ∑ j, dpart_appA (dpart_appA (heatT ε f) j) j y := by
  have hs : IsSmoothT (heatT ε f) := isSmoothT_heatT hε (appA_integrable_of_abs_le' hf hB)
  have hsj : ∀ j, IsSmoothT (dpart_appA (heatT ε f) j) := fun j => isSmoothT_dpart hs j
  have hsjj : ∀ j, IsSmoothT (dpart_appA (dpart_appA (heatT ε f) j) j) := fun j => isSmoothT_dpart (hsj j) j
  refine ae_eq_of_cf_eq_appA (memLp_of_abs_le ((measurable_lapHeat_joint (ρ := fun _ => f)
      (hf.comp measurable_snd)).comp (measurable_prodMk_left (x := (0 : ℝ)))) (abs_lapHeat_le hε hB) 2)
    (memLp_of_continuous (continuous_finset_sum _ fun j _ => continuous_of_isSmoothT (hsjj j)) 2)
    fun n => ?_
  rw [cf_lapHeat hε hf hB n, cf_sum _ fun j _ => (memLp_of_continuous
    (continuous_of_isSmoothT (hsjj j)) 1).integrable le_rfl]
  simp_rw [cf_dpart_appA (hsj _), cf_dpart_appA hs, cf_heatT hε hf hB]
  rw [lamN]; push_cast
  set Y : ℂ := (heatMult ε n : ℂ) * cf f n
  have hj : ∀ j, 2 * (π : ℂ) * I * n j * (2 * π * I * n j * Y) = -(4 * π ^ 2) * (n j : ℂ) ^ 2 * Y :=
    fun j => by ring_nf; rw [I_sq]; ring
  simp_rw [hj]
  rw [← Finset.sum_mul, ← Finset.mul_sum]; ring

/-- `∇·e^{εΔ}F` is the classical divergence of `e^{εΔ}F` a.e. -/
theorem divHeatT_ae_eq {ε : ℝ} (hε : 0 < ε) {F : UnitAddTorus ι → ι → ℝ}
    (hF : ∀ k, Measurable fun z => F z k) {B : ℝ} (hB : ∀ z k, |F z k| ≤ B) :
    divHeatT ε F =ᵐ[volume] fun y => ∑ j, dpart_appA (heatT ε fun z => F z j) j y := by
  have hs : ∀ j, IsSmoothT (heatT ε fun z => F z j) := fun j =>
    isSmoothT_heatT hε (appA_integrable_of_abs_le' (hF j) fun z => hB z j)
  have hsj : ∀ j, IsSmoothT (dpart_appA (heatT ε fun z => F z j) j) := fun j => isSmoothT_dpart (hs j) j
  have hdm : Measurable (divHeatT ε F) :=
    (measurable_divHeatT_joint (N := fun _ => F) hε fun k => (hF k).comp measurable_snd).comp
      (measurable_prodMk_left (x := (0 : ℝ)))
  refine ae_eq_of_cf_eq_appA (memLp_of_abs_le hdm (abs_divHeatT_le hε
      (fun k => Eventually.of_forall fun z => hB z k)) 2)
    (memLp_of_continuous (continuous_finset_sum _ fun j _ => continuous_of_isSmoothT (hsj j)) 2)
    fun n => ?_
  rw [cf_divHeatT hε hF hB n, cf_sum _ fun j _ => (memLp_of_continuous
    (continuous_of_isSmoothT (hsj j)) 1).integrable le_rfl]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cf_dpart_appA (hs j), cf_heatT hε (hF j) (fun z => hB z j)]

/-- **Periodic integration by parts** for the energy computation. -/
theorem ibp_energy {Gp Gpp : ℝ → ℝ} (hGp : ∀ r, HasDerivAt Gp (Gpp r) r) (hGpp : Continuous Gpp)
    {φ ψ : UnitAddTorus ι → ℝ} (hφ : IsSmoothT φ) (hψ : IsSmoothT ψ) (j : ι) :
    ∫ y, Gp (φ y) * (dpart_appA (dpart_appA φ j) j y + dpart_appA ψ j y) =
      -∫ y, Gpp (φ y) * (dpart_appA φ j y * (dpart_appA φ j y + ψ y)) := by
  have hderiv : deriv Gp = Gpp := funext fun r => (hGp r).deriv
  have hGp1 : ContDiff ℝ 1 Gp :=
    contDiff_one_iff_deriv.2 ⟨fun r => (hGp r).differentiableAt, by rw [hderiv]; exact hGpp⟩
  have hGpc : Continuous Gp := hGp1.continuous
  set Φ := φ ∘ liftT with hΦ
  set D := dpart_appA φ j ∘ liftT with hD
  set Ψ := ψ ∘ liftT with hΨ
  have hDs : ContDiff ℝ ∞ D := isSmoothT_dpart hφ j
  set W : UnitAddTorus ι → ℝ := fun y => Gp (φ y) * (dpart_appA φ j y + ψ y) with hW
  have hWl : W ∘ liftT = fun x => Gp (Φ x) * (D x + Ψ x) := rfl
  have hW1 : ContDiff ℝ 1 (W ∘ liftT) := by
    rw [hWl]
    exact (hGp1.comp (hφ.of_le (by simp))).mul ((hDs.add hψ).of_le (by simp))
  have h0 := integral_fderiv_torus_eq_zero hW1 (Pi.single j 1)
  have hfd : ∀ y, fderiv ℝ (W ∘ liftT) (secT y) (Pi.single j 1) =
      Gp (φ y) * (dpart_appA (dpart_appA φ j) j y + dpart_appA ψ j y) +
        Gpp (φ y) * (dpart_appA φ j y * (dpart_appA φ j y + ψ y)) := by
    intro y
    set x := secT y
    have hΦd : HasFDerivAt Φ (fderiv ℝ Φ x) x :=
      ((hφ.differentiable (by simp)) x).hasFDerivAt
    have hDd : HasFDerivAt D (fderiv ℝ D x) x := ((hDs.differentiable (by simp)) x).hasFDerivAt
    have hΨd : HasFDerivAt Ψ (fderiv ℝ Ψ x) x := ((hψ.differentiable (by simp)) x).hasFDerivAt
    have h1 := (hGp (Φ x)).comp_hasFDerivAt x hΦd
    have h2 := h1.mul (hDd.add hΨd)
    rw [hWl, show (fun x => Gp (Φ x) * (D x + Ψ x)) = (Gp ∘ Φ) * (D + Ψ) from rfl, h2.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have e1 : Φ x = φ y := by simp [hΦ, x, liftT_secT]
    have e2 : D x = dpart_appA φ j y := by simp [hD, x, liftT_secT]
    have e3 : Ψ x = ψ y := by simp [hΨ, x, liftT_secT]
    simp only [Function.comp_apply, Pi.add_apply, e1, e2, e3]
    simp only [dpart_appA, x, hD, hΨ, hΦ]
    ring
  simp_rw [hfd] at h0
  have hc : ∀ {v : UnitAddTorus ι → ℝ}, IsSmoothT v → Continuous v := fun hv => continuous_of_isSmoothT hv
  have i1 : Integrable fun y => Gp (φ y) * (dpart_appA (dpart_appA φ j) j y + dpart_appA ψ j y) :=
    (memLp_of_continuous ((hGpc.comp (hc hφ)).mul ((hc (isSmoothT_dpart (isSmoothT_dpart hφ j) j)).add
      (hc (isSmoothT_dpart hψ j)))) 1).integrable le_rfl
  have i2 : Integrable fun y => Gpp (φ y) * (dpart_appA φ j y * (dpart_appA φ j y + ψ y)) :=
    (memLp_of_continuous ((hGpp.comp (hc hφ)).mul ((hc (isSmoothT_dpart hφ j)).mul
      ((hc (isSmoothT_dpart hφ j)).add (hc hψ)))) 1).integrable le_rfl
  rw [integral_add i1 i2] at h0
  linarith

end SharpLSI
