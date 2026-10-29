import Mathlib
import DGPS.Examples.PositiveH1.Transfer
import DGPS.Analysis.ForceMultiplierH1
import DGPS.Foundations.SobolevEmbedding
import DGPS.Foundations.WeakContractions

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open DGPS
open DGPS.Examples.PositiveH1.Transfer
open DGPS.Analysis.ForceMultiplierH1
open DGPS.Examples.PositiveH1.Fourier

namespace DGPS.Examples.PositiveH1.Transfer

section torus
variable {d : ℕ}

/-- Product rule with a smooth periodic factor and an `H¹` factor. -/
theorem mul_smooth_H1 {v w : Torus d → ℝ} {h : Torus d → Tangent d}
    (hv : IsSmoothPeriodic v) (hw : IsWeakGradient w h) :
    IsWeakGradient (fun x => v x * w x) (fun x => w x • smoothGrad v x + v x • h x) where
  memLp := by
    have := memLp_mul_top (a := v) hv.memLp_top hw.memLp
    simpa [mul_comm] using this
  memLp_grad := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      hv.continuous_smoothGrad.continuousOn
    have h1 : MemLp (fun x => w x • smoothGrad v x) 2 (haar d) := by
      refine hw.memLp.of_le_mul (c := C) (hw.memLp.aestronglyMeasurable.smul
        hv.continuous_smoothGrad.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
      rw [norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right (hC x (Set.mem_univ _)) (norm_nonneg _)
    exact h1.add (memLp_smul_top hv.memLp_top hw.memLp_grad)
  ibp φ hφ j := by
    have hvφ : IsSmoothPeriodic (fun x => v x * φ x) := hv.mul hφ
    have e1 := hw.ibp _ hvφ j
    have hwt := hw.memLp
    have hhj : MemLp (fun x => h x j) 2 (haar d) := memLp_coord hw.memLp_grad j
    have s1 : IsSmoothPeriodic (fun x => v x * coordPartial j φ x) :=
      hv.mul (hφ.isSmoothPeriodic_coordPartial j)
    have s2 : IsSmoothPeriodic (fun x => coordPartial j v x * φ x) :=
      (hv.isSmoothPeriodic_coordPartial j).mul hφ
    have i1 := integrable_mul_of_memLp_two hwt s1.memLp_top
    have i2 := integrable_mul_of_memLp_two hwt s2.memLp_top
    have i3 := integrable_mul_of_memLp_two hhj hvφ.memLp_top
    simp_rw [coordPartial_mul hv hφ, mul_add] at e1
    rw [integral_add i1 i2] at e1
    have eL : (fun x => v x * w x * coordPartial j φ x)
        = fun x => w x * (v x * coordPartial j φ x) := by funext x; ring
    have eR : (fun x => (w x • smoothGrad v x + v x • h x) j * φ x)
        = fun x => w x * (coordPartial j v x * φ x) + h x j * (v x * φ x) := by
      funext x; simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, smoothGrad_apply]; ring
    rw [eL, eR, integral_add i2 i3]
    linarith

end torus

section reverse
variable (N : ℕ+)

/-- Particle gradient built from a torus gradient. -/
noncomputable def gPart (G : Torus (N : ℕ) → Tangent (N : ℕ)) :
    ParticleSpace 1 N → Fin N → Tangent 1 :=
  fun x i => WithLp.toLp 2 fun _ => G (EE N x) i

theorem EE_symm_torusLift (s : Fin N → ℝ) :
    (EE N).symm (torusLift s) = particleLift (fun i _ => s i) := by
  rw [MeasurableEquiv.symm_apply_eq]
  rfl

theorem isSmooth_comp_EE_symm {φ : ParticleSpace 1 N → ℝ} (hφ : IsSmoothPeriodicParticle φ) :
    IsSmoothPeriodic (fun y => φ ((EE N).symm y)) := by
  have : ((fun y => φ ((EE N).symm y)) ∘ torusLift) =
      (φ ∘ particleLift) ∘ (fun s : Fin N → ℝ => fun i (_ : Fin 1) => s i) := by
    funext s; simp [EE_symm_torusLift]
  unfold IsSmoothPeriodic
  rw [this]
  refine hφ.comp ?_
  exact contDiff_pi.2 fun i => contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ i

theorem transport_weak_symm {v : Torus (N : ℕ) → ℝ} {G : Torus (N : ℕ) → Tangent (N : ℕ)}
    (hg : IsWeakGradient v G) :
    IsParticleHaarWeakGradient N (fun x => v (EE N x)) (gPart N G) := by
  have hmp := mp_EE N
  refine ⟨hg.memLp.comp_measurePreserving hmp, ?_, ?_⟩
  · refine memLp_pi_iff.2 fun i => ?_
    have h2 : MemLp (fun x => G (EE N x) i) 2 (particleHaar 1 N) :=
      (memLp_coord hg.memLp_grad i).comp_measurePreserving hmp
    refine h2.of_le ?_ (Eventually.of_forall fun x => ?_)
    · have hc : Continuous fun r : ℝ => (WithLp.toLp 2 fun _ : Fin 1 => r : Tangent 1) :=
        (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).comp (continuous_pi fun _ => continuous_id)
      exact hc.comp_aestronglyMeasurable h2.aestronglyMeasurable
    · simp [gPart, EuclideanSpace.norm_eq, Real.sqrt_sq_eq_abs]
  · intro φ hφ i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    set φ' : Torus (N : ℕ) → ℝ := fun y => φ ((EE N).symm y) with hφ'def
    have hφ' : IsSmoothPeriodic φ' := isSmooth_comp_EE_symm N hφ
    have hφeq : φ = fun x => φ' (EE N x) := by
      funext x; simp [hφ'def]
    have hI := hmp.integral_comp' (fun y => v y * coordPartial i φ' y)
    have hJ := hmp.integral_comp' (fun y => G y i * φ' y)
    have := hg.ibp φ' hφ' i
    have e : ∀ x, particlePartial i 0 φ x = coordPartial i φ' (EE N x) := by
      intro x; rw [hφeq]; exact particlePartial_comp_EE N hφ' i x
    simp_rw [e]
    rw [hφeq]
    simp only [gPart]
    rw [hI, hJ]
    exact this

end reverse

section chain
open DGPS.Examples.PositiveH1.Particle

variable (κ : ℝ) (N : ℕ+)

theorem EE_symm_eq : ⇑(EE N).symm = fun (y : Torus (N : ℕ)) (i : Fin N) (_ : Fin 1) => y i := by
  funext y
  rw [MeasurableEquiv.symm_apply_eq]
  rfl

theorem continuous_EE_symm : Continuous (EE N).symm := by
  rw [EE_symm_eq]
  exact continuous_pi fun i => continuous_pi fun _ => continuous_apply i

/-- `U_N` transported to `𝕋^N`. -/
noncomputable def Ut (y : Torus (N : ℕ)) : ℝ := U κ N ((EE N).symm y)

/-- The gradient of `U_N` transported to `𝕋^N`. -/
noncomputable def Fv : Torus (N : ℕ) → Tangent (N : ℕ) := gTorus N (roughForce κ N)

/-- The weight `1/√p_N` transported to `𝕋^N`. -/
noncomputable def Wf (y : Torus (N : ℕ)) : ℝ := Real.sqrt (K κ N) * Real.exp (Ut κ N y / 2)

theorem continuous_Ut : Continuous (Ut κ N) :=
  (continuous_U κ N).comp (continuous_EE_symm N)

theorem continuous_Wf : Continuous (Wf κ N) :=
  continuous_const.mul (Real.continuous_exp.comp ((continuous_Ut κ N).div_const 2))

theorem Wf_pos (y : Torus (N : ℕ)) : 0 < Wf κ N y :=
  mul_pos (Real.sqrt_pos.2 (K_pos κ N)) (Real.exp_pos _)

theorem weak_Ut : IsWeakGradient (Ut κ N) (Fv κ N) :=
  transport_weak N (weak_rough_particle_gradient κ N).2.1

theorem weak_Wf : IsWeakGradient (Wf κ N) (fun y => (1 / 2 * Wf κ N y) • Fv κ N y) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous_Ut κ N).continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (fun _ => 0) (Set.mem_univ _))
  have hab : -C - 1 < C + 1 := by linarith
  have hr : ∀ y, Ut κ N y ∈ Set.Icc (-C - 1) (C + 1) := fun y => by
    have := abs_le.1 (by simpa using hC y (Set.mem_univ _))
    constructor <;> linarith [this.1, this.2]
  set F : ℝ → ℝ := fun s => Real.sqrt (K κ N) * Real.exp (s / 2) with hF
  have hFd : ContDiffOn ℝ ∞ F (Set.Icc (-C - 1) (C + 1)) := by
    refine ContDiff.contDiffOn ?_
    exact contDiff_const.mul (Real.contDiff_exp.comp (contDiff_id.div_const 2))
  have h := chain_rule_of_cont_rep (weak_Ut κ N) (continuous_Ut κ N) (Filter.EventuallyEq.refl _ _)
    hab hr hFd
  refine h.congr_ae (Eventually.of_forall fun y => rfl) (Eventually.of_forall fun y => ?_)
  have hd : HasDerivAt F (Real.sqrt (K κ N) * (Real.exp (Ut κ N y / 2) * (1 / 2))) (Ut κ N y) := by
    have := ((hasDerivAt_id (Ut κ N y)).div_const 2).exp.const_mul (Real.sqrt (K κ N))
    simpa using this
  beta_reduce
  rw [hd.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab _ (hr y))]
  simp only [Wf]
  congr 1
  ring

theorem Fv_eq (y : Torus (N : ℕ)) :
    Fv κ N y = κ • forceB (fun t => (EuclideanSpace.single (0 : Fin 1) (dR t) : Tangent 1) 0) y := by
  ext j
  simp only [Fv, gTorus, forceB_apply, PiLp.smul_apply, smul_eq_mul]
  rw [roughForce_apply, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [EE_symm_eq]
  have e : ((fun _ : Fin 1 => y j) - fun _ => y i) = fun _ => y j - y i := rfl
  rw [e]
  ring

/-- `‖R‖_∞`. -/
noncomputable def LR : ℝ := (eLpNorm R ⊤ (haar 1)).toReal

/-- `‖R'‖₂`. -/
noncomputable def βR : ℝ :=
  Real.sqrt (∫ t, ‖(EuclideanSpace.single (0 : Fin 1) (dR t) : Tangent 1)‖ ^ 2 ∂haar 1)

theorem force_mult {u : Torus (N : ℕ) → ℝ} {gu : Torus (N : ℕ) → Tangent (N : ℕ)}
    (hu : IsWeakGradient u gu) :
    MemLp (fun y => u y • Fv κ N y) 2 (haar (N : ℕ)) ∧
    eLpNorm (fun y => u y • Fv κ N y) 2 (haar (N : ℕ)) ≤ ENNReal.ofReal (|κ| *
      bound1 (N : ℕ) LR βR (Real.sqrt (∫ x, u x ^ 2 ∂haar (N : ℕ)))
        (Real.sqrt (∫ x, ‖gu x‖ ^ 2 ∂haar (N : ℕ)))) := by
  obtain ⟨h1, h2⟩ := stage2 (N := (N : ℕ)) N.pos weak_gradient_R hu
  have e : (fun y => u y • Fv κ N y) =
      fun y => κ • (u y • forceB (fun t => (EuclideanSpace.single (0 : Fin 1) (dR t) : Tangent 1) 0) y) := by
    funext y; rw [Fv_eq, smul_comm]
  rw [e]
  refine ⟨h1.const_smul κ, ?_⟩
  have key := eLpNorm_const_smul (μ := haar (N : ℕ)) (p := 2) (c := κ)
    (f := fun x => u x • forceB (fun t => (EuclideanSpace.single (0 : Fin 1) (dR t) : Tangent 1) 0) x)
  refine key.le.trans ?_
  rw [ENNReal.ofReal_mul (abs_nonneg κ), Real.enorm_eq_ofReal_abs]
  gcongr
  exact h2

theorem sub_wg {d : ℕ} {u v : Torus d → ℝ} {g k : Torus d → Tangent d}
    (hg : IsWeakGradient u g) (hk : IsWeakGradient v k) :
    IsWeakGradient (fun x => u x - v x) (fun x => g x - k x) :=
  (hg.add (hk.smul (-1))).congr_ae (Eventually.of_forall fun x => by ring)
    (Eventually.of_forall fun x => by simp [sub_eq_add_neg])

theorem lintegral_coord_le {d : ℕ} {F : Torus d → Tangent d} (hF : MemLp F 2 (haar d))
    (j : Fin d) : ∫⁻ y, ‖F y j‖ₑ ∂haar d ≤ eLpNorm F 2 (haar d) := by
  have hj := memLp_coord hF j
  have e := eLpNorm_one_eq_lintegral_enorm hj.aestronglyMeasurable
  have e2 := eLpNorm_le_eLpNorm_of_exponent_le (μ := haar d) (f := fun y => F y j) one_le_two
  have e3 : eLpNorm (fun y => F y j) 2 (haar d) ≤ eLpNorm F 2 (haar d) :=
    eLpNorm_mono_ae hj.aestronglyMeasurable (Eventually.of_forall fun y => PiLp.norm_apply_le (F y) j)
  calc ∫⁻ y, ‖F y j‖ₑ ∂haar d = eLpNorm (fun y => F y j) 1 (haar d) := e.symm
    _ ≤ _ := e2
    _ ≤ _ := e3

theorem tendsto_sqrt_coord {d : ℕ} {D : ℕ → Torus d → Tangent d}
    (hD : ∀ n, MemLp (D n) 2 (haar d))
    (h : ∀ j, Tendsto (fun n => eLpNorm (fun x => D n x j) 2 (haar d)) atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (∫ x, ‖D n x‖ ^ 2 ∂haar d)) atTop (𝓝 0) := by
  have e : ∀ n, Real.sqrt (∫ x, ‖D n x‖ ^ 2 ∂haar d) =
      Real.sqrt (∑ j, ((eLpNorm (fun x => D n x j) 2 (haar d)).toReal) ^ 2) := by
    intro n
    rw [integral_norm_sq_eq_sum (hD n)]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [toReal_eLpNorm_two (memLp_coord (hD n) j), Real.sq_sqrt (integral_nonneg fun x => by positivity)]
    try simp only [Real.norm_eq_abs, sq_abs]
  simp_rw [e]
  have h1 : ∀ j, Tendsto (fun n => (eLpNorm (fun x => D n x j) 2 (haar d)).toReal) atTop (𝓝 0) :=
    fun j => by simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (h j)
  have h2 := (tendsto_finsetSum Finset.univ fun j _ => (h1 j).pow 2).sqrt
  simpa using h2

theorem tendsto_sqrt_scalar {d : ℕ} {F : ℕ → Torus d → ℝ} (hF : ∀ n, MemLp (F n) 2 (haar d))
    (h : Tendsto (fun n => eLpNorm (F n) 2 (haar d)) atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (∫ x, F n x ^ 2 ∂haar d)) atTop (𝓝 0) := by
  have e : ∀ n, Real.sqrt (∫ x, F n x ^ 2 ∂haar d) = (eLpNorm (F n) 2 (haar d)).toReal := by
    intro n
    rw [toReal_eLpNorm_two (hF n)]
  simp_rw [e]
  simpa [Function.comp_def] using (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h

/-- Torus version: `Ψ ∈ H¹` implies `Ψ · Wf ∈ H¹` with the expected gradient. -/
theorem torus_main {Ψ : Torus (N : ℕ) → ℝ} {GΨ : Torus (N : ℕ) → Tangent (N : ℕ)}
    (hΨ : IsWeakGradient Ψ GΨ) :
    IsWeakGradient (fun y => Ψ y * Wf κ N y)
      (fun y => Wf κ N y • GΨ y + (1 / 2 * (Ψ y * Wf κ N y)) • Fv κ N y) := by
  obtain ⟨ψs, hs, hsw, hs2, hsg⟩ := exists_smooth_tendsto_H1 hΨ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn (continuous_Wf κ N).continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (fun _ => 0) (Set.mem_univ _))
  have hCa : ∀ y, ‖Wf κ N y‖ ≤ C := fun y => hC y (Set.mem_univ _)
  have hWm : MemLp (Wf κ N) ⊤ (haar (N : ℕ)) :=
    memLp_top_of_bound (continuous_Wf κ N).aestronglyMeasurable C (Eventually.of_forall hCa)
  have hΔ := fun n => sub_wg (hsw n) hΨ
  have hFm := (force_mult κ N hΨ).1
  have e2 : (fun y => (1 / 2 * (Ψ y * Wf κ N y)) • Fv κ N y) =
      fun y => Wf κ N y • ((1 / 2 : ℝ) • (Ψ y • Fv κ N y)) := by
    funext y; rw [smul_smul, smul_smul]; congr 1; ring
  refine IsWeakGradient.of_tendsto_L1 (U := fun n y => ψs n y * Wf κ N y)
    (G := fun n y => Wf κ N y • smoothGrad (ψs n) y + ψs n y • ((1 / 2 * Wf κ N y) • Fv κ N y))
    (memLp_mul_top hWm hΨ.memLp) ?_
    (fun n => mul_smooth_H1 (hs n) (weak_Wf κ N)) ?_ ?_
  · have h3 : MemLp (fun y => (1 / 2 : ℝ) • (Ψ y • Fv κ N y)) 2 (haar (N : ℕ)) :=
      hFm.const_smul (1 / 2 : ℝ)
    have hB : MemLp (fun y => (1 / 2 * (Ψ y * Wf κ N y)) • Fv κ N y) 2 (haar (N : ℕ)) := by
      rw [e2]; exact memLp_smul_top hWm h3
    exact (memLp_smul_top hWm hΨ.memLp_grad).add hB
  · refine tendsto_zero_of_le_two (C := C) (C' := 0) (b := fun _ => 0)
      (tendsto_lintegral_of_eLpNorm_two
        (fun n => (DGPS.Analysis.ForceMultiplier.memLp_two_of_smooth (hs n)).aestronglyMeasurable)
        hΨ.memLp.aestronglyMeasurable hs2) tendsto_const_nhds (fun n => ?_)
    exact (lintegral_mul_sub_le (a := ψs n) (b := Ψ) (w := Wf κ N)
      (Eventually.of_forall hCa)).trans (by simp)
  · intro j
    have ha : Tendsto (fun n => ∫⁻ y, ‖smoothGrad (ψs n) y j - GΨ y j‖ₑ ∂haar (N : ℕ)) atTop
        (𝓝 0) :=
      tendsto_lintegral_of_eLpNorm_two
        (fun n => (memLp_coord (hsw n).memLp_grad j).aestronglyMeasurable)
        (memLp_coord hΨ.memLp_grad j).aestronglyMeasurable (hsg j)
    have hu : Tendsto (fun n => Real.sqrt (∫ x, (ψs n x - Ψ x) ^ 2 ∂haar (N : ℕ))) atTop (𝓝 0) :=
      tendsto_sqrt_scalar (fun n => (hΔ n).memLp) hs2
    have hv : Tendsto (fun n => Real.sqrt (∫ x, ‖smoothGrad (ψs n) x - GΨ x‖ ^ 2 ∂haar (N : ℕ)))
        atTop (𝓝 0) :=
      tendsto_sqrt_coord (D := fun n x => smoothGrad (ψs n) x - GΨ x)
        (fun n => (hΔ n).memLp_grad) (fun j => by simpa using hsg j)
    have hbd : Tendsto (fun n => bound1 (N : ℕ) LR βR
        (Real.sqrt (∫ x, (ψs n x - Ψ x) ^ 2 ∂haar (N : ℕ)))
        (Real.sqrt (∫ x, ‖smoothGrad (ψs n) x - GΨ x‖ ^ 2 ∂haar (N : ℕ)))) atTop (𝓝 0) := by
      have := ((continuous_bound1 (N : ℕ)).tendsto (LR, βR, 0, 0)).comp
        (tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.prodMk_nhds (hu.prodMk_nhds hv)))
      simpa [Function.comp_def, bound1] using this
    have hb : Tendsto (fun n => eLpNorm (fun y => (ψs n y - Ψ y) • Fv κ N y) 2 (haar (N : ℕ)))
        atTop (𝓝 0) := by
      have hc : Tendsto (fun n => ENNReal.ofReal |κ| * ENNReal.ofReal (bound1 (N : ℕ) LR βR
          (Real.sqrt (∫ x, (ψs n x - Ψ x) ^ 2 ∂haar (N : ℕ)))
          (Real.sqrt (∫ x, ‖smoothGrad (ψs n) x - GΨ x‖ ^ 2 ∂haar (N : ℕ))))) atTop (𝓝 0) := by
        have h0 := ENNReal.tendsto_ofReal hbd
        have h1 := ENNReal.Tendsto.const_mul h0 (Or.inr (ENNReal.ofReal_ne_top (r := |κ|)))
        simpa using h1
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => zero_le)
        (fun n => ?_)
      have := (force_mult κ N (hΔ n)).2
      rw [ENNReal.ofReal_mul (abs_nonneg κ)] at this
      exact this
    refine tendsto_zero_of_le_two (C := C) (C' := C / 2) ha hb (fun n => ?_)
    have hmeas1 : AEMeasurable (fun y => ‖smoothGrad (ψs n) y j - GΨ y j‖ₑ) (haar (N : ℕ)) :=
      ((memLp_coord (hsw n).memLp_grad j).aestronglyMeasurable.sub
        (memLp_coord hΨ.memLp_grad j).aestronglyMeasurable).enorm
    have hfn := (force_mult κ N (hΔ n)).1
    calc ∫⁻ y, ‖(Wf κ N y • smoothGrad (ψs n) y + ψs n y • ((1 / 2 * Wf κ N y) • Fv κ N y)) j
            - (Wf κ N y • GΨ y + (1 / 2 * (Ψ y * Wf κ N y)) • Fv κ N y) j‖ₑ ∂haar (N : ℕ)
        ≤ ∫⁻ y, (ENNReal.ofReal C * ‖smoothGrad (ψs n) y j - GΨ y j‖ₑ
            + ENNReal.ofReal (C / 2) * ‖((ψs n y - Ψ y) • Fv κ N y) j‖ₑ) ∂haar (N : ℕ) := by
          refine lintegral_mono_ae ?_
          refine Eventually.of_forall fun y => ?_
          have e : (Wf κ N y • smoothGrad (ψs n) y + ψs n y • ((1 / 2 * Wf κ N y) • Fv κ N y)) j
              - (Wf κ N y • GΨ y + (1 / 2 * (Ψ y * Wf κ N y)) • Fv κ N y) j
              = Wf κ N y * (smoothGrad (ψs n) y j - GΨ y j)
                + (1 / 2 * Wf κ N y) * ((ψs n y - Ψ y) • Fv κ N y) j := by
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
          rw [e]
          refine (enorm_add_le _ _).trans ?_
          rw [enorm_mul, enorm_mul]
          have hw1 : ‖Wf κ N y‖ₑ ≤ ENNReal.ofReal C := by
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hCa y)
          have hw2 : ‖1 / 2 * Wf κ N y‖ₑ ≤ ENNReal.ofReal (C / 2) := by
            rw [← ofReal_norm]; refine ENNReal.ofReal_le_ofReal ?_
            rw [norm_mul]; have := hCa y; rw [Real.norm_eq_abs] at this ⊢; norm_num; linarith
          exact add_le_add (by gcongr) (by gcongr)
      _ = ENNReal.ofReal C * ∫⁻ y, ‖smoothGrad (ψs n) y j - GΨ y j‖ₑ ∂haar (N : ℕ)
            + ENNReal.ofReal (C / 2) *
              ∫⁻ y, ‖((ψs n y - Ψ y) • Fv κ N y) j‖ₑ ∂haar (N : ℕ) := by
          rw [lintegral_add_left' (hmeas1.const_mul _), lintegral_const_mul' _ _
            ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by
          gcongr
          exact lintegral_coord_le hfn j

theorem p_pos (x : ParticleSpace 1 N) : 0 < p κ N x :=
  mul_pos (inv_pos.2 (K_pos κ N)) (Real.exp_pos _)

theorem sqrt_p_inv (x : ParticleSpace 1 N) :
    (Real.sqrt (p κ N x))⁻¹ = Wf κ N (EE N x) := by
  have hK : 0 ≤ (K κ N)⁻¹ := (inv_pos.2 (K_pos κ N)).le
  have h2 : Real.exp (-U κ N x) = Real.exp (-U κ N x / 2) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h3 : Real.sqrt (p κ N x) = (Real.sqrt (K κ N))⁻¹ * Real.exp (-U κ N x / 2) := by
    unfold p
    rw [Real.sqrt_mul hK, Real.sqrt_inv, h2, Real.sqrt_sq (Real.exp_pos _).le]
  rw [h3, mul_inv, inv_inv, ← Real.exp_neg]
  simp only [Wf, Ut, MeasurableEquiv.symm_apply_apply]
  have h4 : -(-U κ N x / 2) = U κ N x / 2 := by ring
  rw [h4]

theorem tangentNormSq_smul (c : ℝ) (v : Fin N → Tangent 1) :
    particleTangentNormSq (fun i => c • v i) = c ^ 2 * particleTangentNormSq v := by
  unfold particleTangentNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]

/-- **H1029** (inverse ground-state map). For every real coupling `κ`, every `N`, and every
`ψ ∈ H¹(Q_N)` with Haar weak gradient `g`, the function `f = ψ/√p_N` lies in `H¹(P_N)`, with weak
gradient `(∇ψ + ½ ψ ∇U_N)/√p_N`, and `E_N(f) = ‖∇ψ + ½ ψ ∇U_N‖²_{L²(Q_N)}`. -/
theorem inverse_ground_state_map {ψ : ParticleSpace 1 N → ℝ}
    {g : ParticleSpace 1 N → Fin N → Tangent 1} (hψ : IsParticleHaarWeakGradient N ψ g) :
    ∃ hf : MemParticleH1 (kernelData κ) N (fun x => ψ x / Real.sqrt (p κ N x)),
      IsParticleWeakGradient (kernelData κ) N (fun x => ψ x / Real.sqrt (p κ N x))
        (fun x i => (Real.sqrt (p κ N x))⁻¹ • (g x i + (1 / 2 * ψ x) • roughForce κ N x i)) ∧
      particleEnergy (kernelData κ) N ⟨_, hf⟩ =
        ∫ x, particleTangentNormSq (fun i => g x i + (1 / 2 * ψ x) • roughForce κ N x i)
          ∂particleHaar 1 N := by
  have hM := torus_main κ N (transport_weak N hψ)
  have hP := transport_weak_symm N hM
  have hfun : (fun x => ψ x / Real.sqrt (p κ N x)) =
      fun x => ψ ((EE N).symm (EE N x)) * Wf κ N (EE N x) := by
    funext x
    rw [MeasurableEquiv.symm_apply_apply, ← sqrt_p_inv, div_eq_mul_inv]
  have hgrad : (fun x i => (Real.sqrt (p κ N x))⁻¹ • (g x i + (1 / 2 * ψ x) • roughForce κ N x i)) =
      gPart N (fun y => Wf κ N y • gTorus N g y +
        (1 / 2 * (ψ ((EE N).symm y) * Wf κ N y)) • Fv κ N y) := by
    funext x i
    ext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp only [gPart, gTorus, Fv, MeasurableEquiv.symm_apply_apply, PiLp.smul_apply,
      PiLp.add_apply, smul_eq_mul, sqrt_p_inv]
    ring
  have key : IsParticleWeakGradient (kernelData κ) N (fun x => ψ x / Real.sqrt (p κ N x))
      (fun x i => (Real.sqrt (p κ N x))⁻¹ • (g x i + (1 / 2 * ψ x) • roughForce κ N x i)) := by
    rw [isParticleWeakGradient_iff, hfun, hgrad]
    exact hP
  refine ⟨⟨_, key⟩, key, ?_⟩
  rw [particleEnergy_eq_of_isParticleWeakGradient (A := kernelData κ) (N := N)
    ⟨_, ⟨_, key⟩⟩ key, DGPS.Particle.integral_particleLaw]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [density_eq]
  rw [tangentNormSq_smul, inv_pow, Real.sq_sqrt (p_pos κ N x).le,
    ← mul_assoc, mul_inv_cancel₀ (p_pos κ N x).ne', one_mul]

end chain

end DGPS.Examples.PositiveH1.Transfer
