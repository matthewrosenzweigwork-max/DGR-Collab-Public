import Mathlib
import DGPS.Examples.PositiveH1.TransferCommonTail
import DGPS.Examples.PositiveH1.TransferEntropyChange

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open DGPS
open DGPS.Examples.PositiveH1.Particle DGPS.Examples.PositiveH1.Fourier
open DGPS.Examples.PositiveH1.Model

/-!
# H1036: full-domain Dirichlet transfer

For `f ∈ H¹(P_N)` (at `κ = 1/100`) and `g = f h_{N,M}`, the weak gradient of `g` is
`h_{N,M} (∇f - ½ f ∇T_{N,M})`, so that
`E_{N,M}(g) = ∫ |∇f - ½ f ∇T_{N,M}|² dP_N`, and for every `η > 0`
`E_{N,M}(g) ≤ (1+η) E_N(f) + (1+η⁻¹) ε_M (E_N(f) + ‖f‖₂²) / 4`.
Main result: `full_domain_dirichlet_transfer`.
-/

namespace DGPS.Examples.PositiveH1.Transfer

theorem coordPartial_const_exp_half {d : ℕ} {P : Torus d → ℝ} (hP : IsSmoothPeriodic P) (c : ℝ)
    (j : Fin d) (y : Torus d) :
    coordPartial j (fun x => c * Real.exp (P x / 2)) y =
      1 / 2 * (c * Real.exp (P y / 2)) * coordPartial j P y := by
  have h1 : DifferentiableAt ℝ (P ∘ SharpLSI.liftT) (SharpLSI.secT y) :=
    (hP.differentiable (by simp)) _
  have h2 : ((fun x => c * Real.exp (P x / 2)) ∘ SharpLSI.liftT) =
      fun s => c * Real.exp ((P ∘ SharpLSI.liftT) s / 2) := rfl
  have h3 : HasFDerivAt (fun s => (P ∘ SharpLSI.liftT) s / 2)
      ((1 / 2 : ℝ) • fderiv ℝ (P ∘ SharpLSI.liftT) (SharpLSI.secT y)) (SharpLSI.secT y) := by
    have := h1.hasFDerivAt.const_smul (1 / 2 : ℝ)
    convert this using 1
    funext s
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hd := (h3.exp).const_mul c
  unfold coordPartial
  rw [h2, hd.fderiv]
  simp only [smul_apply, smul_eq_mul, Function.comp_apply, SharpLSI.liftT_secT]
  ring

theorem smoothGrad_wtM (N : ℕ+) (M : ℕ) (y : Torus (N : ℕ)) :
    smoothGrad (wtM N M) y = (1 / 2 * wtM N M y) • smoothGrad (PhiM N M) y := by
  ext j
  simp only [smoothGrad_apply, PiLp.smul_apply, smul_eq_mul]
  have := coordPartial_const_exp_half (isSmooth_PhiM N M) (Real.sqrt (KM N M)) j y
  unfold wtM
  rw [this]

/-- A weak gradient of `T_{N,M}` (transported from the torus). -/
noncomputable def gradTail (N : ℕ+) (M : ℕ) : ParticleSpace 1 N → Fin N → Tangent 1 :=
  gPart N (fun y => Fv (1 / 100) N y - smoothGrad (PhiM N M) y)

theorem isWeakGradient_gradTail (N : ℕ+) (M : ℕ) :
    IsParticleHaarWeakGradient N (tailT (1 / 100) N M) (gradTail N M) := by
  have h1 : IsWeakGradient (fun y => Ut (1 / 100) N y - PhiM N M y)
      (fun y => Fv (1 / 100) N y - smoothGrad (PhiM N M) y) :=
    sub_wg (weak_Ut _ _) (isSmooth_PhiM N M).isWeakGradient
  have h2 := transport_weak_symm N h1
  have e : (fun x => Ut (1 / 100) N (EE N x) - PhiM N M (EE N x)) = tailT (1 / 100) N M := by
    funext x
    rw [← U_sub_UM (1 / 100) N M x, UM_eq_PhiM]
    simp [Ut]
  rw [e] at h2
  exact h2


/-- The gradient `h (∇f - ½ f ∇T)` of `g = f h_{N,M}`. -/
noncomputable def gradG (N : ℕ+) (M : ℕ) (f : ParticleH1 (kernelData (1 / 100)) N) :
    ParticleSpace 1 N → Fin N → Tangent 1 :=
  fun x i => hNM N M x • (particleWeakGradient f x i - (1 / 2 * f x) • gradTail N M x i)

theorem hNM_eq_mul_wtM (N : ℕ+) (M : ℕ) (x : ParticleSpace 1 N) :
    hNM N M x = Real.sqrt (p (1 / 100) N x) * wtM N M (EE N x) := by
  rw [hNM_eq, ← sqrt_pM_inv]

theorem isWeakGradient_gradG (N : ℕ+) (M : ℕ) (f : ParticleH1 (kernelData (1 / 100)) N) :
    IsParticleHaarWeakGradient N (fun x => f x * hNM N M x) (gradG N M f) := by
  have hgf := isParticleWeakGradient_particleWeakGradient f
  have hψ := (ground_state_map_on_every_rough_particle_test N f.1 f.2 _ hgf).2.1
  have h := mul_smooth_H1 (isSmooth_wtM N M) (transport_weak N hψ)
  have hP := transport_weak_symm N h
  have hfun : (fun x => f x * hNM N M x) = fun x => wtM N M (EE N x) *
      (f ((EE N).symm (EE N x)) * Real.sqrt (p (1 / 100) N ((EE N).symm (EE N x)))) := by
    funext x
    rw [MeasurableEquiv.symm_apply_apply, hNM_eq_mul_wtM]
    ring
  have hgrad : gradG N M f = gPart N (fun y =>
      (f ((EE N).symm y) * Real.sqrt (p (1 / 100) N ((EE N).symm y))) • smoothGrad (wtM N M) y +
        wtM N M y • gTorus N (fun x i => Real.sqrt (p (1 / 100) N x) • particleWeakGradient f x i -
          ((1 / 2 : ℝ) * (f x * Real.sqrt (p (1 / 100) N x))) • roughForce (1 / 100) N x i) y) := by
    funext x i
    ext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp only [gradG, gradTail, gPart, gTorus, Fv, MeasurableEquiv.symm_apply_apply,
      PiLp.smul_apply, PiLp.add_apply, PiLp.sub_apply, smul_eq_mul, smoothGrad_wtM,
      hNM_eq_mul_wtM]
    ring
  rw [hfun, hgrad]
  exact hP


theorem normSq_gradG (N : ℕ+) (M : ℕ) (f : ParticleH1 (kernelData (1 / 100)) N)
    (x : ParticleSpace 1 N) :
    particleDensity (positiveH1Cutoff M) N x * particleTangentNormSq (gradG N M f x) =
      particleDensity (kernelData (1 / 100)) N x * particleTangentNormSq
        (fun i => particleWeakGradient f x i - (1 / 2 * f x) • gradTail N M x i) := by
  have h := DGPS.Particle.particleDensity_pos (positiveH1Cutoff M) N x
  unfold gradG
  rw [tangentNormSq_smul, hNM_sq, ← mul_assoc]
  field_simp

theorem energy_cutoff_eq (N : ℕ+) (M : ℕ) (f : ParticleH1 (kernelData (1 / 100)) N)
    (hg : MemParticleH1 (positiveH1Cutoff M) N (fun x => f x * hNM N M x)) :
    particleEnergy (positiveH1Cutoff M) N ⟨_, hg⟩ =
      ∫ x, particleTangentNormSq
        (fun i => particleWeakGradient f x i - (1 / 2 * f x) • gradTail N M x i)
        ∂particleLaw (kernelData (1 / 100)) N := by
  have hG := (isParticleWeakGradient_iff (positiveH1Cutoff M) N _ _).2 (isWeakGradient_gradG N M f)
  rw [particleEnergy_eq_of_isParticleWeakGradient (A := positiveH1Cutoff M) ⟨_, hg⟩ hG,
    DGPS.Particle.integral_particleLaw, DGPS.Particle.integral_particleLaw]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => normSq_gradG N M f x)

theorem integrable_normSq_diff (N : ℕ+) (M : ℕ) (f : ParticleH1 (kernelData (1 / 100)) N) :
    Integrable (fun x => particleTangentNormSq
        (fun i => particleWeakGradient f x i - (1 / 2 * f x) • gradTail N M x i))
      (particleLaw (kernelData (1 / 100)) N) := by
  rw [integrable_law_iff]
  have hK := K_pos (1 / 100 : ℝ) N
  have hKM := KM_pos N M
  have hI := integrable_particleTangentNormSq (isWeakGradient_gradG N M f).memLp_grad
  have hT : Continuous (tailT (1 / 100) N M) := by
    have : tailT (1 / 100) N M = fun x => U (1 / 100) N x - UM (1 / 100) N M x := by
      funext x; rw [U_sub_UM]
    rw [this]; exact (continuous_U _ N).sub (continuous_UM N M)
  have hq : Continuous fun x => K (1 / 100) N / KM N M * Real.exp (tailT (1 / 100) N M x) :=
    continuous_const.mul (Real.continuous_exp.comp hT)
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hq.continuousOn
  have h := hI.mul_bdd hq.aestronglyMeasurable (c := C)
    (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ _))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  have hr : hNM N M x ^ 2 = KM N M / K (1 / 100) N * Real.exp (-tailT (1 / 100) N M x) := by
    rw [hNM_sq, ratio_eq]
  have e : particleTangentNormSq (gradG N M f x) = hNM N M x ^ 2 * particleTangentNormSq
      (fun i => particleWeakGradient f x i - (1 / 2 * f x) • gradTail N M x i) := by
    unfold gradG; rw [tangentNormSq_smul]
  show particleTangentNormSq (gradG N M f x) *
      (K (1 / 100) N / KM N M * Real.exp (tailT (1 / 100) N M x)) = _
  rw [e, hr]
  have : Real.exp (-tailT (1 / 100) N M x) * Real.exp (tailT (1 / 100) N M x) = 1 := by
    rw [← Real.exp_add]; simp
  field_simp
  rw [mul_right_comm, this, one_mul]


theorem normSq_sub_le (N : ℕ+) {η : ℝ} (hη : 0 < η) (a b : Fin N → Tangent 1) :
    particleTangentNormSq (fun i => a i - b i) ≤
      (1 + η) * particleTangentNormSq a + (1 + η⁻¹) * particleTangentNormSq b := by
  unfold particleTangentNormSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  set s := ‖a i‖
  set t := ‖b i‖
  have hs : 0 ≤ s := norm_nonneg _
  have ht : 0 ≤ t := norm_nonneg _
  have h1 : ‖a i - b i‖ ^ 2 ≤ (s + t) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
  have h2 : 2 * s * t ≤ η * s ^ 2 + η⁻¹ * t ^ 2 := by
    have : η * s ^ 2 + η⁻¹ * t ^ 2 - 2 * s * t = η⁻¹ * (η * s - t) ^ 2 := by
      field_simp
      ring
    have h3 : 0 ≤ η⁻¹ * (η * s - t) ^ 2 := by positivity
    linarith
  nlinarith

theorem integrable_sq_mul_normSq_tail (N : ℕ+) (M : ℕ) (f : ParticleH1 (kernelData (1 / 100)) N) :
    Integrable (fun x => f x ^ 2 * particleTangentNormSq (gradTail N M x))
      (particleLaw (kernelData (1 / 100)) N) := by
  have hgf := isParticleWeakGradient_particleWeakGradient f
  have hac : particleLaw (kernelData (1 / 100)) N ≪ particleHaar 1 N :=
    withDensity_absolutelyContinuous _ _
  have hA : Integrable (fun x => particleTangentNormSq (particleWeakGradient f x))
      (particleLaw (kernelData (1 / 100)) N) := integrable_particleTangentNormSq hgf.memLp_grad
  have hD := integrable_normSq_diff N M f
  have hGm : AEStronglyMeasurable (fun x => particleTangentNormSq (gradTail N M x))
      (particleLaw (kernelData (1 / 100)) N) :=
    (integrable_particleTangentNormSq
      (isWeakGradient_gradTail N M).memLp_grad).aestronglyMeasurable.mono_ac hac
  have hfm : AEStronglyMeasurable (fun x => f x ^ 2) (particleLaw (kernelData (1 / 100)) N) :=
    hgf.memLp.aestronglyMeasurable.pow 2
  refine Integrable.mono' ((hA.const_mul 8).add (hD.const_mul 8)) (hfm.mul hGm)
    (Filter.Eventually.of_forall fun x => ?_)
  have hn : 0 ≤ f x ^ 2 * particleTangentNormSq (gradTail N M x) :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [Real.norm_of_nonneg hn]
  set a := particleWeakGradient f x
  have e1 : particleTangentNormSq (fun i => (1 / 2 * f x) • gradTail N M x i) =
      (1 / 2 * f x) ^ 2 * particleTangentNormSq (gradTail N M x) := tangentNormSq_smul N _ _
  have e2 : particleTangentNormSq (fun i => (1 / 2 * f x) • gradTail N M x i) ≤
      2 * particleTangentNormSq a +
        2 * particleTangentNormSq (fun i => a i - (1 / 2 * f x) • gradTail N M x i) := by
    have := normSq_sub_le N (η := 1) one_pos a (fun i => a i - (1 / 2 * f x) • gradTail N M x i)
    simp only [sub_sub_cancel] at this
    norm_num at this ⊢
    linarith
  simp only [Pi.add_apply]
  nlinarith [Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖a i‖)]

theorem full_domain_dirichlet_transfer (N : ℕ+) (M : ℕ) (hM : 2 ≤ M)
    (f : ParticleH1 (kernelData (1 / 100)) N) :
    ∃ hg : MemParticleH1 (positiveH1Cutoff M) N (fun x => f x * hNM N M x),
      (∃ G, IsParticleHaarWeakGradient N (tailT (1 / 100) N M) G) ∧
      (∀ G, IsParticleHaarWeakGradient N (tailT (1 / 100) N M) G →
        particleEnergy (positiveH1Cutoff M) N ⟨_, hg⟩ =
          ∫ x, particleTangentNormSq (fun i => particleWeakGradient f x i - (1 / 2 * f x) • G x i)
            ∂particleLaw (kernelData (1 / 100)) N) ∧
      ∀ η : ℝ, 0 < η →
        particleEnergy (positiveH1Cutoff M) N ⟨_, hg⟩ ≤
          (1 + η) * particleEnergy (kernelData (1 / 100)) N f +
            (1 + η⁻¹) * (h1033_eps M * (particleEnergy (kernelData (1 / 100)) N f +
              ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N) / 4) := by
  have hg : MemParticleH1 (positiveH1Cutoff M) N (fun x => f x * hNM N M x) :=
    ⟨_, (isParticleWeakGradient_iff (positiveH1Cutoff M) N _ _).2 (isWeakGradient_gradG N M f)⟩
  have hac : particleLaw (kernelData (1 / 100)) N ≪ particleHaar 1 N :=
    withDensity_absolutelyContinuous _ _
  have hE := energy_cutoff_eq N M f hg
  refine ⟨hg, ⟨_, isWeakGradient_gradTail N M⟩, fun G hG => ?_, fun η hη => ?_⟩
  · rw [hE]
    have hx := hac.ae_le ((isWeakGradient_gradTail N M).ae_eq hG)
    refine integral_congr_ae ?_
    filter_upwards [hx] with x hx
    rw [hx]
  · have hgf := isParticleWeakGradient_particleWeakGradient f
    have hA : Integrable (fun x => particleTangentNormSq (particleWeakGradient f x))
        (particleLaw (kernelData (1 / 100)) N) := integrable_particleTangentNormSq hgf.memLp_grad
    have hD := integrable_normSq_diff N M f
    have hT := integrable_sq_mul_normSq_tail N M f
    have hb := ((common_vanishing_tail_coefficient.2 N M hM f).2 _
      (isWeakGradient_gradTail N M))
    have hpt : ∀ x, particleTangentNormSq
        (fun i => particleWeakGradient f x i - (1 / 2 * f x) • gradTail N M x i) ≤
        (1 + η) * particleTangentNormSq (particleWeakGradient f x) +
          (1 + η⁻¹) / 4 * (f x ^ 2 * particleTangentNormSq (gradTail N M x)) := by
      intro x
      have h := normSq_sub_le N hη (particleWeakGradient f x)
        (fun i => (1 / 2 * f x) • gradTail N M x i)
      rw [tangentNormSq_smul] at h
      refine h.trans (le_of_eq ?_)
      ring
    have hI : Integrable (fun x => (1 + η) * particleTangentNormSq (particleWeakGradient f x) +
        (1 + η⁻¹) / 4 * (f x ^ 2 * particleTangentNormSq (gradTail N M x)))
        (particleLaw (kernelData (1 / 100)) N) :=
      (hA.const_mul (1 + η)).add (hT.const_mul ((1 + η⁻¹) / 4))
    have hmono := integral_mono hD hI (fun x => hpt x)
    have hsum : ∫ x, ((1 + η) * particleTangentNormSq (particleWeakGradient f x) +
        (1 + η⁻¹) / 4 * (f x ^ 2 * particleTangentNormSq (gradTail N M x)))
          ∂particleLaw (kernelData (1 / 100)) N =
        (1 + η) * ∫ x, particleTangentNormSq (particleWeakGradient f x)
          ∂particleLaw (kernelData (1 / 100)) N +
        (1 + η⁻¹) / 4 * ∫ x, (f x ^ 2 * particleTangentNormSq (gradTail N M x))
          ∂particleLaw (kernelData (1 / 100)) N := by
      rw [integral_add (hA.const_mul (1 + η)) (hT.const_mul ((1 + η⁻¹) / 4)),
        integral_const_mul, integral_const_mul]
    rw [hsum] at hmono
    have hc : 0 ≤ (1 + η⁻¹) / 4 := by positivity
    have hEf : particleEnergy (kernelData (1 / 100)) N f =
        ∫ x, particleTangentNormSq (particleWeakGradient f x)
          ∂particleLaw (kernelData (1 / 100)) N := rfl
    rw [hE]
    calc _ ≤ _ := hmono
      _ ≤ (1 + η) * particleEnergy (kernelData (1 / 100)) N f +
            (1 + η⁻¹) / 4 * (h1033_eps M * (particleEnergy (kernelData (1 / 100)) N f +
              ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N)) := by
          rw [hEf]
          gcongr
          exact hb
      _ = _ := by ring

end DGPS.Examples.PositiveH1.Transfer
