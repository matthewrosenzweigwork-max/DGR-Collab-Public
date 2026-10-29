import Mathlib
import DGPS.Examples.PositiveH1.TransferAbsorption
import DGPS.Examples.PositiveH1.TransferInverse

/-!
# Ground state map on every rough particle test (H1028)

For `κ = 1/100`, every `N` and every `f ∈ H¹(P_N)` with weak gradient `g`, the function
`ψ = f √p_N` lies in `H¹(m^N)` with weak gradient `√p_N g - ½ ψ ∇U_N`, and satisfies the two
estimates of H1027.

Route.  Transported to `𝕋^N`, the weight `s = √p_N` is an `H¹` function with bounded values and
weak gradient `-½ s ∇U_N` (`isWeakGradient_sP`).  For a smooth approximation `ψ_n → Ψ` in `H¹(𝕋^N)`
the products `ψ_n s` are weak-`H¹` with the product-rule gradient (`mul_smooth_H1`); the force
multiplier bound (`force_mult`) applied to `ψ_n - Ψ` gives `L¹` convergence of the gradients, and the
closure `IsWeakGradient.of_tendsto_L1` passes the gradient identity to the limit
(`rough_torus_main`).  The estimates then follow from the absorption `torus_absorb` applied directly
to the limit, exactly as in the smooth case of H1027.
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open DGPS
open DGPS.Examples.PositiveH1.Particle DGPS.Examples.PositiveH1.Fourier
open DGPS.Analysis.ForceMultiplierH1

namespace DGPS.Examples.PositiveH1.Transfer

private theorem rough_continuous_sP (κ : ℝ) (N : ℕ+) : Continuous (sP κ N) := by
  have h : sP κ N = fun y => (Real.sqrt (K κ N))⁻¹ *
      Real.exp (-(U κ N ((EE N).symm y)) / 2) := funext (sP_eq κ N)
  rw [h]
  exact continuous_const.mul (Real.continuous_exp.comp
    (((continuous_U κ N).comp (abs_continuous_EE_symm N)).neg.div_const 2))

/-- Torus form of the ground-state map on `H¹`. -/
private theorem rough_torus_main (κ : ℝ) (hκ : 0 ≤ κ) (N : ℕ+) {Ψ : Torus (N : ℕ) → ℝ}
    {GΨ : Torus (N : ℕ) → Tangent (N : ℕ)} (hΨ : IsWeakGradient Ψ GΨ) :
    IsWeakGradient (fun y => Ψ y * sP κ N y)
      (fun y => sP κ N y • GΨ y +
        (-(1 / 2 : ℝ) * (Ψ y * sP κ N y)) • Fv κ N y) := by
  obtain ⟨ψs, hs, hsw, hs2, hsg⟩ := exists_smooth_tendsto_H1 hΨ
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
    (rough_continuous_sP κ N).continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (fun _ => 0) (Set.mem_univ _))
  have hCa : ∀ y, ‖sP κ N y‖ ≤ C := fun y => hC y (Set.mem_univ _)
  have hWm : MemLp (sP κ N) ⊤ (haar (N : ℕ)) :=
    memLp_top_of_bound (rough_continuous_sP κ N).aestronglyMeasurable C
      (Eventually.of_forall hCa)
  have hΔ := fun n => sub_wg (hsw n) hΨ
  have hFm := (force_mult κ N hΨ).1
  have e2 : (fun y => (-(1 / 2 : ℝ) * (Ψ y * sP κ N y)) • Fv κ N y) =
      fun y => sP κ N y • ((-(1 / 2) : ℝ) • (Ψ y • Fv κ N y)) := by
    funext y; rw [smul_smul, smul_smul]; congr 1; ring
  have hsP : IsWeakGradient (sP κ N)
      (fun y => (-(1 / 2 : ℝ) * sP κ N y) • Fv κ N y) := isWeakGradient_sP κ hκ N
  refine IsWeakGradient.of_tendsto_L1 (U := fun n y => ψs n y * sP κ N y)
    (G := fun n y => sP κ N y • smoothGrad (ψs n) y +
      ψs n y • ((-(1 / 2 : ℝ) * sP κ N y) • Fv κ N y))
    (memLp_mul_top hWm hΨ.memLp) ?_
    (fun n => mul_smooth_H1 (hs n) hsP) ?_ ?_
  · have h3 : MemLp (fun y => (-(1 / 2) : ℝ) • (Ψ y • Fv κ N y)) 2 (haar (N : ℕ)) :=
      hFm.const_smul (-(1 / 2) : ℝ)
    have hB : MemLp (fun y => (-(1 / 2 : ℝ) * (Ψ y * sP κ N y)) • Fv κ N y) 2
        (haar (N : ℕ)) := by
      rw [e2]; exact memLp_smul_top hWm h3
    exact (memLp_smul_top hWm hΨ.memLp_grad).add hB
  · refine tendsto_zero_of_le_two (C := C) (C' := 0) (b := fun _ => 0)
      (tendsto_lintegral_of_eLpNorm_two
        (fun n => (DGPS.Analysis.ForceMultiplier.memLp_two_of_smooth (hs n)).aestronglyMeasurable)
        hΨ.memLp.aestronglyMeasurable hs2) tendsto_const_nhds (fun n => ?_)
    exact (lintegral_mul_sub_le (a := ψs n) (b := Ψ) (w := sP κ N)
      (Eventually.of_forall hCa)).trans (by simp)
  · intro j
    have ha : Tendsto (fun n => ∫⁻ y, ‖smoothGrad (ψs n) y j - GΨ y j‖ₑ ∂haar (N : ℕ)) atTop
        (𝓝 0) :=
      tendsto_lintegral_of_eLpNorm_two
        (fun n => (memLp_coord (hsw n).memLp_grad j).aestronglyMeasurable)
        (memLp_coord hΨ.memLp_grad j).aestronglyMeasurable (hsg j)
    have hu : Tendsto (fun n => Real.sqrt (∫ x, (ψs n x - Ψ x) ^ 2 ∂haar (N : ℕ))) atTop
        (𝓝 0) :=
      tendsto_sqrt_scalar (fun n => (hΔ n).memLp) hs2
    have hv : Tendsto (fun n => Real.sqrt (∫ x, ‖smoothGrad (ψs n) x - GΨ x‖ ^ 2
        ∂haar (N : ℕ))) atTop (𝓝 0) :=
      tendsto_sqrt_coord (D := fun n x => smoothGrad (ψs n) x - GΨ x)
        (fun n => (hΔ n).memLp_grad) (fun j => by simpa using hsg j)
    have hbd : Tendsto (fun n => bound1 (N : ℕ) LR βR
        (Real.sqrt (∫ x, (ψs n x - Ψ x) ^ 2 ∂haar (N : ℕ)))
        (Real.sqrt (∫ x, ‖smoothGrad (ψs n) x - GΨ x‖ ^ 2 ∂haar (N : ℕ)))) atTop (𝓝 0) := by
      have := ((continuous_bound1 (N : ℕ)).tendsto (LR, βR, 0, 0)).comp
        (tendsto_const_nhds.prodMk_nhds (tendsto_const_nhds.prodMk_nhds (hu.prodMk_nhds hv)))
      simpa [Function.comp_def, bound1] using this
    have hb : Tendsto (fun n => eLpNorm (fun y => (ψs n y - Ψ y) • Fv κ N y) 2
        (haar (N : ℕ))) atTop (𝓝 0) := by
      have hc : Tendsto (fun n => ENNReal.ofReal |κ| * ENNReal.ofReal (bound1 (N : ℕ) LR βR
          (Real.sqrt (∫ x, (ψs n x - Ψ x) ^ 2 ∂haar (N : ℕ)))
          (Real.sqrt (∫ x, ‖smoothGrad (ψs n) x - GΨ x‖ ^ 2 ∂haar (N : ℕ))))) atTop
          (𝓝 0) := by
        have h0 := ENNReal.tendsto_ofReal hbd
        have h1 := ENNReal.Tendsto.const_mul h0 (Or.inr (ENNReal.ofReal_ne_top (r := |κ|)))
        simpa using h1
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc
        (fun _ => zero_le) (fun n => ?_)
      have := (force_mult κ N (hΔ n)).2
      rw [ENNReal.ofReal_mul (abs_nonneg κ)] at this
      exact this
    refine tendsto_zero_of_le_two (C := C) (C' := C / 2) ha hb (fun n => ?_)
    have hmeas1 : AEMeasurable (fun y => ‖smoothGrad (ψs n) y j - GΨ y j‖ₑ) (haar (N : ℕ)) :=
      ((memLp_coord (hsw n).memLp_grad j).aestronglyMeasurable.sub
        (memLp_coord hΨ.memLp_grad j).aestronglyMeasurable).enorm
    have hfn := (force_mult κ N (hΔ n)).1
    calc ∫⁻ y, ‖(sP κ N y • smoothGrad (ψs n) y +
              ψs n y • ((-(1 / 2 : ℝ) * sP κ N y) • Fv κ N y)) j
            - (sP κ N y • GΨ y + (-(1 / 2 : ℝ) * (Ψ y * sP κ N y)) • Fv κ N y) j‖ₑ
            ∂haar (N : ℕ)
        ≤ ∫⁻ y, (ENNReal.ofReal C * ‖smoothGrad (ψs n) y j - GΨ y j‖ₑ
            + ENNReal.ofReal (C / 2) * ‖((ψs n y - Ψ y) • Fv κ N y) j‖ₑ)
            ∂haar (N : ℕ) := by
          refine lintegral_mono_ae ?_
          refine Eventually.of_forall fun y => ?_
          have e : (sP κ N y • smoothGrad (ψs n) y +
                ψs n y • ((-(1 / 2 : ℝ) * sP κ N y) • Fv κ N y)) j
              - (sP κ N y • GΨ y + (-(1 / 2 : ℝ) * (Ψ y * sP κ N y)) • Fv κ N y) j
              = sP κ N y * (smoothGrad (ψs n) y j - GΨ y j)
                + (-(1 / 2 : ℝ) * sP κ N y) * ((ψs n y - Ψ y) • Fv κ N y) j := by
            simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]; ring
          rw [e]
          refine (enorm_add_le _ _).trans ?_
          rw [enorm_mul, enorm_mul]
          have hw1 : ‖sP κ N y‖ₑ ≤ ENNReal.ofReal C := by
            rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hCa y)
          have hw2 : ‖-(1 / 2 : ℝ) * sP κ N y‖ₑ ≤ ENNReal.ofReal (C / 2) := by
            rw [← ofReal_norm]; refine ENNReal.ofReal_le_ofReal ?_
            rw [norm_mul]; have := hCa y; rw [Real.norm_eq_abs] at this ⊢; norm_num
            linarith
          exact add_le_add (by gcongr) (by gcongr)
      _ = ENNReal.ofReal C * ∫⁻ y, ‖smoothGrad (ψs n) y j - GΨ y j‖ₑ ∂haar (N : ℕ)
            + ENNReal.ofReal (C / 2) *
              ∫⁻ y, ‖((ψs n y - Ψ y) • Fv κ N y) j‖ₑ ∂haar (N : ℕ) := by
          rw [lintegral_add_left' (hmeas1.const_mul _), lintegral_const_mul' _ _
            ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ _ := by
          gcongr
          exact lintegral_coord_le hfn j

private theorem rough_ground_state_general (κ : ℝ) (hκ : 0 ≤ κ)
    (hc : κ * (8 / 3 + 2 * Real.pi) < 1) (hd : 2 * Real.pi * κ < 1) (N : ℕ+)
    {f : ParticleSpace 1 N → ℝ} {g : ParticleSpace 1 N → Fin N → Tangent 1}
    (hg : IsParticleWeakGradient (kernelData κ) N f g) :
    MemParticleHaarH1 N (fun x => f x * Real.sqrt (p κ N x)) ∧
    IsParticleHaarWeakGradient N (fun x => f x * Real.sqrt (p κ N x))
      (fun x i => Real.sqrt (p κ N x) • g x i -
        ((1 / 2 : ℝ) * (f x * Real.sqrt (p κ N x))) • roughForce κ N x i) ∧
    Real.sqrt (∫ x, particleTangentNormSq (fun i => Real.sqrt (p κ N x) • g x i -
        ((1 / 2 : ℝ) * (f x * Real.sqrt (p κ N x))) • roughForce κ N x i)
        ∂particleHaar 1 N) ≤
      2 * Real.sqrt (∫ x, particleTangentNormSq (g x) ∂particleLaw (kernelData κ) N) +
        2 * Real.pi * κ * Real.sqrt (∫ x, f x ^ 2 ∂particleLaw (kernelData κ) N) ∧
    ∫ x, particleTangentNormSq (fun i => Real.sqrt (p κ N x) • g x i -
        ((1 / 2 : ℝ) * (f x * Real.sqrt (p κ N x))) • roughForce κ N x i)
        ∂particleHaar 1 N ≤
      8 * ∫ x, particleTangentNormSq (g x) ∂particleLaw (kernelData κ) N +
        2 * ∫ x, f x ^ 2 ∂particleLaw (kernelData κ) N := by
  have hgH := (isParticleWeakGradient_iff _ _ _ _).1 hg
  have hgT : IsWeakGradient (fun y => f ((EE N).symm y)) (gTorus N g) := transport_weak N hgH
  set A : Torus (N : ℕ) → Tangent (N : ℕ) := fun y => sP κ N y • gTorus N g y with hA
  set G' : Torus (N : ℕ) → Tangent (N : ℕ) := fun y => A y +
    (-(1 / 2 : ℝ) * (f ((EE N).symm y) * sP κ N y)) • gTorus N (roughForce κ N) y with hG'
  have hprod2 : IsWeakGradient (fun y => f ((EE N).symm y) * sP κ N y) G' :=
    rough_torus_main κ hκ N hgT
  have hG : ∀ x i, (Real.sqrt (p κ N x) • g x i -
        ((1 / 2 : ℝ) * (f x * Real.sqrt (p κ N x))) • roughForce κ N x i) =
      (EuclideanSpace.single (0 : Fin 1) (G' (EE N x) i) : Tangent 1) := by
    intro x i
    rw [gT_single N g x i, gT_single N (roughForce κ N) x i]
    ext j
    fin_cases j
    simp [hG', hA, sP, gTorus]
    ring
  have hW : IsParticleHaarWeakGradient N (fun x => f x * Real.sqrt (p κ N x))
      (fun x i => Real.sqrt (p κ N x) • g x i -
        ((1 / 2 : ℝ) * (f x * Real.sqrt (p κ N x))) • roughForce κ N x i) :=
    abs_transport_weak_symm N (by simpa [sP] using hprod2) hG
  obtain ⟨hmem, -⟩ := multiplier_torus κ hκ N hprod2
  have hB : MemLp (fun y => (-(1 / 2 : ℝ) * (f ((EE N).symm y) * sP κ N y)) •
      gTorus N (roughForce κ N) y) 2 (haar (N : ℕ)) := by
    have := hmem.const_smul (-(1 / 2 : ℝ))
    exact this.ae_eq (Eventually.of_forall fun y => by simp [smul_smul])
  have hAm : MemLp A 2 (haar (N : ℕ)) := by
    have := hprod2.memLp_grad.sub hB
    convert this using 1
    funext y
    simp [hG', hA]
  obtain ⟨h1, h2⟩ := torus_absorb κ hκ hc hd N hprod2 hAm (fun y => rfl)
  have eG := integral_normSq_particle N (v := G') (G := fun x i => Real.sqrt (p κ N x) • g x i -
        ((1 / 2 : ℝ) * (f x * Real.sqrt (p κ N x))) • roughForce κ N x i) hG
  have eA := integral_normSq_particle N (v := A) (G := fun x i => Real.sqrt (p κ N x) • g x i)
    (fun x i => by
      rw [gT_single N g x i]
      ext j
      fin_cases j
      simp [hA, sP, gTorus])
  have eP : ∫ y, (f ((EE N).symm y) * sP κ N y) ^ 2 ∂haar (N : ℕ) =
      ∫ x, f x ^ 2 ∂particleLaw (kernelData κ) N := by
    have := integral_sq_EE N (fun x => f x * Real.sqrt (p κ N x))
    rw [DGPS.Particle.integral_particleLaw]
    simp only [sP]
    rw [this]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [density_eq]
    rw [mul_pow, Real.sq_sqrt (p_nonneg' κ N x)]
    ring
  have eL : ∫ x, particleTangentNormSq (g x) ∂particleLaw (kernelData κ) N =
      ∫ x, particleTangentNormSq (fun i => Real.sqrt (p κ N x) • g x i) ∂particleHaar 1 N := by
    rw [DGPS.Particle.integral_particleLaw]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [density_eq, particleTangentNormSq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (p_nonneg' κ N x), Finset.mul_sum]
  rw [eL, eA, eG, ← eP]
  exact ⟨⟨_, hW⟩, hW, h1, h2⟩

/-- H1028: the ground-state map `f ↦ f √p_N` on every rough particle test `f ∈ H¹(P_N)` at the
fixed coupling `κ = 1/100`: `ψ = f √p_N ∈ H¹(m^N)`, with weak gradient
`√p_N ∇f - ½ ψ ∇U_N`, and the two estimates of H1027. -/
theorem ground_state_map_on_every_rough_particle_test (N : ℕ+) :
    ∀ (f : ParticleSpace 1 N → ℝ), MemParticleH1 (kernelData (1 / 100)) N f →
      ∀ (g : ParticleSpace 1 N → Fin N → Tangent 1),
      IsParticleWeakGradient (kernelData (1 / 100)) N f g →
      MemParticleHaarH1 N (fun x => f x * Real.sqrt (p (1 / 100) N x)) ∧
      IsParticleHaarWeakGradient N (fun x => f x * Real.sqrt (p (1 / 100) N x))
        (fun x i => Real.sqrt (p (1 / 100) N x) • g x i -
          ((1 / 2 : ℝ) * (f x * Real.sqrt (p (1 / 100) N x))) • roughForce (1 / 100) N x i) ∧
      Real.sqrt (∫ x, particleTangentNormSq (fun i => Real.sqrt (p (1 / 100) N x) • g x i -
          ((1 / 2 : ℝ) * (f x * Real.sqrt (p (1 / 100) N x))) • roughForce (1 / 100) N x i)
          ∂particleHaar 1 N) ≤
        2 * Real.sqrt (∫ x, particleTangentNormSq (g x) ∂particleLaw (kernelData (1 / 100)) N) +
          2 * Real.pi * (1 / 100 : ℝ) *
            Real.sqrt (∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N) ∧
      ∫ x, particleTangentNormSq (fun i => Real.sqrt (p (1 / 100) N x) • g x i -
          ((1 / 2 : ℝ) * (f x * Real.sqrt (p (1 / 100) N x))) • roughForce (1 / 100) N x i)
          ∂particleHaar 1 N ≤
        8 * ∫ x, particleTangentNormSq (g x) ∂particleLaw (kernelData (1 / 100)) N +
          2 * ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N := by
  have hpi := Real.pi_lt_d2
  have hc : (1 / 100 : ℝ) * (8 / 3 + 2 * Real.pi) < 1 := by nlinarith
  have hd : 2 * Real.pi * (1 / 100 : ℝ) < 1 := by nlinarith
  intro f _ g hg
  exact rough_ground_state_general (1 / 100) (by norm_num) hc hd N hg

end DGPS.Examples.PositiveH1.Transfer
