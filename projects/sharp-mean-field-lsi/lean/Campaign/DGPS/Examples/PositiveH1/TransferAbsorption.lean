import Mathlib
import DGPS.Examples.PositiveH1.Transfer
import DGPS.Analysis.ForceMultiplierH1
import DGPS.Foundations.SobolevEmbedding
import DGPS.Foundations.WeakSobolev
import DGPS.Analysis.ForceMultiplierSmooth

/-!
# Small fixed coupling absorption (H1027)

For `κ = 1/100` and every `N`, `ψ ∈ H¹(m^N)` with weak gradient `g`:
`‖ψ ∇U_N‖₂ ≤ κ(8/3 + 2π) ‖∇ψ‖₂ + 2πκ ‖ψ‖₂` (`multiplier_particle`, transported from the torus
`multiplier_torus`), with `c = κ(8/3+2π) < 1`, `d = 2πκ < 1`.  For smooth `f` and `ψ = f √p_N`,
the weak gradient is `√p_N ∇f - ½ ψ ∇U_N` (bounded Sobolev chain rule `isWeakGradient_sP` plus the
`W^{1,∞}` product rule), and absorption (`absorb_arith`, `torus_absorb`) gives
`‖∇ψ‖₂ ≤ 2 √E_N(f) + d ‖f‖₂` and `‖∇ψ‖₂² ≤ 8 E_N(f) + 2 ‖f‖₂²`
(`small_fixed_coupling_absorption`).
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open DGPS
open DGPS.Examples.PositiveH1.Particle DGPS.Examples.PositiveH1.Fourier

namespace DGPS.Examples.PositiveH1.Transfer

theorem R_bound (x : Torus 1) : |R x| ≤ A := by
  unfold R A
  have hs := a_summable
  have hn : Summable (fun n : ℕ => ‖a n * cosMode n x‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => term_abs_le n x) hs
  calc |∑' n : ℕ, a n * cosMode n x| = ‖∑' n : ℕ, a n * cosMode n x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖a n * cosMode n x‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, a n := hn.tsum_le_tsum (fun n => term_abs_le n x) hs


theorem sqrt_integral_sq_dR_le : Real.sqrt (∫ t, ‖(EuclideanSpace.single (0 : Fin 1) (dR t) : Tangent 1)‖ ^ 2 ∂haar 1) ≤ 2 * Real.pi := by
  have h1 : ∫ t, ‖(EuclideanSpace.single (0 : Fin 1) (dR t) : Tangent 1)‖ ^ 2 ∂haar 1 = B 1 ^ 2 := by
    have : ∀ t, ‖(EuclideanSpace.single (0 : Fin 1) (dR t) : Tangent 1)‖ ^ 2 = dR t ^ 2 := by
      intro t; simp
    simp_rw [this, integral_sq_dR]
    unfold B
    rw [Real.sq_sqrt]
    · rfl
    · positivity
  rw [h1, Real.sqrt_sq (by unfold B; exact Real.sqrt_nonneg _)]
  exact fourier_coefficient_and_tail_bounds.2.2.1

theorem L_le : (eLpNorm R ⊤ (haar 1)).toReal ≤ 4 / 3 := by
  have h : eLpNormEssSup R (haar 1) ≤ ENNReal.ofReal (4/3) :=
    eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact (R_bound x).trans fourier_coefficient_and_tail_bounds.2.1)
  rw [eLpNorm_exponent_top]
  · exact ENNReal.toReal_le_of_le_ofReal (by norm_num) h
  · exact continuous_R.aestronglyMeasurable


open DGPS.Analysis.ForceMultiplierH1 in
theorem gTorus_rough_eq (κ : ℝ) (N : ℕ+) (y : Torus (N : ℕ)) :
    gTorus N (roughForce κ N) y = κ • forceB dR y := by
  ext j
  simp only [gTorus, roughForce_apply, forceB_apply, PiLp.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : ((EE N).symm y j - (EE N).symm y k : Torus 1) = fun _ => y j - y k := by
    funext i; rfl
  rw [this]; ring

open DGPS.Analysis.ForceMultiplierH1 in
theorem multiplier_torus (κ : ℝ) (hκ : 0 ≤ κ) (N : ℕ+) {ψ : Torus (N : ℕ) → ℝ}
    {g : Torus (N : ℕ) → Tangent (N : ℕ)} (hψ : IsWeakGradient ψ g) :
    MemLp (fun y => ψ y • gTorus N (roughForce κ N) y) 2 (haar (N : ℕ)) ∧
    Real.sqrt (∫ y, ‖ψ y • gTorus N (roughForce κ N) y‖ ^ 2 ∂haar (N : ℕ)) ≤
      κ * (8 / 3 + 2 * Real.pi) * Real.sqrt (∫ y, ‖g y‖ ^ 2 ∂haar (N : ℕ)) +
        2 * Real.pi * κ * Real.sqrt (∫ y, ψ y ^ 2 ∂haar (N : ℕ)) := by
  have hQ : MemH1 R := ⟨_, weak_gradient_R⟩
  have hψ' : MemH1 ψ := ⟨g, hψ⟩
  obtain ⟨hmem, hle, hle2⟩ := full_h1_force_multiplier_closure (N : ℕ) N.pos R hQ ψ hψ'
    (L := (eLpNorm R ⊤ (haar 1)).toReal)
    (β := Real.sqrt (∫ t, ‖weakGradient R hQ t‖ ^ 2 ∂haar 1))
    (u := Real.sqrt (∫ x, ψ x ^ 2 ∂haar (N : ℕ)))
    (v := Real.sqrt (∫ x, ‖weakGradient ψ hψ' x‖ ^ 2 ∂haar (N : ℕ))) rfl rfl rfl rfl
  have hwg : weakGradient ψ hψ' =ᵐ[haar (N : ℕ)] g := weakGradient_ae_eq hψ
  have hv : (∫ x, ‖weakGradient ψ hψ' x‖ ^ 2 ∂haar (N : ℕ)) = ∫ x, ‖g x‖ ^ 2 ∂haar (N : ℕ) :=
    integral_congr_ae (by filter_upwards [hwg] with x hx; rw [hx])
  have hwR : weakGradient R hQ =ᵐ[haar 1] fun x => (EuclideanSpace.single (0 : Fin 1) (dR x) : Tangent 1) :=
    weakGradient_ae_eq weak_gradient_R
  have hb : (∫ t, ‖weakGradient R hQ t‖ ^ 2 ∂haar 1) =
      ∫ t, ‖(EuclideanSpace.single (0 : Fin 1) (dR t) : Tangent 1)‖ ^ 2 ∂haar 1 :=
    integral_congr_ae (by filter_upwards [hwR] with x hx; rw [hx])
  rw [hv, hb] at hle hle2
  have hβ := sqrt_integral_sq_dR_le
  have hL := L_le
  have hL0 : 0 ≤ (eLpNorm R ⊤ (haar 1)).toReal := ENNReal.toReal_nonneg
  have hβ0 := Real.sqrt_nonneg (∫ t, ‖(EuclideanSpace.single (0 : Fin 1) (dR t) : Tangent 1)‖ ^ 2 ∂haar 1)
  have hu0 := Real.sqrt_nonneg (∫ x, ψ x ^ 2 ∂haar (N : ℕ))
  have hv0 := Real.sqrt_nonneg (∫ x, ‖g x‖ ^ 2 ∂haar (N : ℕ))
  -- ae replacement of the force
  have hae : (fun x => ψ x • forceB (fun t => weakGradient R hQ t 0) x) =ᵐ[haar (N : ℕ)]
      fun x => ψ x • forceB dR x := by
    have hall : ∀ᵐ x ∂haar (N : ℕ), ∀ i j : Fin (N : ℕ), i ≠ j →
        weakGradient R hQ (fun _ : Fin 1 => x i - x j) 0 = dR (fun _ : Fin 1 => x i - x j) := by
      rw [ae_all_iff]; intro i; rw [ae_all_iff]; intro j
      by_cases hij : i = j
      · exact Eventually.of_forall fun x h => absurd hij h
      · have h0 : (fun t => weakGradient R hQ t 0) =ᵐ[haar 1] dR := by
          filter_upwards [hwR] with t ht; rw [ht]; simp
        have := (DGPS.Analysis.ForceMultiplier.measurePreserving_pairDiff hij).quasiMeasurePreserving.ae_eq_comp h0
        filter_upwards [this] with x hx _ using hx
    filter_upwards [hall] with x hx
    congr 1
    ext i
    simp only [forceB_apply]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    exact hx i j (Finset.ne_of_mem_erase hj).symm
  have hF : MemLp (fun x => ψ x • forceB dR x) 2 (haar (N : ℕ)) := hmem.ae_eq hae
  have hG : ∀ y, ψ y • gTorus N (roughForce κ N) y = κ • (ψ y • forceB dR y) := by
    intro y; rw [gTorus_rough_eq, smul_comm]
  simp_rw [hG]
  refine ⟨hF.const_smul κ, ?_⟩
  have hT := DGPS.Analysis.ForceMultiplierH1.toReal_eLpNorm_two (hF.const_smul κ)
  have hE := eLpNorm_const_smul (c := κ) (f := fun y => ψ y • forceB dR y) 2 (haar (N : ℕ))
  calc √(∫ y, ‖κ • (ψ y • forceB dR y)‖ ^ 2 ∂haar (N : ℕ))
      = (eLpNorm (κ • fun y => ψ y • forceB dR y) 2 (haar (N : ℕ))).toReal := hT.symm
    _ = κ * (eLpNorm (fun x => ψ x • forceB (fun t => weakGradient R hQ t 0) x) 2 (haar (N : ℕ))).toReal := by
        rw [hE, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs, abs_of_nonneg hκ,
          eLpNorm_congr_ae hae]
    _ ≤ _ := ?_
  have h1 := hle.trans hle2
  have h2 : ((2 * (eLpNorm R ⊤ (haar 1)).toReal + √(∫ t, ‖(EuclideanSpace.single (0 : Fin 1) (dR t) : Tangent 1)‖ ^ 2 ∂haar 1)) * √(∫ x, ‖g x‖ ^ 2 ∂haar (N : ℕ)) + √(∫ t, ‖(EuclideanSpace.single (0 : Fin 1) (dR t) : Tangent 1)‖ ^ 2 ∂haar 1) * √(∫ x, ψ x ^ 2 ∂haar (N : ℕ))) ≤ (8 / 3 + 2 * Real.pi) * √(∫ x, ‖g x‖ ^ 2 ∂haar (N : ℕ)) + 2 * Real.pi * √(∫ x, ψ x ^ 2 ∂haar (N : ℕ)) := by
    gcongr; linarith
  nlinarith [mul_le_mul_of_nonneg_left (h1.trans h2) hκ]


theorem abs_continuous_EE_symm (N : ℕ+) : Continuous (EE N).symm :=
  continuous_pi fun i => continuous_pi fun _ => continuous_apply i

/-- Inverse of `LL`. -/
noncomputable def LL' (N : ℕ+) : (Fin N → ℝ) →L[ℝ] (Fin N → Fin 1 → ℝ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun _ =>
    ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) i

theorem LL_LL' (N : ℕ+) (z : Fin N → ℝ) : LL N (LL' N z) = z := rfl

theorem abs_EE_symm_torusLift (N : ℕ+) (z : Fin N → ℝ) :
    (EE N).symm (torusLift z) = particleLift (LL' N z) := by
  apply (EE N).injective
  rw [MeasurableEquiv.apply_symm_apply, EE_particleLift, LL_LL']

theorem abs_isSmooth_comp_EE_symm (N : ℕ+) {f : ParticleSpace 1 N → ℝ}
    (hf : IsSmoothPeriodicParticle f) : IsSmoothPeriodic (fun y => f ((EE N).symm y)) := by
  have : ((fun y => f ((EE N).symm y)) ∘ torusLift) = (f ∘ particleLift) ∘ LL' N := by
    funext z; simp [abs_EE_symm_torusLift]
  unfold IsSmoothPeriodic
  rw [this]
  exact hf.comp (LL' N).contDiff

/-- The square root of the density, on the torus. -/
noncomputable def sP (κ : ℝ) (N : ℕ+) (y : Torus (N : ℕ)) : ℝ :=
  Real.sqrt (p κ N ((EE N).symm y))

theorem sP_eq (κ : ℝ) (N : ℕ+) (y : Torus (N : ℕ)) :
    sP κ N y = (Real.sqrt (K κ N))⁻¹ * Real.exp (-(U κ N ((EE N).symm y)) / 2) := by
  unfold sP p
  rw [Real.sqrt_mul (inv_nonneg.2 (K_pos κ N).le), Real.sqrt_inv, Real.exp_half]

theorem isWeakGradient_sP (κ : ℝ) (hκ : 0 ≤ κ) (N : ℕ+) :
    IsWeakGradient (sP κ N)
      (fun y => (-(1 / 2 : ℝ) * sP κ N y) • gTorus N (roughForce κ N) y) := by
  have hg := transport_weak N (weak_rough_particle_gradient κ N).2.1
  have hWc : Continuous (fun y : Torus (N : ℕ) => U κ N ((EE N).symm y)) :=
    (continuous_U κ N).comp (abs_continuous_EE_symm N)
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hWc.continuousOn
  set F : ℝ → ℝ := fun t => (Real.sqrt (K κ N))⁻¹ * Real.exp (-t / 2) with hFdef
  have hd : ∀ t, HasDerivAt F (-(1 / 2 : ℝ) * F t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => -t / 2) (-(1 / 2 : ℝ)) t := by
      convert ((hasDerivAt_id t).neg.div_const 2) using 1 <;> norm_num
    have := (h1.exp.const_mul (Real.sqrt (K κ N))⁻¹)
    convert this using 1
    simp only [hFdef]; ring
  have hF : ContDiffOn ℝ ∞ F (Set.Icc 0 (M + 1)) := by
    refine ContDiff.contDiffOn ?_
    exact contDiff_const.mul (Real.contDiff_exp.comp (contDiff_id.neg.div_const 2))
  have hab : (0 : ℝ) < M + 1 := by
    have : 0 ≤ M := (norm_nonneg _).trans (hM (Classical.arbitrary _) (Set.mem_univ _))
    linarith
  have hr : ∀ y, U κ N ((EE N).symm y) ∈ Set.Icc 0 (M + 1) := fun y =>
    ⟨U_nonneg hκ N _, by
      have := hM y (Set.mem_univ _)
      rw [Real.norm_eq_abs] at this
      linarith [le_abs_self (U κ N ((EE N).symm y))]⟩
  have h := chain_rule_of_cont_rep hg hWc Filter.EventuallyEq.rfl hab hr hF
  have e1 : (fun y => F (U κ N ((EE N).symm y))) = sP κ N := by
    funext y; rw [sP_eq]
  have e2 : ∀ y, derivWithin F (Set.Icc 0 (M + 1)) (U κ N ((EE N).symm y)) =
      -(1 / 2 : ℝ) * sP κ N y := by
    intro y
    rw [(hd _).hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hab _ (hr y)), sP_eq]
  simp_rw [e1, e2] at h
  exact h


/-- Embedding a torus vector field into particle tangent vectors. -/
noncomputable def singleMap (N : ℕ+) : Tangent (N : ℕ) → (Fin N → Tangent 1) :=
  fun w i => (EuclideanSpace.single (0 : Fin 1) (w i) : Tangent 1)

theorem continuous_singleMap (N : ℕ+) : Continuous (singleMap N) := by
  have hc : Continuous (fun t : ℝ => (EuclideanSpace.single (0 : Fin 1) t : Tangent 1)) :=
    (Isometry.of_dist_eq fun a b => PiLp.dist_single_same 2 (fun _ : Fin 1 => ℝ) 0 a b).continuous
  refine continuous_pi fun i => hc.comp ?_
  exact (EuclideanSpace.proj i : Tangent (N : ℕ) →L[ℝ] ℝ).continuous

theorem norm_single1 (a : ℝ) : ‖(EuclideanSpace.single (0 : Fin 1) a : Tangent 1)‖ = ‖a‖ := by
  simp

theorem memLp_particle_of_torus (N : ℕ+) {v : Torus (N : ℕ) → Tangent (N : ℕ)}
    (hv : MemLp v 2 (haar (N : ℕ))) {G : ParticleSpace 1 N → Fin N → Tangent 1}
    (hG : ∀ x i, G x i = (EuclideanSpace.single (0 : Fin 1) (v (EE N x) i) : Tangent 1)) :
    MemLp G 2 (particleHaar 1 N) := by
  have hGe : G = fun x => singleMap N (v (EE N x)) := by
    funext x i; exact hG x i
  have hvE := hv.comp_measurePreserving (mp_EE N)
  have hmeas : AEStronglyMeasurable G (particleHaar 1 N) := by
    rw [hGe]
    exact (continuous_singleMap N).comp_aestronglyMeasurable hvE.aestronglyMeasurable
  refine hvE.mono hmeas (Eventually.of_forall fun x => ?_)
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  rw [hG, norm_single1]
  exact PiLp.norm_apply_le (v (EE N x)) i

theorem integral_normSq_particle (N : ℕ+) {v : Torus (N : ℕ) → Tangent (N : ℕ)}
    {G : ParticleSpace 1 N → Fin N → Tangent 1}
    (hG : ∀ x i, G x i = (EuclideanSpace.single (0 : Fin 1) (v (EE N x) i) : Tangent 1)) :
    ∫ x, particleTangentNormSq (G x) ∂particleHaar 1 N = ∫ y, ‖v y‖ ^ 2 ∂haar (N : ℕ) := by
  have e := (mp_EE N).integral_comp' (fun y => ‖v y‖ ^ 2)
  rw [← e]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [particleTangentNormSq, hG, norm_single1]
  rw [EuclideanSpace.norm_sq_eq]

theorem abs_transport_weak_symm (N : ℕ+) {ψ : ParticleSpace 1 N → ℝ}
    {G' : Torus (N : ℕ) → Tangent (N : ℕ)}
    (h : IsWeakGradient (fun y => ψ ((EE N).symm y)) G')
    {G : ParticleSpace 1 N → Fin N → Tangent 1}
    (hG : ∀ x i, G x i = (EuclideanSpace.single (0 : Fin 1) (G' (EE N x) i) : Tangent 1)) :
    IsParticleHaarWeakGradient N ψ G := by
  refine ⟨?_, memLp_particle_of_torus N h.memLp_grad hG, ?_⟩
  · have := h.memLp.comp_measurePreserving (mp_EE N)
    simpa [Function.comp_def] using this
  · intro φ hφ i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have hφ' := abs_isSmooth_comp_EE_symm N hφ
    have hI := (mp_EE N).integral_comp' (fun y => ψ ((EE N).symm y) *
      coordPartial i (fun y => φ ((EE N).symm y)) y)
    have hJ := (mp_EE N).integral_comp' (fun y => G' y i * φ ((EE N).symm y))
    simp only [MeasurableEquiv.symm_apply_apply] at hI hJ
    have hpp := particlePartial_comp_EE N hφ' i
    simp only [MeasurableEquiv.symm_apply_apply] at hpp
    have := h.ibp _ hφ' i
    rw [← hI, ← hJ] at this
    simpa [hG, hpp] using this


theorem gT_single (N : ℕ+) (g : ParticleSpace 1 N → Fin N → Tangent 1) (x : ParticleSpace 1 N)
    (i : Fin N) :
    g x i = (EuclideanSpace.single (0 : Fin 1) (gTorus N g (EE N x) i) : Tangent 1) := by
  ext j
  fin_cases j
  simp [gTorus]

theorem integral_sq_EE (N : ℕ+) (ψ : ParticleSpace 1 N → ℝ) :
    ∫ y, ψ ((EE N).symm y) ^ 2 ∂haar (N : ℕ) = ∫ x, ψ x ^ 2 ∂particleHaar 1 N := by
  have e := (mp_EE N).integral_comp' (fun y => ψ ((EE N).symm y) ^ 2)
  simp only [MeasurableEquiv.symm_apply_apply] at e
  exact e.symm

theorem integral_gTorus (N : ℕ+) (g : ParticleSpace 1 N → Fin N → Tangent 1) :
    ∫ y, ‖gTorus N g y‖ ^ 2 ∂haar (N : ℕ) = ∫ x, particleTangentNormSq (g x) ∂particleHaar 1 N :=
  (integral_normSq_particle N (v := gTorus N g) (G := g) (fun x i => gT_single N g x i)).symm

theorem multiplier_particle (κ : ℝ) (hκ : 0 ≤ κ) (N : ℕ+) {ψ : ParticleSpace 1 N → ℝ}
    {g : ParticleSpace 1 N → Fin N → Tangent 1} (hg : IsParticleHaarWeakGradient N ψ g) :
    MemLp (fun x i => ψ x • roughForce κ N x i) 2 (particleHaar 1 N) ∧
    Real.sqrt (∫ x, particleTangentNormSq (fun i => ψ x • roughForce κ N x i) ∂particleHaar 1 N) ≤
      κ * (8 / 3 + 2 * Real.pi) *
          Real.sqrt (∫ x, particleTangentNormSq (g x) ∂particleHaar 1 N) +
        2 * Real.pi * κ * Real.sqrt (∫ x, ψ x ^ 2 ∂particleHaar 1 N) := by
  obtain ⟨hmem, hb⟩ := multiplier_torus κ hκ N (transport_weak N hg)
  have hG : ∀ x i, (ψ x • roughForce κ N x i) = (EuclideanSpace.single (0 : Fin 1)
      ((ψ ((EE N).symm (EE N x)) • gTorus N (roughForce κ N) (EE N x)) i) : Tangent 1) := by
    intro x i
    ext j
    fin_cases j
    simp [gTorus]
  refine ⟨memLp_particle_of_torus N hmem hG, ?_⟩
  rw [integral_normSq_particle N (v := fun y => ψ ((EE N).symm y) • gTorus N (roughForce κ N) y) (G := fun x i => ψ x • roughForce κ N x i) hG, ← integral_gTorus N g, ← integral_sq_EE N ψ]
  exact hb


theorem absorb_arith {v w u c d : ℝ} (hv : 0 ≤ v) (hu : 0 ≤ u)
    (hc : c < 1) (hd0 : 0 ≤ d) (hd : d < 1) (h : v ≤ w + (c * v + d * u) / 2) :
    v ≤ 2 * w + d * u ∧ v ^ 2 ≤ 8 * w ^ 2 + 2 * u ^ 2 := by
  have h1 : c * v ≤ v := by nlinarith
  have h2 : v ≤ 2 * w + d * u := by linarith
  refine ⟨h2, ?_⟩
  have h3 : v ^ 2 ≤ (2 * w + d * u) ^ 2 := by gcongr
  have h4 : (d * u) ^ 2 ≤ u ^ 2 := by
    have : d * u ≤ u := by nlinarith
    have h0 : 0 ≤ d * u := mul_nonneg hd0 hu
    nlinarith
  nlinarith [sq_nonneg (2 * w - d * u)]

theorem torus_absorb (κ : ℝ) (hκ : 0 ≤ κ) (hc : κ * (8 / 3 + 2 * Real.pi) < 1)
    (hd : 2 * Real.pi * κ < 1) (N : ℕ+) {ψ' : Torus (N : ℕ) → ℝ} {G' A : Torus (N : ℕ) → Tangent (N : ℕ)}
    (hψ : IsWeakGradient ψ' G') (hA : MemLp A 2 (haar (N : ℕ)))
    (hGA : ∀ y, G' y = A y + (-(1 / 2 : ℝ) * ψ' y) • gTorus N (roughForce κ N) y) :
    Real.sqrt (∫ y, ‖G' y‖ ^ 2 ∂haar (N : ℕ)) ≤
        2 * Real.sqrt (∫ y, ‖A y‖ ^ 2 ∂haar (N : ℕ)) +
          2 * Real.pi * κ * Real.sqrt (∫ y, ψ' y ^ 2 ∂haar (N : ℕ)) ∧
      ∫ y, ‖G' y‖ ^ 2 ∂haar (N : ℕ) ≤
        8 * ∫ y, ‖A y‖ ^ 2 ∂haar (N : ℕ) + 2 * ∫ y, ψ' y ^ 2 ∂haar (N : ℕ) := by
  obtain ⟨hmem, hb⟩ := multiplier_torus κ hκ N hψ
  set M : Torus (N : ℕ) → Tangent (N : ℕ) := fun y => ψ' y • gTorus N (roughForce κ N) y with hM
  set B : Torus (N : ℕ) → Tangent (N : ℕ) := (-(1 / 2 : ℝ)) • M with hBdef
  have hB : MemLp B 2 (haar (N : ℕ)) := hmem.const_smul _
  have hGeq : G' = A + B := by
    funext y
    simp [hGA, hBdef, hM, smul_smul]
  have hG2 : MemLp G' 2 (haar (N : ℕ)) := by rw [hGeq]; exact hA.add hB
  have hle := eLpNorm_add_le (μ := haar (N : ℕ)) (p := 2) (f := A) (g := B) (by norm_num)
  have e1 : (eLpNorm G' 2 (haar (N : ℕ))).toReal ≤
      (eLpNorm A 2 (haar (N : ℕ))).toReal + (eLpNorm B 2 (haar (N : ℕ))).toReal := by
    rw [← ENNReal.toReal_add hA.eLpNorm_ne_top hB.eLpNorm_ne_top]
    refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hA.eLpNorm_ne_top, hB.eLpNorm_ne_top⟩) ?_
    rw [hGeq]; exact hle
  have e2 : (eLpNorm B 2 (haar (N : ℕ))).toReal = 1 / 2 * (eLpNorm M 2 (haar (N : ℕ))).toReal := by
    rw [hBdef, eLpNorm_const_smul, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs]
    norm_num
  have tG := DGPS.Analysis.ForceMultiplierH1.toReal_eLpNorm_two hG2
  have tA := DGPS.Analysis.ForceMultiplierH1.toReal_eLpNorm_two hA
  have tM := DGPS.Analysis.ForceMultiplierH1.toReal_eLpNorm_two hmem
  rw [tG, tA, e2, tM] at e1
  have hbM : Real.sqrt (∫ y, ‖M y‖ ^ 2 ∂haar (N : ℕ)) ≤
      κ * (8 / 3 + 2 * Real.pi) * Real.sqrt (∫ y, ‖G' y‖ ^ 2 ∂haar (N : ℕ)) +
        2 * Real.pi * κ * Real.sqrt (∫ y, ψ' y ^ 2 ∂haar (N : ℕ)) := hb
  have hv0 := Real.sqrt_nonneg (∫ y, ‖G' y‖ ^ 2 ∂haar (N : ℕ))
  have hw0 := Real.sqrt_nonneg (∫ y, ‖A y‖ ^ 2 ∂haar (N : ℕ))
  have hu0 := Real.sqrt_nonneg (∫ y, ψ' y ^ 2 ∂haar (N : ℕ))
  have hc0 : 0 ≤ κ * (8 / 3 + 2 * Real.pi) := by positivity
  have hd0 : 0 ≤ 2 * Real.pi * κ := by positivity
  have key := absorb_arith (w := Real.sqrt (∫ y, ‖A y‖ ^ 2 ∂haar (N : ℕ))) hv0 hu0 hc hd0 hd (by linarith)
  refine ⟨key.1, ?_⟩
  have iG : 0 ≤ ∫ y, ‖G' y‖ ^ 2 ∂haar (N : ℕ) := integral_nonneg fun _ => by positivity
  have iA : 0 ≤ ∫ y, ‖A y‖ ^ 2 ∂haar (N : ℕ) := integral_nonneg fun _ => by positivity
  have iu : 0 ≤ ∫ y, ψ' y ^ 2 ∂haar (N : ℕ) := integral_nonneg fun _ => by positivity
  have := key.2
  rwa [Real.sq_sqrt iG, Real.sq_sqrt iA, Real.sq_sqrt iu] at this


theorem smooth_W1infty {d : ℕ} {φ : Torus d → ℝ} (hφ : IsSmoothPeriodic φ) :
    IsWeakGradientLp ⊤ φ (smoothGrad φ) where
  memLp := hφ.memLp_top
  memLp_grad := by
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      hφ.continuous_smoothGrad.continuousOn
    exact memLp_top_of_bound hφ.continuous_smoothGrad.aestronglyMeasurable C
      (Eventually.of_forall fun x => hC x (Set.mem_univ x))
  ibp := hφ.isWeakGradient.ibp

theorem p_nonneg' (κ : ℝ) (N : ℕ+) (x : ParticleSpace 1 N) : 0 ≤ p κ N x :=
  mul_nonneg (inv_nonneg.2 (K_pos κ N).le) (Real.exp_pos _).le

theorem small_fixed_coupling_absorption_smooth (κ : ℝ) (hκ : 0 ≤ κ)
    (hc : κ * (8 / 3 + 2 * Real.pi) < 1) (hd : 2 * Real.pi * κ < 1) (N : ℕ+)
    {f : ParticleSpace 1 N → ℝ} (hf : IsSmoothPeriodicParticle f)
    {g : ParticleSpace 1 N → Fin N → Tangent 1}
    (hg : IsParticleWeakGradient (kernelData κ) N f g) :
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
  have hf' := abs_isSmooth_comp_EE_symm N hf
  have hae : gTorus N g =ᵐ[haar (N : ℕ)] smoothGrad (fun y => f ((EE N).symm y)) :=
    hgT.ae_eq hf'.isWeakGradient
  have hprod := (isWeakGradient_sP κ hκ N).mul_W1infty (smooth_W1infty hf')
  set A : Torus (N : ℕ) → Tangent (N : ℕ) := fun y => sP κ N y • gTorus N g y with hA
  set G' : Torus (N : ℕ) → Tangent (N : ℕ) := fun y => A y +
    (-(1 / 2 : ℝ) * (f ((EE N).symm y) * sP κ N y)) • gTorus N (roughForce κ N) y with hG'
  have hprod2 : IsWeakGradient (fun y => f ((EE N).symm y) * sP κ N y) G' := by
    refine hprod.congr_ae (Eventually.of_forall fun y => mul_comm _ _) ?_
    filter_upwards [hae] with y hy
    simp only [hG', hA]
    rw [← hy]
    module
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
  -- norm bookkeeping
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
  exact ⟨hW, h1, h2⟩


/-- H1027: small fixed coupling absorption at `κ = 1/100`. -/
theorem small_fixed_coupling_absorption (N : ℕ+) :
    (1 / 100 : ℝ) * (8 / 3 + 2 * Real.pi) < 1 ∧ 2 * Real.pi * (1 / 100 : ℝ) < 1 ∧
    (∀ (ψ : ParticleSpace 1 N → ℝ) (g : ParticleSpace 1 N → Fin N → Tangent 1),
      IsParticleHaarWeakGradient N ψ g →
      MemLp (fun x i => ψ x • roughForce (1 / 100) N x i) 2 (particleHaar 1 N) ∧
      Real.sqrt (∫ x, particleTangentNormSq (fun i => ψ x • roughForce (1 / 100) N x i)
          ∂particleHaar 1 N) ≤
        (1 / 100 : ℝ) * (8 / 3 + 2 * Real.pi) *
            Real.sqrt (∫ x, particleTangentNormSq (g x) ∂particleHaar 1 N) +
          2 * Real.pi * (1 / 100 : ℝ) * Real.sqrt (∫ x, ψ x ^ 2 ∂particleHaar 1 N)) ∧
    (∀ (f : ParticleSpace 1 N → ℝ), IsSmoothPeriodicParticle f →
      ∀ (g : ParticleSpace 1 N → Fin N → Tangent 1),
      IsParticleWeakGradient (kernelData (1 / 100)) N f g →
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
          2 * ∫ x, f x ^ 2 ∂particleLaw (kernelData (1 / 100)) N) := by
  have hpi := Real.pi_lt_d2
  have hc : (1 / 100 : ℝ) * (8 / 3 + 2 * Real.pi) < 1 := by nlinarith
  have hd : 2 * Real.pi * (1 / 100 : ℝ) < 1 := by nlinarith
  exact ⟨hc, hd, fun _ _ hg => multiplier_particle (1 / 100) (by norm_num) N hg,
    fun _ hf _ hg => small_fixed_coupling_absorption_smooth (1 / 100) (by norm_num) hc hd N hf hg⟩

end DGPS.Examples.PositiveH1.Transfer
