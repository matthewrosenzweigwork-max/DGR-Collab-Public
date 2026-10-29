import DGPS.FiniteN.SecondHarmonicResidual

/-!
# Residual orthogonality and reversible energy (FIN092)

For the second-harmonic Gibbs generator `L_N = Δ − ∇H_N·∇` (`particleGenerator`) on the unit-period
circle with `N` particles:

* reversibility: `⟨−L_N u, v⟩_{P_N} = E_N(u, v)` for smooth periodic `u, v`, where
  `E_N(u,v) = ∫ ∑ᵢ ∂ᵢu ∂ᵢv dP_N` (`particleMixedEnergy`, no factor `1/N`), proved by integrating
  the weighted divergence `div(e^{-H_N} ∇u · v)` over the torus (no boundary terms);
* `⟨R_N, 1⟩ = 0`, `⟨R_N, F_N⟩ = 0` and `E_N(F_N, R_N) = ‖R_N‖²`,

for every `N ≥ 1` (strict positivity of `‖R_N‖²` is FIN091, only for `N ≥ 2`).
-/

open MeasureTheory
open scoped ContDiff

namespace DGPS.FiniteN

/-- The bilinear Gibbs Dirichlet form `E_N(u, v) = ∫ ∑ᵢ ∂ᵢu ∂ᵢv dP_N` on smooth periodic
functions of the unit-period circle particle system (no factor `1/N`). -/
noncomputable def particleMixedEnergy (A : DGPS.InteractionData 1) (N : ℕ+)
    (u v : DGPS.ParticleSpace 1 N → ℝ) : ℝ :=
  ∫ x, ∑ i, DGPS.particlePartial i 0 u x * DGPS.particlePartial i 0 v x ∂DGPS.particleLaw A N

/-! ### Smoothness toolkit -/

section Smooth

variable {N : ℕ+}

theorem isSmooth_particlePartial {φ : DGPS.ParticleSpace 1 N → ℝ}
    (hφ : DGPS.IsSmoothPeriodicParticle φ) (i : Fin N) :
    DGPS.IsSmoothPeriodicParticle (DGPS.particlePartial i 0 φ) := by
  have h : DGPS.particlePartial i 0 φ =
      (DGPS.coordPartial (DGPS.particleIdx 1 N (i, 0)) (φ ∘ (DGPS.particleTorusEquiv 1 N).symm)) ∘
        DGPS.particleTorusEquiv 1 N :=
    funext (DGPS.particlePartial_eq_coordPartial φ i 0)
  rw [h]
  exact DGPS.isSmoothPeriodicParticle_comp_particleTorusEquiv
    ((DGPS.isSmoothPeriodic_comp_particleTorusEquiv_symm hφ).isSmoothPeriodic_coordPartial _)

theorem isSmooth_const (c : ℝ) : DGPS.IsSmoothPeriodicParticle (fun _ : DGPS.ParticleSpace 1 N => c) :=
  contDiff_const

theorem isSmooth_mul {φ ψ : DGPS.ParticleSpace 1 N → ℝ} (hφ : DGPS.IsSmoothPeriodicParticle φ)
    (hψ : DGPS.IsSmoothPeriodicParticle ψ) :
    DGPS.IsSmoothPeriodicParticle (fun x => φ x * ψ x) := hφ.mul hψ

theorem isSmooth_sub {φ ψ : DGPS.ParticleSpace 1 N → ℝ} (hφ : DGPS.IsSmoothPeriodicParticle φ)
    (hψ : DGPS.IsSmoothPeriodicParticle ψ) :
    DGPS.IsSmoothPeriodicParticle (fun x => φ x - ψ x) := hφ.sub hψ

theorem isSmooth_sum {φ : Fin N → DGPS.ParticleSpace 1 N → ℝ}
    (h : ∀ i, DGPS.IsSmoothPeriodicParticle (φ i)) :
    DGPS.IsSmoothPeriodicParticle (fun x => ∑ i, φ i x) :=
  ContDiff.sum fun i _ => h i

theorem isSmooth_exp_neg {H : DGPS.ParticleSpace 1 N → ℝ} (hH : DGPS.IsSmoothPeriodicParticle H) :
    DGPS.IsSmoothPeriodicParticle (fun x => Real.exp (-H x)) :=
  Real.contDiff_exp.comp hH.neg

theorem integrable_haar_of_smooth {φ : DGPS.ParticleSpace 1 N → ℝ}
    (hφ : DGPS.IsSmoothPeriodicParticle φ) : Integrable φ (DGPS.particleHaar 1 N) :=
  hφ.memLp_top.integrable le_top

theorem particlePartial_const (c : ℝ) (i : Fin N) (x : DGPS.ParticleSpace 1 N) :
    DGPS.particlePartial i 0 (fun _ => c) x = 0 := by
  unfold DGPS.particlePartial
  simp [Function.comp_def]

theorem particlePartial_exp_neg {H : DGPS.ParticleSpace 1 N → ℝ}
    (hH : DGPS.IsSmoothPeriodicParticle H) (i : Fin N) (x : DGPS.ParticleSpace 1 N) :
    DGPS.particlePartial i 0 (fun y => Real.exp (-H y)) x =
      -(Real.exp (-H x) * DGPS.particlePartial i 0 H x) := by
  unfold DGPS.particlePartial
  have hd : DifferentiableAt ℝ (H ∘ DGPS.particleLift) (fun k => SharpLSI.secT (x k)) :=
    (hH.differentiable (by simp)) _
  have h : ((fun y => Real.exp (-H y)) ∘ DGPS.particleLift) =
      fun z => Real.exp (-((H ∘ DGPS.particleLift) z)) := rfl
  have hE := fderiv_exp (f := fun z => -(H ∘ DGPS.particleLift) z)
    (x := fun k => SharpLSI.secT (x k)) hd.neg
  rw [h, hE, fderiv_fun_neg]
  simp [Function.comp_def, DGPS.FiniteN.PositiveRate.particleLift_secT]

end Smooth

/-! ### Weighted integration by parts on the torus -/

section Reversibility

variable {N : ℕ+}

/-- One label of the weighted divergence identity (integrals against Haar measure). -/
theorem weighted_ibp_label {H u v : DGPS.ParticleSpace 1 N → ℝ}
    (hH : DGPS.IsSmoothPeriodicParticle H) (hu : DGPS.IsSmoothPeriodicParticle u)
    (hv : DGPS.IsSmoothPeriodicParticle v) (i : Fin N) :
    ∫ x, Real.exp (-H x) * (DGPS.particlePartial i 0 u x * DGPS.particlePartial i 0 v x)
        ∂DGPS.particleHaar 1 N =
      ∫ x, Real.exp (-H x) * v x *
        (DGPS.particlePartial i 0 H x * DGPS.particlePartial i 0 u x -
          DGPS.particlePartial i 0 (DGPS.particlePartial i 0 u) x) ∂DGPS.particleHaar 1 N := by
  have hρ := isSmooth_exp_neg hH
  have hdu := isSmooth_particlePartial hu i
  have hdv := isSmooth_particlePartial hv i
  have hdH := isSmooth_particlePartial hH i
  have hddu := isSmooth_particlePartial hdu i
  have hφ : DGPS.IsSmoothPeriodicParticle (fun x => Real.exp (-H x) * v x) := isSmooth_mul hρ hv
  have hw := DGPS.FiniteN.PositiveRate.isParticleHaarWeakGradient_of_smooth hdu
  have key := hw.ibp _ hφ i 0
  have hp : ∀ x, DGPS.particlePartial i 0 (fun y => Real.exp (-H y) * v y) x =
      v x * (-(Real.exp (-H x) * DGPS.particlePartial i 0 H x)) +
        Real.exp (-H x) * DGPS.particlePartial i 0 v x := fun x => by
    rw [DGPS.FiniteN.PositiveRate.particlePartial_mul hρ hv, particlePartial_exp_neg hH]
  simp_rw [hp] at key
  have i1 : Integrable (fun x => Real.exp (-H x) * (DGPS.particlePartial i 0 u x *
      DGPS.particlePartial i 0 v x)) (DGPS.particleHaar 1 N) :=
    integrable_haar_of_smooth (isSmooth_mul hρ (isSmooth_mul hdu hdv))
  have i2 : Integrable (fun x => Real.exp (-H x) * v x *
      (DGPS.particlePartial i 0 H x * DGPS.particlePartial i 0 u x)) (DGPS.particleHaar 1 N) :=
    integrable_haar_of_smooth (isSmooth_mul (isSmooth_mul hρ hv) (isSmooth_mul hdH hdu))
  have i3 : Integrable (fun x => Real.exp (-H x) * v x *
      DGPS.particlePartial i 0 (DGPS.particlePartial i 0 u) x) (DGPS.particleHaar 1 N) :=
    integrable_haar_of_smooth (isSmooth_mul (isSmooth_mul hρ hv) hddu)
  have e1 : (fun x => DGPS.particlePartial i 0 u x * (v x * (-(Real.exp (-H x) *
        DGPS.particlePartial i 0 H x)) + Real.exp (-H x) * DGPS.particlePartial i 0 v x)) =
      fun x => Real.exp (-H x) * (DGPS.particlePartial i 0 u x * DGPS.particlePartial i 0 v x) -
        Real.exp (-H x) * v x * (DGPS.particlePartial i 0 H x *
          DGPS.particlePartial i 0 u x) := funext fun x => by ring
  have e2 : (fun x => DGPS.particlePartial i 0 (DGPS.particlePartial i 0 u) x *
        (Real.exp (-H x) * v x)) =
      fun x => Real.exp (-H x) * v x *
        DGPS.particlePartial i 0 (DGPS.particlePartial i 0 u) x := funext fun x => by ring
  rw [e1, integral_sub i1 i2, e2] at key
  have e3 : (fun x => Real.exp (-H x) * v x * (DGPS.particlePartial i 0 H x *
        DGPS.particlePartial i 0 u x - DGPS.particlePartial i 0 (DGPS.particlePartial i 0 u) x)) =
      fun x => Real.exp (-H x) * v x * (DGPS.particlePartial i 0 H x *
        DGPS.particlePartial i 0 u x) - Real.exp (-H x) * v x *
          DGPS.particlePartial i 0 (DGPS.particlePartial i 0 u) x :=
    funext fun x => by ring
  rw [e3, integral_sub i2 i3]
  linarith

/-- Reversibility of the Gibbs generator in Haar form. -/
theorem weighted_ibp {H u v : DGPS.ParticleSpace 1 N → ℝ}
    (hH : DGPS.IsSmoothPeriodicParticle H) (hu : DGPS.IsSmoothPeriodicParticle u)
    (hv : DGPS.IsSmoothPeriodicParticle v) :
    ∫ x, Real.exp (-H x) * ∑ i, DGPS.particlePartial i 0 u x * DGPS.particlePartial i 0 v x
        ∂DGPS.particleHaar 1 N =
      ∫ x, Real.exp (-H x) * v x *
        (∑ i, DGPS.particlePartial i 0 H x * DGPS.particlePartial i 0 u x -
          ∑ i, DGPS.particlePartial i 0 (DGPS.particlePartial i 0 u) x) ∂DGPS.particleHaar 1 N := by
  have hρ := isSmooth_exp_neg hH
  have s1 : ∀ i : Fin N, Integrable (fun x => Real.exp (-H x) * (DGPS.particlePartial i 0 u x *
      DGPS.particlePartial i 0 v x)) (DGPS.particleHaar 1 N) := fun i =>
    integrable_haar_of_smooth (isSmooth_mul hρ (isSmooth_mul (isSmooth_particlePartial hu i)
      (isSmooth_particlePartial hv i)))
  have s2 : ∀ i : Fin N, Integrable (fun x => Real.exp (-H x) * v x *
      (DGPS.particlePartial i 0 H x * DGPS.particlePartial i 0 u x -
        DGPS.particlePartial i 0 (DGPS.particlePartial i 0 u) x)) (DGPS.particleHaar 1 N) := fun i =>
    integrable_haar_of_smooth (isSmooth_mul (isSmooth_mul hρ hv)
      (isSmooth_sub (isSmooth_mul (isSmooth_particlePartial hH i) (isSmooth_particlePartial hu i))
        (isSmooth_particlePartial (isSmooth_particlePartial hu i) i)))
  have l1 : ∀ x, Real.exp (-H x) * ∑ i, DGPS.particlePartial i 0 u x * DGPS.particlePartial i 0 v x =
      ∑ i, Real.exp (-H x) * (DGPS.particlePartial i 0 u x * DGPS.particlePartial i 0 v x) :=
    fun x => Finset.mul_sum _ _ _
  have l2 : ∀ x, Real.exp (-H x) * v x *
      (∑ i, DGPS.particlePartial i 0 H x * DGPS.particlePartial i 0 u x -
        ∑ i, DGPS.particlePartial i 0 (DGPS.particlePartial i 0 u) x) =
      ∑ i, Real.exp (-H x) * v x * (DGPS.particlePartial i 0 H x * DGPS.particlePartial i 0 u x -
        DGPS.particlePartial i 0 (DGPS.particlePartial i 0 u) x) := fun x => by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  simp_rw [l1, l2]
  rw [integral_finsetSum _ (fun i _ => s1 i), integral_finsetSum _ (fun i _ => s2 i)]
  exact Finset.sum_congr rfl fun i _ => weighted_ibp_label hH hu hv i

/-- **Reversibility** for any smooth periodic interaction Hamiltonian: `⟨−L u, v⟩ = E(u, v)`. -/
theorem particle_reversibility (A : DGPS.InteractionData 1)
    (hH : DGPS.IsSmoothPeriodicParticle (DGPS.particleHamiltonian A N))
    {u v : DGPS.ParticleSpace 1 N → ℝ} (hu : DGPS.IsSmoothPeriodicParticle u)
    (hv : DGPS.IsSmoothPeriodicParticle v) :
    ∫ x, -particleGenerator A N u x * v x ∂DGPS.particleLaw A N = particleMixedEnergy A N u v := by
  unfold particleMixedEnergy
  rw [DGPS.Particle.integral_particleLaw, DGPS.Particle.integral_particleLaw]
  have hd : ∀ x, DGPS.particleDensity A N x =
      (DGPS.particlePartition A N)⁻¹ * Real.exp (-DGPS.particleHamiltonian A N x) := fun _ => rfl
  simp_rw [hd, mul_assoc, integral_const_mul]
  congr 1
  rw [weighted_ibp hH hu hv]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [particleGenerator]
  ring

end Reversibility

/-! ### The second-harmonic residual -/

theorem secondHarmonicResidual_eq_fun (κ : ℝ) (N : ℕ+) :
    secondHarmonicResidual κ N = explicitResidual κ N :=
  funext (secondHarmonicResidual_eq κ N)

theorem isSmooth_secondHarmonicResidual (κ : ℝ) (N : ℕ+) :
    DGPS.IsSmoothPeriodicParticle (secondHarmonicResidual κ N) := by
  rw [secondHarmonicResidual_eq_fun]; exact isSmooth_explicitResidual κ N

theorem continuous_secondHarmonicResidual (κ : ℝ) (N : ℕ+) :
    Continuous (secondHarmonicResidual κ N) := by
  rw [secondHarmonicResidual_eq_fun]; exact continuous_explicitResidual κ N

/-- The mixed energy of a smooth test with itself is the Gibbs energy of its `H¹` representative. -/
theorem particleEnergy_eq_mixedEnergy (A : DGPS.InteractionData 1) (N : ℕ+)
    (f : DGPS.ParticleH1 A N) (hf : DGPS.IsSmoothPeriodicParticle f.1) :
    DGPS.particleEnergy A N f = particleMixedEnergy A N f.1 f.1 := by
  have hG := DGPS.FiniteN.PositiveRate.isParticleHaarWeakGradient_of_smooth hf
  have hGP : DGPS.IsParticleWeakGradient A N f.1
      (fun x i => WithLp.toLp 2 fun j => DGPS.particlePartial i j f.1 x) :=
    (DGPS.isParticleWeakGradient_iff A N _ _).2 hG
  rw [DGPS.particleEnergy_eq_of_isParticleWeakGradient f hGP]
  unfold particleMixedEnergy
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [DGPS.particleTangentNormSq_eq, Fin.sum_univ_one]
  refine Finset.sum_congr rfl fun i _ => by ring

/-- **FIN092.** For the second-harmonic Gibbs generator `L_N` (every `N ≥ 1`, every `κ`):
`⟨−L_N u, v⟩ = E_N(u, v)` for smooth periodic `u, v` (and `E_N(f) = E_N(f, f)`), and for the
residual `R_N = −L_N F_N − a₀ F_N` of the symmetric trial `F_N`:
`⟨R_N, 1⟩ = 0`, `⟨R_N, F_N⟩ = 0` and `E_N(F_N, R_N) = ‖R_N‖²`. -/
theorem residual_orthogonality_and_reversible_energy (κ : ℝ) (N : ℕ+) :
    (∀ u v : DGPS.ParticleSpace 1 N → ℝ, DGPS.IsSmoothPeriodicParticle u →
      DGPS.IsSmoothPeriodicParticle v →
      ∫ x, -particleGenerator (secondHarmonicData κ) N u x * v x
          ∂DGPS.particleLaw (secondHarmonicData κ) N =
        particleMixedEnergy (secondHarmonicData κ) N u v) ∧
    (∀ f : DGPS.ParticleH1 (secondHarmonicData κ) N, DGPS.IsSmoothPeriodicParticle f.1 →
      DGPS.particleEnergy (secondHarmonicData κ) N f =
        particleMixedEnergy (secondHarmonicData κ) N f.1 f.1) ∧
    ∫ x, secondHarmonicResidual κ N x ∂DGPS.particleLaw (secondHarmonicData κ) N = 0 ∧
    ∫ x, secondHarmonicResidual κ N x * harmonicTrial N x
        ∂DGPS.particleLaw (secondHarmonicData κ) N = 0 ∧
    particleMixedEnergy (secondHarmonicData κ) N (harmonicTrial N) (secondHarmonicResidual κ N) =
      ∫ x, (secondHarmonicResidual κ N x) ^ 2 ∂DGPS.particleLaw (secondHarmonicData κ) N := by
  set A := secondHarmonicData κ with hA
  set P := DGPS.particleLaw A N with hP
  have hH : DGPS.IsSmoothPeriodicParticle (DGPS.particleHamiltonian A N) := isSmooth_hamiltonian κ N
  have hrev : ∀ u v : DGPS.ParticleSpace 1 N → ℝ, DGPS.IsSmoothPeriodicParticle u →
      DGPS.IsSmoothPeriodicParticle v →
      ∫ x, -particleGenerator A N u x * v x ∂P = particleMixedEnergy A N u v :=
    fun u v hu hv => particle_reversibility A hH hu hv
  have hFs := isSmooth_harmonicTrial N
  have hRs := isSmooth_secondHarmonicResidual κ N
  have hPprob : IsProbabilityMeasure P := DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  have hint : ∀ {h : DGPS.ParticleSpace 1 N → ℝ}, Continuous h → Integrable h P := fun hc =>
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFc := continuous_harmonicTrial N
  have hRc := continuous_secondHarmonicResidual κ N
  -- the identity `-L F = R + a₀ F`
  have hLF : ∀ x, -particleGenerator A N (harmonicTrial N) x =
      secondHarmonicResidual κ N x + DGPS.Circle.AngularNormalization.a0 * harmonicTrial N x :=
    fun x => by unfold secondHarmonicResidual; ring
  -- FIN090 inputs
  obtain ⟨f, hf1, -, -, -, hmean, hvar, -, hen, -⟩ := exact_symmetric_harmonic_covariance_trial κ N
  have hfv : f.1 = harmonicTrial N := hf1
  have hmean' : ∫ x, harmonicTrial N x ∂P = 0 := by rw [← hfv]; exact hmean
  have hvar' : ProbabilityTheory.variance (harmonicTrial N) P = (N : ℝ) / 2 := by
    rw [← hfv]; exact hvar
  have hsq : ∫ x, (harmonicTrial N x) ^ 2 ∂P = (N : ℝ) / 2 := by
    rw [ProbabilityTheory.variance_eq_integral hFc.aemeasurable] at hvar'
    simpa [hmean'] using hvar'
  have hEFF : particleMixedEnergy A N (harmonicTrial N) (harmonicTrial N) =
      DGPS.Circle.AngularNormalization.a0 * ∫ x, (harmonicTrial N x) ^ 2 ∂P := by
    have := particleEnergy_eq_mixedEnergy A N f (by rw [hfv]; exact hFs)
    rw [hfv] at this
    rw [← this, hen, hsq]; ring
  -- ⟨R, F⟩ = 0
  have hRF : ∫ x, secondHarmonicResidual κ N x * harmonicTrial N x ∂P = 0 := by
    have h1 := hrev _ _ hFs hFs
    simp_rw [hLF, add_mul] at h1
    have j1 : Integrable (fun x => secondHarmonicResidual κ N x * harmonicTrial N x) P :=
      hint (hRc.mul hFc)
    have j2 : Integrable (fun x => DGPS.Circle.AngularNormalization.a0 * harmonicTrial N x *
        harmonicTrial N x) P := hint ((continuous_const.mul hFc).mul hFc)
    rw [integral_add j1 j2, hEFF] at h1
    have : ∫ x, DGPS.Circle.AngularNormalization.a0 * harmonicTrial N x * harmonicTrial N x ∂P =
        DGPS.Circle.AngularNormalization.a0 * ∫ x, (harmonicTrial N x) ^ 2 ∂P := by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    linarith
  refine ⟨hrev, fun f hf => particleEnergy_eq_mixedEnergy A N f hf, ?_, hRF, ?_⟩
  · -- ⟨R, 1⟩ = 0
    have h1 := hrev _ _ hFs (isSmooth_const (N := N) 1)
    have h0 : particleMixedEnergy A N (harmonicTrial N) (fun _ => 1) = 0 := by
      unfold particleMixedEnergy
      simp [particlePartial_const]
    rw [h0] at h1
    simp_rw [hLF, mul_one] at h1
    have j1 : Integrable (fun x => secondHarmonicResidual κ N x) P := hint hRc
    have j2 : Integrable (fun x => DGPS.Circle.AngularNormalization.a0 * harmonicTrial N x) P :=
      hint (continuous_const.mul hFc)
    rw [integral_add j1 j2, integral_const_mul, hmean'] at h1
    linarith
  · -- E(F, R) = ‖R‖²
    have h1 := hrev _ _ hFs hRs
    simp_rw [hLF, add_mul] at h1
    have j1 : Integrable (fun x => secondHarmonicResidual κ N x * secondHarmonicResidual κ N x) P :=
      hint (hRc.mul hRc)
    have j2 : Integrable (fun x => DGPS.Circle.AngularNormalization.a0 * harmonicTrial N x *
        secondHarmonicResidual κ N x) P := hint ((continuous_const.mul hFc).mul hRc)
    rw [integral_add j1 j2] at h1
    have : ∫ x, DGPS.Circle.AngularNormalization.a0 * harmonicTrial N x *
        secondHarmonicResidual κ N x ∂P = 0 := by
      have e : ∀ x, DGPS.Circle.AngularNormalization.a0 * harmonicTrial N x *
          secondHarmonicResidual κ N x = DGPS.Circle.AngularNormalization.a0 *
            (secondHarmonicResidual κ N x * harmonicTrial N x) := fun x => by ring
      simp_rw [e]
      rw [integral_const_mul, hRF, mul_zero]
    rw [this] at h1
    rw [← h1, add_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [sq])

end DGPS.FiniteN
