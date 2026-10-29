import DGPS.FiniteN.SecondHarmonicOrthogonality

/-!
# Strict symmetric perturbation quotient (FIN093)

For `κ > 0` and `N ≥ 2` there is `η > 0` such that `F_{N,η} = F_N − η R_N` is a smooth, permutation
symmetric, centered `H¹(P_N)` test with positive variance and
`E(F_{N,η}) − a₀‖F_{N,η}‖² = −2η‖R_N‖² + η²[E(R_N) − a₀‖R_N‖²] < 0`; hence its Poincare quotient
is strictly below `a₀`.
-/

open MeasureTheory

namespace DGPS.FiniteN

section Perturbation

variable {N : ℕ+}

theorem particlePartial_sub_smul {F R : DGPS.ParticleSpace 1 N → ℝ}
    (hF : DGPS.IsSmoothPeriodicParticle F) (hR : DGPS.IsSmoothPeriodicParticle R) (η : ℝ)
    (i : Fin N) (x : DGPS.ParticleSpace 1 N) :
    DGPS.particlePartial i 0 (fun y => F y - η * R y) x =
      DGPS.particlePartial i 0 F x - η * DGPS.particlePartial i 0 R x := by
  unfold DGPS.particlePartial
  have hdF : DifferentiableAt ℝ (F ∘ DGPS.particleLift) (fun k => SharpLSI.secT (x k)) :=
    (hF.differentiable (by simp)) _
  have hdR : DifferentiableAt ℝ (R ∘ DGPS.particleLift) (fun k => SharpLSI.secT (x k)) :=
    (hR.differentiable (by simp)) _
  have h : ((fun y => F y - η * R y) ∘ DGPS.particleLift) =
      fun z => (F ∘ DGPS.particleLift) z - η * (R ∘ DGPS.particleLift) z := rfl
  rw [h, fderiv_fun_sub hdF (hdR.const_mul η), fderiv_const_mul hdR]
  simp

theorem isSmooth_sub_smul {F R : DGPS.ParticleSpace 1 N → ℝ}
    (hF : DGPS.IsSmoothPeriodicParticle F) (hR : DGPS.IsSmoothPeriodicParticle R) (η : ℝ) :
    DGPS.IsSmoothPeriodicParticle (fun y => F y - η * R y) :=
  isSmooth_sub hF (isSmooth_mul (isSmooth_const η) hR)

/-- Smooth periodic functions are integrable for the Gibbs law. -/
theorem integrable_law_of_smooth (A : DGPS.InteractionData 1) {φ : DGPS.ParticleSpace 1 N → ℝ}
    (hφ : DGPS.IsSmoothPeriodicParticle φ) : Integrable φ (DGPS.particleLaw A N) := by
  have : IsProbabilityMeasure (DGPS.particleLaw A N) :=
    DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  exact ((DGPS.Particle.memLp_particleLaw_iff A N).2 hφ.memLp_top).integrable le_top

/-- Quadratic expansion of the mixed energy along `F − ηR`. -/
theorem particleMixedEnergy_sub_smul (A : DGPS.InteractionData 1) {F R : DGPS.ParticleSpace 1 N → ℝ}
    (hF : DGPS.IsSmoothPeriodicParticle F) (hR : DGPS.IsSmoothPeriodicParticle R) (η : ℝ) :
    particleMixedEnergy A N (fun y => F y - η * R y) (fun y => F y - η * R y) =
      particleMixedEnergy A N F F - 2 * η * particleMixedEnergy A N F R +
        η ^ 2 * particleMixedEnergy A N R R := by
  have hdF := fun i => isSmooth_particlePartial hF i
  have hdR := fun i => isSmooth_particlePartial hR i
  have i1 : Integrable (fun x => ∑ i, DGPS.particlePartial i 0 F x * DGPS.particlePartial i 0 F x)
      (DGPS.particleLaw A N) :=
    integrable_law_of_smooth A (isSmooth_sum fun i => isSmooth_mul (hdF i) (hdF i))
  have i2 : Integrable (fun x => ∑ i, DGPS.particlePartial i 0 F x * DGPS.particlePartial i 0 R x)
      (DGPS.particleLaw A N) :=
    integrable_law_of_smooth A (isSmooth_sum fun i => isSmooth_mul (hdF i) (hdR i))
  have i3 : Integrable (fun x => ∑ i, DGPS.particlePartial i 0 R x * DGPS.particlePartial i 0 R x)
      (DGPS.particleLaw A N) :=
    integrable_law_of_smooth A (isSmooth_sum fun i => isSmooth_mul (hdR i) (hdR i))
  unfold particleMixedEnergy
  have e : (fun x => ∑ i, DGPS.particlePartial i 0 (fun y => F y - η * R y) x *
      DGPS.particlePartial i 0 (fun y => F y - η * R y) x) =
      fun x => (∑ i, DGPS.particlePartial i 0 F x * DGPS.particlePartial i 0 F x) -
        2 * η * (∑ i, DGPS.particlePartial i 0 F x * DGPS.particlePartial i 0 R x) +
        η ^ 2 * (∑ i, DGPS.particlePartial i 0 R x * DGPS.particlePartial i 0 R x) :=
    funext fun x => by
      simp_rw [particlePartial_sub_smul hF hR η, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
  have j1 : Integrable (fun x => (∑ i, DGPS.particlePartial i 0 F x * DGPS.particlePartial i 0 F x) -
      2 * η * (∑ i, DGPS.particlePartial i 0 F x * DGPS.particlePartial i 0 R x))
      (DGPS.particleLaw A N) := i1.sub (i2.const_mul _)
  rw [e, integral_add j1 (i3.const_mul _), integral_sub i1 (i2.const_mul _),
    integral_const_mul, integral_const_mul]

end Perturbation

/-- **FIN093.** For `κ > 0` and `N ≥ 2` there is `η > 0` such that `F_{N,η} = F_N − η R_N` is a
smooth, permutation symmetric, centered `H¹(P_N)` test with positive variance, and
`E(F_{N,η}) − a₀‖F_{N,η}‖² = −2η‖R_N‖² + η²[E(R_N) − a₀‖R_N‖²] < 0`; hence its Poincare quotient is
strictly below `a₀`. -/
theorem strict_symmetric_perturbation_quotient (κ : ℝ) (hκ : 0 < κ) (N : ℕ+) (hN : 2 ≤ N) :
    ∃ η : ℝ, 0 < η ∧ ∃ g : DGPS.ParticleH1 (secondHarmonicData κ) N,
      g.1 = (fun x => harmonicTrial N x - η * secondHarmonicResidual κ N x) ∧
      DGPS.IsSmoothPeriodicParticle g.1 ∧
      (∀ (σ : Equiv.Perm (Fin N)) (x : DGPS.ParticleSpace 1 N),
        g.1 (DGPS.permuteParticles σ x) = g.1 x) ∧
      DGPS.IsSymmetricParticleTest g ∧
      ∫ x, g.1 x ∂DGPS.particleLaw (secondHarmonicData κ) N = 0 ∧
      0 < ProbabilityTheory.variance g.1 (DGPS.particleLaw (secondHarmonicData κ) N) ∧
      DGPS.particleEnergy (secondHarmonicData κ) N g -
          DGPS.Circle.AngularNormalization.a0 *
            ∫ x, (g.1 x) ^ 2 ∂DGPS.particleLaw (secondHarmonicData κ) N =
        -2 * η * ∫ x, (secondHarmonicResidual κ N x) ^ 2
            ∂DGPS.particleLaw (secondHarmonicData κ) N +
          η ^ 2 * (particleMixedEnergy (secondHarmonicData κ) N (secondHarmonicResidual κ N)
              (secondHarmonicResidual κ N) -
            DGPS.Circle.AngularNormalization.a0 *
              ∫ x, (secondHarmonicResidual κ N x) ^ 2
                ∂DGPS.particleLaw (secondHarmonicData κ) N) ∧
      DGPS.particleEnergy (secondHarmonicData κ) N g -
          DGPS.Circle.AngularNormalization.a0 *
            ∫ x, (g.1 x) ^ 2 ∂DGPS.particleLaw (secondHarmonicData κ) N < 0 ∧
      DGPS.particlePoincareQuotient (secondHarmonicData κ) N g <
        ENNReal.ofReal DGPS.Circle.AngularNormalization.a0 := by
  set A := secondHarmonicData κ with hA
  set P := DGPS.particleLaw A N with hP
  have hPprob : IsProbabilityMeasure P := DGPS.Particle.particleLaw_isProbabilityMeasure' A N
  set F := harmonicTrial N with hFdef
  set R := secondHarmonicResidual κ N with hRdef
  set a0 := DGPS.Circle.AngularNormalization.a0 with ha0def
  have ha0 : 0 < a0 := DGPS.Circle.AngularNormalization.a0_pos
  -- inputs
  obtain ⟨-, hRs, hRsym, -, hApos⟩ := second_harmonic_residual_explicit_strict_sign κ hκ N hN
  obtain ⟨-, -, hRmean, hRF, hER⟩ := residual_orthogonality_and_reversible_energy κ N
  have hFs : DGPS.IsSmoothPeriodicParticle F := isSmooth_harmonicTrial N
  have hFc : Continuous F := continuous_harmonicTrial N
  have hRc : Continuous R := continuous_secondHarmonicResidual κ N
  have hint : ∀ {h : DGPS.ParticleSpace 1 N → ℝ}, Continuous h → Integrable h P := fun hc =>
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  -- FIN090 data about F
  obtain ⟨f, hf1, -, hFsym, -, hmean, hvar, -, hen, -⟩ := exact_symmetric_harmonic_covariance_trial κ N
  have hfv : f.1 = F := hf1
  have hmean' : ∫ x, F x ∂P = 0 := by rw [← hfv]; exact hmean
  have hvar' : ProbabilityTheory.variance F P = (N : ℝ) / 2 := by rw [← hfv]; exact hvar
  have hsq : ∫ x, (F x) ^ 2 ∂P = (N : ℝ) / 2 := by
    rw [ProbabilityTheory.variance_eq_integral hFc.aemeasurable] at hvar'
    simpa [hmean'] using hvar'
  have hEFF : particleMixedEnergy A N F F = a0 * ∫ x, (F x) ^ 2 ∂P := by
    have := particleEnergy_eq_mixedEnergy A N f (by rw [hfv]; exact hFs)
    rw [hfv] at this
    rw [← this, hen, hsq]; ring
  have hFsym' : ∀ (σ : Equiv.Perm (Fin N)) (x : DGPS.ParticleSpace 1 N),
      F (DGPS.permuteParticles σ x) = F x := fun σ x => by rw [← hfv]; exact hFsym σ x
  -- constants
  set Anorm := ∫ x, (R x) ^ 2 ∂P with hAnorm
  set B := particleMixedEnergy A N R R - a0 * Anorm with hB
  have hAnorm_pos : 0 < Anorm := hApos
  set η : ℝ := Anorm / (|B| + 1) with hη
  have hη0 : 0 < η := by positivity
  have hηB : η * B < Anorm := by
    have h1 : η * |B| < Anorm := by
      rw [hη, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [abs_nonneg B]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_abs_self B) hη0.le) h1
  -- the perturbed test
  have hgs : DGPS.IsSmoothPeriodicParticle (fun x => F x - η * R x) := isSmooth_sub_smul hFs hRs η
  have hG := DGPS.FiniteN.PositiveRate.isParticleHaarWeakGradient_of_smooth hgs
  have hGP : DGPS.IsParticleWeakGradient A N (fun x => F x - η * R x)
      (fun x i => WithLp.toLp 2 fun j => DGPS.particlePartial i j (fun y => F y - η * R y) x) :=
    (DGPS.isParticleWeakGradient_iff A N _ _).2 hG
  have hmem : DGPS.MemParticleH1 A N (fun x => F x - η * R x) := ⟨_, hGP⟩
  set g : DGPS.ParticleH1 A N := ⟨fun x => F x - η * R x, hmem⟩ with hg
  have hgv : g.1 = fun x => F x - η * R x := rfl
  have hgc : Continuous g.1 := hFc.sub (continuous_const.mul hRc)
  -- integrals
  have hRFint : ∫ x, F x * R x ∂P = 0 := by
    rw [← hRF]; exact integral_congr_ae (Filter.Eventually.of_forall fun x => mul_comm _ _)
  have hgmean : ∫ x, g.1 x ∂P = 0 := by
    rw [hgv]
    show ∫ x, (F x - η * R x) ∂P = 0
    rw [integral_sub (hint hFc) ((hint hRc).const_mul η), integral_const_mul, hmean', hRmean]
    simp
  have hgsq : ∫ x, (g.1 x) ^ 2 ∂P = ∫ x, (F x) ^ 2 ∂P + η ^ 2 * Anorm := by
    rw [hgv]
    show ∫ x, (F x - η * R x) ^ 2 ∂P = _
    have e : (fun x => (F x - η * R x) ^ 2) =
        fun x => (F x) ^ 2 - 2 * η * (F x * R x) + η ^ 2 * (R x) ^ 2 := funext fun x => by ring
    have k1 : Integrable (fun x => (F x) ^ 2) P := hint (hFc.pow 2)
    have k2 : Integrable (fun x => F x * R x) P := hint (hFc.mul hRc)
    have k3 : Integrable (fun x => (R x) ^ 2) P := hint (hRc.pow 2)
    have k4 : Integrable (fun x => (F x) ^ 2 - 2 * η * (F x * R x)) P := k1.sub (k2.const_mul _)
    rw [e, integral_add k4 (k3.const_mul _), integral_sub k1 (k2.const_mul _),
      integral_const_mul, integral_const_mul, hRFint]
    rw [hAnorm]; ring
  have hgen : DGPS.particleEnergy A N g = particleMixedEnergy A N (fun x => F x - η * R x)
      (fun x => F x - η * R x) := particleEnergy_eq_mixedEnergy A N g hgs
  have hexp := particleMixedEnergy_sub_smul A hFs hRs η
  have hFR : particleMixedEnergy A N F R = Anorm := hER
  have hkey : DGPS.particleEnergy A N g - a0 * ∫ x, (g.1 x) ^ 2 ∂P =
      -2 * η * Anorm + η ^ 2 * B := by
    rw [hgen, hexp, hFR, hEFF, hgsq, hB]; ring
  have hneg : -2 * η * Anorm + η ^ 2 * B < 0 := by
    have : η ^ 2 * B = η * (η * B) := by ring
    nlinarith [mul_lt_mul_of_pos_left hηB hη0]
  have hgpos : 0 < ∫ x, (g.1 x) ^ 2 ∂P := by
    rw [hgsq]
    have : 0 ≤ ∫ x, (F x) ^ 2 ∂P := integral_nonneg fun x => sq_nonneg _
    have : 0 < η ^ 2 * Anorm := by positivity
    linarith
  have hgvar : ProbabilityTheory.variance g.1 P = ∫ x, (g.1 x) ^ 2 ∂P := by
    rw [ProbabilityTheory.variance_eq_integral hgc.aemeasurable]
    simp [hgmean]
  have hRsym' : ∀ (σ : Equiv.Perm (Fin N)) (x : DGPS.ParticleSpace 1 N),
      R (DGPS.permuteParticles σ x) = R x := hRsym
  have hgsym : ∀ (σ : Equiv.Perm (Fin N)) (x : DGPS.ParticleSpace 1 N),
      g.1 (DGPS.permuteParticles σ x) = g.1 x := fun σ x => by
    rw [hgv]
    show F (DGPS.permuteParticles σ x) - η * R (DGPS.permuteParticles σ x) = F x - η * R x
    rw [hFsym' σ x, hRsym' σ x]
  refine ⟨η, hη0, g, hgv, hgs, hgsym, ?_, hgmean, ?_, ?_, ?_, ?_⟩
  · exact fun σ => Filter.Eventually.of_forall fun x => hgsym σ x
  · rw [hgvar]; exact hgpos
  · rw [hkey]
  · rw [hkey]; exact hneg
  · unfold DGPS.particlePoincareQuotient
    rw [hgvar, ENNReal.div_lt_iff (Or.inl (by simpa using hgpos)) (Or.inr ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul ha0.le, ENNReal.ofReal_lt_ofReal_iff (by positivity)]
    have := hkey ▸ hneg
    linarith

end DGPS.FiniteN
