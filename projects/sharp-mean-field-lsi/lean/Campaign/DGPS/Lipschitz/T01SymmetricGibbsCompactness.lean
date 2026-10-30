import DGPS.Lipschitz.T01SymmetricJointLaw
import DGPS.Lipschitz.T01UnnormalizedRoots
import DGPS.Lipschitz.T01ParticleNormalizer

/-!
# Actual bounded symmetric Gibbs compactness

Reference compactness is applied to `f * sqrt (exp (-U))`. Its joint second-chaos
limit determines the normalizer and the tilted Gaussian on the same coordinates.
Only genuine uniform density moments and bounded particle energies are used.
-/

open MeasureTheory Filter Topology SharpLSI
open scoped ENNReal BoundedContinuousFunction InnerProductSpace

namespace DGPS.Lipschitz

open KernelApproximation

variable {d : ℕ}

/-- Compactness of bounded symmetric particle observables under the actual Gibbs law.
The covariance is the inverse of the actual same-reference density Hessian. -/
theorem t01_bounded_symmetric_gibbs_compactness (A : InteractionData d)
    (hA : LipschitzData A) (hd : 0 < d) (S : Spec d) (aux : Aux S) (D : KData d)
    (hD : D.K = DGPS.Lipschitz.centeredKernel A S.mu)
    (hfix : (frozenGibbs A (specProbability_LIP016 S)).measure = S.mu)
    (he : IsRefEigenbasis S.mu S.v S.lam) (hC1 : ∀ j, SharpLSI.FL.Gross.C1T (S.v j))
    (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1) (hmono : Monotone S.lam)
    (htend : Tendsto S.lam atTop atTop) {σ : ℝ} (hσ : 0 < σ)
    (hH : ∀ g : DGPS.centeredL2 (specProbability_LIP016 S),
      σ * ‖g‖ ^ 2 ≤ inner ℝ g (DGPS.densityHessian A (specProbability_LIP016 S) g))
    {p C : ℝ} (hp : 1 < p) (hC0 : 0 ≤ C)
    (hN : ∀ N : ℕ+, |Real.log (centeredParticleNormalizer A (specProbability_LIP016 S) N)| ≤ C ∧
      ∫ x, centeredParticleDensity A (specProbability_LIP016 S) N x ^ p
        ∂Measure.pi (fun _ : Fin N => S.mu) ≤ C)
    (Ns : ℕ → ℕ+) (hNs : Tendsto (fun k => (Ns k : ℕ)) atTop atTop)
    (f : (k : ℕ) → ParticleH1 A (Ns k))
    (hs : ∀ k, IsSymmetricParticleFun A (Ns k) (f k))
    (B E0 : ℝ) (hB0 : 0 ≤ B) (hE0 : 0 ≤ E0)
    (hbound : ∀ k X, |f k X| ≤ B) (henergy : ∀ k, particleEnergy A (Ns k) (f k) ≤ E0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Q : (ℕ → ℝ) → ℝ,
      IsSecondChaos (Tmat A.W S.mu S.v) Q ∧
      IsCenteredGaussianCov (gammaInfOf A.W S.mu Q) (t01CovarianceMatrix S A) ∧
      ∃ F : (ℕ → ℝ) → ℝ, MemLp F 2 (gammaInfOf A.W S.mu Q) ∧
        (∀ (J : ℕ) (g : ℝ × (Fin J → ℝ) →ᵇ ℝ),
          Tendsto (fun k => ∫ X, g (f (φ k) X,
            fun n => fluct S.v (Ns (φ k)) n X) ∂particleLaw A (Ns (φ k))) atTop
              (𝓝 (∫ z, g (F z, fun n => z n) ∂gammaInfOf A.W S.mu Q))) ∧
        Tendsto (fun k => ∫ X, f (φ k) X ^ 2 ∂particleLaw A (Ns (φ k))) atTop
          (𝓝 (∫ z, F z ^ 2 ∂gammaInfOf A.W S.mu Q)) := by
  let μ := specProbability_LIP016 S
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  let Ψ : (k : ℕ) → Config (Ns k) d → ℝ := fun k X =>
    f k X * Real.sqrt (Real.exp (-centeredParticlePotential A μ (Ns k) X))
  obtain ⟨L, hL⟩ := t01_unnormalized_roots_reference_bounds A hA hd μ hfix hp hC0 hN
    B E0 hB0 hE0
  have hΨH := fun k => (hL (Ns k) (f k) (hbound k) (henergy k)).1
  have hΨM := fun k => (hL (Ns k) (f k) (hbound k) (henergy k)).2.1
  have hΨE := fun k => (hL (Ns k) (f k) (hbound k) (henergy k)).2.2
  have hΨsym : ∀ k, ∀ π : Equiv.Perm (Fin (Ns k)),
      (fun X => Ψ k (X ∘ π)) =ᵐ[Measure.pi (fun _ : Fin (Ns k) => S.mu)] Ψ k := by
    intro k π
    have hf := (reference_absolutelyContinuous_particleLaw A μ hfix (Ns k)).ae_le (hs k π)
    filter_upwards [hf] with X hX
    change f k (permuteParticles π X) = f k X at hX
    change f k (permuteParticles π X) *
      Real.sqrt (Real.exp (-centeredParticlePotential A μ (Ns k) (permuteParticles π X))) = _
    rw [hX, centeredParticlePotential_permute]
  obtain ⟨φ, hφ, Ψinf, hΨinf, Q, hQ, hmass, hjoint⟩ :=
    t01_reference_compactness_joint A S aux D hD he hC1 hlam0 hlam1 hmono htend
      (fun k => (Ns k : ℕ)) hNs Ψ hΨH hΨsym L hΨM hΨE
  have hKD := t01_actual_kernelData_emod A S aux D hD he
  have hT : ∀ i j, Tmat A.W S.mu S.v i j = Tmat A.W S.mu S.v j i := hKD.T_symm
  have hS : Summable fun ij : ℕ × ℕ => Tmat A.W S.mu S.v ij.1 ij.2 ^ 2 := hKD.hs.summable
  have hσ' : 0 < min 1 σ := lt_min zero_lt_one hσ
  have hsec := t01_Tmat_finiteSection_coercive S A hH
  have hK : 0 < Kinf A.W S.mu Q := Kinf_pos hT hS hσ' hsec hQ
  have hcov' : IsInverseOfIPlus (Tmat A.W S.mu S.v) (t01CovarianceMatrix S A) :=
    (t01CovarianceMatrix_symPkg S aux A D hD hσ hH).inv
  have hGauss := isCenteredGaussianCov_gammaInf (W := A.W) (μ := S.mu)
    hT hS hσ' hsec hQ hcov'
  let γ := gammaInfOf A.W S.mu Q
  letI : IsProbabilityMeasure γ := hGauss.1
  let F : (ℕ → ℝ) → ℝ := fun z => Ψinf z / Real.sqrt (Real.exp (-Uinf A.W S.mu Q z))
  have hFm : AEStronglyMeasurable F gammaRef := by
    have hc : Continuous fun t : ℝ × ℝ => t.1 / Real.sqrt (Real.exp (-t.2)) := by
      exact continuous_fst.div (Real.continuous_sqrt.comp (Real.continuous_exp.comp
        continuous_snd.neg)) (fun t => (Real.sqrt_pos.2 (Real.exp_pos _)).ne')
    exact hc.comp_aestronglyMeasurable (hΨinf.aestronglyMeasurable.prodMk
      (aestronglyMeasurable_Uinf hQ))
  have hFsq : ∀ z, Real.exp (-Uinf A.W S.mu Q z) / Kinf A.W S.mu Q * F z ^ 2 =
      (Kinf A.W S.mu Q)⁻¹ * Ψinf z ^ 2 := by
    intro z
    dsimp only [F]
    rw [div_pow, Real.sq_sqrt (Real.exp_pos _).le]
    field_simp
  have hF2 : MemLp F 2 γ := by
    refine memLp_two_of_lintegral (hFm.mono_ac (withDensity_absolutelyContinuous _ _)) ?_
    unfold γ gammaInfOf
    rw [lintegral_withDensity_eq_lintegral_mul₀ (g := fun z => ENNReal.ofReal (F z ^ 2))
      (aemeasurable_dens (W := A.W) (μ := S.mu) hT hS hσ' hsec hQ)
      (hFm.pow 2).aemeasurable.ennreal_ofReal]
    have hi : Integrable (fun z => (Kinf A.W S.mu Q)⁻¹ * Ψinf z ^ 2) gammaRef :=
      hΨinf.integrable_sq.const_mul _
    have heq : ∀ z, ENNReal.ofReal (Real.exp (-Uinf A.W S.mu Q z) / Kinf A.W S.mu Q) *
        ENNReal.ofReal (F z ^ 2) = ENNReal.ofReal ((Kinf A.W S.mu Q)⁻¹ * Ψinf z ^ 2) := by
      intro z
      rw [← ENNReal.ofReal_mul (div_nonneg (Real.exp_pos _).le hK.le), hFsq]
    simp only [Pi.mul_apply, heq]
    exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun z =>
      mul_nonneg (inv_nonneg.mpr hK.le) (sq_nonneg _))).mp hi.hasFiniteIntegral
  have hUeq (N : ℕ+) : centeredParticlePotential A μ N = Ucentered A.W S.mu N := by
    exact t01_centeredParticlePotential_eq_legacy A μ N
  have hUm : ∀ k, Continuous (Ucentered A.W S.mu (Ns (φ k))) := by
    intro k
    rw [← hUeq]
    exact centeredParticlePotential_continuous A μ (Ns (φ k))
  have hfluct : ∀ (k J : ℕ), Continuous (fun X : Config (Ns (φ k)) d =>
      fun n : Fin J => fluct S.v (Ns (φ k)) n X) := by
    intro k J
    apply continuous_pi
    intro n
    unfold fluct
    exact continuous_const.mul (continuous_finset_sum _ fun i _ =>
      (S.vc _).comp (continuous_apply i))
  have hΨm : ∀ k, AEStronglyMeasurable (Ψ (φ k))
      (Measure.pi fun _ : Fin (Ns (φ k)) => S.mu) := fun k =>
    ((measurableEmbedding_flat.memLp_map_measure_iff).mp (hΨH (φ k)).2.1).aestronglyMeasurable
  have hi : ∀ k, Integrable (fun X => Real.exp (-Ucentered A.W S.mu (Ns (φ k)) X))
      (Measure.pi fun _ : Fin (Ns (φ k)) => S.mu) := fun k =>
    (hUm k).neg.rexp.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpi : ∀ k, Integrable (fun X => Real.exp (-Ucentered A.W S.mu (Ns (φ k)) X) ^ p)
      (Measure.pi fun _ : Fin (Ns (φ k)) => S.mu) := fun k =>
    ((Real.continuous_rpow_const (by linarith : 0 ≤ p)).comp (hUm k).neg.rexp
      ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmoment : ∀ k, ∫ X, Real.exp (-Ucentered A.W S.mu (Ns (φ k)) X) ^ p
      ∂Measure.pi (fun _ : Fin (Ns (φ k)) => S.mu) ≤ Real.exp C ^ p * C := by
    intro k
    rw [← hUeq]
    exact t01_unnormalized_exponential_moment A μ (Ns (φ k)) hp (hN _).1 (hN _).2
  have hweighted : ∀ J : ℕ, ∀ G : (ℝ × (Fin J → ℝ)) × ℝ →ᵇ ℝ,
      Tendsto (fun k => ∫ X, Real.exp (-Ucentered A.W S.mu (Ns (φ k)) X) *
        G ((Ψ (φ k) X, fun n => fluct S.v (Ns (φ k)) n X),
          Ucentered A.W S.mu (Ns (φ k)) X)
            ∂Measure.pi (fun _ : Fin (Ns (φ k)) => S.mu)) atTop
        (𝓝 (∫ z, Real.exp (-Uinf A.W S.mu Q z) *
          G ((Ψinf z, fun n => z n), Uinf A.W S.mu Q z) ∂gammaRef)) := by
    intro J
    exact (t01_weighted_joint_limit
      (P := fun k => Measure.pi fun _ : Fin (Ns (φ k)) => S.mu)
      (A := fun k X => (Ψ (φ k) X, fun n : Fin J => fluct S.v (Ns (φ k)) n X))
      (U := fun k X => Ucentered A.W S.mu (Ns (φ k)) X)
      (A' := fun z => (Ψinf z, fun n : Fin J => z n)) (U' := Uinf A.W S.mu Q)
      (fun G => hjoint J (rearr G)) (Real.continuous_exp.comp continuous_neg)
      (fun u => (Real.exp_pos _).le) hp
      (fun k => ((hΨm k).prodMk (hfluct k J).aestronglyMeasurable).prodMk
        (hUm k).aestronglyMeasurable)
      ((hΨinf.aestronglyMeasurable.prodMk
        (continuous_pi fun n => continuous_apply _).aestronglyMeasurable).prodMk
          (aestronglyMeasurable_Uinf hQ)) hi hpi hmoment).2
  have hKN : Tendsto (fun k => centeredParticleNormalizer A μ (Ns (φ k))) atTop
      (𝓝 (Kinf A.W S.mu Q)) := by
    have ht := hweighted 0 (BoundedContinuousFunction.const _ (1 : ℝ))
    simp only [BoundedContinuousFunction.const_apply, mul_one] at ht
    have ht' : Tendsto (fun k => ∫ X : Config (Ns (φ k)) d,
        Real.exp (-Ucentered A.W S.mu (Ns (φ k)) X)
          ∂Measure.pi (fun _ : Fin (Ns (φ k)) => S.mu)) atTop (𝓝 (Kinf A.W S.mu Q)) := ht
    refine ht'.congr fun k => ?_
    rw [centeredParticleNormalizer_eq_integral A μ hfix, hUeq]
    rfl
  have hInv : Tendsto (fun k => (centeredParticleNormalizer A μ (Ns (φ k)))⁻¹) atTop
      (𝓝 (Kinf A.W S.mu Q)⁻¹) := hKN.inv₀ hK.ne'
  have hGI := integral_gammaInf (W := A.W) (μ := S.mu) hT hS hσ' hsec hQ
  have hGibbs : ∀ (J : ℕ) (g : ℝ × (Fin J → ℝ) →ᵇ ℝ),
      Tendsto (fun k => ∫ X, g (f (φ k) X, fun n => fluct S.v (Ns (φ k)) n X)
        ∂particleLaw A (Ns (φ k))) atTop (𝓝 (∫ z, g (F z, fun n => z n) ∂γ)) := by
    intro J g
    have ht := hweighted J (phiG zero_lt_one g)
    have hl := hInv.mul ht
    have hR : (Kinf A.W S.mu Q)⁻¹ *
        (∫ z, Real.exp (-Uinf A.W S.mu Q z) *
          phiG zero_lt_one g ((Ψinf z, fun n => z n), Uinf A.W S.mu Q z) ∂gammaRef) =
          ∫ z, g (F z, fun n => z n) ∂γ := by
      rw [hGI, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [phiG_apply, wK, div_one, F]
      ring
    rw [hR] at hl
    refine hl.congr fun k => ?_
    rw [integral_particleLaw_eq_centered A μ hfix, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    simp only [phiG_apply, wK, div_one, Ψ]
    rw [← hUeq]
    rw [mul_div_cancel_right₀ _ (Real.sqrt_pos.2 (Real.exp_pos _)).ne']
    unfold centeredParticleDensity
    ring
  have hmass' : Tendsto (fun k => ∫ X, f (φ k) X ^ 2 ∂particleLaw A (Ns (φ k))) atTop
      (𝓝 (∫ z, F z ^ 2 ∂γ)) := by
    have ht := hInv.mul hmass
    have hR : (Kinf A.W S.mu Q)⁻¹ * (∫ z, Ψinf z ^ 2 ∂gammaRef) =
        ∫ z, F z ^ 2 ∂γ := by
      rw [hGI]
      simp_rw [hFsq]
      rw [integral_const_mul]
    rw [hR] at ht
    refine ht.congr fun k => ?_
    rw [integral_particleLaw_eq_centered A μ hfix, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun X => ?_)
    dsimp only [Ψ]
    rw [mul_pow, Real.sq_sqrt (Real.exp_pos _).le]
    unfold centeredParticleDensity
    ring
  exact ⟨φ, hφ, Q, hQ, hGauss, F, hF2, hGibbs, hmass'⟩

end DGPS.Lipschitz
