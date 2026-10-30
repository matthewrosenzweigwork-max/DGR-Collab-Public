import DGPS.Lipschitz.T01GaussianEnergyLower
import DGPS.Lipschitz.T01CenteredGeneratorPairing
import DGPS.Lipschitz.T01ParticleCylinderEnergy
import DGPS.Lipschitz.T01ActualScoreData

/-!
# The actual bounded-particle Gaussian energy lower bound

One common smoothing witness supplies the residual force threshold and generator
pairing limit. The true centered kernel and its separately differentiated diagonal
provide the bounded measurable native force. Both limiting inputs of the variational
energy adapter are discharged here.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace BoundedContinuousFunction

namespace DGPS.Lipschitz

open DGPS.Analysis DGPS.Particle ParabolicChainRule KernelApproximation SharpLSI SharpLSI.FL

/-- Bounded original particle H1 tests with the actual joint law satisfy the Gaussian
energy lower bound. No generator pairing limit or energy limit is an input. -/
theorem t01_actual_bounded_gaussian_energy_lower {d : ℕ}
    (A : InteractionData d) (hA : LipschitzData A) (S : Spec d) (aux : Aux S)
    (D : KData d) (hD : D.K = centeredKernel A S.mu)
    (hfix : (frozenGibbs A (specProbability_LIP016 S)).measure = S.mu)
    (he : IsRefEigenbasis S.mu S.v S.lam)
    (hφ : ∀ j, IsC1Periodic (S.v j)) (htop : Tendsto S.lam atTop atTop)
    (hcoerc : IsCoerciveDensityHessian A (specProbability_LIP016 S))
    (H : ℕ → Fin d → Fin d → Torus d → ℝ)
    (hH : ∀ j, IsWeakHessian (S.v j) (smoothGrad (S.v j)) (H j))
    {gμ : Torus d → Tangent d} (hμ : IsWeakGradient (frozenPotential A S.mu) gμ)
    (hlap : ∀ j, IsWeakLaplacian (S.v j)
      (fun z => inner ℝ (gμ z) (smoothGrad (S.v j) z) - S.lam j * S.v j z))
    {p Cρ : ℝ} (hp : 1 < p) (hCρ : 0 ≤ Cρ)
    (hρ : ∀ N : ℕ+, ∫ X, centeredParticleDensity A (specProbability_LIP016 S) N X ^ p
      ∂Measure.pi (fun _ : Fin N => S.mu) ≤ Cρ)
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ (t01CovarianceMatrix S A))
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable (Tmat A.W S.mu S.v) γ i (Y i))
    {FInf : (ℕ → ℝ) → ℝ} (hFInf : MemLp FInf 2 γ)
    (Ns : ℕ → ℕ+) (hNs : Tendsto (fun k => (Ns k : ℕ)) atTop atTop)
    (f : (k : ℕ) → ParticleH1 A (Ns k)) {B : ℝ} (hB : 0 ≤ B)
    (hfb : ∀ k X, |(f k).1 X| ≤ B)
    (hlaw : ∀ J (g : ℝ × (Fin J → ℝ) →ᵇ ℝ),
      Tendsto (fun k => ∫ X, g ((f k).1 X, fun i => fluct S.v (Ns k) i X)
        ∂particleLaw A (Ns k)) atTop (𝓝 (∫ z, g (FInf z, fun i => z i) ∂γ))) :
    gaussForm (lamShift S.lam) γ FInf ≤
      liminf (fun k => ENNReal.ofReal (particleEnergy A (Ns k) (f k))) atTop := by
  classical
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  let μ := specProbability_LIP016 S
  obtain ⟨t, m, Cs, F, ht, -, htlim, hm, hs, ha, hCs, hK, h1, h2, hUapprox, hH1⟩ :=
    exists_legacy_finiteRankApprox_with_smoothing A S aux D hD
  obtain ⟨gδ, hδm, ⟨Mδ, hδb⟩, hδ⟩ :=
    exists_centeredKernel_diagonal_gradient A hA S.mu
  have hδ' : IsWeakGradient (fun x => D.K x x) gδ := by rw [hD]; exact hδ
  let gU : (N : ℕ+) → ParticleSpace d N → Fin N → Tangent d :=
    fun N X l => WithLp.toLp 2 (fun k =>
      Gpart (fun x y j => D.G1 x y j) (fun x j => gδ x j / 2) N X l k)
  have hU : ∀ N, IsParticleHaarWeakGradient N (centeredParticlePotential A μ N) (gU N) :=
    fun N => (actual_centered_Gpart_data A μ D hD hδ' N).1
  have hRep := kernel_force_rep D hδm hδb
  have hG1 := t01_smoothing_G1_error_tendsto S aux D t m hH1
  have hforce := t01_actual_residual_force_threshold S aux A D hD hfix gδ hδm hδb hδ'
    t m h1 h2 hG1 F hs ha hp hCρ hρ
  have hac : S.mu ≪ haar d := by
    rw [← hfix]
    exact (frozenGibbs A μ).measure_ac_haar
  have hmem : ∀ (c : Cyl) (k : ℕ), MemParticleH1 A (Ns k)
      (fun X => c.φ (dualZ (Ns k) (fun i : Fin c.J => S.v (i.val + 1)) X)) := by
    intro c k
    exact ⟨_, (isParticleWeakGradient_iff A (Ns k) _ _).2
      (dg_cyl (fun i : Fin c.J => hφ (i.val + 1)) (c.smooth.of_le (by norm_num)))⟩
  have hpos1 : 0 < S.lam 1 := by
    have hpow : 0 < ((1 : ℕ) : ℝ) ^ (2 / (d : ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    exact (mul_pos aux.a_pos hpow).trans_le (aux.weyl 1 le_rfl)
  apply t01_gaussian_energy_lower S aux A D hD hpos1 he.mono htop hcoerc hγ hY hFInf
    Ns f H (fun i => hφ (i + 1)) (fun i => hH (i + 1)) hμ (fun i => hlap (i + 1))
    (fun k => gU (Ns k)) (fun k => hU (Ns k)) hmem
  · intro c
    exact t01_centered_generator_pairing_tendsto A S aux D hD hfix he hφ hcoerc
      t m (fun R => (ht R).le) htlim hm F ha hp hCρ hρ gU hU hforce hγ hY hFInf
      Ns hNs (fun k => (f k).1)
      (fun k => (isParticleWeakGradient_particleWeakGradient (f k)).memLp.aestronglyMeasurable)
      hB hfb hlaw c (fun N i => t01_Gpart_dualD_bddMeas hφ hRep N i)
  · intro c
    exact t01_particle_cylinder_energy_tendsto A μ hfix hac he hφ hp hCρ hρ
      Ns hNs hγ (fun k => (f k).1) FInf hlaw c (hmem c)

end DGPS.Lipschitz
