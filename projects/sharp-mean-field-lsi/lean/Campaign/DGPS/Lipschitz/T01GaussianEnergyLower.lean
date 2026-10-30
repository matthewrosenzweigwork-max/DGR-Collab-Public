import DGPS.Lipschitz.T01GaussianFormDuality
import DGPS.Lipschitz.T01CenteredDualGenerator
import SharpSymmetricLSI.Paper.FormLiminfS6

/-!
# Gaussian energy lower bound from the actual native dual generator

The only limiting inputs are convergence of cylinder generator pairings and of the
cylinder energies. The finite-particle variational inequality is proved by the native
centered weak generator theorem, with its full Sobolev domain and original particle law.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal InnerProductSpace

namespace DGPS.Lipschitz

open DGPS.Analysis ParabolicChainRule KernelApproximation SharpLSI

/-- Actual centered native integration by parts and the two cylinder limits imply the
Gaussian form lower bound for the original unscaled particle energies. -/
theorem t01_gaussian_energy_lower {d : ℕ} (S : Spec d) (aux : Aux S)
    (A : InteractionData d) (D : KData d) (hD : D.K = centeredKernel A S.mu)
    (hpos1 : 0 < S.lam 1) (hmono : Monotone S.lam)
    (htop : Tendsto S.lam atTop atTop)
    (hcoerc : IsCoerciveDensityHessian A (specProbability_LIP016 S))
    {γ : Measure (ℕ → ℝ)} (hγ : IsCenteredGaussianCov γ (t01CovarianceMatrix S A))
    {Y : ℕ → (ℕ → ℝ) → ℝ} (hY : ∀ i, IsRowVariable (Tmat A.W S.mu S.v) γ i (Y i))
    {F : (ℕ → ℝ) → ℝ} (hF : MemLp F 2 γ)
    (Ns : ℕ → ℕ+) (f : (k : ℕ) → ParticleH1 A (Ns k))
    (H : ℕ → Fin d → Fin d → Torus d → ℝ)
    (hv : ∀ i, IsC1Periodic (S.v (i + 1)))
    (hH : ∀ i, IsWeakHessian (S.v (i + 1)) (smoothGrad (S.v (i + 1))) (H (i + 1)))
    {gμ : Torus d → Tangent d}
    (hμ : IsWeakGradient (frozenPotential A S.mu) gμ)
    (hlap : ∀ i, IsWeakLaplacian (S.v (i + 1))
      (fun z => inner ℝ (gμ z) (smoothGrad (S.v (i + 1)) z) - S.lam (i + 1) * S.v (i + 1) z))
    (gU : (k : ℕ) → ParticleSpace d (Ns k) → Fin (Ns k) → Tangent d)
    (hU : ∀ k, IsParticleHaarWeakGradient (Ns k)
      (centeredParticlePotential A (specProbability_LIP016 S) (Ns k)) (gU k))
    (hmem : ∀ (c : Cyl) (k : ℕ), MemParticleH1 A (Ns k)
      (fun X => c.φ (dualZ (Ns k) (fun i : Fin c.J => S.v (i.val + 1)) X)))
    (hpair : ∀ c : Cyl, Tendsto
      (fun k => ∫ X, (f k).1 X * dualGen (Ns k)
        (fun i : Fin c.J => S.lam (i.val + 1))
        (fun i : Fin c.J => S.v (i.val + 1)) c.φ (gU k) X ∂particleLaw A (Ns k))
      atTop (𝓝 (∫ z, F z * (-(c.gen (lamShift S.lam) Y z)) ∂γ)))
    (henergy : ∀ c : Cyl, Tendsto
      (fun k => particleEnergy A (Ns k) ⟨_, hmem c k⟩)
      atTop (𝓝 (c.form (lamShift S.lam) γ).toReal)) :
    gaussForm (lamShift S.lam) γ F ≤
      liminf (fun k => ENNReal.ofReal (particleEnergy A (Ns k) (f k))) atTop := by
  haveI := hγ.1
  apply gaussForm_le_liminf_of_duality (fun _ => ENNReal.ofReal_ne_top)
    (t01_gaussian_form_duality S aux A D hD hpos1 hmono htop hcoerc hγ hY hF)
  intro c
  refine ⟨_, _, hpair c, henergy c, fun k => ?_⟩
  obtain ⟨hm, hle⟩ := t01_centered_weak_particle_dual_generator_identity A
    (specProbability_LIP016 S) (fun i : Fin c.J => S.lam (i.val + 1))
    (fun i : Fin c.J => S.v (i.val + 1)) (fun i : Fin c.J => H (i.val + 1))
    (fun i => hv i.val) (fun i => hH i.val) hμ (fun i => hlap i.val)
    (c.smooth.of_le (by norm_num)) (hU k) (f k)
  simpa only [ENNReal.toReal_ofReal (particleEnergy_nonneg (f k))] using hle

end DGPS.Lipschitz
