import DGPS.FiniteN.ScalarFoldFIN060D

/-!
# FIN060 (part E): torus transfer at the level of the Hamiltonian

FIN013b requires the pointwise identities `A.V x = U x - h ⬝ φ x`, `A.W x y = -φ x ⬝ D φ y`.
For the scalar cosine model the interaction data is `V = -h c - κ c²/2`, `W = κ (c x - c y)²/2`,
which only agrees with the Hubbard form after summation (`W` carries diagonal terms).  Here the
same transfer is proved under the weaker, Hamiltonian-level, hypothesis
`particleWeight U φ D h N x = exp (-H_N x)`.
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped ContDiff ENNReal

namespace DGPS.FiniteN.ScalarFoldFIN060

open DGPS DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.GaussianCoupling
  DGPS.FiniteN.Tools.ConditionalMeanDerivative DGPS.FiniteN.Tools.BoundedComparison
  DGPS.FiniteN.Tools.AuxiliaryTransfer DGPS.FiniteN.Tools.AuxiliaryTransferTorus
  DGPS.FiniteN.Tools.WeightedSobolev

variable {d k : ℕ} {A : InteractionData d} {N : ℕ+} {U : Torus d → ℝ} {φ : Torus d → Fin k → ℝ}
  {D : Matrix (Fin k) (Fin k) ℝ} {h : Fin k → ℝ}

theorem particleMass_eq_FIN060
    (hH : ∀ x, particleWeight U φ D h N x = Real.exp (-particleHamiltonian A N x)) :
    particleMass D h U φ (haar d) N = ENNReal.ofReal (particlePartition A N) := by
  unfold particleMass particlePartition
  simp_rw [hH]
  rw [ofReal_integral_eq_lintegral_ofReal (DGPS.Particle.exp_neg_hamiltonian_integrable A N)
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
  rfl

theorem hubbardParticleLaw_eq_particleLaw_FIN060
    (hH : ∀ x, particleWeight U φ D h N x = Real.exp (-particleHamiltonian A N x)) :
    hubbardParticleLaw D h U φ (haar d) N = particleLaw A N := by
  have hZ := DGPS.Particle.particlePartition_pos A N
  rw [DGPS.Particle.particleLaw_eq_smul, hubbardParticleLaw, particleMass_eq_FIN060 hH,
    ENNReal.ofReal_inv_of_pos hZ]
  congr 2
  funext x
  rw [hH]

/-- Torus instantiation of the FIN013 transfer under a Hamiltonian-level Hubbard identity and with
smooth auxiliary tests. -/
theorem particle_poincare_torus_FIN060 (hD : D.PosDef) (hyp : HubbardHyp (haar d) U φ)
    (hH : ∀ x, particleWeight U φ D h N x = Real.exp (-particleHamiltonian A N x))
    {lam : ℝ} (hlam : 0 < lam)
    (haux : PoincareAt (auxLaw D h U φ (haar d) N) AuxSmoothFIN060 auxGradSq lam⁻¹)
    {C : (Fin k → ℝ) → ℝ} (hC : Measurable C)
    (hcond : ∀ w, PoincareAt (condLaw U φ (haar d) N w) IsSmoothPeriodicParticle smoothGamma
      (C w))
    {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ x, ∫⁻ w, ENNReal.ofReal (C w) ∂(gaussLaw D N (posteriorCenter D h φ N x))
      ≤ ENNReal.ofReal K)
    {L : ℝ} (hL : ∀ x, √(∑ j, φ x j ^ 2) ≤ L) :
    ∀ f : ParticleH1 A N,
      variance f.1 (particleLaw A N) ≤ K * (1 + N * L ^ 2 / lam) * particleEnergy A N f := by
  have hmain := poincare_transfer_FIN060 hyp hD h N hlam haux
    (Sm := IsSmoothPeriodicParticle) (Γ := smoothGamma)
    (fun f hf => measurable_bounded_of_smooth hf)
    (fun f hf => measurable_smoothGamma_of_smooth hf) hC hcond hK0 hK hL
  rw [hubbardParticleLaw_eq_particleLaw_FIN060 hH] at hmain
  have hC0 : 0 ≤ K * (1 + N * L ^ 2 / lam) := by positivity
  exact (fixed_n_weighted_sobolev_extension A N).2.2.1 _ fun f hf =>
    variance_le_of_poincareAt A hC0 hmain hf

end DGPS.FiniteN.ScalarFoldFIN060
