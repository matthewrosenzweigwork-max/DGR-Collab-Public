import SharpSymmetricLSI.Defs.D07_rStar
import SharpSymmetricLSI.Defs.D08_Gibbs
import SharpSymmetricLSI.Defs.D16_GaussianLimit
import SharpSymmetricLSI.Paper.GaussLaw11
import SharpSymmetricLSI.Paper.Prop21Conclusion
import SharpSymmetricLSI.Statements.R19_Lemma_5_2

/-!
# R27: (6.10) and Lemma 6.1 (`lem:Gaussian-law`), the limiting Gibbs law

Manuscript (6.10), Lemma 6.1, (6.11). Assume (1.2), `r_* > 0`, `μ` the minimizer, `(e, λ)` a
reference eigenbasis, `Q = Q_T`. Then `K_N → K_∞ = ∫ e^{-U_∞} dγ > 0`; the probability
`γ_∞ = K_∞^{-1} e^{-U_∞} γ` is centered Gaussian with covariance `C = (I+T)^{-1}`; and the finite
fluctuation vectors converge in law under `P_N` to their laws under `γ_∞`.
-/

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace SharpLSI

variable {d : ℕ}

/-- (6.10) and Lemma 6.1. -/
theorem gaussian_limit_law {V : Torus d → ℝ} {W : Torus d → Torus d → ℝ} {KV KW : ℝ}
    (hd : 1 ≤ d) (hyp : Hyp V W KV KW) (hr : 0 < rStar V W)
    {μ : ProbabilityMeasure (Torus d)} (hμ : IsMinimizer V W μ)
    {e : ℕ → Torus d → ℝ} {lam : ℕ → ℝ} (he : IsRefEigenbasis (μ : Measure (Torus d)) e lam)
    {Q : (ℕ → ℝ) → ℝ} (hQ : IsSecondChaos (Tmat W μ e) Q)
    {C : ℕ → ℕ → ℝ} (hC : IsInverseOfIPlus (Tmat W μ e) C) :
    Tendsto (fun N => centeredPartition W μ N) atTop (𝓝 (Kinf W μ Q)) ∧ 0 < Kinf W μ Q ∧
    IsCenteredGaussianCov (gammaInfOf W μ Q) C ∧
    ∀ (J : ℕ) (g : (Fin J → ℝ) →ᵇ ℝ),
      Tendsto (fun N : ℕ => ∫ X, g (fun n => fluct e N n X) ∂gibbs V W N) atTop
        (𝓝 (∫ z, g (fun n => z n) ∂gammaInfOf W μ Q)) := by
  obtain ⟨Cp, p, hp, hCp⟩ := reference_entropy hd hyp hr hμ
  exact gaussian_limit_law_of hyp (prop21Conclusion_of_equilibrium (prop_equilibrium hd hyp hr) hμ)
    he hQ hC ⟨Cp, p, hp, fun N hN => ⟨(hCp N hN).2.1, (hCp N hN).2.2⟩⟩

end SharpLSI
