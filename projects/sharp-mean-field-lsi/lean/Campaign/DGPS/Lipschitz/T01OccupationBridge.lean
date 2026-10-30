import DGPS.Lipschitz.T01SpectralBridge
import DGPS.Lipschitz.T01ReferenceEigenbasis
import SharpSymmetricLSI.Paper.Occ13
import SharpSymmetricLSI.Paper.Occ14

/-!
# Occupation-to-Hermite limits on the actual equilibrium reference

The common campaign spectral witness supplies the assumption-clean legacy occupation CLT
and its uniform moments. Legacy occupation multiplicity `a n` refers to physical mode
`n + 1`; the deterministic constant mode is excluded from the fluctuations.

Identification with the campaign ordered-word `SymmetricOccupation.Eocc` is a separate
combinatorial conversion and is not asserted here.
-/

open MeasureTheory Filter Topology
open scoped BoundedContinuousFunction

namespace DGPS.Lipschitz

open KernelApproximation

variable {d : ℕ}

/-- One common actual equilibrium spectral witness supplies centered kernel data, the exact
reference eigenbasis, joint occupation/fluctuation convergence, and uniform occupation moments.
No particle lower bound or semiconvexity premise is imported. -/
theorem exists_t01_reference_occupation_limits (A : InteractionData d) (hA : LipschitzData A)
    (hd : 0 < d) (μ : ProbabilityMeasure (Torus d))
    (hμ : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A μ ≤ freeEnergy A ν) :
    ∃ (S : Spec d) (_ : Aux S) (D : KData d),
      S.mu = (μ : Measure (Torus d)) ∧ D.K = centeredKernel A S.mu ∧
      SharpLSI.IsRefEigenbasis S.mu S.v S.lam ∧
      (∀ (F : Finset (ℕ →₀ ℕ)) (J : ℕ)
        (g : (F → ℝ) × (Fin J → ℝ) →ᵇ ℝ),
        Tendsto (fun N : ℕ => ∫ X,
          g (fun a => SharpLSI.occBasis S.v a N X, fun n => SharpLSI.fluct S.v N n X)
            ∂Measure.pi (fun _ : Fin N => S.mu)) atTop
          (𝓝 (∫ z, g (fun a => SharpLSI.hermiteBasis a z, fun n => z n)
            ∂SharpLSI.gammaRef))) ∧
      ∀ (a : ℕ →₀ ℕ) (p : ℕ), ∃ C : ℝ, ∀ N : ℕ, SharpLSI.occSize a ≤ N →
        ∫ X, |SharpLSI.occBasis S.v a N X| ^ p
          ∂Measure.pi (fun _ : Fin N => S.mu) ≤ C := by
  obtain ⟨S, aux, D, hS, hmono, hl0, hl01, hC1, heig, hD⟩ :=
    exists_equilibrium_spectral_data A hA hd μ hμ
  let : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have href := legacy_reference_eigenbasis S aux hmono heig
  have hb : ∀ j, ∃ C : ℝ, ∀ᵐ x ∂S.mu, |S.v j x| ≤ C := by
    intro j
    refine ⟨aux.Kc * (1 + S.lam j) ^ d, Eventually.of_forall fun x => ?_⟩
    exact (le_add_of_nonneg_right (norm_nonneg (aux.g j x))).trans (aux.c1 j x)
  exact ⟨S, aux, D, hS, hD, href,
    fun F J g => SharpLSI.tendsto_occBasis_joint href F J g,
    fun a p => SharpLSI.occBasis_moments_of_bdd href hb a p⟩

end DGPS.Lipschitz
