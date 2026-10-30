import DGPS.Lipschitz.T01ActualSpectralComparison
import DGPS.Lipschitz.T01SpectralCut

/-!
# Comparison on the full current reference Sobolev domain

The finite-rank approximation and inverses are constructed from the actual centered kernel.
The spectral comparison and the uniform smoothing/cutoff estimates then give a nonnegative
lower limit for every reference Sobolev family with the specified uniform energy and higher
moment bounds. These are form bounds on the reference family, not a particle lower bound.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation SharpLSI SharpLSI.FL

/-- Full reference comparison at each fixed genuine rank, with all matrix data constructed. -/
theorem exists_actual_reference_comparison {d : ℕ} (J : InteractionData d)
    (S : Spec d) (aux : Aux S) (D : KData d) (hD : D.K = centeredKernel J S.mu)
    (he : IsRefEigenbasis S.mu S.v S.lam) (hC1 : ∀ j, Gross.C1T (S.v j))
    (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1)
    (hH : IsCoerciveDensityHessian J (specProbability_LIP016 S)) :
    ∃ (F : FiniteRankApprox J.W S.mu S.v) (CR : ℕ → ℕ → ℕ → ℝ),
      (∀ R, IsInverseOfIPlus (F.a R) (CR R)) ∧
      ∀ (R : ℕ) (p M1 M2 : ℝ), 1 < p → 0 ≤ M1 → 0 ≤ M2 →
        ∀ Ψ : (N : ℕ) → Config N d → ℝ,
          (∀ N, 1 ≤ N → MemH1C (QN S.mu N) (Ψ N) ∧
            refEnergy S.mu (Ψ N) ≤ ENNReal.ofReal M1 ∧
            ∫⁻ X, ENNReal.ofReal (|Ψ N X| ^ (2 * p)) ∂QN S.mu N ≤
              ENNReal.ofReal M2) →
          ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, -ε ≤ Jexpr F S.lam (CR R) R (Ψ N) := by
  obtain ⟨F, CR, hCR, hspec⟩ :=
    exists_actual_finiteRank_spectral_comparison J S aux D hD he hC1 hlam0 hlam1 hH
  refine ⟨F, CR, hCR, ?_⟩
  intro R p M1 M2 hp hM1 hM2 Ψ hΨ ε hε
  obtain ⟨t, ht, L, hcut⟩ := campaign_J_cut S aux he hC1 hlam0 F CR R hp hM1 hM2
    (ε / 2) (by positivity)
  let G : (N : ℕ) → Config N d → ℝ := fun N =>
    if 1 ≤ N then Spectral.Fcut S.mu S.v S.lam t L (Ψ N) else fun _ => 0
  have hG : ∀ N, 1 ≤ N → G N = Spectral.Fcut S.mu S.v S.lam t L (Ψ N) :=
    fun N hN => by simp only [G, if_pos hN]
  have hrange : ∀ N, InSpectralRange S.v S.lam L (G N) := by
    intro N
    by_cases hN : 1 ≤ N
    · rw [hG N hN]
      obtain ⟨h1, h2, h3⟩ := hΨ N hN
      exact (hcut L le_rfl N hN (Ψ N) h1 h2 h3).1
    · simp only [G, if_neg hN]
      exact ⟨∅, fun _ => 0, by simp, by simp⟩
  have hbnd : ∃ B : ℝ, ∀ N, eLpNorm (G N) 2 (Measure.pi fun _ : Fin N => S.mu) ≤
      ENNReal.ofReal B := by
    refine ⟨M2 ^ (1 / (2 * p)), fun N => ?_⟩
    by_cases hN : 1 ≤ N
    · rw [hG N hN]
      obtain ⟨h1, h2, h3⟩ := hΨ N hN
      exact (hcut L le_rfl N hN (Ψ N) h1 h2 h3).2.1
    · simp [G, hN]
  filter_upwards [hspec R L G hrange hbnd (ε / 2) (by positivity),
    eventually_ge_atTop 1] with N hlow hN
  obtain ⟨h1, h2, h3⟩ := hΨ N hN
  have hclose := (hcut L le_rfl N hN (Ψ N) h1 h2 h3).2.2
  rw [← hG N hN] at hclose
  linarith

end DGPS.Lipschitz
