import DGPS.Lipschitz.T01SpectralComparison
import DGPS.Lipschitz.T01FiniteRankPositivity
import FullLabeledLSI.Paper.Prop23HAltA

/-!
# Actual finite-rank spectral comparison from Hessian coercivity

The approximation, positivity, and finite-section inverses are constructed for the centered
kernel of the current interaction data. No finite matrix hypothesis or reference comparison
conclusion is assumed. The remaining passage from the reference form to the particle form
requires the Gibbs, rank, and smoothing estimates.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation SharpLSI SharpLSI.FL

/-- Actual centered-kernel approximations have the spectral comparison at every fixed rank. -/
theorem exists_actual_finiteRank_spectral_comparison {d : ℕ} (J : InteractionData d)
    (S : Spec d) (aux : Aux S) (D : KData d) (hD : D.K = centeredKernel J S.mu)
    (he : IsRefEigenbasis S.mu S.v S.lam) (hC1 : ∀ j, Gross.C1T (S.v j))
    (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1)
    (hH : IsCoerciveDensityHessian J (specProbability_LIP016 S)) :
    ∃ (F : FiniteRankApprox J.W S.mu S.v) (CR : ℕ → ℕ → ℕ → ℝ),
      (∀ R, IsInverseOfIPlus (F.a R) (CR R)) ∧
      ∀ (R : ℕ) (L : ℝ) (G : (N : ℕ) → Config N d → ℝ),
        (∀ N, InSpectralRange S.v S.lam L (G N)) →
        (∃ B : ℝ, ∀ N, eLpNorm (G N) 2 (Measure.pi fun _ : Fin N => S.mu) ≤
          ENNReal.ofReal B) →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, -ε ≤ Jexpr F S.lam (CR R) R (G N) := by
  obtain ⟨t, m, F, ht, -, -, hs, ha⟩ := exists_legacy_finiteRankApprox J S aux D hD
  obtain ⟨σ, hσ, hHσ⟩ := hH
  have hσ' : 0 < 2 * min 1 σ := mul_pos two_pos (lt_min one_pos hσ)
  have hpos : ∀ R, PosIPlus F R (2 * min 1 σ) := fun R =>
    finiteRank_posIPlus_of_hessian J S D hD F R (m R) hHσ (ht R).le (hs R) (ha R)
  have hinv : ∀ R, ∃ C : ℕ → ℕ → ℝ, IsInverseOfIPlus (F.a R) C :=
    fun R => exists_inv_of_pos F R hσ' (hpos R)
  choose CR hCR using hinv
  exact ⟨F, CR, hCR, fun R L G hGr hB =>
    finite_rank_spectral_comparison S aux he hC1 hlam0 hlam1 F R hσ' (hpos R)
      (CR R) (hCR R) L G hGr hB⟩

end DGPS.Lipschitz
