import DGPS.FiniteN.ScalarFoldFIN060J

/-!
# FIN060: fold auxiliary and particle lower powers

For the scalar cosine model at the fold field `h = h_c(κ)`, `κ > 2`:

1. the fold auxiliary law (the Hubbard auxiliary law of the model, i.e. `η_N ∝ e^{-N ψ}` on `ℝ`)
   satisfies the Poincare inequality with rate `≥ c N^{2/3}` for `N ≥ N₀`, against smooth bounded
   tests with bounded gradient (`ScalarFoldFIN060.AuxSmoothFIN060`);
2. the particle law has unrestricted Poincare rate `≥ c' N^{-1/3}` for every `N ≥ 1`;
3. the particle law has unrestricted LSI rate `particleRateAll ≥ c'' N^{-4/3}` for every `N ≥ 1`.

Proof route: the auxiliary Poincare estimate (FIN056/FIN059/FIN024 globalization, parts A-G),
the conditional Poincare constants and Gaussian-posterior moment bound with bounded comparison
(FIN013, parts D-F, H), then the `O(N)` entropy defect (FIN017) and Rothaus (FIN005) in part I/J.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace DGPS.FiniteN

open DGPS DGPS.Models DGPS.FiniteN.Tools.AuxiliaryTransfer DGPS.FiniteN.Tools.Hubbard
  DGPS.FiniteN.Tools.BoundedComparison

theorem fold_auxiliary_and_particle_lower_powers {κ : ℝ} (hκ : 2 < κ) :
    (∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℕ+, N₀ ≤ (N : ℝ) →
      PoincareAt (auxLaw (ScalarFoldFIN060.dSFIN060 κ)
        (ScalarFoldFIN060.hSFIN060 (scalarFoldField κ)) ScalarFoldFIN060.uSFIN060
        ScalarFoldFIN060.phiSFIN060 (haar 1) N)
        ScalarFoldFIN060.AuxSmoothFIN060 auxGradSq (c * (N : ℝ) ^ (2 / 3 : ℝ))⁻¹) ∧
    (∃ c' : ℝ, 0 < c' ∧ ∀ N : ℕ+,
      ENNReal.ofReal (c' * (N : ℝ) ^ (-(1 / 3 : ℝ))) ≤
        particlePoincareRate (scalarCosineFold κ) N) ∧
    (∃ c'' : ℝ, 0 < c'' ∧ ∀ N : ℕ+,
      ENNReal.ofReal (c'' * (N : ℝ) ^ (-(4 / 3 : ℝ))) ≤
        particleRateAll (scalarCosineFold κ) N) :=
  ⟨ScalarFoldFIN060.haux_FIN060 hκ, ScalarFoldFIN060.poincare_lower_FIN060 hκ,
    ScalarFoldFIN060.lsi_lower_FIN060 hκ⟩

end DGPS.FiniteN
