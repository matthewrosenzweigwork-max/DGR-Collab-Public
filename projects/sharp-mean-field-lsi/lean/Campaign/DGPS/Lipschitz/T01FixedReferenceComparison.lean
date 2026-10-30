import DGPS.Lipschitz.T01SpectralComparison
import DGPS.Lipschitz.T01SpectralCut

/-!
# Full reference comparison preserving the chosen approximation witness

This form accepts the genuine finite-rank carrier used by the caller. Thus its kernel,
normalizer, resolvent and force-error estimates can all remain tied to the same smoothing
sequence in the final rank limit.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation SharpLSI SharpLSI.FL

/-- Full reference comparison at a fixed rank of the caller's chosen approximation. -/
theorem fixed_reference_comparison {d : ℕ} (S : Spec d) (aux : Aux S)
    (he : IsRefEigenbasis S.mu S.v S.lam) (hC1 : ∀ j, Gross.C1T (S.v j))
    (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1)
    {W : Torus d → Torus d → ℝ} (F : FiniteRankApprox W S.mu S.v) (R : ℕ)
    {σ : ℝ} (hσ : 0 < σ) (hpos : PosIPlus F R σ) (C : ℕ → ℕ → ℝ)
    (hC : IsInverseOfIPlus (F.a R) C) {p M1 M2 : ℝ} (hp : 1 < p)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (Ψ : (N : ℕ) → Config N d → ℝ)
    (hΨ : ∀ N, 1 ≤ N → MemH1C (QN S.mu N) (Ψ N) ∧
      refEnergy S.mu (Ψ N) ≤ ENNReal.ofReal M1 ∧
      ∫⁻ X, ENNReal.ofReal (|Ψ N X| ^ (2 * p)) ∂QN S.mu N ≤ ENNReal.ofReal M2) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, -ε ≤ Jexpr F S.lam C R (Ψ N) := by
  have hspec := finite_rank_spectral_comparison S aux he hC1 hlam0 hlam1 F R hσ hpos C hC
  intro ε hε
  obtain ⟨t, ht, L, hcut⟩ := campaign_J_cut S aux he hC1 hlam0 F (fun _ => C) R hp hM1 hM2
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
  filter_upwards [hspec L G hrange hbnd (ε / 2) (by positivity),
    eventually_ge_atTop 1] with N hlow hN
  obtain ⟨h1, h2, h3⟩ := hΨ N hN
  have hclose := (hcut L le_rfl N hN (Ψ N) h1 h2 h3).2.2
  rw [← hG N hN] at hclose
  linarith


end DGPS.Lipschitz
