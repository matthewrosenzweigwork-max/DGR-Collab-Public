import DGPS.Lipschitz.T01BoundedComparisonUniformity
import DGPS.Lipschitz.T01ActualRankReplacement
import DGPS.Lipschitz.T01GaussianNormalizer
import DGPS.Lipschitz.T01RankRateConvergence

/-! The unrestricted bounded-observable comparison from actual direct-Lipschitz reference data.
All rank inputs are proved on one smoothing witness. No bounded comparison is assumed. -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

open KernelApproximation SharpLSI SharpLSI.FL

/-- Actual fixed-point, Hessian and uniform density-moment data imply the unrestricted
bounded-observable comparison on the full canonical particle H1 domain. -/
theorem actual_unrestricted_bounded_comparison {d : ℕ} (J : InteractionData d)
    (hJ : LipschitzData J) (S : Spec d) (aux : Aux S) (D : KData d)
    (hD : D.K = centeredKernel J S.mu)
    (hfix : (frozenGibbs J (specProbability_LIP016 S)).measure = S.mu)
    (he : IsRefEigenbasis S.mu S.v S.lam) (hC1 : ∀ j, Gross.C1T (S.v j))
    (hlam0 : S.lam 0 = 0) (hlam1 : 0 < S.lam 1)
    (hH : IsCoerciveDensityHessian J (specProbability_LIP016 S))
    {p C : ℝ} (hp : 1 < p) (hC0 : 0 ≤ C)
    (hN : ∀ N : ℕ+, |Real.log (centeredParticleNormalizer J (specProbability_LIP016 S) N)| ≤ C ∧
      (∫ X, centeredParticleDensity J (specProbability_LIP016 S) N X ^ p
        ∂Measure.pi (fun _ : Fin N => S.mu)) ≤ C) :
    let b := (bRate S.mu S.lam (t01CovarianceMatrix S J)).toReal
    ∀ B E0 ε : ℝ, 0 < B → 0 < E0 → 0 < ε →
      ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 J N,
        (∀ X, |f X| ≤ B) → particleEnergy J N f ≤ E0 →
        ENNReal.ofReal (b / 2) * particleEntropy J N f ≤
          ENNReal.ofReal (particleEnergy J N f + ε) := by
  dsimp only
  classical
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  let μ := specProbability_LIP016 S
  obtain ⟨t, m, Cs, F, ht, -, htlim, hm, hs, ha, hCs, hK, h1, h2, hU, hH1⟩ :=
    exists_legacy_finiteRankApprox_with_smoothing J S aux D hD
  obtain ⟨σ, hσ, hHσ⟩ := hH
  have hσ' : 0 < 2 * min 1 σ := mul_pos two_pos (lt_min one_pos hσ)
  have hpos : ∀ R, PosIPlus F R (2 * min 1 σ) := fun R =>
    finiteRank_posIPlus_of_hessian J S D hD F R (m R) hHσ (ht R).le (hs R) (ha R)
  have hinv : ∀ R, ∃ CR : ℕ → ℕ → ℝ, IsInverseOfIPlus (F.a R) CR :=
    fun R => exists_inv_of_pos F R hσ' (hpos R)
  choose CR hCR using hinv
  obtain ⟨-, hKinf, hκ⟩ := t01_kappaR_tendsto_canonicalQT S aux J D hD hσ hHσ
    t m (fun R => (ht R).le) htlim hm hK hU F hs ha
  have hKN := t01_legacy_centeredPartition_tendsto S aux J D hD hfix hp hN
  have hvalues : ∀ q : ℝ≥0∞, 1 ≤ q → q ≠ ⊤ →
      Tendsto (fun R => ⨆ N ∈ {N : ℕ | 1 ≤ N},
        eLpNorm (fun X => Ucentered J.W S.mu N X - URN F R N X) q (QN S.mu N)) atTop (𝓝 0) := by
    intro q hq1 hq
    have hall := t01_residual_Ucentered_eLpNorm_tendsto S aux J D hD t m hU F hs ha hq
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hall
      (fun R => bot_le) (fun R => ?_)
    exact iSup_le fun N => iSup_le fun _ => le_iSup
      (fun n => eLpNorm (fun X => Ucentered J.W S.mu n X - URN F R n X) q (QN S.mu n)) N
  obtain ⟨gδ, hδm, ⟨Mδ, hδb⟩, hδ⟩ :=
    exists_centeredKernel_diagonal_gradient J hJ S.mu
  have hδ' : IsWeakGradient (fun x => D.K x x) gδ := by rw [hD]; exact hδ
  have hG1 := t01_smoothing_G1_error_tendsto S aux D t m hH1
  have hforce := t01_actual_residual_force_threshold S aux J D hD hfix gδ hδm hδb hδ'
    t m h1 h2 hG1 F hs ha hp hC0 (fun N => (hN N).2)
  have hac : S.mu ≪ haar d := by
    rw [← hfix]
    exact (frozenGibbs J μ).measure_ac_haar
  obtain ⟨M, hM⟩ := (hC1 1).bounded
  have hM' : ∀ x : SharpLSI.Torus d, |S.v 1 x| ≤ M := hM
  have hrl := rLS_le_lam_one_of_bdd (C := M) hac he (Eventually.of_forall hM')
  have hbf : bRate S.mu S.lam (t01CovarianceMatrix S J) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      ((min_le_left _ _).trans hrl)
  have hbR := (ENNReal.tendsto_toReal hbf).comp
    (t01_bRate_rank_tendsto S aux J D hD hσ hHσ t m (fun R => (ht R).le)
      htlim hm F ha CR (Eventually.of_forall hCR))
  apply uniform_bounded_comparison_of_family J ENNReal.toReal_nonneg
  intro B E0 hB hE f hfB hfE
  exact actual_bounded_family_comparison J hJ S aux hfix he hC1 hlam0 hlam1 F CR hσ' hpos hCR
    hKinf (by simpa only [neg_div] using hKN) hκ hvalues hforce ENNReal.toReal_nonneg hbR
    hp hC0 (fun N => (hN N).2) B E0 hB.le hE.le f hfB hfE

end DGPS.Lipschitz
