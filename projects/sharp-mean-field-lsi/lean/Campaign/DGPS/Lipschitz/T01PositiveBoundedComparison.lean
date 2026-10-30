import DGPS.Lipschitz.T01ActualBoundedComparison
import DGPS.Lipschitz.T01ReferenceData
import DGPS.Lipschitz.T01SpeciesOrdinaryRate
import DGPS.Lipschitz.T01LegacyRateBridge
import DGPS.Lipschitz.T01GaussianSpectralTests
import DGPS.Lipschitz.T01HybridComparison
import DGPS.Variational.SpeciesInclusion

/-! The unrestricted bounded comparison at a positive rate above the actual species rate. -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

open SharpLSI SharpLSI.FL KernelApproximation

/-- Positive scalar rate supplies one actual equilibrium and spectral witness and a positive
unrestricted bounded-comparison rate at least the species rate. No comparison estimate,
compactness conclusion, matrix positivity, or reference moment is assumed. -/
theorem t01_positive_rate_unrestricted_bounded_comparison {d : ℕ} (J : InteractionData d)
    (hJ : LipschitzData J) (hd : 0 < d) (drift : AbsoluteDrift J)
    (hrate : 0 < scalarRate J drift) :
    ∃ r : ℝ, 0 < r ∧ speciesRate J drift ≤ ENNReal.ofReal r ∧
      ∀ B E0 ε : ℝ, 0 < B → 0 < E0 → 0 < ε →
        ∀ᶠ N : ℕ+ in atTop, ∀ f : ParticleH1 J N,
          (∀ X, |f X| ≤ B) → particleEnergy J N f ≤ E0 →
          ENNReal.ofReal (r / 2) * particleEntropy J N f ≤
            ENNReal.ofReal (particleEnergy J N f + ε) := by
  obtain ⟨μ, hμ, -, hH, hfix, c, C, p, -, -, hC, hp, -, hN⟩ :=
    t01_positive_rate_reference_data J hJ drift hrate
  have hmin : ∀ ν : ProbabilityMeasure (Torus d), DGPS.freeEnergy J μ ≤ DGPS.freeEnergy J ν := by
    intro ν
    rw [hμ]
    exact iInf_le (fun ν => DGPS.freeEnergy J ν) ν
  obtain ⟨S, aux, D, hS, hD, he, hC1, hzero, hone, -⟩ :=
    exists_equilibrium_hybrid_reference J hJ hd μ hmin
  letI : IsProbabilityMeasure S.mu := isProbabilityMeasure_iff_real.mpr S.real_univ
  have hμS : specProbability_LIP016 S = μ :=
    ProbabilityMeasure.toMeasure_injective hS
  have hfixS : (frozenGibbs J (specProbability_LIP016 S)).measure = S.mu := by
    rw [hμS, hfix, hS]
  have hHS : IsCoerciveDensityHessian J (specProbability_LIP016 S) := by
    rw [hμS]; exact hH
  have hNS : ∀ N : ℕ+,
      |Real.log (centeredParticleNormalizer J (specProbability_LIP016 S) N)| ≤ C ∧
      (∫ X, centeredParticleDensity J (specProbability_LIP016 S) N X ^ p
        ∂Measure.pi (fun _ : Fin N => S.mu)) ≤ C := by
    intro N
    simpa only [hμS, hS] using And.intro (hN N).1 (hN N).2.1
  have hsc := t01_scalarRate_le_lamG S aux J hJ drift (by rw [hμS]; exact hmin) hHS D hD
  have hspG : speciesRate J drift ≤ lamG (lamShift S.lam) (t01CovarianceMatrix S J) :=
    (speciesRate_le_scalarRate J drift).trans hsc
  let P := frozenGibbs J μ
  have hspLS : speciesRate J drift ≤ rLS S.mu := by
    have hh := (t01_speciesRate_le_ordinaryLSRate J hJ drift hμ).trans
      (ordinaryLSRate_le_legacy_rLS_reference P)
    simpa only [P, hfix, ← hS] using hh
  let B := bRate S.mu S.lam (t01CovarianceMatrix S J)
  have hspB : speciesRate J drift ≤ B := le_min hspLS hspG
  have hrl0 : 0 < rLS S.mu := by
    have hpup : 0 < P.upper := Real.exp_pos _
    have hpos : 0 < ENNReal.ofReal (P.lower / P.upper) :=
      ENNReal.ofReal_pos.mpr (div_pos P.lower_pos hpup)
    have hb := hpos.trans_le (legacy_reference_lsi_lower_bound P)
    simpa only [P, hfix, ← hS] using hb
  have hB0 : 0 < B := lt_min hrl0 (hrate.trans_le hsc)
  have hac : S.mu ≪ haar d := by
    rw [← hfixS]
    exact (frozenGibbs J (specProbability_LIP016 S)).measure_ac_haar
  obtain ⟨M, hM⟩ := (hC1 1).bounded
  have hM' : ∀ x : SharpLSI.Torus d, |S.v 1 x| ≤ M := hM
  have hrl := rLS_le_lam_one_of_bdd (C := M) hac he (Eventually.of_forall hM')
  have hBf : B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top ((min_le_left _ _).trans hrl)
  refine ⟨B.toReal, ENNReal.toReal_pos hB0.ne' hBf, ?_, ?_⟩
  · simpa only [ENNReal.ofReal_toReal hBf] using hspB
  · exact actual_unrestricted_bounded_comparison J hJ S aux D hD hfixS he hC1 hzero hone
      hHS hp hC.le hNS

end DGPS.Lipschitz
