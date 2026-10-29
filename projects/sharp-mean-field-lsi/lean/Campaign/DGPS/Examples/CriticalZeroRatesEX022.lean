import DGPS.Examples.AttractiveXYStationaryEX020
import DGPS.Examples.CriticalRecoveryBundleEX021
import DGPS.Analysis.RateTopology
import DGPS.Variational.SpeciesInclusion

/-!
# Critical zero rates and nonattainment (EX022)

At `(κ, h) = (2, 0)` the scalar rate `r_*` and the multi-species rate `r_ms` both vanish, and no
absolute-admissible scalar density and no finite positive-weight species family with positive gap
attains the zero quotient.

Route: the scalar quotients along the EX021 von Mises family tend to zero, so `r_* ≤ 0`; the
one-species inclusion gives `r_ms ≤ r_*`. A positive-gap zero quotient forces zero dissipation
(the denominator is finite and positive), EX020 then makes every species Haar, and the gap of an
all-Haar family vanishes, a contradiction.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples

/-- A density that is a.e. equal to one gives the Haar probability. -/
theorem densityMeasure_eq_haar_of_ae_one_EX022 {d : ℕ} (ρ : DGPS.AbsoluteDensity d)
    (h : ρ.density =ᵐ[DGPS.haar d] fun _ => (1 : ℝ)) :
    DGPS.densityMeasure ρ = DGPS.haarProbability d := by
  apply Subtype.ext
  change (DGPS.haar d).withDensity (fun x => ENNReal.ofReal (ρ.density x)) = DGPS.haar d
  have h2 : (fun x => ENNReal.ofReal (ρ.density x)) =ᵐ[DGPS.haar d] fun _ => (1 : ℝ≥0∞) :=
    h.mono fun x hx => by simp [hx]
  rw [withDensity_congr_ae h2, withDensity_const, one_smul]

/-- The Haar probability density gives a.e. density one. -/
theorem ae_one_of_densityMeasure_eq_haar_EX022 {d : ℕ} (ρ : DGPS.AbsoluteDensity d)
    (h : DGPS.densityMeasure ρ = DGPS.haarProbability d) :
    ρ.density =ᵐ[DGPS.haar d] fun _ => (1 : ℝ) := by
  have hm : (DGPS.haar d).withDensity (fun x => ENNReal.ofReal (ρ.density x)) = DGPS.haar d :=
    congrArg Subtype.val h
  have hm1 : (DGPS.haar d).withDensity (fun x => ENNReal.ofReal (ρ.density x)) =
      (DGPS.haar d).withDensity 1 := by
    rw [hm, withDensity_one]
  have hf : AEMeasurable (fun x => ENNReal.ofReal (ρ.density x)) (DGPS.haar d) :=
    ρ.integrable_density.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hae := (withDensity_eq_iff_of_sigmaFinite hf measurable_one.aemeasurable).1 hm1
  filter_upwards [hae] with x hx
  have hx' : ENNReal.ofReal (ρ.density x) = 1 := hx
  exact ENNReal.ofReal_eq_one.1 hx'

/-- The barycenter of a family of Haar species has density one almost everywhere. -/
theorem barycenter_ae_one_EX022 (F : DGPS.SpeciesFamily 1)
    (hF : ∀ s, DGPS.densityMeasure (F.density s) = DGPS.haarProbability 1) :
    (DGPS.barycenter F).density =ᵐ[DGPS.haar 1] fun _ => (1 : ℝ) := by
  have hs : ∀ᵐ x ∂(DGPS.haar 1), ∀ s, (F.density s).density x = 1 :=
    ae_all_iff.2 fun s => ae_one_of_densityMeasure_eq_haar_EX022 (F.density s) (hF s)
  filter_upwards [hs] with x hx
  show (DGPS.barycenter F).density x = 1
  have hx' : ∀ s, (F.density s).sqrt x ^ 2 = 1 := hx
  rw [DGPS.SpeciesFamily.barycenter_density_apply]
  simp only [hx', mul_one]
  exact F.weight_sum

/-- The free energy of the Haar probability at the critical XY point is one. -/
theorem densityFreeEnergy_haar_EX022 (ρ : DGPS.AbsoluteDensity 1)
    (h : DGPS.densityMeasure ρ = DGPS.haarProbability 1) :
    DGPS.densityFreeEnergy (DGPS.Models.attractiveXY 2 0) ρ = 1 := by
  have h1 := DGPS.coe_densityFreeEnergy (DGPS.Models.attractiveXY 2 0) ρ
  rw [h, AttractiveXYCritical.freeEnergy_haar_xyc] at h1
  exact EReal.coe_injective h1

/-- The minimal free energy at the critical XY point is one. -/
theorem freeEnergyMinimumReal_attractiveXY_EX022 :
    DGPS.freeEnergyMinimumReal (DGPS.Models.attractiveXY 2 0) = 1 :=
  (DGPS.Examples.strict_entropy_fourier_inequality_at_criticality).2.2.2.2.2.1

/-- A density equal to Haar has zero scalar gap at the critical XY point. -/
theorem scalarGap_eq_zero_haar_EX022 (ρ : DGPS.AbsoluteDensity 1)
    (h : DGPS.densityMeasure ρ = DGPS.haarProbability 1) :
    DGPS.scalarGap (DGPS.Models.attractiveXY 2 0) ρ = 0 := by
  apply NNReal.eq
  rw [DGPS.coe_scalarGap, densityFreeEnergy_haar_EX022 ρ h,
    freeEnergyMinimumReal_attractiveXY_EX022]
  simp

/-- Real decomposition of the free energy of an absolute-admissible density. -/
theorem densityFreeEnergy_real_EX022 (A : DGPS.InteractionData 1)
    (ρ : DGPS.AbsoluteDensity 1) :
    DGPS.densityFreeEnergy A ρ =
      (DGPS.relativeEntropy (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal +
        DGPS.potentialEnergy A (DGPS.densityMeasure ρ) +
        (1 / 2 : ℝ) * DGPS.interactionEnergy A (DGPS.densityMeasure ρ) := by
  have hfin := (DGPS.absoluteDensity_entropy_finite ρ).2.2.1
  have h1 : ((DGPS.densityFreeEnergy A ρ : ℝ) : EReal) =
      (((DGPS.relativeEntropy (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal +
        DGPS.potentialEnergy A (DGPS.densityMeasure ρ) +
        (1 / 2 : ℝ) * DGPS.interactionEnergy A (DGPS.densityMeasure ρ) : ℝ) : EReal) := by
    rw [DGPS.coe_densityFreeEnergy]
    exact DGPS.freeEnergy_eq_real A _ hfin
  exact EReal.coe_injective h1

/-- The Haar probability has zero entropy relative to Haar. -/
theorem relativeEntropy_haar_zero_EX022 :
    (DGPS.relativeEntropy
      (DGPS.haarProbability 1 : ProbabilityMeasure (DGPS.Torus 1)) (DGPS.haar 1)).toReal = 0 := by
  have : IsProbabilityMeasure (DGPS.haar 1) := (DGPS.haarProbability 1).2
  show (DGPS.relativeEntropy (DGPS.haar 1) (DGPS.haar 1)).toReal = 0
  rw [DGPS.relativeEntropy_self]
  simp

/-- A species family of Haar species has zero species gap at the critical XY point. -/
theorem speciesGap_eq_zero_haar_EX022 (F : DGPS.SpeciesFamily 1)
    (hF : ∀ s, DGPS.densityMeasure (F.density s) = DGPS.haarProbability 1) :
    DGPS.speciesGap (DGPS.Models.attractiveXY 2 0) F = 0 := by
  have hB : DGPS.densityMeasure (DGPS.barycenter F) = DGPS.haarProbability 1 :=
    densityMeasure_eq_haar_of_ae_one_EX022 _ (barycenter_ae_one_EX022 F hF)
  have hsum : ∑ s, F.weight s *
      (DGPS.relativeEntropy (DGPS.densityMeasure (F.density s) : Measure (DGPS.Torus 1))
        (DGPS.haar 1)).toReal = 0 := by
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [hF s, relativeEntropy_haar_zero_EX022, mul_zero]
  have hH : (DGPS.relativeEntropy (DGPS.densityMeasure (DGPS.barycenter F) : Measure (DGPS.Torus 1))
      (DGPS.haar 1)).toReal = 0 := by
    rw [hB, relativeEntropy_haar_zero_EX022]
  have hdec := densityFreeEnergy_real_EX022 (DGPS.Models.attractiveXY 2 0) (DGPS.barycenter F)
  have hfree := densityFreeEnergy_haar_EX022 (DGPS.barycenter F) hB
  have hmin := freeEnergyMinimumReal_attractiveXY_EX022
  rw [hH, hfree] at hdec
  apply NNReal.eq
  rw [DGPS.coe_speciesGap, NNReal.coe_zero]
  unfold DGPS.speciesRawGap
  linarith

/-- Quotient bound: if `|toReal Q - c| ≤ K` and `K < c`, then `Q ≤ ofReal (c + K)`. -/
theorem quotient_le_ofReal_add_EX022 (Q : ℝ≥0∞) (c K : ℝ) (hK : K < c)
    (h : |Q.toReal - c| ≤ K) : Q ≤ ENNReal.ofReal (c + K) := by
  have hQtop : Q ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at h
    have := (abs_le.1 h).1
    linarith
  have hb := (abs_le.1 h).2
  calc Q = ENNReal.ofReal Q.toReal := (ENNReal.ofReal_toReal hQtop).symm
    _ ≤ ENNReal.ofReal (c + K) := ENNReal.ofReal_le_ofReal (by linarith)

/-- The scalar quotient of the von Mises family is at most `π² t² + 1600 π² t⁴`. -/
theorem scalarQuotient_vonMises_le_EX022 (t : ℝ) (ht0 : 0 < t) (ht1 : t ≤ 1 / 100) :
    DGPS.scalarQuotient (DGPS.Models.attractiveXY 2 0)
      CriticalRecoveryBridgesEX021.vonMisesDriftEX021
      (CriticalRecoveryBridgesEX021.vonMisesAbsoluteDensityEX021 t) ≤
      ENNReal.ofReal ((4 * Real.pi ^ 2) * t ^ 2 / 4 + 400 * (4 * Real.pi ^ 2) * t ^ 4) := by
  obtain ⟨-, -, -, hQ⟩ := DGPS.Examples.critical_recovery_and_exact_hessian_kernel.1 t ht0 ht1
  have hpi : 0 < Real.pi ^ 2 := by positivity
  have ht2 : 1600 * t ^ 2 < 1 := by nlinarith
  refine quotient_le_ofReal_add_EX022 _ _ _ ?_ hQ
  nlinarith [mul_pos (mul_pos hpi (pow_pos ht0 2)) (sub_pos.2 ht2)]

/-- The scalar rate vanishes at the critical XY point. -/
theorem scalarRate_zero_canonical_EX022 :
    DGPS.scalarRate (DGPS.Models.attractiveXY 2 0) (DGPS.Models.attractiveXYDrift 2 0) = 0 := by
  have hrate : DGPS.scalarRate (DGPS.Models.attractiveXY 2 0) (DGPS.Models.attractiveXYDrift 2 0) =
      DGPS.scalarRate (DGPS.Models.attractiveXY 2 0)
        CriticalRecoveryBridgesEX021.vonMisesDriftEX021 :=
    DGPS.Analysis.RateTopology.scalarRate_eq_of_providers _ _
  have hle : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      DGPS.scalarRate (DGPS.Models.attractiveXY 2 0) (DGPS.Models.attractiveXYDrift 2 0) ≤
        ENNReal.ofReal ((4 * Real.pi ^ 2) * t ^ 2 / 4 + 400 * (4 * Real.pi ^ 2) * t ^ 4) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 100 by norm_num)] with t ht
    rw [hrate]
    refine (DGPS.scalarRate_le_quotient _ _ _ ?_).trans
      (scalarQuotient_vonMises_le_EX022 t ht.1 ht.2.le)
    exact (DGPS.Examples.critical_recovery_and_exact_hessian_kernel.1 t ht.1 ht.2.le).2.1
  have hlim : Tendsto (fun t : ℝ =>
      ENNReal.ofReal ((4 * Real.pi ^ 2) * t ^ 2 / 4 + 400 * (4 * Real.pi ^ 2) * t ^ 4))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hc : Continuous fun t : ℝ =>
        (4 * Real.pi ^ 2) * t ^ 2 / 4 + 400 * (4 * Real.pi ^ 2) * t ^ 4 := by
      fun_prop
    have h0 : Tendsto (fun t : ℝ =>
        (4 * Real.pi ^ 2) * t ^ 2 / 4 + 400 * (4 * Real.pi ^ 2) * t ^ 4) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
      simpa using this
    have h1 := ENNReal.tendsto_ofReal h0
    simpa using h1
  have hle0 := ge_of_tendsto hlim hle
  exact le_antisymm hle0 (by simp)

/-- The multi-species rate vanishes at the critical XY point. -/
theorem speciesRate_zero_canonical_EX022 :
    DGPS.speciesRate (DGPS.Models.attractiveXY 2 0) (DGPS.Models.attractiveXYDrift 2 0) = 0 :=
  le_antisymm ((DGPS.speciesRate_le_scalarRate _ _).trans scalarRate_zero_canonical_EX022.le)
    (by simp)

/-- No positive-gap scalar density attains the zero quotient at the critical XY point. -/
theorem scalar_no_attainment_zero_EX022 :
    ¬ ∃ ρ : DGPS.AbsoluteDensity 1, 0 < DGPS.scalarGap (DGPS.Models.attractiveXY 2 0) ρ ∧
      DGPS.scalarQuotient (DGPS.Models.attractiveXY 2 0) (DGPS.Models.attractiveXYDrift 2 0) ρ = 0 := by
  rintro ⟨ρ, hG, hQ⟩
  have h2 : (2 * (DGPS.scalarGap (DGPS.Models.attractiveXY 2 0) ρ : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
  have hD : DGPS.scalarDissipation (DGPS.Models.attractiveXY 2 0)
      (DGPS.Models.attractiveXYDrift 2 0) ρ = 0 := by
    unfold DGPS.scalarQuotient at hQ
    exact (ENNReal.div_eq_zero_iff.1 hQ).resolve_right h2
  have hS : DGPS.speciesDissipation (DGPS.Models.attractiveXY 2 0)
      (DGPS.Models.attractiveXYDrift 2 0) (DGPS.SpeciesFamily.single ρ) = 0 := by
    rw [DGPS.speciesDissipation_single]
    exact hD
  have hρ : DGPS.densityMeasure ρ = DGPS.haarProbability 1 :=
    critical_zero_dissipation_family_haar_EX020 (DGPS.SpeciesFamily.single ρ) hS 0
  have hg := scalarGap_eq_zero_haar_EX022 ρ hρ
  rw [hg] at hG
  exact lt_irrefl _ hG

/-- No finite positive-weight species family with positive gap attains the zero quotient at the
critical XY point. -/
theorem species_no_attainment_zero_EX022 :
    ¬ ∃ F : DGPS.SpeciesFamily 1, 0 < DGPS.speciesGap (DGPS.Models.attractiveXY 2 0) F ∧
      DGPS.speciesQuotient (DGPS.Models.attractiveXY 2 0) (DGPS.Models.attractiveXYDrift 2 0) F = 0 := by
  rintro ⟨F, hG, hQ⟩
  have h2 : (2 * (DGPS.speciesGap (DGPS.Models.attractiveXY 2 0) F : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
  have hD : DGPS.speciesDissipation (DGPS.Models.attractiveXY 2 0)
      (DGPS.Models.attractiveXYDrift 2 0) F = 0 := by
    unfold DGPS.speciesQuotient at hQ
    exact (ENNReal.div_eq_zero_iff.1 hQ).resolve_right h2
  have hall := critical_zero_dissipation_family_haar_EX020 F hD
  have hg := speciesGap_eq_zero_haar_EX022 F hall
  rw [hg] at hG
  exact lt_irrefl _ hG

/-- EX022: at `(κ, h) = (2, 0)` both zero rates vanish, and neither zero infimum is attained by a
positive-gap scalar density or finite positive-weight species family. -/
theorem critical_zero_rates_and_nonattainment :
    DGPS.scalarRate (DGPS.Models.attractiveXY 2 0) (DGPS.Models.attractiveXYDrift 2 0) = 0 ∧
    DGPS.speciesRate (DGPS.Models.attractiveXY 2 0) (DGPS.Models.attractiveXYDrift 2 0) = 0 ∧
    (¬ ∃ ρ : DGPS.AbsoluteDensity 1, 0 < DGPS.scalarGap (DGPS.Models.attractiveXY 2 0) ρ ∧
      DGPS.scalarQuotient (DGPS.Models.attractiveXY 2 0) (DGPS.Models.attractiveXYDrift 2 0) ρ = 0) ∧
    (¬ ∃ F : DGPS.SpeciesFamily 1, 0 < DGPS.speciesGap (DGPS.Models.attractiveXY 2 0) F ∧
      DGPS.speciesQuotient (DGPS.Models.attractiveXY 2 0) (DGPS.Models.attractiveXYDrift 2 0) F = 0) :=
  ⟨scalarRate_zero_canonical_EX022, speciesRate_zero_canonical_EX022,
    scalar_no_attainment_zero_EX022, species_no_attainment_zero_EX022⟩

end DGPS.Examples
