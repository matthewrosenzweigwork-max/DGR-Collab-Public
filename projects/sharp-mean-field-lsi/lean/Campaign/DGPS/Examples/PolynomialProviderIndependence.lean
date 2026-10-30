import DGPS.Examples.PolynomialRatesOrigin

/-! Exact provider independence for the actual polynomial full-domain rates,
followed by coarse origin limits for arbitrary sequence-dependent genuine
absolute drifts. No regularity of the choice of drift is required. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization

namespace DGPS.Examples.PolynomialSpecies

private theorem family_dissipation_eq (h : ℝ)
    (b1 b2 : AbsoluteDrift (canonical_elementary_polynomial_model h)) (F : SpeciesFamily 1) :
    speciesDissipation (canonical_elementary_polynomial_model h) b1 F =
      speciesDissipation (canonical_elementary_polynomial_model h) b2 F := by
  obtain ⟨_, _, hfin1, hd1⟩ := polynomial_family_gap_and_dissipation h b1 F
  obtain ⟨_, _, hfin2, hd2⟩ := polynomial_family_gap_and_dissipation h b2 F
  calc
    _ = ENNReal.ofReal (speciesDissipation (canonical_elementary_polynomial_model h) b1 F).toReal :=
      (ENNReal.ofReal_toReal hfin1).symm
    _ = ENNReal.ofReal (speciesDissipation (canonical_elementary_polynomial_model h) b2 F).toReal :=
      congrArg ENNReal.ofReal (hd1.trans hd2.symm)
    _ = _ := ENNReal.ofReal_toReal hfin2

/-- Both full variational infima are unchanged by choosing another genuine
absolute drift on the same actual canonical polynomial model. -/
theorem polynomial_rates_independent_of_drift (h : ℝ)
    (b1 b2 : AbsoluteDrift (canonical_elementary_polynomial_model h)) :
    speciesRate (canonical_elementary_polynomial_model h) b1 =
      speciesRate (canonical_elementary_polynomial_model h) b2 ∧
    scalarRate (canonical_elementary_polynomial_model h) b1 =
      scalarRate (canonical_elementary_polynomial_model h) b2 := by
  have hscalar (ρ : AbsoluteDensity 1) : scalarDissipation (canonical_elementary_polynomial_model h) b1 ρ =
      scalarDissipation (canonical_elementary_polynomial_model h) b2 ρ := by
    simpa only [speciesDissipation_single] using family_dissipation_eq h b1 b2 (SpeciesFamily.single ρ)
  constructor
  · unfold speciesRate
    apply iInf_congr
    intro F
    unfold speciesQuotient
    rw [family_dissipation_eq h b1 b2 F.1]
  · unfold scalarRate
    apply iInf_congr
    intro ρ
    unfold scalarQuotient
    rw [hscalar ρ.1]

/-- The actual native rate limits hold for an arbitrary sequence of genuine
drifts, even when the physical fields repeat. Provider equality is proved
before composing the fixed canonical-provider limit with the field sequence. -/
theorem polynomial_sequence_rates_at_origin (h : ℕ → ℝ) (hh : Tendsto h atTop (𝓝 0))
    (b : ∀ n, AbsoluteDrift (canonical_elementary_polynomial_model (h n))) :
    Tendsto (fun n => speciesRate (canonical_elementary_polynomial_model (h n)) (b n)) atTop
      (𝓝 (ENNReal.ofReal a0)) ∧
    Tendsto (fun n => scalarRate (canonical_elementary_polynomial_model (h n)) (b n)) atTop
      (𝓝 (ENNReal.ofReal a0)) := by
  let c := fun h : ℝ => lipschitz_absoluteDrift (canonical_elementary_polynomial_model h) (lipschitzData_canonical_model h)
  obtain ⟨hs, hc⟩ := polynomial_scalar_species_rates_at_origin c
  constructor
  · apply (hs.comp hh).congr'
    exact Eventually.of_forall fun n => (polynomial_rates_independent_of_drift (h n) (c (h n)) (b n)).1
  · apply (hc.comp hh).congr'
    exact Eventually.of_forall fun n => (polynomial_rates_independent_of_drift (h n) (c (h n)) (b n)).2

end DGPS.Examples.PolynomialSpecies
