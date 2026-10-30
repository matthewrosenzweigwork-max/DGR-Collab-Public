import DGPS.Examples.PolynomialSpeciesNativeDescentFactory
import DGPS.Examples.PolynomialNativeRayleighWitness
import DGPS.Examples.PolynomialScalarAttainmentFactory

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
namespace DGPS.Examples.PolynomialSpecies

/-- Strict multispecies/scalar separation on the original domain. Attainment
of the scalar rate is proved; attainment of the Poincare rate is NOT needed.
An arbitrary normalized Rayleigh test strictly below the scalar rate suffices. -/
theorem polynomial_actual_speciesRate_lt_scalarRate :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ b : AbsoluteDrift (canonical_elementary_polynomial_model h),
        speciesRate (canonical_elementary_polynomial_model h) b <
          scalarRate (canonical_elementary_polynomial_model h) b := by
  obtain ⟨δP, c, hδP, _hc, hPC⟩ := polynomial_all_actual_optimizers_poincare_margin
  obtain ⟨δA, hδA, hattain⟩ := polynomial_scalar_attainment
  obtain ⟨δS, hδS, hsmooth⟩ := polynomial_scalarMinimizer_smooth_representative
  refine ⟨min δP (min δA δS), lt_min hδP (lt_min hδA hδS), ?_⟩
  intro h hh hsmall b
  obtain ⟨ρ, hG, hmin⟩ := hattain h hh
    (hsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))) b
  have hpc := (hPC h hh (hsmall.trans_le (min_le_left _ _)) b ρ hG hmin).2
  obtain ⟨v, hv, hvrep, hvlo, _hvlog⟩ := hsmooth h hh
    (hsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _))) b ρ hG hmin
  have hvpos : ∀ x, 0 < v x := fun x => lt_of_lt_of_le (by norm_num) (hvlo x)
  have hD : scalarDissipation (canonical_elementary_polynomial_model h) b ρ ≠ ⊤ := by
    have hi := (polynomial_family_gap_and_dissipation h b (SpeciesFamily.single ρ)).2.2.1
    simpa only [speciesDissipation_single] using hi
  have hRfin : scalarRate (canonical_elementary_polynomial_model h) b ≠ ⊤ := by
    rw [← hmin]
    unfold scalarQuotient
    exact ENNReal.div_ne_top hD (mul_ne_zero (by norm_num) (by exact_mod_cast hG.ne'))
  obtain ⟨f, hmean, hmass, henergy⟩ := native_normalized_rayleigh_witness (densityMeasure ρ)
    (scalarRate (canonical_elementary_polynomial_model h) b) hRfin hpc
  rw [← hmin] at henergy
  obtain ⟨g, hc, hg, hm, _hae, _hμae, ε, hε, hsplit⟩ :=
    nativeH1BinarySplit_strict_improvement (canonical_elementary_polynomial_model h) b ρ v
      hv.continuous_torus hvpos hvrep hG hD f hmean hmass henergy
  have ht0 : 0 < |ε / 2| := abs_pos.2 (ne_of_gt (half_pos hε))
  have htε : |ε / 2| < ε := by rw [abs_of_pos (half_pos hε)]; linarith
  obtain ⟨hp, _hbary, _hgap, hGsplit, _hDsplit, hQsplit⟩ := hsplit (ε / 2) ht0 htε
  have hs := speciesRate_le (canonical_elementary_polynomial_model h) b
    (nativeH1BinarySplit ρ g f.grad hg hc hm (ε / 2) hp) hGsplit
  exact (hs.trans_lt hQsplit).trans_eq hmin

end DGPS.Examples.PolynomialSpecies
