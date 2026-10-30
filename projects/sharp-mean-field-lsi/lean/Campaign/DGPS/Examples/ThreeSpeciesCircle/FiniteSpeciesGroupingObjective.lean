import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesGrouping
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesCorrections

/-! Exact production objectives of the genuine three-group family. Only
positive original group masses and same-label law equality are used. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

variable (F : SpeciesFamily 1) (label : Fin F.count → Fin 3)
  (hp : ∀ j, 0 < finiteSpeciesGroupWeight F label j)
  (hsame : ∀ s t, label s = label t → densityMeasure (F.density s) = densityMeasure (F.density t))

include hsame

theorem finiteSpeciesGroup3_ordinaryEntropy (h : ℝ) :
    (∑ j : Fin 3, (finiteSpeciesGroup3 F label hp).weight j *
      (ordinaryEntropy h ((finiteSpeciesGroup3 F label hp).density j)).toReal) =
        ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal := by
  exact finiteSpeciesGroup3_statistic F label hp hsame
    (fun ρ => (ordinaryEntropy h ρ).toReal) (fun ρ σ hρσ => by unfold ordinaryEntropy; rw [hρσ])

theorem finiteSpeciesGroup3_ordinaryFisher (h : ℝ) :
    (∑ j : Fin 3, (finiteSpeciesGroup3 F label hp).weight j *
      (ordinaryFisher h ((finiteSpeciesGroup3 F label hp).density j)).toReal) =
        ∑ s, F.weight s * (ordinaryFisher h (F.density s)).toReal := by
  exact finiteSpeciesGroup3_statistic F label hp hsame
    (fun ρ => (ordinaryFisher h ρ).toReal) (fun ρ σ hρσ => by unfold ordinaryFisher; rw [hρσ])

/-- The actual correction polynomial sees exactly the same barycenter moments;
the zero-error application has no interaction-identity premise. -/
theorem finiteSpeciesGroup3_corrections (h r : ℝ) :
    elementaryC h r (barycenter (finiteSpeciesGroup3 F label hp)) = elementaryC h r (barycenter F) ∧
      elementaryJ h (barycenter (finiteSpeciesGroup3 F label hp)) = elementaryJ h (barycenter F) := by
  obtain ⟨K, _, hLip⟩ := elementaryCorrection_moment_lipschitz h r
  have he := hLip (barycenter (finiteSpeciesGroup3 F label hp)) (barycenter F) 0 le_rfl
    (fun k => by
      rw [finiteSpeciesGroup3_barycenter_moment F label hp hsame _
        (continuous_elementaryCorrectionObservable h k)]
      simp)
  constructor
  · exact sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using he.1))
  · exact sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using he.2))

theorem finiteSpeciesGroup3_Q (h : ℝ) :
    elementaryQ h (densityMeasure (barycenter (finiteSpeciesGroup3 F label hp))) =
      elementaryQ h (densityMeasure (barycenter F)) := by
  have h0 := (finiteSpeciesGroup3_corrections F label hp hsame h 0).1
  have h1 := (finiteSpeciesGroup3_corrections F label hp hsame h 1).1
  unfold elementaryC at h0 h1
  simp only [zero_mul, sub_zero, one_mul] at h0 h1
  linarith only [h0, h1]

private theorem finiteSpeciesGroup3_AK_integral (h : ℝ) :
    (∫ x, (barycenter (finiteSpeciesGroup3 F label hp)).density x *
      elementaryAK h (densityMeasure (barycenter (finiteSpeciesGroup3 F label hp))) x ∂haar 1) =
      ∫ x, (barycenter F).density x * elementaryAK h (densityMeasure (barycenter F)) x ∂haar 1 := by
  have hc := (finiteSpeciesGroup3_corrections F label hp hsame h 0).1
  unfold elementaryC at hc
  simp only [zero_mul, sub_zero] at hc
  linarith only [hc]

/-- Both full-family dissipations are finite by the production expansion
before their equality is recovered from real values. -/
theorem speciesDissipation_finiteSpeciesGroup3 (h ε : ℝ) (b : AbsoluteDrift (modelData h ε)) :
    speciesDissipation (modelData h ε) b (finiteSpeciesGroup3 F label hp) =
      speciesDissipation (modelData h ε) b F := by
  have hT := elementaryModel_speciesDissipation_expansion h ε b (finiteSpeciesGroup3 F label hp)
  have hF := elementaryModel_speciesDissipation_expansion h ε b F
  apply (ENNReal.toReal_eq_toReal_iff' hT.1 hF.1).mp
  have hI := finiteSpeciesGroup3_ordinaryFisher F label hp hsame h
  change (∑ j : Fin (finiteSpeciesGroup3 F label hp).count, (finiteSpeciesGroup3 F label hp).weight j * (ordinaryFisher h ((finiteSpeciesGroup3 F label hp).density j)).toReal) = _ at hI
  rw [hT.2, hF.2, hI,
    finiteSpeciesGroup3_AK_integral F label hp hsame,
    (finiteSpeciesGroup3_corrections F label hp hsame h 0).2]

theorem speciesGap_finiteSpeciesGroup3 {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) :
    speciesGap (modelData h ε) (finiteSpeciesGroup3 F label hp) = speciesGap (modelData h ε) F := by
  apply NNReal.coe_injective
  have hE := finiteSpeciesGroup3_ordinaryEntropy F label hp hsame h
  change (∑ j : Fin (finiteSpeciesGroup3 F label hp).count, (finiteSpeciesGroup3 F label hp).weight j * (ordinaryEntropy h ((finiteSpeciesGroup3 F label hp).density j)).toReal) = _ at hE
  rw [elementaryModel_speciesGap_expansion hh hε hεmax,
    elementaryModel_speciesGap_expansion hh hε hεmax,
    hE, finiteSpeciesGroup3_Q F label hp hsame]

/-- The genuine production quotient is unchanged, including its zero-gap
convention. No optimizer or classification assertion is assumed. -/
theorem speciesQuotient_finiteSpeciesGroup3 {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) :
    speciesQuotient (modelData h ε) b (finiteSpeciesGroup3 F label hp) =
      speciesQuotient (modelData h ε) b F := by
  unfold speciesQuotient
  rw [speciesDissipation_finiteSpeciesGroup3 F label hp hsame,
    speciesGap_finiteSpeciesGroup3 F label hp hsame hh hε hεmax]

end DGPS.Examples.ThreeSpeciesCircle
