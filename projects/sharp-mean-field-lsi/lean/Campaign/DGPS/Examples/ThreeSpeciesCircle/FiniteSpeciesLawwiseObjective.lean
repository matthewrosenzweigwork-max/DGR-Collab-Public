import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesCorrections

/-! Replacing original density records by equal probability laws at the SAME
original count and weights preserves the actual finite-family objectives. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

def finiteSpeciesLawwiseReplace (F : SpeciesFamily 1) (ρ : Fin F.count → AbsoluteDensity 1) :
    SpeciesFamily 1 where
  count := F.count
  weight := F.weight
  weight_pos := F.weight_pos
  weight_sum := F.weight_sum
  density := ρ

@[simp] theorem finiteSpeciesLawwiseReplace_count (F : SpeciesFamily 1)
    (ρ : Fin F.count → AbsoluteDensity 1) : (finiteSpeciesLawwiseReplace F ρ).count = F.count := rfl

theorem finiteSpeciesLawwiseReplace_weight (F : SpeciesFamily 1)
    (ρ : Fin F.count → AbsoluteDensity 1) (s : Fin F.count) :
    (finiteSpeciesLawwiseReplace F ρ).weight s = F.weight s := rfl

theorem finiteSpeciesLawwiseReplace_density (F : SpeciesFamily 1)
    (ρ : Fin F.count → AbsoluteDensity 1) (s : Fin F.count) :
    (finiteSpeciesLawwiseReplace F ρ).density s = ρ s := rfl

variable (F : SpeciesFamily 1) (ρ : Fin F.count → AbsoluteDensity 1)
  (hLaw : ∀ s, densityMeasure (ρ s) = densityMeasure (F.density s))

include hLaw

theorem finiteSpeciesLawwiseReplace_barycenter_moment (g : Torus 1 → ℝ) (hg : Continuous g) :
    (∫ x, g x ∂(densityMeasure (barycenter (finiteSpeciesLawwiseReplace F ρ)) : Measure (Torus 1))) =
      ∫ x, g x ∂(densityMeasure (barycenter F) : Measure (Torus 1)) := by
  rw [Structural.budget_integral_barycenter _ hg, Structural.budget_integral_barycenter F hg]
  change (∑ s : Fin F.count, F.weight s * ∫ x, g x ∂(densityMeasure (ρ s) : Measure (Torus 1))) = _
  apply Finset.sum_congr rfl
  intro s _
  rw [hLaw s]

private theorem finiteSpeciesLawwiseReplace_ordinaryEntropy (h : ℝ) :
    (∑ s, (finiteSpeciesLawwiseReplace F ρ).weight s *
      (ordinaryEntropy h ((finiteSpeciesLawwiseReplace F ρ).density s)).toReal) =
        ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal := by
  change (∑ s : Fin F.count, F.weight s * (ordinaryEntropy h (ρ s)).toReal) = _
  apply Finset.sum_congr rfl
  intro s _
  unfold ordinaryEntropy
  rw [hLaw s]

private theorem finiteSpeciesLawwiseReplace_ordinaryFisher (h : ℝ) :
    (∑ s, (finiteSpeciesLawwiseReplace F ρ).weight s *
      (ordinaryFisher h ((finiteSpeciesLawwiseReplace F ρ).density s)).toReal) =
        ∑ s, F.weight s * (ordinaryFisher h (F.density s)).toReal := by
  change (∑ s : Fin F.count, F.weight s * (ordinaryFisher h (ρ s)).toReal) = _
  apply Finset.sum_congr rfl
  intro s _
  unfold ordinaryFisher
  rw [hLaw s]

theorem finiteSpeciesLawwiseReplace_corrections (h r : ℝ) :
    elementaryC h r (barycenter (finiteSpeciesLawwiseReplace F ρ)) = elementaryC h r (barycenter F) ∧
      elementaryJ h (barycenter (finiteSpeciesLawwiseReplace F ρ)) = elementaryJ h (barycenter F) := by
  obtain ⟨K, _, hLip⟩ := elementaryCorrection_moment_lipschitz h r
  have he := hLip (barycenter (finiteSpeciesLawwiseReplace F ρ)) (barycenter F) 0 le_rfl
    (fun k => by
      rw [finiteSpeciesLawwiseReplace_barycenter_moment F ρ hLaw _
        (continuous_elementaryCorrectionObservable h k)]
      simp)
  constructor
  · exact sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using he.1))
  · exact sub_eq_zero.mp (abs_nonpos_iff.mp (by simpa using he.2))

private theorem finiteSpeciesLawwiseReplace_Q (h : ℝ) :
    elementaryQ h (densityMeasure (barycenter (finiteSpeciesLawwiseReplace F ρ))) =
      elementaryQ h (densityMeasure (barycenter F)) := by
  have h0 := (finiteSpeciesLawwiseReplace_corrections F ρ hLaw h 0).1
  have h1 := (finiteSpeciesLawwiseReplace_corrections F ρ hLaw h 1).1
  unfold elementaryC at h0 h1
  simp only [zero_mul, sub_zero, one_mul] at h0 h1
  linarith only [h0, h1]

private theorem finiteSpeciesLawwiseReplace_AK_integral (h : ℝ) :
    (∫ x, (barycenter (finiteSpeciesLawwiseReplace F ρ)).density x *
      elementaryAK h (densityMeasure (barycenter (finiteSpeciesLawwiseReplace F ρ))) x ∂haar 1) =
      ∫ x, (barycenter F).density x * elementaryAK h (densityMeasure (barycenter F)) x ∂haar 1 := by
  have hc := (finiteSpeciesLawwiseReplace_corrections F ρ hLaw h 0).1
  unfold elementaryC at hc
  simp only [zero_mul, sub_zero] at hc
  linarith only [hc]

/-- Both finite-family dissipations are proved finite before passing to real
values. The result concerns the original full variational domain. -/
theorem speciesDissipation_finiteSpeciesLawwiseReplace (h ε : ℝ)
    (b : AbsoluteDrift (modelData h ε)) :
    speciesDissipation (modelData h ε) b (finiteSpeciesLawwiseReplace F ρ) =
      speciesDissipation (modelData h ε) b F := by
  have hT := elementaryModel_speciesDissipation_expansion h ε b (finiteSpeciesLawwiseReplace F ρ)
  have hF := elementaryModel_speciesDissipation_expansion h ε b F
  apply (ENNReal.toReal_eq_toReal_iff' hT.1 hF.1).mp
  rw [hT.2, hF.2, finiteSpeciesLawwiseReplace_ordinaryFisher F ρ hLaw,
    finiteSpeciesLawwiseReplace_AK_integral F ρ hLaw,
    (finiteSpeciesLawwiseReplace_corrections F ρ hLaw h 0).2]

theorem speciesGap_finiteSpeciesLawwiseReplace {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) :
    speciesGap (modelData h ε) (finiteSpeciesLawwiseReplace F ρ) = speciesGap (modelData h ε) F := by
  apply NNReal.coe_injective
  rw [elementaryModel_speciesGap_expansion hh hε hεmax,
    elementaryModel_speciesGap_expansion hh hε hεmax,
    finiteSpeciesLawwiseReplace_ordinaryEntropy F ρ hLaw, finiteSpeciesLawwiseReplace_Q F ρ hLaw]

theorem speciesQuotient_finiteSpeciesLawwiseReplace {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) :
    speciesQuotient (modelData h ε) b (finiteSpeciesLawwiseReplace F ρ) =
      speciesQuotient (modelData h ε) b F := by
  unfold speciesQuotient
  rw [speciesDissipation_finiteSpeciesLawwiseReplace F ρ hLaw,
    speciesGap_finiteSpeciesLawwiseReplace F ρ hLaw hh hε hεmax]

end DGPS.Examples.ThreeSpeciesCircle
