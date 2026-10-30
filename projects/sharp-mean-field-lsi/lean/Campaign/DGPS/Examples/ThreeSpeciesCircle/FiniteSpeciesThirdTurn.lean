import DGPS.Examples.ThreeSpeciesCircle.InteractingKernelRotation

/-! Actual third turns of finite species families, preserving every original
count and weight. Native family expansions prove gap/dissipation/quotient
covariance on the full H1 domain; no scalar restriction argument is used. -/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
open DGPS.Circle.VonMisesParity

namespace DGPS.Examples.ThreeSpeciesCircle

def finiteSpeciesThirdTurn (j : Fin 3) (F : SpeciesFamily 1) : SpeciesFamily 1 where
  count := F.count
  weight := F.weight
  weight_pos := F.weight_pos
  weight_sum := F.weight_sum
  density := fun s => interactingDensityTranslate (pt ((j : ℕ) / 3)) (F.density s)

@[simp] theorem finiteSpeciesThirdTurn_count (j : Fin 3) (F : SpeciesFamily 1) :
    (finiteSpeciesThirdTurn j F).count = F.count := rfl

theorem finiteSpeciesThirdTurn_weight (j : Fin 3) (F : SpeciesFamily 1) (s : Fin F.count) :
    (finiteSpeciesThirdTurn j F).weight s = F.weight s := rfl

theorem finiteSpeciesThirdTurn_density (j : Fin 3) (F : SpeciesFamily 1) (s : Fin F.count) :
    (finiteSpeciesThirdTurn j F).density s =
      interactingDensityTranslate (pt ((j : ℕ) / 3)) (F.density s) := rfl

/-- The actual barycenter is the translated original barycenter, including its
genuine H1 representative and all probability constraints. -/
theorem finiteSpeciesThirdTurn_barycenter (j : Fin 3) (F : SpeciesFamily 1) :
    barycenter (finiteSpeciesThirdTurn j F) =
      interactingDensityTranslate (pt ((j : ℕ) / 3)) (barycenter F) := by
  rfl

theorem finiteSpeciesThirdTurn_barycenter_law (j : Fin 3) (F : SpeciesFamily 1) :
    densityMeasure (barycenter (finiteSpeciesThirdTurn j F)) =
      densityMeasure (interactingDensityTranslate (pt ((j : ℕ) / 3)) (barycenter F)) := by
  rw [finiteSpeciesThirdTurn_barycenter]

/-- Exact pushforward identity, for every real observable of the barycenter. -/
theorem finiteSpeciesThirdTurn_barycenter_integral (j : Fin 3) (F : SpeciesFamily 1)
    (g : Torus 1 → ℝ) :
    (∫ x, g x ∂(densityMeasure (barycenter (finiteSpeciesThirdTurn j F)) : Measure (Torus 1))) =
      ∫ x, g (x + pt ((j : ℕ) / 3)) ∂(densityMeasure (barycenter F) : Measure (Torus 1)) := by
  rw [finiteSpeciesThirdTurn_barycenter, interactingDensityTranslate_integral]

theorem finiteSpeciesThirdTurn_ordinaryEntropy (h : ℝ) (j : Fin 3) (F : SpeciesFamily 1) :
    (∑ s, (finiteSpeciesThirdTurn j F).weight s *
      (ordinaryEntropy h ((finiteSpeciesThirdTurn j F).density s)).toReal) =
        ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal := by
  change (∑ s : Fin F.count, F.weight s *
    (ordinaryEntropy h (interactingDensityTranslate (pt ((j : ℕ) / 3)) (F.density s))).toReal) = _
  simp only [ordinaryEntropy_interactingThirdTurn]

theorem finiteSpeciesThirdTurn_ordinaryFisher (h : ℝ) (j : Fin 3) (F : SpeciesFamily 1) :
    (∑ s, (finiteSpeciesThirdTurn j F).weight s *
      (ordinaryFisher h ((finiteSpeciesThirdTurn j F).density s)).toReal) =
        ∑ s, F.weight s * (ordinaryFisher h (F.density s)).toReal := by
  change (∑ s : Fin F.count, F.weight s *
    (ordinaryFisher h (interactingDensityTranslate (pt ((j : ℕ) / 3)) (F.density s))).toReal) = _
  simp only [ordinaryFisher_interactingThirdTurn]

theorem finiteSpeciesThirdTurn_Q (h : ℝ) (j : Fin 3) (F : SpeciesFamily 1) :
    elementaryQ h (densityMeasure (barycenter (finiteSpeciesThirdTurn j F))) =
      elementaryQ h (densityMeasure (barycenter F)) := by
  rw [finiteSpeciesThirdTurn_barycenter, elementaryQ_interactingThirdTurn]

theorem finiteSpeciesThirdTurn_C (h r : ℝ) (j : Fin 3) (F : SpeciesFamily 1) :
    elementaryC h r (barycenter (finiteSpeciesThirdTurn j F)) =
      elementaryC h r (barycenter F) := by
  rw [finiteSpeciesThirdTurn_barycenter, elementaryC_interactingThirdTurn]

theorem finiteSpeciesThirdTurn_J (h : ℝ) (j : Fin 3) (F : SpeciesFamily 1) :
    elementaryJ h (barycenter (finiteSpeciesThirdTurn j F)) =
      elementaryJ h (barycenter F) := by
  rw [finiteSpeciesThirdTurn_barycenter, elementaryJ_interactingThirdTurn]

private theorem finiteSpeciesThirdTurn_AK_integral (h : ℝ) (j : Fin 3) (F : SpeciesFamily 1) :
    (∫ x, (barycenter (finiteSpeciesThirdTurn j F)).density x *
      elementaryAK h (densityMeasure (barycenter (finiteSpeciesThirdTurn j F))) x ∂haar 1) =
      ∫ x, (barycenter F).density x * elementaryAK h (densityMeasure (barycenter F)) x ∂haar 1 := by
  have hc := finiteSpeciesThirdTurn_C h 0 j F
  unfold elementaryC at hc
  simp only [zero_mul, sub_zero] at hc
  linarith only [hc]

/-- Full production family dissipation covariance. Both sides are finite by
the actual unrestricted finite-family expansion before applying toReal. -/
theorem speciesDissipation_finiteSpeciesThirdTurn (h ε : ℝ)
    (b : AbsoluteDrift (modelData h ε)) (j : Fin 3) (F : SpeciesFamily 1) :
    speciesDissipation (modelData h ε) b (finiteSpeciesThirdTurn j F) =
      speciesDissipation (modelData h ε) b F := by
  have hT := elementaryModel_speciesDissipation_expansion h ε b (finiteSpeciesThirdTurn j F)
  have hF := elementaryModel_speciesDissipation_expansion h ε b F
  apply (ENNReal.toReal_eq_toReal_iff' hT.1 hF.1).mp
  rw [hT.2, hF.2, finiteSpeciesThirdTurn_ordinaryFisher,
    finiteSpeciesThirdTurn_AK_integral, finiteSpeciesThirdTurn_J]

/-- The true interacting finite-family gap, with the original positive weights
and no optimizer hypothesis, is invariant at every actual small coupling. -/
theorem speciesGap_finiteSpeciesThirdTurn {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (j : Fin 3) (F : SpeciesFamily 1) :
    speciesGap (modelData h ε) (finiteSpeciesThirdTurn j F) =
      speciesGap (modelData h ε) F := by
  apply NNReal.coe_injective
  rw [elementaryModel_speciesGap_expansion hh hε hεmax,
    elementaryModel_speciesGap_expansion hh hε hεmax,
    finiteSpeciesThirdTurn_ordinaryEntropy, finiteSpeciesThirdTurn_Q]

/-- Exact actual quotient covariance, retaining the production zero-gap
convention; this is a full finite-family statement. -/
theorem speciesQuotient_finiteSpeciesThirdTurn {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (j : Fin 3) (F : SpeciesFamily 1) :
    speciesQuotient (modelData h ε) b (finiteSpeciesThirdTurn j F) =
      speciesQuotient (modelData h ε) b F := by
  unfold speciesQuotient
  rw [speciesDissipation_finiteSpeciesThirdTurn, speciesGap_finiteSpeciesThirdTurn hh hε hεmax]

end DGPS.Examples.ThreeSpeciesCircle
