import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesThreeGrouping
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesThreeSymmetry
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesAttainment
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootMomentSeparation
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesLawwiseObjective

/-! Actual arbitrary-family classification by merged orbit weights and laws.
This checkpoint constructs a genuine attaining triple, exact equal merged
weights, actual law rotation, and uniqueness of the merged law classes. It does
not yet assert pointwise smooth stored roots; those require the separate
factual representation and actual active-smoothness producers. -/

noncomputable section
open MeasureTheory
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem sixMomentVector_h1_bound (h : ℝ) (M : ℝ) (hM : 0 < M)
    (hObs : ∀ (i : Fin 6) x, |elementarySixObservable h i x| ≤ M)
    (σ ρ : AbsoluteDensity 1) :
    ‖ordinaryRootSixMomentVector h ρ - ordinaryRootSixMomentVector h σ‖ ≤
      2 * M * ordinaryRootH1Deviation σ ρ σ.sqrt := by
  have hdev : 0 ≤ ordinaryRootH1Deviation σ ρ σ.sqrt :=
    add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * M * ordinaryRootH1Deviation σ ρ σ.sqrt)).2
  intro i
  have hs := Real.sqrt_le_sqrt (rootDistanceSq_le_originalH1 σ ρ)
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hdev] at hs
  change |(∫ x, elementarySixObservable h i x ∂(densityMeasure ρ : Measure (Torus 1))) -
    ∫ x, elementarySixObservable h i x ∂(densityMeasure σ : Measure (Torus 1))| ≤ _
  exact (absolute_moment_error_le_root_distance ρ σ (continuous_elementarySixObservable h i)
    hM.le (hObs i)).trans (mul_le_mul_of_nonneg_left hs (by positivity))

/-- Every actual minimizing family has the same three equal merged masses and
matched original probability laws, represented by an actual attaining triple.
The original family may retain arbitrarily many duplicate labels. -/
theorem elementaryModel_speciesRate_merged_orbit_classification (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j θ, (σ j).density (angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) ∧
        ∃ K ε0 : ℝ, 0 < K ∧ 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ b : AbsoluteDrift (modelData h ε),
        ∃ p : Fin 3 → ℝ, ∃ hp : ∀ j, 0 < p j, ∃ hps : ∑ j, p j = 1,
        ∃ ρ : Fin 3 → AbsoluteDensity 1,
          0 < speciesGap (modelData h ε) (SpeciesFamily.ofData 3 p hp hps ρ) ∧
          speciesQuotient (modelData h ε) b (SpeciesFamily.ofData 3 p hp hps ρ) =
            speciesRate (modelData h ε) b ∧
          (∀ j, ordinaryRootH1Deviation (σ j) (ρ j) (σ j).sqrt ≤ K * ε) ∧
          Function.Injective (fun j => densityMeasure (ρ j)) ∧
          (∀ j, p j = 1 / 3) ∧
          (∀ j : Fin 3, densityMeasure (ρ (j + 1)) =
            densityMeasure (interactingDensityTranslate (pt (1 / 3)) (ρ j))) ∧
          ∀ F : SpeciesFamily 1, 0 < speciesGap (modelData h ε) F →
            speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b →
            ∃ label : Fin F.count → Fin 3,
              (∀ j, finiteSpeciesGroupWeight F label j = 1 / 3) ∧
              ∀ s, densityMeasure (F.density s) = densityMeasure (ρ (label s)) := by
  obtain ⟨δG, hδG, hδGr, hGrouping⟩ := elementaryModel_speciesRate_three_grouping D
  obtain ⟨δU, hδU, _, hUniqueness⟩ := elementaryModel_three_minimizers_unique D
  obtain ⟨δS, hδS, _, hSymmetry⟩ := elementaryModel_three_minimizer_equal_weights_rotation D
  obtain ⟨δA, hδA, _, hAttainment⟩ := elementaryModel_speciesRate_attainment_four D
  obtain ⟨δV, hδV, _, hVectors⟩ := ordinaryRoot_six_moment_separation D
  let δ := min δG (min δU (min δS (min δA δV)))
  refine ⟨δ, lt_min hδG (lt_min hδU (lt_min hδS (lt_min hδA hδV))),
    (min_le_left _ _).trans hδGr, fun h hh hhd => ?_⟩
  have hhG : h < δG := hhd.trans_le (min_le_left _ _)
  have hhU : h < δU := hhd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hhS : h < δS := hhd.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhA : h < δA := hhd.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hhV : h < δV := hhd.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨σ, hσ, K, εG, hK, hεG, hεGmax, hGroup⟩ := hGrouping h hh hhG
  obtain ⟨εU, hεU, _, hUnique⟩ := hUniqueness h hh hhU σ hσ K hK
  obtain ⟨εS, hεS, _, hSymmetric⟩ := hSymmetry h hh hhS σ hσ K hK
  obtain ⟨εA, hεA, _, hAttain⟩ := hAttainment h hh hhA
  obtain ⟨η, hη, hSeparate⟩ := hVectors h hh hhV σ hσ
  obtain ⟨M, hM, hObs⟩ := elementaryCorrection_coordinates_bound h
  let εV := η / (4 * M * K + 1)
  have hεV : 0 < εV := div_pos hη (by positivity)
  let ε0 := min εG (min εU (min εS (min εA εV)))
  refine ⟨σ, hσ, K, ε0, hK, lt_min hεG (lt_min hεU (lt_min hεS (lt_min hεA hεV))),
    (min_le_left _ _).trans hεGmax, fun ε hε hεsmall b => ?_⟩
  have heG : ε < εG := hεsmall.trans_le (min_le_left _ _)
  have heU : ε < εU := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heS : ε < εS := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heA : ε < εA := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have heV : ε < εV := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  obtain ⟨F0, _, hF0, hF0m⟩ := hAttain ε hε heA b
  obtain ⟨label0, hp0, _, _, hG0, hG0m, hNear0⟩ := hGroup ε hε heG b F0 hF0 hF0m
  let G0 := finiteSpeciesGroup3 F0 label0 hp0
  have hSym := hSymmetric ε hε heS b G0.weight G0.weight_pos G0.weight_sum
    G0.density hG0 hG0m hNear0
  have hMoment (j : Fin 3) :
      ‖ordinaryRootSixMomentVector h (G0.density j) - ordinaryRootSixMomentVector h (σ j)‖ ≤ 2 * M * K * ε :=
    (sixMomentVector_h1_bound h M hM (fun i => hObs (.inl i)) (σ j) (G0.density j)).trans
      (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hNear0 j) (by positivity : 0 ≤ 2 * M))
  have hDistinct : Function.Injective (fun j => densityMeasure (G0.density j)) := by
    intro j k he
    dsimp only at he
    by_contra hjk
    have hv : ordinaryRootSixMomentVector h (G0.density j) = ordinaryRootSixMomentVector h (G0.density k) := by
      funext i
      unfold ordinaryRootSixMomentVector
      rw [he]
    have hUpper : ‖ordinaryRootSixMomentVector h (σ j) - ordinaryRootSixMomentVector h (σ k)‖ ≤ 4 * M * K * ε := by
      calc
        _ = ‖(ordinaryRootSixMomentVector h (σ j) - ordinaryRootSixMomentVector h (G0.density j)) +
          (ordinaryRootSixMomentVector h (G0.density k) - ordinaryRootSixMomentVector h (σ k))‖ := by
            rw [hv]
            congr 1
            abel
        _ ≤ ‖ordinaryRootSixMomentVector h (σ j) - ordinaryRootSixMomentVector h (G0.density j)‖ +
          ‖ordinaryRootSixMomentVector h (G0.density k) - ordinaryRootSixMomentVector h (σ k)‖ := norm_add_le _ _
        _ ≤ _ := by rw [norm_sub_rev]; linarith only [hMoment j, hMoment k]
    have hLower := hSeparate j k hjk
    have hSmall := (lt_div_iff₀ (by positivity : 0 < 4 * M * K + 1)).1 heV
    nlinarith only [hUpper, hLower, hSmall, hε]
  refine ⟨G0.weight, G0.weight_pos, G0.weight_sum, G0.density,
    hG0, hG0m, hNear0, hDistinct, hSym.1, hSym.2, fun F hF hFm => ?_⟩
  obtain ⟨label, hp, _, hLaws, hG, hGm, hNear⟩ := hGroup ε hε heG b F hF hFm
  let G := finiteSpeciesGroup3 F label hp
  have hu := hUnique ε hε heU b G0.weight G.weight G0.weight_pos G.weight_pos
    G0.weight_sum G.weight_sum G0.density G.density hG0 hG0m hG hGm hNear0 hNear
  refine ⟨label, fun j => ?_, fun s => ?_⟩
  · change G.weight j = 1 / 3
    exact (congrFun hu.1 j).symm.trans (hSym.1 j)
  · exact (hLaws s).trans (hu.2 (label s)).symm


/-- The converse classification is an actual objective identity. Arbitrary
original duplicate labels with the canonical three merged masses and laws
have exactly the canonical production gap and quotient. -/
theorem elementaryModel_classified_family_objectives {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (heMax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε))
    (p : Fin 3 → ℝ) (hp : ∀ j, 0 < p j) (hps : ∑ j, p j = 1)
    (ρ : Fin 3 → AbsoluteDensity 1) (hThirds : ∀ j, p j = 1 / 3)
    (T : SpeciesFamily 1) (label : Fin T.count → Fin 3)
    (hMass : ∀ j, finiteSpeciesGroupWeight T label j = 1 / 3)
    (hLaw : ∀ s, densityMeasure (T.density s) = densityMeasure (ρ (label s))) :
    speciesGap (modelData h ε) T = speciesGap (modelData h ε) (SpeciesFamily.ofData 3 p hp hps ρ) ∧
      speciesQuotient (modelData h ε) b T =
        speciesQuotient (modelData h ε) b (SpeciesFamily.ofData 3 p hp hps ρ) := by
  let F := SpeciesFamily.ofData 3 p hp hps ρ
  have hpG (j : Fin 3) : 0 < finiteSpeciesGroupWeight T label j := by rw [hMass j]; norm_num
  have hSame (s t : Fin T.count) (he : label s = label t) :
      densityMeasure (T.density s) = densityMeasure (T.density t) := by
    exact (hLaw s).trans ((congrArg (fun j => densityMeasure (ρ j)) he).trans (hLaw t).symm)
  let G := finiteSpeciesGroup3 T label hpG
  have hLawG (j : Fin 3) : densityMeasure (G.density j) = densityMeasure (ρ j) := by
    have he := hLaw (finiteSpeciesGroupRepresentative T label hpG j)
    rw [finiteSpeciesGroupRepresentative_label T label hpG j] at he
    exact he
  let H := finiteSpeciesLawwiseReplace F G.density
  have hWeights : finiteSpeciesGroupWeight T label = p :=
    funext fun j => (hMass j).trans (hThirds j).symm
  have hRecord : G = H := by
    cases hWeights
    rfl
  have hGap := speciesGap_finiteSpeciesGroup3 T label hpG hSame hh hε heMax
  have hQuotient := speciesQuotient_finiteSpeciesGroup3 T label hpG hSame hh hε heMax b
  have hGapH := speciesGap_finiteSpeciesLawwiseReplace F G.density hLawG hh hε heMax
  have hQuotientH := speciesQuotient_finiteSpeciesLawwiseReplace F G.density hLawG hh hε heMax b
  exact ⟨hGap.symm.trans ((congrArg (speciesGap (modelData h ε)) hRecord).trans hGapH),
    hQuotient.symm.trans ((congrArg (speciesQuotient (modelData h ε) b) hRecord).trans hQuotientH)⟩

end DGPS.Examples.ThreeSpeciesCircle
