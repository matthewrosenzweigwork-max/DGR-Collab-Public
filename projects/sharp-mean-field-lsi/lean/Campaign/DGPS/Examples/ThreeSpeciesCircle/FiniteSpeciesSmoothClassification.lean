import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesClassification
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesActiveSmooth
import DGPS.Examples.ThreeSpeciesCircle.SmoothAbsoluteRepresentative
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesLawwiseObjective

/-! Insert actual smooth positive representatives into the genuine attaining
orbit without changing any production objective. Classification of arbitrary
original families remains by probability laws, allowing duplicate labels. -/

noncomputable section
open MeasureTheory
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem translate_law_congr (a : Torus 1) (ρ σ : AbsoluteDensity 1)
    (he : densityMeasure ρ = densityMeasure σ) :
    densityMeasure (interactingDensityTranslate a ρ) = densityMeasure (interactingDensityTranslate a σ) := by
  apply Subtype.ext
  change (densityMeasure (interactingDensityTranslate a ρ) : Measure (Torus 1)) =
    (densityMeasure (interactingDensityTranslate a σ) : Measure (Torus 1))
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [interactingDensityTranslate_integral, interactingDensityTranslate_integral, he]

/-- Actual smooth positive three-orbit attainment and uniqueness up to merging
and relabeling on the full original H1 family domain. Equal thirds refer to
merged masses; arbitrary duplicate original labels remain admissible. -/
theorem elementaryModel_speciesRate_smooth_orbit_same_graph (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 m : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < m ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
        ∃ p : Fin 3 → ℝ, ∃ hp : ∀ j, 0 < p j, ∃ hps : ∑ j, p j = 1,
        ∃ ρ : Fin 3 → AbsoluteDensity 1,
          0 < speciesGap (modelData h ε) (SpeciesFamily.ofData 3 p hp hps ρ) ∧
          speciesQuotient (modelData h ε) b (SpeciesFamily.ofData 3 p hp hps ρ) =
            speciesRate (modelData h ε) b ∧
          Function.Injective (fun j => densityMeasure (ρ j)) ∧
          (∀ j, p j = 1 / 3) ∧
          (∀ j, IsSmoothPeriodic (ρ j).sqrt) ∧
          (∀ j, IsSmoothPeriodic (ρ j).density) ∧
          (∀ j, IsSmoothPeriodic (fun x => Real.log ((ρ j).density x))) ∧
          (∀ j x, m ≤ (ρ j).sqrt x) ∧
          (∀ (j : Fin 3) x, (ρ (j + 1)).sqrt x = (ρ j).sqrt (x - pt (1 / 3))) ∧
          ∀ F : SpeciesFamily 1,
            (0 < speciesGap (modelData h ε) F ∧
              speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b) ↔
            ∃ label : Fin F.count → Fin 3,
              (∀ j, finiteSpeciesGroupWeight F label j = 1 / 3) ∧
              ∀ s, densityMeasure (F.density s) = densityMeasure (ρ (label s)) := by
  obtain ⟨δC, hδC, hδCr, hClassification⟩ := elementaryModel_speciesRate_merged_orbit_classification D
  obtain ⟨δS, hδS, _, hSmooth⟩ := elementaryModel_speciesRate_active_smooth D
  let δ := min δC δS
  refine ⟨δ, lt_min hδC hδS, (min_le_left _ _).trans hδCr,
    fun h hh hhd => ?_⟩
  obtain ⟨σ, hσ, K, εC, hK, hεC, hεCmax, hClassify⟩ :=
    hClassification h hh (hhd.trans_le (min_le_left _ _))
  obtain ⟨εS, m, hεS, _, hm, hRegular⟩ :=
    hSmooth h hh (hhd.trans_le (min_le_right _ _))
  let ε0 := min εC εS
  refine ⟨ε0, m, lt_min hεC hεS, (min_le_left _ _).trans hεCmax, hm,
    fun ε hε hεsmall b => ?_⟩
  have heC : ε < εC := hεsmall.trans_le (min_le_left _ _)
  have heS : ε < εS := hεsmall.trans_le (min_le_right _ _)
  have heMax : ε < epsMax h := heC.trans_le hεCmax
  obtain ⟨p, hp, hps, ρ, hF, hFm, hNear, hDistinct, hWeights, hRot, hUniversal⟩ := hClassify ε hε heC b
  let F := SpeciesFamily.ofData 3 p hp hps ρ
  classical
  choose v hv hrep hvmin hvsm hlogsm using fun j : Fin 3 => hRegular ε hε heS b F hF hFm j
  let R := fun j : Fin 3 => absoluteDensityWithRoot (ρ j) (v j) (hrep j)
  have hLaw (j : Fin 3) : densityMeasure (R j) = densityMeasure (ρ j) :=
    absoluteDensityWithRoot_law (ρ j) (v j) (hrep j)
  let G := finiteSpeciesLawwiseReplace F R
  have hG : 0 < speciesGap (modelData h ε) G := by
    rw [speciesGap_finiteSpeciesLawwiseReplace F R hLaw hh hε heMax]
    exact hF
  have hGm : speciesQuotient (modelData h ε) b G = speciesRate (modelData h ε) b := by
    rw [speciesQuotient_finiteSpeciesLawwiseReplace F R hLaw hh hε heMax b]
    exact hFm
  have hDistinctR : Function.Injective (fun j => densityMeasure (R j)) := by
    intro j k he
    exact hDistinct ((hLaw j).symm.trans (he.trans (hLaw k)))
  have hRootRot (j : Fin 3) (x : Torus 1) : (R (j + 1)).sqrt x = (R j).sqrt (x - pt (1 / 3)) := by
    have hTurn := translate_law_congr (pt (1 / 3)) (R j) (ρ j) (hLaw j)
    have hL : densityMeasure (R (j + 1)) = densityMeasure (interactingDensityTranslate (pt (1 / 3)) (R j)) :=
      (hLaw (j + 1)).trans ((hRot j).trans hTurn.symm)
    have hae := AbsoluteDensity.sqrt_ae_eq_of_density_ae_eq
      ((densityMeasure_eq_iff_STR02901 _ _).1 (congrArg Subtype.val hL))
    have hc : Continuous (fun y => (R j).sqrt (y - pt (1 / 3))) :=
      (hv j).comp (continuous_id.sub continuous_const)
    have heq : (R (j + 1)).sqrt = fun y => (R j).sqrt (y - pt (1 / 3)) :=
      ((hv (j + 1)).ae_eq_iff_eq (haar 1) hc).1 hae
    exact congrFun heq x
  refine ⟨p, hp, hps, R, hG, hGm, hDistinctR, hWeights, hvsm,
    (fun j => (hvsm j).pow 2), hlogsm, hvmin, hRootRot, fun T => ?_⟩
  constructor
  · rintro ⟨hT, hTm⟩
    obtain ⟨label, hMasses, hLaws⟩ := hUniversal T hT hTm
    exact ⟨label, hMasses, fun s => (hLaws s).trans (hLaw (label s)).symm⟩
  · rintro ⟨label, hMasses, hLaws⟩
    have he := elementaryModel_classified_family_objectives hh hε heMax b
      p hp hps R hWeights T label hMasses hLaws
    constructor
    · rw [he.1]
      exact hG
    · rw [he.2]
      exact hGm


/-- The actual model chooses its ordinary graph internally. This full original
family-domain classification has no graph, smoothness or attainment premise. -/
theorem elementaryModel_speciesRate_smooth_orbit_classification :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 m : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < m ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
        ∃ p : Fin 3 → ℝ, ∃ hp : ∀ j, 0 < p j, ∃ hps : ∑ j, p j = 1,
        ∃ ρ : Fin 3 → AbsoluteDensity 1,
          0 < speciesGap (modelData h ε) (SpeciesFamily.ofData 3 p hp hps ρ) ∧
          speciesQuotient (modelData h ε) b (SpeciesFamily.ofData 3 p hp hps ρ) =
            speciesRate (modelData h ε) b ∧
          Function.Injective (fun j => densityMeasure (ρ j)) ∧
          (∀ j, p j = 1 / 3) ∧
          (∀ j, IsSmoothPeriodic (ρ j).sqrt) ∧
          (∀ j, IsSmoothPeriodic (ρ j).density) ∧
          (∀ j, IsSmoothPeriodic (fun x => Real.log ((ρ j).density x))) ∧
          (∀ j x, m ≤ (ρ j).sqrt x) ∧
          (∀ (j : Fin 3) x, (ρ (j + 1)).sqrt x = (ρ j).sqrt (x - pt (1 / 3))) ∧
          ∀ F : SpeciesFamily 1,
            (0 < speciesGap (modelData h ε) F ∧
              speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b) ↔
            ∃ label : Fin F.count → Fin 3,
              (∀ j, finiteSpeciesGroupWeight F label j = 1 / 3) ∧
              ∀ s, densityMeasure (F.density s) = densityMeasure (ρ (label s)) := by
  let D := Classical.choice exists_ordinaryRootGraphData
  obtain ⟨δ, hδ, _, hmain⟩ := elementaryModel_speciesRate_smooth_orbit_same_graph D
  exact ⟨δ, hδ, hmain⟩

end DGPS.Examples.ThreeSpeciesCircle
