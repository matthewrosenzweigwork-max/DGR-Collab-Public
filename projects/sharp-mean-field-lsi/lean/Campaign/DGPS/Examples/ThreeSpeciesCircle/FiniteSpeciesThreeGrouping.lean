import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesMerging
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesOrbitLocalization
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesGroupingObjective

/-! Genuine grouping of every actual minimizing family into three original
positive law classes at one SAME ordinary-root chart. No imposed weight floor
or distinct-law/count premise is added. Duplicate labels are preserved by the
classification and removed only in the constructed grouped family. -/

noncomputable section
open MeasureTheory
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Every actual full-family minimizer admits genuine positive three-group
reindexing, preserving the full production quotient and original root chart. -/
theorem elementaryModel_speciesRate_three_grouping (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j θ, (σ j).density (angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) ∧
        ∃ K ε0 : ℝ, 0 < K ∧ 0 < ε0 ∧ ε0 ≤ epsMax h ∧
          ∀ ε : ℝ, 0 < ε → ε < ε0 →
            ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
            0 < speciesGap (modelData h ε) F →
            speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b →
            ∃ label : Fin F.count → Fin 3,
              ∃ hp : ∀ j, 0 < finiteSpeciesGroupWeight F label j,
              (∀ s t, label s = label t → densityMeasure (F.density s) = densityMeasure (F.density t)) ∧
              (∀ s, densityMeasure (F.density s) =
                densityMeasure ((finiteSpeciesGroup3 F label hp).density (label s))) ∧
              0 < speciesGap (modelData h ε) (finiteSpeciesGroup3 F label hp) ∧
              speciesQuotient (modelData h ε) b (finiteSpeciesGroup3 F label hp) =
                speciesRate (modelData h ε) b ∧
              ∀ j : Fin 3, ordinaryRootH1Deviation (σ j)
                ((finiteSpeciesGroup3 F label hp).density j) (σ j).sqrt ≤ K * ε := by
  obtain ⟨δM, hδM, hδMr, hMerge⟩ := elementaryModel_speciesRate_same_branch_law D
  obtain ⟨δO, hδO, _, hOrbit⟩ := elementaryModel_speciesRate_orbit_mass_lower_of_localization D
  let δ := min δM δO
  refine ⟨δ, lt_min hδM hδO, (min_le_left _ _).trans hδMr,
    fun h hh hhd => ?_⟩
  obtain ⟨σ, hσ, K, εM, hK, hεM, hεMmax, hMerged⟩ :=
    hMerge h hh (hhd.trans_le (min_le_left _ _))
  obtain ⟨η, εO, hη, hεO, _, hMass⟩ :=
    hOrbit h hh (hhd.trans_le (min_le_right _ _)) σ hσ K hK
  let ε0 := min εM εO
  refine ⟨σ, hσ, K, ε0, hK, lt_min hεM hεO, (min_le_left _ _).trans hεMmax,
    fun ε hε hεsmall b F hF hmin => ?_⟩
  have heM : ε < εM := hεsmall.trans_le (min_le_left _ _)
  have heO : ε < εO := hεsmall.trans_le (min_le_right _ _)
  have heMax : ε < epsMax h := heM.trans_le hεMmax
  obtain ⟨label, hNear, hSame⟩ := hMerged ε hε heM b F hF hmin
  let label4 := fun s : Fin F.count => (label s).succ
  have hNear4 (s : Fin F.count) :
      ordinaryRootH1Deviation
        (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ (label4 s))
        (F.density s)
        (Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ (label4 s)).sqrt ≤ K * ε := by
    exact hNear s
  have hMasses := hMass ε hε heO b F hF hmin label4 hNear4
  have hp (j : Fin 3) : 0 < finiteSpeciesGroupWeight F label j := by
    have he : assignedOrbitWeights F label4 j = finiteSpeciesGroupWeight F label j := by
      simp only [assignedOrbitWeights, label4, finiteSpeciesGroupWeight, Fin.succ_inj]
    have hm := hMasses j
    rw [he] at hm
    exact hη.trans_le hm
  refine ⟨label, hp, hSame, fun s => ?_, ?_, ?_, fun j => ?_⟩
  · exact hSame s (finiteSpeciesGroupRepresentative F label hp (label s))
      (finiteSpeciesGroupRepresentative_label F label hp (label s)).symm
  · rw [speciesGap_finiteSpeciesGroup3 F label hp hSame hh hε heMax]
    exact hF
  · rw [speciesQuotient_finiteSpeciesGroup3 F label hp hSame hh hε heMax b]
    exact hmin
  · have hr := finiteSpeciesGroupRepresentative_label F label hp j
    have hn := hNear (finiteSpeciesGroupRepresentative F label hp j)
    rw [hr] at hn
    exact hn

end DGPS.Examples.ThreeSpeciesCircle
