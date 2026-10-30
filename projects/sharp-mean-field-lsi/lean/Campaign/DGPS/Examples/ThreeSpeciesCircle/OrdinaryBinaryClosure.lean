import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootMomentSigns
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryDeficitMomentError
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryAssignmentZero
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryBinaryDilution

/-! Actual binary closure on the original finite positive-weight family domain.
All coefficient signs and distance estimates come from the SAME retained graph.
The final producer assumes no desired strict deficit or binary rate conclusion. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Actual positive-gap binary competitors have strictly positive ordinary-rate
interacting deficit. The endpoint zero case is excluded by true original-law
identification, with no uniform lower bound on the individual weights. -/
theorem ordinaryBinary_strict_deficit_same_graph (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
          (F.count : ℕ) ≤ 2 → 0 < speciesGap (modelData h ε) F →
          0 < (speciesDissipation (modelData h ε) b F).toReal -
            2 * (ordinaryLSRate (ordinaryReference h)).toReal * (speciesGap (modelData h ε) F : ℝ) := by
  obtain ⟨δs, hδs, hδsr, hsign⟩ := ordinaryRoot_correction_coefficient_signs D
  obtain ⟨δe, hδe, hδer, herr⟩ := ordinaryDeficit_C_error_same_graph D
  let δ := min δs δe
  refine ⟨δ, lt_min hδs hδe, (min_le_left _ _).trans hδsr, fun h hh hhd => ?_⟩
  have hhs : h < δs := hhd.trans_le (min_le_left _ _)
  have hhe : h < δe := hhd.trans_le (min_le_right _ _)
  have hhr : h < D.radius := hhs.trans_le hδsr
  obtain ⟨σ, hσ, c, hc, herror⟩ := herr h hh hhe
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  obtain ⟨hα0, hα, hβ⟩ := hsign h hh hhs σ hσ
  obtain ⟨K, hK, hCerror⟩ := herror a
  let ε0 := min (epsMax h) (1 / (4 * (K + 1) ^ 2))
  have hε0 : 0 < ε0 := lt_min (epsMax_pos h) (by positivity)
  refine ⟨ε0, hε0, min_le_left _ _, fun ε hε hεε0 b F hcount hG => ?_⟩
  have hεmax : ε < epsMax h := hεε0.trans_le (min_le_left _ _)
  have hεbound : ε * (K + 1) ^ 2 ≤ 1 / 4 := by
    have he : ε < 1 / (4 * (K + 1) ^ 2) := hεε0.trans_le (min_le_right _ _)
    have ht := (lt_div_iff₀ (by positivity : (0 : ℝ) < 4 * (K + 1) ^ 2)).mp he
    nlinarith
  have hεK : ε * K ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left (show K ≤ (K + 1) ^ 2 by nlinarith [sq_nonneg K]) hε.le).trans hεbound
  have hεK2 : ε * K ^ 2 ≤ 1 / 4 :=
    (mul_le_mul_of_nonneg_left (show K ^ 2 ≤ (K + 1) ^ 2 by nlinarith) hε.le).trans hεbound
  obtain ⟨label, hbudget, herrorF⟩ := hCerror F
  let R : Fin 4 → AbsoluteDensity 1 := Fin.cases (ordinaryReferenceAbsolute h) σ
  let D0 := ∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
    2 * a * (ordinaryEntropy h (F.density s)).toReal)
  let u := nonreferenceRootWeight F label
  obtain ⟨hD0, hJ, hDfinite, _, hdef⟩ := elementaryModel_exactDeficitExpansion hh hε hεmax b F
  change 0 ≤ D0 at hD0
  change (speciesDissipation (modelData h ε) b F).toReal -
    2 * a * (speciesGap (modelData h ε) F : ℝ) =
      D0 + ε * elementaryC h a (barycenter F) + ε ^ 2 * elementaryJ h (barycenter F) at hdef
  have hu : 0 ≤ u := nonreferenceRootWeight_nonneg F label
  have hmargin := elementaryC_assigned_binary_margin D hh
    (show h ∈ Set.Ioo (-D.radius) D.radius from ⟨by linarith [D.radius_pos], hhr⟩)
    σ hσ a hβ.le hα.le F hcount label
  have hClower : u ^ 2 / 2 - K * (u * Real.sqrt D0 + D0) ≤ elementaryC h a (barycenter F) := by
    have he := (abs_le.mp herrorF).1
    change -(K * (u * Real.sqrt D0 + D0)) ≤ elementaryC h a (barycenter F) -
      elementaryC h a (barycenter (assignedRootFamily F R label)) at he
    change u ^ 2 / 2 ≤ elementaryC h a (barycenter (assignedRootFamily F R label)) at hmargin
    linarith
  have habsorb := binary_deficit_absorption hD0 hu hK.le hε.le hJ hεK hεK2 hClower
  rw [← hdef] at habsorb
  by_contra hn
  have hnonpos : (speciesDissipation (modelData h ε) b F).toReal -
      2 * a * (speciesGap (modelData h ε) F : ℝ) ≤ 0 := not_lt.mp hn
  have hDz : D0 = 0 := by nlinarith [mul_nonneg hε.le (sq_nonneg u)]
  have huz : u = 0 := by
    by_contra hne
    have hp := mul_pos hε (sq_pos_of_ne_zero hne)
    nlinarith
  have hRz : rootDistanceBudget F R label = 0 := by
    apply le_antisymm _ (rootDistanceBudget_nonneg F R label)
    change rootDistanceBudget F R label ≤ D0 / c at hbudget
    simpa only [hDz, zero_div] using hbudget
  have hR0 : (densityMeasure (R 0) : Measure (Torus 1)) = threefoldReference h :=
    ordinaryReferenceAbsolute_measure h
  have hz := ordinaryAssignment_zero_gap hh hε hεmax F R label hR0 hRz huz
  exact hG.ne' hz

/-- Every actual positive-gap binary quotient lies strictly above the actual
ordinary rate, although the infimum is approached by the genuine dilution sequence. -/
theorem ordinaryBinary_strict_quotient_same_graph (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
          (F.count : ℕ) ≤ 2 → 0 < speciesGap (modelData h ε) F →
          ordinaryLSRate (ordinaryReference h) < speciesQuotient (modelData h ε) b F := by
  obtain ⟨δ, hδ, hδr, hstrict⟩ := ordinaryBinary_strict_deficit_same_graph D
  refine ⟨δ, hδ, hδr, fun h hh hhd => ?_⟩
  obtain ⟨ε0, hε0, hε0max, hdef⟩ := hstrict h hh hhd
  obtain ⟨_, _, _, _, _, _, _, hRateFinite, _⟩ := D.roots h hh (hhd.trans_le hδr)
  refine ⟨ε0, hε0, hε0max, fun ε hε hεε0 b F hcount hG => ?_⟩
  have hdf := hdef ε hε hεε0 b F hcount hG
  have hDfinite := (elementaryModel_speciesDissipation_expansion h ε b F).1
  have hGr : (0 : ℝ) < (speciesGap (modelData h ε) F : ℝ) := hG
  have hreal : (ordinaryLSRate (ordinaryReference h)).toReal <
      (speciesDissipation (modelData h ε) b F).toReal / (2 * (speciesGap (modelData h ε) F : ℝ)) := by
    apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (speciesGap (modelData h ε) F : ℝ))).2
    nlinarith
  have hq : speciesQuotient (modelData h ε) b F = ENNReal.ofReal
      ((speciesDissipation (modelData h ε) b F).toReal / (2 * (speciesGap (modelData h ε) F : ℝ))) := by
    unfold speciesQuotient
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hDfinite]
    simp
  rw [hq, ← ENNReal.ofReal_toReal hRateFinite]
  exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hreal, ENNReal.toReal_nonneg.trans_lt hreal⟩

/-- Actual at-most-two rate equality and nonattainment on the full original
binary family domain, with all analytic coefficient premises discharged. -/
theorem elementaryModel_binary_rate_eq_and_strict :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ b : AbsoluteDrift (modelData h ε),
          speciesRateAtMost (modelData h ε) b 2 = ordinaryLSRate (ordinaryReference h) ∧
          ∀ F : SpeciesFamily 1, (F.count : ℕ) ≤ 2 → 0 < speciesGap (modelData h ε) F →
            speciesRateAtMost (modelData h ε) b 2 < speciesQuotient (modelData h ε) b F := by
  let D := Classical.choice exists_ordinaryRootGraphData
  obtain ⟨δ, hδ, hδr, hstrict⟩ := ordinaryBinary_strict_quotient_same_graph D
  refine ⟨δ, hδ, fun h hh hhd => ?_⟩
  obtain ⟨εs, hεs, hεsmax, hs⟩ := hstrict h hh hhd
  obtain ⟨εu, hεu, hεumax, hu⟩ := ordinaryBinary_rate_upper_same_graph D hh (hhd.trans_le hδr)
  let ε0 := min εs εu
  refine ⟨ε0, lt_min hεs hεu, (min_le_left _ _).trans hεsmax, fun ε hε hεε0 b => ?_⟩
  have hεs' : ε < εs := hεε0.trans_le (min_le_left _ _)
  have hεu' : ε < εu := hεε0.trans_le (min_le_right _ _)
  have hlow : ordinaryLSRate (ordinaryReference h) ≤ speciesRateAtMost (modelData h ε) b 2 := by
    unfold speciesRateAtMost
    exact le_iInf fun F => (hs ε hε hεs' b F.1 F.2.1 F.2.2).le
  have heq := le_antisymm (hu ε hε hεu' b) hlow
  refine ⟨heq, fun F hcount hG => ?_⟩
  rw [heq]
  exact hs ε hε hεs' b F hcount hG

end DGPS.Examples.ThreeSpeciesCircle
