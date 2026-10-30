import DGPS.Examples.ThreeSpeciesCircle.ThreeSpeciesTrial
import DGPS.Examples.ThreeSpeciesCircle.InteractingPositiveRate
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarStrictRates
import DGPS.Examples.ThreeSpeciesCircle.GaussianTwoSector
import DGPS.Examples.ThreeSpeciesCircle.GaussianRateFinite
import DGPS.Foundations.RateArithmetic

/-! The complete actual T08 rate chain, positivity and seven finite-rate guards.
The field precedes the coupling threshold, which precedes every drift provider.
Optimizer classification and fixed-barycenter uphill splitting are separate. -/

noncomputable section
open MeasureTheory
open scoped ENNReal
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- A retained graph supplies a genuine ternary trial. Every other comparison
and all finite-rate guards are discharged from their actual production providers. -/
theorem elementaryModel_full_rate_chain_of_graph (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, (hh : 0 < h) → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∃ hH : IsCoerciveDensityHessian (modelData h ε) (refProb hh),
          ∀ b : AbsoluteDrift (modelData h ε),
            (∀ r ∈ [speciesRate (modelData h ε) b,
              speciesRateAtMost (modelData h ε) b 2, scalarRate (modelData h ε) b,
              ordinaryLSRate (ordinaryReference h), poincareRate (refProb hh),
              gaussianRate (modelData h ε) (refProb hh) hH,
              twoSectorRate (modelData h ε) (ordinaryReference h) hH], FiniteRate r) ∧
            0 < speciesRate (modelData h ε) b ∧
            speciesRate (modelData h ε) b < speciesRateAtMost (modelData h ε) b 2 ∧
            speciesRateAtMost (modelData h ε) b 2 = ordinaryLSRate (ordinaryReference h) ∧
            ordinaryLSRate (ordinaryReference h) < scalarRate (modelData h ε) b ∧
            scalarRate (modelData h ε) b <
              twoSectorRate (modelData h ε) (ordinaryReference h) hH ∧
            twoSectorRate (modelData h ε) (ordinaryReference h) hH = poincareRate (refProb hh) ∧
            poincareRate (refProb hh) < gaussianRate (modelData h ε) (refProb hh) hH ∧
            ∀ F : SpeciesFamily 1, (F.count : ℕ) ≤ 2 → 0 < speciesGap (modelData h ε) F →
              speciesRateAtMost (modelData h ε) b 2 < speciesQuotient (modelData h ε) b F := by
  obtain ⟨δT, hδT, hδTD, hTrial⟩ := elementaryModel_equalThird_trial D
  obtain ⟨δP, hδP, hPositive⟩ := elementaryModel_speciesRate_positive_small_coupling
  obtain ⟨δB, hδB, hBinary⟩ := elementaryModel_binary_rate_eq_and_strict
  obtain ⟨δS, hδS, hScalar⟩ := elementaryModel_scalarRate_strict_between
  let δ := min δT (min δP (min δB (min δS (1 / 1000))))
  have hδ : 0 < δ := lt_min hδT (lt_min hδP (lt_min hδB (lt_min hδS (by norm_num))))
  refine ⟨δ, hδ, (min_le_left _ _).trans hδTD, fun h hh hhd => ?_⟩
  have hhT : h < δT := hhd.trans_le (min_le_left _ _)
  have hh1 : h < min δP (min δB (min δS (1 / 1000))) := hhd.trans_le (min_le_right _ _)
  have hhP : h < δP := hh1.trans_le (min_le_left _ _)
  have hh2 : h < min δB (min δS (1 / 1000)) := hh1.trans_le (min_le_right _ _)
  have hhB : h < δB := hh2.trans_le (min_le_left _ _)
  have hh3 : h < min δS (1 / 1000) := hh2.trans_le (min_le_right _ _)
  have hhS : h < δS := hh3.trans_le (min_le_left _ _)
  have hhsmall : |h| ≤ 1 / 1000 := by
    rw [abs_of_pos hh]
    exact (hh3.trans_le (min_le_right _ _)).le
  obtain ⟨F, _, εT, hεT, hεTmax, hT⟩ := hTrial h hh hhT
  obtain ⟨εP, hεP, _, hP⟩ := hPositive h hh hhP
  obtain ⟨εB, hεB, _, hB⟩ := hBinary h hh hhB
  obtain ⟨εS, hεS, _, hS⟩ := hScalar h hh hhS
  obtain ⟨εG, hεG, _, hG⟩ := elementaryModel_twoSector_and_strictGaussian hh hhsmall
  let ε0 := min εT (min εP (min εB (min εS εG)))
  have hε0 : 0 < ε0 := lt_min hεT (lt_min hεP (lt_min hεB (lt_min hεS hεG)))
  have hε0max : ε0 ≤ epsMax h := (min_le_left _ _).trans hεTmax
  refine ⟨ε0, hε0, hε0max, fun ε hε hεsmall => ?_⟩
  have heT : ε < εT := hεsmall.trans_le (min_le_left _ _)
  have he1 : ε < min εP (min εB (min εS εG)) := hεsmall.trans_le (min_le_right _ _)
  have heP : ε < εP := he1.trans_le (min_le_left _ _)
  have he2 : ε < min εB (min εS εG) := he1.trans_le (min_le_right _ _)
  have heB : ε < εB := he2.trans_le (min_le_left _ _)
  have he3 : ε < min εS εG := he2.trans_le (min_le_right _ _)
  have heS : ε < εS := he3.trans_le (min_le_left _ _)
  have heG : ε < εG := he3.trans_le (min_le_right _ _)
  let hH := elementaryModel_coerciveHessian hh hε (hεsmall.trans_le hε0max)
  refine ⟨hH, fun b => ?_⟩
  obtain ⟨hFgap, hFquot⟩ := hT ε hε heT b
  have hMsA : speciesRate (modelData h ε) b < ordinaryLSRate (ordinaryReference h) :=
    (speciesRate_le (modelData h ε) b F hFgap).trans_lt hFquot
  have hPos := (hP ε hε heP b).2
  have hBin := hB ε hε heB b
  have hSc := hS ε hε heS b
  have hGauss := hG ε hε heG hH
  have hfinPC : FiniteRate (poincareRate (refProb hh)) := threefold_reference_poincare_ne_top hh
  have hfinScalar : FiniteRate (scalarRate (modelData h ε) b) :=
    ne_top_of_le_ne_top hfinPC hSc.2.le
  have hfinA : FiniteRate (ordinaryLSRate (ordinaryReference h)) :=
    ne_top_of_le_ne_top hfinScalar hSc.1.le
  have hfinMs : FiniteRate (speciesRate (modelData h ε) b) :=
    ne_top_of_le_ne_top hfinA hMsA.le
  have hfinBinary : FiniteRate (speciesRateAtMost (modelData h ε) b 2) := by
    rw [hBin.1]
    exact hfinA
  have hfinGaussian : FiniteRate (gaussianRate (modelData h ε) (refProb hh) hH) :=
    elementaryModel_gaussianRate_ne_top hh hH
  have hfinTwo : FiniteRate (twoSectorRate (modelData h ε) (ordinaryReference h) hH) := by
    rw [hGauss.1]
    exact hfinPC
  have hfinite : ∀ r ∈ [speciesRate (modelData h ε) b,
      speciesRateAtMost (modelData h ε) b 2, scalarRate (modelData h ε) b,
      ordinaryLSRate (ordinaryReference h), poincareRate (refProb hh),
      gaussianRate (modelData h ε) (refProb hh) hH,
      twoSectorRate (modelData h ε) (ordinaryReference h) hH], FiniteRate r := by
    intro r hr
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  refine ⟨hfinite, hPos, ?_, hBin.1, hSc.1, ?_, hGauss.1, hGauss.2, hBin.2⟩
  · rw [hBin.1]
    exact hMsA
  · rw [hGauss.1]
    exact hSc.2

/-- The complete frozen rate-chain component with an actual retained graph
constructed internally. No rate, trial, attainment or coefficient comparison is
an input; the coupling interval precedes all genuine drift providers. -/
theorem elementaryModel_full_rate_chain :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, (hh : 0 < h) → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∃ hH : IsCoerciveDensityHessian (modelData h ε) (refProb hh),
          ∀ b : AbsoluteDrift (modelData h ε),
            (∀ r ∈ [speciesRate (modelData h ε) b,
              speciesRateAtMost (modelData h ε) b 2, scalarRate (modelData h ε) b,
              ordinaryLSRate (ordinaryReference h), poincareRate (refProb hh),
              gaussianRate (modelData h ε) (refProb hh) hH,
              twoSectorRate (modelData h ε) (ordinaryReference h) hH], FiniteRate r) ∧
            0 < speciesRate (modelData h ε) b ∧
            speciesRate (modelData h ε) b < speciesRateAtMost (modelData h ε) b 2 ∧
            speciesRateAtMost (modelData h ε) b 2 = ordinaryLSRate (ordinaryReference h) ∧
            ordinaryLSRate (ordinaryReference h) < scalarRate (modelData h ε) b ∧
            scalarRate (modelData h ε) b <
              twoSectorRate (modelData h ε) (ordinaryReference h) hH ∧
            twoSectorRate (modelData h ε) (ordinaryReference h) hH = poincareRate (refProb hh) ∧
            poincareRate (refProb hh) < gaussianRate (modelData h ε) (refProb hh) hH ∧
            ∀ F : SpeciesFamily 1, (F.count : ℕ) ≤ 2 → 0 < speciesGap (modelData h ε) F →
              speciesRateAtMost (modelData h ε) b 2 < speciesQuotient (modelData h ε) b F := by
  obtain ⟨D⟩ := exists_ordinaryRootGraphData
  obtain ⟨δ, hδ, _, hmain⟩ := elementaryModel_full_rate_chain_of_graph D
  exact ⟨δ, hδ, hmain⟩

end DGPS.Examples.ThreeSpeciesCircle
