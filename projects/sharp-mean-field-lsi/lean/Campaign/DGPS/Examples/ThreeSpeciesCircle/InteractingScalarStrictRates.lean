import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarAttainment
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryBinaryClosure
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarTrialLinear
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReferencePoincareGap

/-! Actual strict scalar rate comparisons. The lower comparison uses genuine
scalar attainment and the already proved strict count-at-most-two quotient
theorem, so no new moment-continuity or optimizer-classification premise is needed. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Actual scalar attainment makes the strict binary quotient lower bound
strict at the scalar infimum. All competitors retain their original H1 domain. -/
theorem elementaryModel_ordinary_lt_scalarRate :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ b : AbsoluteDrift (modelData h ε),
          ordinaryLSRate (ordinaryReference h) < scalarRate (modelData h ε) b := by
  obtain ⟨D⟩ := exists_ordinaryRootGraphData
  obtain ⟨δA, hδA, _, hAttain⟩ := elementaryModel_scalar_attainment_of_graph D
  obtain ⟨δB, hδB, _, hBinary⟩ := ordinaryBinary_strict_quotient_same_graph D
  refine ⟨min δA δB, lt_min hδA hδB, fun h hh hhd => ?_⟩
  obtain ⟨εA, hεA, hεAmax, hA⟩ := hAttain h hh (hhd.trans_le (min_le_left _ _))
  obtain ⟨εB, hεB, _, hB⟩ := hBinary h hh (hhd.trans_le (min_le_right _ _))
  refine ⟨min εA εB, lt_min hεA hεB, (min_le_left _ _).trans hεAmax,
    fun ε hε hεsmall b => ?_⟩
  obtain ⟨σ, hG, hmin⟩ := hA ε hε (hεsmall.trans_le (min_le_left _ _)) b
  have hs := hB ε hε (hεsmall.trans_le (min_le_right _ _)) b
    (SpeciesFamily.single σ) (by norm_num [SpeciesFamily.single])
    (by simpa only [speciesGap_single] using hG)
  rwa [speciesQuotient_single, hmin] at hs

/-- Actual linear scalar trials and the ordinary/reference Poincare gap give
the strict upper comparison, uniformly over genuine weak drift providers. -/
theorem elementaryModel_scalarRate_lt_referencePoincare :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, (hh : 0 < h) → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ b : AbsoluteDrift (modelData h ε),
          scalarRate (modelData h ε) b < poincareRate (refProb hh) := by
  obtain ⟨D⟩ := exists_ordinaryRootGraphData
  obtain ⟨δP, hδP, hReference⟩ := threefold_reference_rate_and_strictPoincareGap
  refine ⟨min D.radius δP, lt_min D.radius_pos hδP, fun h hh hhd => ?_⟩
  have hhD := hhd.trans_le (min_le_left _ _)
  obtain ⟨hAfin, _, hAP⟩ := hReference h hh (hhd.trans_le (min_le_right _ _))
  obtain ⟨p, hap, hpP⟩ := exists_between hAP
  have hpfin : p ≠ ⊤ := (hpP.trans_le le_top).ne
  have hgap : 0 < p.toReal - (ordinaryLSRate (ordinaryReference h)).toReal :=
    sub_pos.mpr ((ENNReal.toReal_lt_toReal hAfin hpfin).2 hap)
  obtain ⟨σ, _, hpos, hquot, _⟩ := D.roots h hh hhD
  obtain ⟨εT, K, hεT, hεTmax, hK, hTrial⟩ :=
    ordinaryRoot_interacting_scalar_trial_linear hh (σ 0) (hpos 0) (hquot 0)
  let ε0 := min εT ((p.toReal - (ordinaryLSRate (ordinaryReference h)).toReal) / (2 * K))
  have hε0 : 0 < ε0 := lt_min hεT (div_pos hgap (by positivity))
  refine ⟨ε0, hε0, (min_le_left _ _).trans hεTmax, fun ε hε hεsmall b => ?_⟩
  obtain ⟨hTG, hTQ⟩ := hTrial ε hε (hεsmall.trans_le (min_le_left _ _)) b
  have he := (lt_div_iff₀ (by positivity : 0 < 2 * K)).1
    (hεsmall.trans_le (min_le_right _ _))
  have hupper : (ordinaryLSRate (ordinaryReference h)).toReal + K * ε < p.toReal := by
    nlinarith
  have hrp : ENNReal.ofReal ((ordinaryLSRate (ordinaryReference h)).toReal + K * ε) < p := by
    rw [← ENNReal.ofReal_toReal hpfin]
    exact ENNReal.ofReal_lt_ofReal_iff'.2 ⟨hupper,
      (show 0 ≤ (ordinaryLSRate (ordinaryReference h)).toReal + K * ε by positivity).trans_lt hupper⟩
  exact ((scalarRate_le_quotient (modelData h ε) b (σ 0) hTG).trans hTQ).trans_lt
    (hrp.trans hpP)

/-- Both actual strict scalar comparisons, with field chosen before the
coupling threshold and no analytic or classification premise. -/
theorem elementaryModel_scalarRate_strict_between :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, (hh : 0 < h) → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ b : AbsoluteDrift (modelData h ε),
          ordinaryLSRate (ordinaryReference h) < scalarRate (modelData h ε) b ∧
            scalarRate (modelData h ε) b < poincareRate (refProb hh) := by
  obtain ⟨δL, hδL, hLower⟩ := elementaryModel_ordinary_lt_scalarRate
  obtain ⟨δU, hδU, hUpper⟩ := elementaryModel_scalarRate_lt_referencePoincare
  refine ⟨min δL δU, lt_min hδL hδU, fun h hh hhd => ?_⟩
  obtain ⟨εL, hεL, hεLmax, hL⟩ := hLower h hh (hhd.trans_le (min_le_left _ _))
  obtain ⟨εU, hεU, _, hU⟩ := hUpper h hh (hhd.trans_le (min_le_right _ _))
  refine ⟨min εL εU, lt_min hεL hεU, (min_le_left _ _).trans hεLmax,
    fun ε hε hεsmall b => ⟨hL ε hε (hεsmall.trans_le (min_le_left _ _)) b,
      hU ε hε (hεsmall.trans_le (min_le_right _ _)) b⟩⟩

end DGPS.Examples.ThreeSpeciesCircle
