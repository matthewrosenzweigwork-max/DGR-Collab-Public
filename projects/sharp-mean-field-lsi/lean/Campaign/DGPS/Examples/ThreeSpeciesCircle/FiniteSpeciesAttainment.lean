import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesCompactness
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesGapBarrier
import DGPS.Examples.ThreeSpeciesCircle.ThreeSpeciesTrial

/-! Actual attainment of the full finite-species infimum after genuine zero-weight
compactness and uniform exclusion of the zero-gap boundary. The minimizer has at
most four original species; excluding count four is a separate theorem. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Actual full-family attainment with at most four species. The strict trial,
weighted-information bound, positive limit gap and actual D lower semicontinuity
are all constructed internally, without an attainment or desired-rate premise. -/
theorem elementaryModel_speciesRate_attainment_four (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ b : AbsoluteDrift (modelData h ε), ∃ G : SpeciesFamily 1,
          (G.count : ℕ) ≤ 4 ∧ 0 < speciesGap (modelData h ε) G ∧
          speciesQuotient (modelData h ε) b G = speciesRate (modelData h ε) b := by
  obtain ⟨δG, hδG, hδGr, hGap⟩ := elementaryModel_uniformGap_sublevel D
  obtain ⟨δT, hδT, hδTr, hTrial⟩ := elementaryModel_equalThird_trial D
  let δ := min δG δT
  refine ⟨δ, lt_min hδG hδT, (min_le_left _ _).trans hδGr, fun h hh hhd => ?_⟩
  obtain ⟨εG, hεG, hεGmax, hGapBound⟩ := hGap h hh (hhd.trans_le (min_le_left _ _))
  obtain ⟨Ftrial, hFtrial, εT, hεT, hεTmax, hTrialBound⟩ :=
    hTrial h hh (hhd.trans_le (min_le_right _ _))
  obtain ⟨εC, hεC, hεCmax, hCompact⟩ := elementaryModel_boundedQuotient_family_compactness hh
  let ε0 := min εG (min εT εC)
  refine ⟨ε0, lt_min hεG (lt_min hεT hεC), (min_le_left _ _).trans hεGmax,
    fun ε hε hε0' b => ?_⟩
  have heG : ε < εG := hε0'.trans_le (min_le_left _ _)
  have heT : ε < εT := hε0'.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heC : ε < εC := hε0'.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hemax : ε < epsMax h := heG.trans_le hεGmax
  obtain ⟨hTrialPos, hTrialLt⟩ := hTrialBound ε hε heT b
  let r := speciesRate (modelData h ε) b
  have hrle (F : SpeciesFamily 1) (hF : 0 < speciesGap (modelData h ε) F) :
      r ≤ speciesQuotient (modelData h ε) b F := speciesRate_le _ _ F hF
  have hrlt : r < ordinaryLSRate (ordinaryReference h) := (hrle Ftrial hTrialPos).trans_lt hTrialLt
  have hrfin : r ≠ ⊤ := (hrlt.trans_le le_top).ne
  have hOrdFin : ordinaryLSRate (ordinaryReference h) ≠ ⊤ := by
    obtain ⟨σ, hσ, hpos, hquot, hmin, hdist, hexact, hfin, hrate⟩ :=
      D.roots h hh (hhd.trans_le ((min_le_left _ _).trans hδGr))
    exact hfin
  have hex : ∀ n : ℕ, ∃ F : SpeciesFamily 1, 0 < speciesGap (modelData h ε) F ∧
      speciesQuotient (modelData h ε) b F < r + ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have hx : r < r + ((n : ℝ≥0∞) + 1)⁻¹ := ENNReal.lt_add_right hrfin (by simp)
    change (⨅ F : {F : SpeciesFamily 1 // 0 < speciesGap (modelData h ε) F},
      speciesQuotient (modelData h ε) b F.1) < _ at hx
    obtain ⟨⟨F, hF⟩, hq⟩ := iInf_lt_iff.1 hx
    exact ⟨F, hF, hq⟩
  choose Fraw hRawPos hRawQ using hex
  choose F hF using fun n => finiteFeature_family_support_reduce_four hh hε hemax b (Fraw n) (hRawPos n)
  have hcount (n : ℕ) : ((F n).count : ℕ) ≤ 4 := (hF n).1
  have hpos (n : ℕ) : 0 < speciesGap (modelData h ε) (F n) := (hF n).2.1
  have hupper (n : ℕ) : speciesQuotient (modelData h ε) b (F n) ≤ r + ((n : ℝ≥0∞) + 1)⁻¹ :=
    (hF n).2.2.1.trans (hRawQ n).le
  have hδlim : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
    have ht := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    refine ht.congr (fun n => ?_)
    simp [Function.comp]
  have hupperlim : Tendsto (fun n : ℕ => r + ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 r) := by
    simpa using tendsto_const_nhds.add hδlim
  have hMfin : r + 1 ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨hrfin, ENNReal.one_ne_top⟩
  have hM (n : ℕ) : speciesQuotient (modelData h ε) b (F n) ≤ ENNReal.ofReal (r + 1).toReal := by
    rw [ENNReal.ofReal_toReal hMfin]
    apply (hupper n).trans
    apply add_le_add le_rfl
    rw [ENNReal.inv_le_one]
    exact le_add_self
  obtain ⟨φ, G, hφ, hGc, hGapT, hDLSC, hH, hweak⟩ :=
    hCompact ε hε heC b (r + 1).toReal ENNReal.toReal_nonneg F hcount hpos hM
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  let s := (r.toReal + a) / 2
  have hra : r.toReal < a := (ENNReal.toReal_lt_toReal hrfin hOrdFin).2 hrlt
  have hr0 : 0 ≤ r.toReal := ENNReal.toReal_nonneg
  have hs : 0 < s := by dsimp only [s]; nlinarith only [hr0, hra]
  have hsa : s < a := by dsimp only [s]; linarith
  have hrs : r < ENNReal.ofReal s := by
    rw [← ENNReal.ofReal_toReal hrfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hs).2 (by dsimp only [s]; linarith)
  obtain ⟨η, hη, hGapLow⟩ := hGapBound ε hε heG b s hs.le hsa
  have hQevent : ∀ᶠ n in atTop, speciesQuotient (modelData h ε) b (F n) ≤ ENNReal.ofReal s :=
    ((tendsto_order.mp hupperlim).2 (ENNReal.ofReal s) hrs).mono fun n hn => (hupper n).trans hn.le
  have hGapEvent : ∀ᶠ n in atTop, η ≤ (speciesGap (modelData h ε) (F (φ n)) : ℝ) :=
    (hφ.tendsto_atTop.eventually hQevent).mono fun n hn => hGapLow (F (φ n)) (hpos (φ n)) hn
  have hGpos : 0 < speciesGap (modelData h ε) G := by
    change 0 < (speciesGap (modelData h ε) G : ℝ)
    exact hη.trans_le (ge_of_tendsto hGapT hGapEvent)
  have hDupper (n : ℕ) : speciesDissipation (modelData h ε) b (F (φ n)) ≤
      (r + (((φ n : ℕ) : ℝ≥0∞) + 1)⁻¹) * (2 * (speciesGap (modelData h ε) (F (φ n)) : ℝ≥0∞)) := by
    have hp := hpos (φ n)
    have h2 : (2 : ℝ≥0∞) * (speciesGap (modelData h ε) (F (φ n)) : ℝ≥0∞) ≠ 0 := by positivity
    have h3 : (2 : ℝ≥0∞) * (speciesGap (modelData h ε) (F (φ n)) : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top
    exact (ENNReal.div_le_iff h2 h3).1 (hupper (φ n))
  have hGapE : Tendsto (fun n => (speciesGap (modelData h ε) (F (φ n)) : ℝ≥0∞)) atTop
      (𝓝 (speciesGap (modelData h ε) G : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.tendsto_ofReal hGapT
  have hprod : Tendsto (fun n => (r + (((φ n : ℕ) : ℝ≥0∞) + 1)⁻¹) *
      (2 * (speciesGap (modelData h ε) (F (φ n)) : ℝ≥0∞))) atTop
      (𝓝 (r * (2 * (speciesGap (modelData h ε) G : ℝ≥0∞)))) :=
    ENNReal.Tendsto.mul (hupperlim.comp hφ.tendsto_atTop)
      (Or.inr (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top))
      (ENNReal.Tendsto.const_mul hGapE (Or.inr (by norm_num))) (Or.inr hrfin)
  have hDG : speciesDissipation (modelData h ε) b G ≤ r * (2 * (speciesGap (modelData h ε) G : ℝ≥0∞)) :=
    hDLSC.trans ((liminf_le_liminf (Eventually.of_forall hDupper)).trans_eq hprod.liminf_eq)
  have hQG : speciesQuotient (modelData h ε) b G ≤ r := ENNReal.div_le_of_le_mul hDG
  exact ⟨G, hGc, hGpos, le_antisymm hQG (hrle G hGpos)⟩

end DGPS.Examples.ThreeSpeciesCircle
