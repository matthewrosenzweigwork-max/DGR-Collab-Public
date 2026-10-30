import DGPS.Examples.ThreeSpeciesCircle.InteractingReferenceBarrier
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootGraphData

/-! A genuine below-reference-barrier scalar trial, selected from the actual retained
ordinary roots. All coupling thresholds are fixed before the drift provider. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem scalarQuotient_real (h ε : ℝ) (b : AbsoluteDrift (modelData h ε))
    (ρ : AbsoluteDensity 1) (hG : 0 < scalarGap (modelData h ε) ρ) :
    scalarQuotient (modelData h ε) b ρ = ENNReal.ofReal
      ((scalarDissipation (modelData h ε) b ρ).toReal /
        (2 * (scalarGap (modelData h ε) ρ : ℝ))) := by
  have hD := (elementaryModel_scalarDissipation_real h ε b ρ).1
  have hGr : (0 : ℝ) < (scalarGap (modelData h ε) ρ : ℝ) := hG
  unfold scalarQuotient
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_toReal hD]
  simp

/-- Every genuine positive-entropy ordinary equality root gives an actual scalar
quotient below any fixed strict improvement of the ordinary rate, for small coupling. -/
theorem ordinaryRoot_interacting_scalar_trial {h : ℝ} (hh : 0 < h)
    (σ : AbsoluteDensity 1) (hH : 0 < ordinaryEntropy h σ)
    (hquot : str025_quot h σ = ordinaryLSRate (ordinaryReference h))
    {r : ℝ} (har : (ordinaryLSRate (ordinaryReference h)).toReal < r) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ b : AbsoluteDrift (modelData h ε),
        0 < scalarGap (modelData h ε) σ ∧ scalarQuotient (modelData h ε) b σ < ENNReal.ofReal r := by
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  let H := (ordinaryEntropy h σ).toReal
  let I := (ordinaryFisher h σ).toReal
  have hHreal : 0 < H := ENNReal.toReal_pos hH.ne' (str025_entropy_ne_top h σ)
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  have hr : 0 < r := ha.trans_lt har
  have hq := congrArg ENNReal.toReal hquot
  change (ordinaryFisher h σ / (2 * ordinaryEntropy h σ)).toReal = a at hq
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat] at hq
  change I / (2 * H) = a at hq
  have hI : I = 2 * a * H := by
    have hmul := (div_eq_iff (by positivity : 2 * H ≠ 0)).mp hq
    nlinarith
  obtain ⟨εG, hεG, hεGmax, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  let P := |elementaryC h a σ| + elementaryJ h σ + 1
  have hP : 0 < P := by dsimp only [P]; nlinarith [abs_nonneg (elementaryC h a σ), elementaryJ_nonneg h σ]
  let ε0 := min εG (min 1 ((r - a) * H / P))
  have hε0 : 0 < ε0 := lt_min hεG (lt_min one_pos (div_pos (mul_pos (sub_pos.mpr har) hHreal) hP))
  refine ⟨ε0, hε0, (min_le_left _ _).trans hεGmax, fun ε hε hεε0 b => ?_⟩
  have hεεG : ε < εG := hεε0.trans_le (min_le_left _ _)
  have hεmax : ε < epsMax h := hεεG.trans_le hεGmax
  have hε1 : ε ≤ 1 := (hεε0.trans_le ((min_le_right _ _).trans (min_le_left _ _))).le
  have hεP : ε * P < (r - a) * H := by
    exact (lt_div_iff₀ hP).mp
      (hεε0.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  let G : ℝ := scalarGap (modelData h ε) σ
  let D := (scalarDissipation (modelData h ε) b σ).toReal
  have hGlo : H / 2 ≤ G := by
    have hg := (hgap ε hε hεεG (SpeciesFamily.single σ)).1
    have he : (1 / 2 : ℝ) * H ≤ G := by
      simpa only [speciesGap_single, sum_single_count, SpeciesFamily.single_weight,
        SpeciesFamily.single_density, one_mul] using hg
    linarith
  have hG : 0 < G := (half_pos hHreal).trans_le hGlo
  have hGpos : 0 < scalarGap (modelData h ε) σ := hG
  have hD := elementaryModel_scalar_deficit_real hh hε hεmax b σ a
  have hDzero : D - 2 * a * G = ε * elementaryC h a σ + ε ^ 2 * elementaryJ h σ := by
    change D - 2 * a * G = I - 2 * a * H + ε * elementaryC h a σ + ε ^ 2 * elementaryJ h σ at hD
    rw [hI] at hD
    nlinarith
  have hC := mul_le_mul_of_nonneg_left (le_abs_self (elementaryC h a σ)) hε.le
  have hJ := mul_le_mul_of_nonneg_right
    (show ε ^ 2 ≤ ε by nlinarith) (elementaryJ_nonneg h σ)
  have hDlt : D < 2 * r * G := by
    have hden := mul_le_mul_of_nonneg_left hGlo (sub_nonneg.mpr har.le)
    dsimp only [P] at hεP
    nlinarith
  refine ⟨hGpos, ?_⟩
  rw [scalarQuotient_real h ε b σ hGpos]
  apply (ENNReal.ofReal_lt_ofReal_iff hr).2
  apply (div_lt_iff₀ (by positivity : 0 < 2 * G)).2
  nlinarith

/-- The actual scalar trial and the actual near-reference barrier coexist on a common
coupling interval. No trial, gap-exclusion or attainment premise is supplied. -/
theorem elementaryModel_scalar_trial_below_reference_barrier (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ (σ : AbsoluteDensity 1) (r ε0 η : ℝ),
        (ordinaryLSRate (ordinaryReference h)).toReal < r ∧
        0 < ε0 ∧ ε0 ≤ epsMax h ∧ 0 < η ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
          (0 < scalarGap (modelData h ε) σ ∧ scalarQuotient (modelData h ε) b σ < ENNReal.ofReal r) ∧
          ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
            ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) ρ (str025_w h) ≤ η →
            ENNReal.ofReal r ≤ scalarQuotient (modelData h ε) b ρ := by
  obtain ⟨δB, hδB, hbarrier⟩ := elementaryModel_reference_strict_barrier
  let δ := min δB D.radius
  refine ⟨δ, lt_min hδB D.radius_pos, min_le_right _ _, fun h hh hhd => ?_⟩
  obtain ⟨σ, _, hpos, hquot, _⟩ := D.roots h hh (hhd.trans_le (min_le_right _ _))
  obtain ⟨r, εB, η, har, hεB, hεBmax, hη, hB⟩ := hbarrier h hh (hhd.trans_le (min_le_left _ _))
  obtain ⟨εT, hεT, hεTmax, hT⟩ := ordinaryRoot_interacting_scalar_trial hh (σ 0) (hpos 0) (hquot 0) har
  refine ⟨σ 0, r, min εB εT, η, har, lt_min hεB hεT,
    (min_le_left _ _).trans hεBmax, hη, fun ε hε hεsmall b => ?_⟩
  exact ⟨hT ε hε (hεsmall.trans_le (min_le_right _ _)) b,
    hB ε hε (hεsmall.trans_le (min_le_left _ _)) b⟩

end DGPS.Examples.ThreeSpeciesCircle
