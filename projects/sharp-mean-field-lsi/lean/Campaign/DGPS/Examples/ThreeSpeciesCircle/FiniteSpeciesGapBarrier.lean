import DGPS.Examples.ThreeSpeciesCircle.OrdinaryAssignedRootCBound
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootEntropyDistance
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryDeficitMomentError
import DGPS.Examples.ThreeSpeciesCircle.InteractingEntropyComparison

/-! Actual uniform separation from zero gap on strict sublevels of the ordinary
rate. Every coefficient is supplied by the same actual root graph before epsilon
and every finite family. No positive lower bound on a species weight is used. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem root_weight_square_control {c H K : ℝ} (hc : 0 < c) (hH : 0 < H) (hK : 0 ≤ K) :
    ∃ L : ℝ, 0 < L ∧ ∀ E D R u : ℝ, 0 ≤ E → 0 ≤ D → 0 ≤ R → 0 ≤ u →
      R ≤ D / c → H * u ≤ E + K * Real.sqrt R → u ^ 2 ≤ L * (E ^ 2 + D) := by
  let L := (2 * c + 2 * K ^ 2 + 1) / (c * H ^ 2)
  have hden : 0 < c * H ^ 2 := mul_pos hc (sq_pos_of_pos hH)
  refine ⟨L, div_pos (by positivity) hden, fun E D R u hE hD hR hu hbudget hent => ?_⟩
  have hs := pow_le_pow_left₀ (mul_nonneg hH.le hu) hent 2
  have hKR : (K * Real.sqrt R) ^ 2 = K ^ 2 * R := by rw [mul_pow, Real.sq_sqrt hR]
  have hsq : (H * u) ^ 2 ≤ 2 * E ^ 2 + 2 * K ^ 2 * R := by
    nlinarith only [hs, hKR, sq_nonneg (E - K * Real.sqrt R)]
  have hb := (le_div_iff₀ hc).mp hbudget
  have hh := mul_le_mul_of_nonneg_left hsq hc.le
  have hb' := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * K ^ 2 by positivity)
  have hlarge : (c * H ^ 2) * u ^ 2 ≤ (2 * c + 2 * K ^ 2 + 1) * (E ^ 2 + D) := by
    nlinarith only [hh, hb', mul_nonneg hc.le hD, mul_nonneg (sq_nonneg K) (sq_nonneg E), sq_nonneg E, hD]
  calc
    _ ≤ ((2 * c + 2 * K ^ 2 + 1) * (E ^ 2 + D)) / (c * H ^ 2) :=
      (le_div_iff₀ hden).mpr (by nlinarith [hlarge])
    _ = _ := by dsimp only [L]; ring

/-- The actual finite-family deficit has a quadratic-gap lower bound on an
h-dependent positive coupling interval. All root and correction bounds are
constructed from the SAME retained graph before the family and its weights. -/
theorem elementaryModel_family_deficit_quadratic_gap (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ B ε0 : ℝ, 0 < B ∧ 0 < ε0 ∧ ε0 ≤ epsMax h ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
          (speciesDissipation (modelData h ε) b F).toReal -
            2 * (ordinaryLSRate (ordinaryReference h)).toReal * (speciesGap (modelData h ε) F : ℝ) ≥
              -4 * ε * B * (speciesGap (modelData h ε) F : ℝ) ^ 2 := by
  obtain ⟨δ, hδ, hδr, hroot⟩ := ordinaryDeficit_C_error_same_graph D
  refine ⟨δ, hδ, hδr, fun h hh hhd => ?_⟩
  obtain ⟨σ, hσ, c, hc, herr⟩ := hroot h hh hhd
  have hhr : h < D.radius := hhd.trans_le hδr
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  obtain ⟨KE, hKE, herror⟩ := herr a
  obtain ⟨KA, hKA, hassigned⟩ := ordinaryAssignedRoot_C_abs_bound D hh
    ⟨by linarith, hhr⟩ σ hσ a
  obtain ⟨H, KH, hH, hKH, hentropy⟩ := ordinaryRoot_family_entropy_distance D hh hhr σ hσ
  obtain ⟨L, hL, hweight⟩ := root_weight_square_control hc hH hKH.le
  let B := (KA + 2 * KE + 1) * (L + 1)
  have hB : 0 < B := by dsimp only [B]; positivity
  obtain ⟨εg, hεg, hεgmax, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  let ε0 := min εg (1 / (2 * (B + 1)))
  have hε0 : 0 < ε0 := lt_min hεg (by positivity)
  refine ⟨B, ε0, hB, hε0, (min_le_left _ _).trans hεgmax, fun ε hε hεε0 b F => ?_⟩
  have hεg' : ε < εg := hεε0.trans_le (min_le_left _ _)
  have hεmax : ε < epsMax h := hεg'.trans_le hεgmax
  have hεB : ε * B ≤ 1 / 2 := by
    have he : ε ≤ 1 / (2 * (B + 1)) := (hεε0.trans_le (min_le_right _ _)).le
    have hm := mul_le_mul_of_nonneg_right he hB.le
    have hcoef : (1 / (2 * (B + 1))) * B ≤ 1 / 2 := by
      rw [one_div_mul_eq_div, div_le_iff₀ (by positivity : 0 < 2 * (B + 1))]
      linarith
    exact hm.trans hcoef
  let E := ∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal
  let D0 := ∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
    2 * a * (ordinaryEntropy h (F.density s)).toReal)
  let R := Fin.cases (motive := fun _ : Fin 4 => AbsoluteDensity 1) (ordinaryReferenceAbsolute h) σ
  have hE : 0 ≤ E := Finset.sum_nonneg fun s _ => mul_nonneg (F.weight_nonneg s) ENNReal.toReal_nonneg
  have hD0 : 0 ≤ D0 := Finset.sum_nonneg fun s _ =>
    mul_nonneg (F.weight_nonneg s) (elementary_ordinary_deficit_nonneg h (F.density s))
  obtain ⟨label, hbudget, hCerror⟩ := herror F
  let u := nonreferenceRootWeight F label
  have hu : 0 ≤ u := nonreferenceRootWeight_nonneg F label
  have hU : u ^ 2 ≤ L * (E ^ 2 + D0) := hweight E D0 (rootDistanceBudget F R label) u
    hE hD0 (rootDistanceBudget_nonneg F R label) hu hbudget (hentropy F label)
  have hCA := hassigned F label
  have hC : |elementaryC h a (barycenter F)| ≤ B * (E ^ 2 + D0) := by
    have habs : |elementaryC h a (barycenter F)| ≤
        KA * u ^ 2 + KE * (u * Real.sqrt D0 + D0) := by
      have ht := abs_add_le (elementaryC h a (barycenter F) -
        elementaryC h a (barycenter (assignedRootFamily F R label)))
        (elementaryC h a (barycenter (assignedRootFamily F R label)))
      rw [sub_add_cancel] at ht
      exact ht.trans ((add_le_add hCerror hCA).trans_eq (by ring))
    have hy : u * Real.sqrt D0 ≤ u ^ 2 + D0 := by
      nlinarith [sq_nonneg (u - Real.sqrt D0), Real.sq_sqrt hD0]
    have hcoarse : |elementaryC h a (barycenter F)| ≤ (KA + 2 * KE + 1) * (u ^ 2 + D0) := by
      have hm := mul_le_mul_of_nonneg_left hy hKE.le
      nlinarith only [habs, hm, mul_nonneg hKA.le hD0, mul_nonneg hKE.le (sq_nonneg u), sq_nonneg u, hD0]
    have hu' : u ^ 2 + D0 ≤ (L + 1) * (E ^ 2 + D0) := by nlinarith only [hU, sq_nonneg E]
    exact hcoarse.trans (by
      have hm := mul_le_mul_of_nonneg_left hu' (show 0 ≤ KA + 2 * KE + 1 by positivity)
      simpa only [B, mul_assoc] using hm)
  obtain ⟨-, hJ, hDfinite, -, hdef⟩ := elementaryModel_exactDeficitExpansion hh hε hεmax b F
  have hClo := mul_le_mul_of_nonneg_left (abs_le.mp hC).1 hε.le
  have hJε := mul_nonneg (sq_nonneg ε) hJ
  have hremain := mul_nonneg (sub_nonneg.mpr (hεB.trans (by norm_num : (1 / 2 : ℝ) ≤ 1))) hD0
  have hdeflower : -ε * B * E ^ 2 ≤ (speciesDissipation (modelData h ε) b F).toReal -
      2 * a * (speciesGap (modelData h ε) F : ℝ) := by
    change (speciesDissipation (modelData h ε) b F).toReal -
      2 * a * (speciesGap (modelData h ε) F : ℝ) = D0 + ε * elementaryC h a (barycenter F) +
      ε ^ 2 * elementaryJ h (barycenter F) at hdef
    nlinarith only [hdef, hClo, hJε, hremain]
  have hGap0 : 0 ≤ (speciesGap (modelData h ε) F : ℝ) := (speciesGap (modelData h ε) F).coe_nonneg
  have hEle : E ≤ 2 * (speciesGap (modelData h ε) F : ℝ) := by
    have hh := (hgap ε hε hεg' F).1
    change (1 / 2 : ℝ) * E ≤ _ at hh
    linarith
  have hEsq := pow_le_pow_left₀ hE hEle 2
  have hm := mul_le_mul_of_nonneg_left hEsq (mul_nonneg hε.le hB.le)
  change -4 * ε * B * (speciesGap (modelData h ε) F : ℝ) ^ 2 ≤ _
  change _ ≤ (speciesDissipation (modelData h ε) b F).toReal -
    2 * a * (speciesGap (modelData h ε) F : ℝ)
  nlinarith only [hdeflower, hm]

/-- A strict actual quotient sublevel below the ordinary rate has a uniformly
positive actual gap, before all finite counts, weights and density competitors. -/
theorem elementaryModel_uniformGap_sublevel (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ (b : AbsoluteDrift (modelData h ε)) (r : ℝ), 0 ≤ r →
          r < (ordinaryLSRate (ordinaryReference h)).toReal →
          ∃ η : ℝ, 0 < η ∧ ∀ F : SpeciesFamily 1,
            0 < speciesGap (modelData h ε) F → speciesQuotient (modelData h ε) b F ≤ ENNReal.ofReal r →
              η ≤ (speciesGap (modelData h ε) F : ℝ) := by
  obtain ⟨δ, hδ, hδr, hbound⟩ := elementaryModel_family_deficit_quadratic_gap D
  refine ⟨δ, hδ, hδr, fun h hh hhd => ?_⟩
  obtain ⟨B, ε0, hB, hε0, hεmax, hdef⟩ := hbound h hh hhd
  refine ⟨ε0, hε0, hεmax, fun ε hε hε0' b r hr hra => ?_⟩
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  let η := (a - r) / (2 * ε * B)
  have hη : 0 < η := div_pos (sub_pos.mpr hra) (by positivity)
  refine ⟨η, hη, fun F hGp hq => ?_⟩
  have hG : 0 < (speciesGap (modelData h ε) F : ℝ) := hGp
  have hDfinite := (elementaryModel_speciesDissipation_expansion h ε b F).1
  have hqR := ENNReal.toReal_mono ENNReal.ofReal_ne_top hq
  unfold speciesQuotient at hqR
  rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat,
    ENNReal.coe_toReal, ENNReal.toReal_ofReal hr] at hqR
  have hDq := (div_le_iff₀ (by positivity : 0 < 2 * (speciesGap (modelData h ε) F : ℝ))).mp hqR
  have hdf := hdef ε hε hε0' b F
  have hc : (2 * (a - r)) * (speciesGap (modelData h ε) F : ℝ) ≤
      (4 * ε * B * (speciesGap (modelData h ε) F : ℝ)) * (speciesGap (modelData h ε) F : ℝ) := by
    change -4 * ε * B * (speciesGap (modelData h ε) F : ℝ) ^ 2 ≤
      (speciesDissipation (modelData h ε) b F).toReal - 2 * a * (speciesGap (modelData h ε) F : ℝ) at hdf
    nlinarith only [hDq, hdf]
  have hc' := (mul_le_mul_iff_left₀ hG).mp hc
  dsimp only [η]
  apply (div_le_iff₀ (by positivity : 0 < 2 * ε * B)).mpr
  nlinarith only [hc']

end DGPS.Examples.ThreeSpeciesCircle
