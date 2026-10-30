import DGPS.Examples.ThreeSpeciesCircle.InteractingCrossEntropy
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReferencePoincareGap

/-!
# Positive actual species rate at a sufficiently small h-dependent coupling

The ordinary positive rate is supplied by the actual canonical reference theorem.
The full-family exact deficit, the genuine correction bound and entropy comparison
then give a lower rate uniformly over all finite families and every actual drift provider.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The coupling threshold is chosen after h, before the family, its count or weights.
No positive species-rate, desired deficit bound or entropy comparison is a premise. -/
theorem elementaryModel_speciesRate_positive_small_coupling :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
        ∀ b : AbsoluteDrift (modelData h ε),
          ENNReal.ofReal ((ordinaryLSRate (ordinaryReference h)).toReal / 2) ≤
            speciesRate (modelData h ε) b ∧
          0 < speciesRate (modelData h ε) b := by
  obtain ⟨δ, hδ, href⟩ := threefold_reference_rate_and_strictPoincareGap
  refine ⟨δ, hδ, fun h hh hhd => ?_⟩
  obtain ⟨hfin, hαlower, _⟩ := href h hh hhd
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  have ha : 0 < a := by
    have ha0 : 0 < DGPS.Circle.AngularNormalization.a0 := by
      unfold DGPS.Circle.AngularNormalization.a0
      positivity
    have hl := ENNReal.toReal_mono hfin hαlower
    rw [ENNReal.toReal_ofReal (by positivity)] at hl
    change DGPS.Circle.AngularNormalization.a0 / 2 ≤ a at hl
    linarith
  obtain ⟨K, hK, hC⟩ := elementaryC_family_entropy_bound hh a
  obtain ⟨εG, hεG, hεGmax, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  let ε0 := min εG (a / (2 * K))
  have hε0 : 0 < ε0 := lt_min hεG (div_pos ha (by positivity))
  refine ⟨ε0, hε0, (min_le_left _ _).trans hεGmax, fun ε hε hεε0 b => ?_⟩
  have hεεG : ε < εG := hεε0.trans_le (min_le_left _ _)
  have hεmax : ε < epsMax h := hεεG.trans_le hεGmax
  have hεK : 2 * ε * K ≤ a := by
    have he : ε < a / (2 * K) := hεε0.trans_le (min_le_right _ _)
    have hm := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * K)).mp he
    nlinarith
  have hrate : ENNReal.ofReal (a / 2) ≤ speciesRate (modelData h ε) b := by
    unfold speciesRate
    refine le_iInf fun F => ?_
    let E := ∑ s, F.1.weight s * (ordinaryEntropy h (F.1.density s)).toReal
    let G : ℝ := speciesGap (modelData h ε) F.1
    let D0 := ∑ s, F.1.weight s * ((ordinaryFisher h (F.1.density s)).toReal -
      2 * a * (ordinaryEntropy h (F.1.density s)).toReal)
    obtain ⟨hD0, hJ, hDfinite, _, hD⟩ := elementaryModel_exactDeficitExpansion hh hε hεmax b F.1
    change 0 ≤ D0 at hD0
    change (speciesDissipation (modelData h ε) b F.1).toReal - 2 * a * G =
      D0 + ε * elementaryC h a (barycenter F.1) + ε ^ 2 * elementaryJ h (barycenter F.1) at hD
    have hE : 0 ≤ E := Finset.sum_nonneg fun s _ =>
      mul_nonneg (F.1.weight_nonneg s) ENNReal.toReal_nonneg
    have hG : 0 ≤ G := NNReal.coe_nonneg _
    have hEG : E ≤ 2 * G := by
      have he := (hgap ε hε hεεG F.1).1
      change (1 / 2 : ℝ) * E ≤ G at he
      linarith
    have hCLo : -K * E ≤ elementaryC h a (barycenter F.1) := by
      simpa only [neg_mul, E] using (abs_le.mp (hC F.1)).1
    have hεC := mul_le_mul_of_nonneg_left hCLo hε.le
    have hJε := mul_nonneg (sq_nonneg ε) hJ
    have hεE : ε * K * E ≤ a * G := by
      have h1 := mul_le_mul_of_nonneg_left hEG (mul_nonneg hε.le hK.le)
      have h2 := mul_le_mul_of_nonneg_right hεK hG
      nlinarith
    have hreal : a * G ≤ (speciesDissipation (modelData h ε) b F.1).toReal := by
      nlinarith
    have h2G0 : (2 * (speciesGap (modelData h ε) F.1 : ℝ≥0∞)) ≠ 0 := by
      have hpos : (0 : ℝ≥0∞) < speciesGap (modelData h ε) F.1 := by exact_mod_cast F.2
      simp [hpos.ne']
    unfold speciesQuotient
    rw [ENNReal.le_div_iff_mul_le (Or.inl h2G0)
      (Or.inl (ENNReal.mul_ne_top (by norm_num) ENNReal.coe_ne_top))]
    rw [← ENNReal.ofReal_toReal hDfinite]
    have hGco : 2 * (speciesGap (modelData h ε) F.1 : ℝ≥0∞) =
        ENNReal.ofReal (2 * G) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]
      simp
    rw [hGco, ← ENNReal.ofReal_mul (by positivity : 0 ≤ a / 2)]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  exact ⟨hrate, (ENNReal.ofReal_pos.mpr (div_pos ha (by norm_num))).trans_le hrate⟩

end DGPS.Examples.ThreeSpeciesCircle
