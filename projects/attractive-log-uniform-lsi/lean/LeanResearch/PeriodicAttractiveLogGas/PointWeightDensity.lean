import LeanResearch.PeriodicAttractiveLogGas.SingularRectangleMoments
import LeanResearch.PeriodicAttractiveLogGas.DensityEntropy

/-! Normalization of the singular product under a bounded exponential factor.
This is the normalization algebra in source Lemma 3.3. The geometric Green
decomposition and its perturbation bound must be supplied by the cell proof. -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.PointWeightDensity

open SingularRectangleMoments

variable {ι : Type*} [Fintype ι]

def perturbedWeight (Y : ι → PlanarSpace) (w : ι → ℝ) (H : PlanarSpace → ℝ)
    (Z : PlanarSpace) : ℝ := Real.exp (H Z) * poleProduct Y w Z

def normalizedDensity (μ : Measure PlanarSpace) (G : PlanarSpace → ℝ)
    (Z : PlanarSpace) : ℝ := G Z / ∫ W, G W ∂μ

theorem measurable_perturbedWeight (Y : ι → PlanarSpace) (w : ι → ℝ)
    {H : PlanarSpace → ℝ} (hH : Measurable H) : Measurable (perturbedWeight Y w H) :=
  (Real.continuous_exp.measurable.comp hH).mul (measurable_poleProduct Y w)

theorem perturbedWeight_nonneg (Y : ι → PlanarSpace) (w : ι → ℝ) (H : PlanarSpace → ℝ)
    (Z : PlanarSpace) : 0 ≤ perturbedWeight Y w H Z :=
  mul_nonneg (Real.exp_pos _).le (poleProduct_nonneg Y w Z)

/-- Both real norms below have actual finite extended norms. -/
theorem poleProduct_memLp_four {μ : Measure PlanarSpace} [IsProbabilityMeasure μ]
    (hμ : μ ≤ volume) (Y : ι → PlanarSpace) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hκ : ∑ i, w i ≤ 1 / 4) :
    MemLp (poleProduct Y w) 4 μ ∧
      lpNorm (poleProduct Y w) 4 μ ≤ (1 + 2 * Real.pi) ^ (1 / 4 : ℝ) := by
  have hm := measurable_poleProduct Y w
  have h := poleProduct_fourth_moment hμ Y w hw hκ
  have he : (fun Z ↦ ‖poleProduct Y w Z‖ ^ (4 : ℝ)) =
      (fun Z ↦ |poleProduct Y w Z| ^ (4 : ℕ)) := by
    ext Z
    rw [Real.norm_eq_abs]
    exact Real.rpow_natCast _ 4
  have hmem : MemLp (poleProduct Y w) 4 μ := by
    apply (integrable_norm_rpow_iff hm.aestronglyMeasurable (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ ∞)).mp
    norm_num only [ENNReal.toReal_ofNat]
    rw [he]
    exact h.1
  refine ⟨hmem, ?_⟩
  rw [show (4 : ℝ≥0∞) = ENNReal.ofReal (4 : ℝ) by norm_num,
    DensityMoments.lpNorm_ofReal_eq (by norm_num : (0 : ℝ) < 4) hm.aestronglyMeasurable, he]
  exact Real.rpow_le_rpow (integral_nonneg fun Z ↦ pow_nonneg (abs_nonneg _) 4)
    h.2 (by norm_num)

/-- Bounds before normalization, derived from actual first/fourth moments. -/
theorem weight_bounds {μ : Measure PlanarSpace} [IsProbabilityMeasure μ]
    (hμ : μ ≤ volume) (Y : ι → PlanarSpace) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hκ : ∑ i, w i ≤ 1 / 4)
    {H : PlanarSpace → ℝ} (hHm : Measurable H) {A D : ℝ}
    (hH : ∀ᵐ Z ∂μ, |H Z| ≤ A) (hD : 1 ≤ D)
    (hd : ∀ᵐ Z ∂μ, ∀ i, ‖Z - Y i‖ ≤ D) :
    MemLp (perturbedWeight Y w H) 4 μ ∧
      (∀ᵐ Z ∂μ, Real.exp (-A) * D ^ (-(1 / 4 : ℝ)) ≤ perturbedWeight Y w H Z) ∧
      Real.exp (-A) * D ^ (-(1 / 4 : ℝ)) ≤ ∫ Z, perturbedWeight Y w H Z ∂μ ∧
      (∫ Z, perturbedWeight Y w H Z ∂μ) ≤ Real.exp A * (1 + 8 * Real.pi / 7) ∧
      lpNorm (perturbedWeight Y w H) 4 μ ≤ Real.exp A * (1 + 2 * Real.pi) ^ (1 / 4 : ℝ) := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hP := poleProduct_memLp_four hμ Y w hw hκ
  have hg := measurable_perturbedWeight Y w hHm
  have hupper : ∀ᵐ Z ∂μ, perturbedWeight Y w H Z ≤ Real.exp A * poleProduct Y w Z := by
    filter_upwards [hH] with Z hZ
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (le_trans (le_abs_self _) hZ))
      (poleProduct_nonneg Y w Z)
  have hnorm : ∀ᵐ Z ∂μ, ‖perturbedWeight Y w H Z‖ ≤ Real.exp A * poleProduct Y w Z := by
    filter_upwards [hupper] with Z hZ
    simpa only [Real.norm_of_nonneg (perturbedWeight_nonneg Y w H Z)] using hZ
  have hmem : MemLp (perturbedWeight Y w H) 4 μ :=
    (hP.1.const_mul (Real.exp A)).mono' hg.aestronglyMeasurable hnorm
  have hloP := ae_poleProduct_lower hμ.absolutelyContinuous Y w hw hD0 hd
  have hlo : ∀ᵐ Z ∂μ, Real.exp (-A) * D ^ (-(1 / 4 : ℝ)) ≤ perturbedWeight Y w H Z := by
    filter_upwards [hH, hloP] with Z hZ hPZ
    have hpow : D ^ (-(1 / 4 : ℝ)) ≤ poleProduct Y w Z :=
      (Real.rpow_le_rpow_of_exponent_le hD (by linarith)).trans hPZ
    have hexp : Real.exp (-A) ≤ Real.exp (H Z) := Real.exp_le_exp.mpr (abs_le.mp hZ).1
    exact mul_le_mul hexp hpow (Real.rpow_nonneg hD0.le _) (Real.exp_pos _).le
  have hi := hmem.integrable (by norm_num)
  have hmasslow := integral_mono_ae (integrable_const _) hi hlo
  simp only [integral_const, probReal_univ, one_smul] at hmasslow
  have hmassup : (∫ Z, perturbedWeight Y w H Z ∂μ) ≤ Real.exp A * (1 + 8 * Real.pi / 7) := by
    calc
      _ ≤ ∫ Z, Real.exp A * poleProduct Y w Z ∂μ :=
        integral_mono_ae hi ((poleProduct_first_moment hμ Y w hw hκ).1.const_mul _) hupper
      _ = Real.exp A * ∫ Z, poleProduct Y w Z ∂μ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (poleProduct_first_moment hμ Y w hw hκ).2
        (Real.exp_pos _).le
  refine ⟨hmem, hlo, hmasslow, hmassup, ?_⟩
  have hn : lpNorm (perturbedWeight Y w H) 4 μ ≤
      lpNorm (fun Z ↦ Real.exp A * poleProduct Y w Z) 4 μ :=
    ENNReal.toReal_mono (hP.1.const_mul (Real.exp A)).eLpNorm_ne_top
      (eLpNorm_mono_ae_real hg.aestronglyMeasurable hnorm)
  rw [DensityEntropy.lpNorm_const_mul, abs_of_pos (Real.exp_pos A)] at hn
  exact hn.trans (mul_le_mul_of_nonneg_left hP.2 (Real.exp_pos _).le)

theorem normalizedDensity_probability {μ : Measure PlanarSpace} {G : PlanarSpace → ℝ}
    (hG : Integrable G μ) (hG0 : ∀ Z, 0 ≤ G Z) (hZ : 0 < ∫ Z, G Z ∂μ) :
    IsProbabilityMeasure (μ.withDensity (fun Z ↦ ENNReal.ofReal (normalizedDensity μ G Z))) := by
  have hi : Integrable (normalizedDensity μ G) μ := hG.div_const _
  have hn : ∀ Z, 0 ≤ normalizedDensity μ G Z := fun Z ↦ div_nonneg (hG0 Z) hZ.le
  have hm : (∫ Z, normalizedDensity μ G Z ∂μ) = 1 := by
    unfold normalizedDensity
    rw [integral_div]
    exact div_self hZ.ne'
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall hn), hm, ENNReal.ofReal_one]

/-- The normalization uses the actual mass and gives the source's explicit constants. -/
theorem normalized_bounds {μ : Measure PlanarSpace} [IsProbabilityMeasure μ]
    (hμ : μ ≤ volume) (Y : ι → PlanarSpace) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hκ : ∑ i, w i ≤ 1 / 4)
    {H : PlanarSpace → ℝ} (hHm : Measurable H) {A D : ℝ}
    (hH : ∀ᵐ Z ∂μ, |H Z| ≤ A) (hD : 1 ≤ D)
    (hd : ∀ᵐ Z ∂μ, ∀ i, ‖Z - Y i‖ ≤ D) :
    0 < (∫ Z, perturbedWeight Y w H Z ∂μ) ∧
      IsProbabilityMeasure (μ.withDensity (fun Z ↦
        ENNReal.ofReal (normalizedDensity μ (perturbedWeight Y w H) Z))) ∧
      MemLp (normalizedDensity μ (perturbedWeight Y w H)) 4 μ ∧
      (∀ᵐ Z ∂μ, Real.exp (-2 * A) * D ^ (-(1 / 4 : ℝ)) /
        (1 + 8 * Real.pi / 7) ≤ normalizedDensity μ (perturbedWeight Y w H) Z) ∧
      lpNorm (normalizedDensity μ (perturbedWeight Y w H)) 4 μ ≤
        Real.exp (2 * A) * D ^ (1 / 4 : ℝ) * (1 + 2 * Real.pi) ^ (1 / 4 : ℝ) := by
  have hD0 : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hM : 0 < 1 + 8 * Real.pi / 7 := by positivity
  obtain ⟨hg, hlo, hml, hmu, hnorm⟩ := weight_bounds hμ Y w hw hκ hHm hH hD hd
  have hB : 0 < Real.exp (-A) * D ^ (-(1 / 4 : ℝ)) :=
    mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos hD0 _)
  have hZ : 0 < ∫ Z, perturbedWeight Y w H Z ∂μ := hB.trans_le hml
  have hn : normalizedDensity μ (perturbedWeight Y w H) =
      (fun Z ↦ (∫ W, perturbedWeight Y w H W ∂μ)⁻¹ * perturbedWeight Y w H Z) := by
    ext Z
    simp only [normalizedDensity, div_eq_mul_inv, mul_comm]
  refine ⟨hZ, normalizedDensity_probability (hg.integrable (by norm_num))
    (perturbedWeight_nonneg Y w H) hZ, ?_, ?_, ?_⟩
  · rw [hn]
    exact hg.const_mul _
  · have hc : 0 ≤ Real.exp (-2 * A) * D ^ (-(1 / 4 : ℝ)) /
        (1 + 8 * Real.pi / 7) := by positivity
    have heq : (Real.exp (-2 * A) * D ^ (-(1 / 4 : ℝ)) /
        (1 + 8 * Real.pi / 7)) * (Real.exp A * (1 + 8 * Real.pi / 7)) =
        Real.exp (-A) * D ^ (-(1 / 4 : ℝ)) := by
      calc
        _ = (Real.exp (-2 * A) * Real.exp A) * D ^ (-(1 / 4 : ℝ)) *
            ((1 + 8 * Real.pi / 7)⁻¹ * (1 + 8 * Real.pi / 7)) := by ring
        _ = Real.exp (-A) * D ^ (-(1 / 4 : ℝ)) := by
          rw [inv_mul_cancel₀ hM.ne', mul_one, ← Real.exp_add]
          congr 2; ring
    filter_upwards [hlo] with Z hlow
    apply (le_div_iff₀ hZ).mpr
    exact (mul_le_mul_of_nonneg_left hmu hc).trans (heq.le.trans hlow)
  · rw [hn, DensityEntropy.lpNorm_const_mul, abs_of_pos (inv_pos.mpr hZ)]
    have hi : (∫ Z, perturbedWeight Y w H Z ∂μ)⁻¹ ≤
        (Real.exp (-A) * D ^ (-(1 / 4 : ℝ)))⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hB hml
    have he : (Real.exp (-A))⁻¹ * Real.exp A = Real.exp (2 * A) := by
      rw [Real.exp_neg, inv_inv, ← Real.exp_add]
      congr 1; ring
    calc
      _ ≤ (∫ Z, perturbedWeight Y w H Z ∂μ)⁻¹ *
          (Real.exp A * (1 + 2 * Real.pi) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hZ.le)
      _ ≤ (Real.exp (-A) * D ^ (-(1 / 4 : ℝ)))⁻¹ *
          (Real.exp A * (1 + 2 * Real.pi) ^ (1 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hi (by positivity)
      _ = Real.exp (2 * A) * D ^ (1 / 4 : ℝ) *
          (1 + 2 * Real.pi) ^ (1 / 4 : ℝ) := by
        rw [mul_inv_rev, Real.rpow_neg hD0.le, inv_inv]
        calc
          _ = ((Real.exp (-A))⁻¹ * Real.exp A) * D ^ (1 / 4 : ℝ) *
              (1 + 2 * Real.pi) ^ (1 / 4 : ℝ) := by ring
          _ = _ := by rw [he]

def sourceLowerConstant (D ω C₀ : ℝ) : ℝ :=
  Real.exp (-2 * ω - C₀ / 2) * D ^ (-(1 / 4 : ℝ)) / (1 + 8 * Real.pi / 7)

def sourceNormConstant (D ω C₀ : ℝ) : ℝ :=
  Real.exp (2 * ω + C₀ / 2) * D ^ (1 / 4 : ℝ) * (1 + 2 * Real.pi) ^ (1 / 4 : ℝ)

/-- The two constants in source Lemma 3.3, after the geometric perturbation is bounded. -/
theorem source_normalized_bounds {μ : Measure PlanarSpace} [IsProbabilityMeasure μ]
    (hμ : μ ≤ volume) (Y : ι → PlanarSpace) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hκ : ∑ i, w i ≤ 1 / 4)
    {H : PlanarSpace → ℝ} (hHm : Measurable H) {ω C₀ D : ℝ} (hC₀ : 0 ≤ C₀)
    (hH : ∀ᵐ Z ∂μ, |H Z| ≤ ω + (∑ i, w i) * C₀) (hD : 1 ≤ D)
    (hd : ∀ᵐ Z ∂μ, ∀ i, ‖Z - Y i‖ ≤ D) :
    0 < (∫ Z, perturbedWeight Y w H Z ∂μ) ∧
      IsProbabilityMeasure (μ.withDensity (fun Z ↦
        ENNReal.ofReal (normalizedDensity μ (perturbedWeight Y w H) Z))) ∧
      MemLp (normalizedDensity μ (perturbedWeight Y w H)) 4 μ ∧
      (∀ᵐ Z ∂μ, sourceLowerConstant D ω C₀ ≤
        normalizedDensity μ (perturbedWeight Y w H) Z) ∧
      lpNorm (normalizedDensity μ (perturbedWeight Y w H)) 4 μ ≤
        sourceNormConstant D ω C₀ := by
  have hH' : ∀ᵐ Z ∂μ, |H Z| ≤ ω + C₀ / 4 := by
    filter_upwards [hH] with Z hZ
    have hmul := mul_le_mul_of_nonneg_right hκ hC₀
    linarith
  have h := normalized_bounds hμ Y w hw hκ hHm hH' hD hd
  simpa only [sourceLowerConstant, sourceNormConstant,
    show -2 * (ω + C₀ / 4) = -2 * ω - C₀ / 2 by ring,
    show 2 * (ω + C₀ / 4) = 2 * ω + C₀ / 2 by ring] using h

/-- Constant factors such as the source's `J^κ` cancel in the actual density. -/
theorem normalizedDensity_const_mul (μ : Measure PlanarSpace) (G : PlanarSpace → ℝ)
    {c : ℝ} (hc : c ≠ 0) :
    normalizedDensity μ (fun Z ↦ c * G Z) = normalizedDensity μ G := by
  ext Z
  simp only [normalizedDensity, integral_const_mul, mul_div_mul_left _ _ hc]

/-- Changing a weight on a null set preserves its actual normalized density a.e. -/
theorem normalizedDensity_congr_ae {μ : Measure PlanarSpace} {G F : PlanarSpace → ℝ}
    (h : G =ᵐ[μ] F) : normalizedDensity μ G =ᵐ[μ] normalizedDensity μ F := by
  have hi := integral_congr_ae h
  filter_upwards [h] with Z hZ
  simp only [normalizedDensity, hZ, hi]

end PeriodicAttractiveLogGas.PointWeightDensity
