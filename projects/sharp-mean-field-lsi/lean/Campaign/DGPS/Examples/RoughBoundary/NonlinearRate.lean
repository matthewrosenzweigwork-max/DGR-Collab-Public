import DGPS.Analysis.CircleLSI
import DGPS.Analysis.CircleMoments
import DGPS.Examples.RoughBoundary.FeatureMoments
import DGPS.Examples.RoughBoundary.NonlinearDissipation

/-!
# Exact scalar rate of the rough example (RUF033)

Source: `ROUGH_COUNTEREXAMPLE_RECONCILED_PROOF.md` sections 4.3-4.4.

For the rough product model `W_{L,ε}` (`ε ≠ 0`, `L > 0`) with the exact free-energy decomposition
(RUF027) and every weak-drift provider `b`, the scalar rate is `r_* = a0 = 4π²`:

* every positive-gap competitor has quotient `≥ a0` (infinite dissipation when `M ≠ 0`; when
  `M = 0` the quotient is `I/(2H)` and the sharp circle LSI applies, zeros included);
* the first-harmonic densities `ρ_t = 1 + t cos 2πx` have `M(ρ_t) = 0` (half-period symmetry of
  `U`), positive entropy, and quotient `→ a0` as `t → 0`.

Design choices (R5 notes).
* As in RUF032, `ε ≠ 0` and the exact decomposition `FreeEnergyDecomposition L ε` are hypotheses
  (the latter holds for every selected parameter); `L > 0` is otherwise arbitrary.
* The quotient limit is stated for the function `t ↦ scalarQuotient (ρ_t)` extended by `0` outside
  `|t| < 1`, along `𝓝[≠] 0`.
-/

open MeasureTheory Filter Set
open scoped ENNReal NNReal Real Topology

namespace DGPS.Examples.RoughBoundary.Nonlinear

open DGPS.Examples.RoughBoundary.Feature DGPS.Examples.RoughBoundary.Model
open DGPS.Examples.RoughBoundary.Spikes (pt measurable_pt integral_haar_eq)
open DGPS.Analysis.CircleMoments
open DGPS.Examples.RoughBoundary.FreeEnergy (FreeEnergyDecomposition)

/-- Half-period cancellation: `∫ U cos(2π x) dm` paired with any vector vanishes. -/
lemma integral_cosMode_mul_inner_Ufeat {L : ℝ} (hL : 0 < L) (ε : ℝ) (v : EuclideanSpace ℝ (Fin 2)) :
    ∫ y, cosMode y * inner ℝ v (Ufeat L ε y) ∂haar 1 = 0 := by
  have hc : Continuous fun y : Torus 1 => cosMode y * inner ℝ v (Ufeat L ε y) :=
    continuous_cosMode.mul (continuous_const.inner (continuous_Ufeat hL ε))
  rw [integral_haar_eq hc.aestronglyMeasurable, ← intervalIntegral.integral_of_le zero_le_one]
  have hG : ∀ s : ℝ, cosMode (pt s) * inner ℝ v (Ufeat L ε (pt s)) =
      Real.cos (2 * π * s) * inner ℝ v (Ureal L ε s) := fun s => by
    rw [Ufeat_pt hL, pt, cosMode_lift]
  simp_rw [hG]
  have hcont : Continuous fun s : ℝ => Real.cos (2 * π * s) * inner ℝ v (Ureal L ε s) :=
    (Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul
      (continuous_const.inner (continuous_Ureal L ε))
  have hhalf : ∀ s : ℝ, Real.cos (2 * π * (s + 1 / 2)) * inner ℝ v (Ureal L ε (s + 1 / 2)) =
      -(Real.cos (2 * π * s) * inner ℝ v (Ureal L ε s)) := fun s => by
    rw [(exact_shift_symmetries_and_feature_moments hL ε).1.2.1 s]
    have : 2 * π * (s + 1 / 2) = 2 * π * s + π := by ring
    rw [this, Real.cos_add_pi]
    ring
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have h2 : ∫ s in (1 / 2 : ℝ)..1, Real.cos (2 * π * s) * inner ℝ v (Ureal L ε s) =
      -∫ s in (0 : ℝ)..1 / 2, Real.cos (2 * π * s) * inner ℝ v (Ureal L ε s) := by
    have := intervalIntegral.integral_comp_add_right
      (fun s : ℝ => Real.cos (2 * π * s) * inner ℝ v (Ureal L ε s)) (a := 0) (b := 1 / 2)
      (1 / 2 : ℝ)
    simp only [zero_add] at this
    rw [show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] at this
    rw [← this]
    simp_rw [hhalf]
    rw [intervalIntegral.integral_neg]
  rw [h2]
  ring

/-- The feature mean of the first-harmonic density vanishes. -/
lemma featureMean_firstHarmonic {L : ℝ} (hL : 0 < L) (ε : ℝ) {t : ℝ} (ht : |t| < 1) :
    featureMean L ε (firstHarmonicDensity t ht) = 0 := by
  refine ext_inner_left ℝ fun v => ?_
  rw [inner_zero_right]
  unfold featureMean
  rw [← integral_inner (integrable_density_smul_Ufeat hL ε _)]
  simp_rw [inner_smul_right, firstHarmonicDensity_density ht, firstHarmonic]
  have hU : Integrable (Ufeat L ε) (haar 1) := FreeEnergy.integrable_U hL ε (haar 1)
  have hi1 : Integrable (fun y => inner ℝ v (Ufeat L ε y)) (haar 1) := hU.const_inner v
  have hi2 : Integrable (fun y => cosMode y * inner ℝ v (Ufeat L ε y)) (haar 1) :=
    (integrable_cont (continuous_cosMode.mul (continuous_const.inner (continuous_Ufeat hL ε))))
  have h0 : ∫ y, inner ℝ v (Ufeat L ε y) ∂haar 1 = 0 := by
    rw [integral_inner hU, (exact_shift_symmetries_and_feature_moments hL ε).1.2.2.1, inner_zero_right]
  have e : ∀ y, (1 + t * cosMode y) * inner ℝ v (Ufeat L ε y) =
      inner ℝ v (Ufeat L ε y) + t * (cosMode y * inner ℝ v (Ufeat L ε y)) := fun y => by ring
  simp_rw [e]
  rw [integral_add hi1 (hi2.const_mul t), integral_const_mul, h0,
    integral_cosMode_mul_inner_Ufeat hL ε v]
  ring

/-- Every positive-gap competitor has quotient at least `a0`. -/
lemma ofReal_a0_le_scalarQuotient {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    (hdec : FreeEnergyDecomposition L ε) (b : AbsoluteDrift (modelData hL ε))
    (ρ : AbsoluteDensity 1) (hG : 0 < scalarGap (modelData hL ε) ρ) :
    ENNReal.ofReal (4 * π ^ 2) ≤ scalarQuotient (modelData hL ε) b ρ := by
  obtain ⟨-, h2, h3⟩ := finite_scalar_dissipation_exactly_means_zero_feature_mean hL hε hdec b ρ
  by_cases hM : featureMean L ε ρ = 0
  · obtain ⟨hD, hgap⟩ := h2 hM
    have hne : relativeEntropy (densityMeasure ρ : Measure (Torus 1)) (haar 1) ≠ ⊤ := by
      rw [← hgap]; exact ENNReal.coe_ne_top
    have hgap' : (scalarGap (modelData hL ε) ρ : ℝ≥0∞) =
        ENNReal.ofReal (Analysis.circleEntropy ρ) := by
      rw [hgap, circleEntropy_eq_relativeEntropy, ENNReal.ofReal_toReal hne]
    have hpos : 0 < scalarGap (modelData hL ε) ρ := hG
    have hpos' : (0 : ℝ≥0∞) < (scalarGap (modelData hL ε) ρ : ℝ≥0∞) := by exact_mod_cast hpos
    have hHpos : 0 < Analysis.circleEntropy ρ := by
      rw [hgap'] at hpos'
      exact ENNReal.ofReal_pos.1 hpos'
    have hlsi := (haar_circle_lsi ρ).2.2
    unfold scalarQuotient
    have h2e : (2 : ℝ≥0∞) * ENNReal.ofReal (Analysis.circleEntropy ρ) =
        ENNReal.ofReal (2 * Analysis.circleEntropy ρ) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp
    rw [hD, hgap', h2e,
      ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hHpos)) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : 4 * ∫ x, ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar 1 =
        Analysis.circleFisherInformation ρ := rfl
    rw [this]
    nlinarith
  · rw [(h3 hM hG).1]
    exact le_top

/-- The quotient of the first-harmonic density, as a real number. -/
lemma scalarQuotient_firstHarmonic {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    (hdec : FreeEnergyDecomposition L ε) (b : AbsoluteDrift (modelData hL ε)) {t : ℝ}
    (ht : |t| < 1) (ht0 : t ≠ 0) (hle : |t| ≤ 1 / 2) :
    0 < scalarGap (modelData hL ε) (firstHarmonicDensity t ht) ∧
    scalarQuotient (modelData hL ε) b (firstHarmonicDensity t ht) =
      ENNReal.ofReal (firstHarmonicFisher t / (2 * firstHarmonicEntropy t)) := by
  set ρ := firstHarmonicDensity t ht with hρ
  obtain ⟨hpos, hne, -⟩ := entropy_bounds hle ht0 ht
  have hM := featureMean_firstHarmonic hL ε ht
  obtain ⟨-, h2, -⟩ := finite_scalar_dissipation_exactly_means_zero_feature_mean hL hε hdec b ρ
  obtain ⟨hD, hgap⟩ := h2 hM
  have hgap' : (scalarGap (modelData hL ε) ρ : ℝ≥0∞) =
      ENNReal.ofReal (firstHarmonicEntropy t) := by
    rw [hgap, firstHarmonicEntropy_of_lt ht, ENNReal.ofReal_toReal hne]
  have hH : 0 < firstHarmonicEntropy t := by
    rw [firstHarmonicEntropy_of_lt ht]
    exact ENNReal.toReal_pos hpos.ne' hne
  refine ⟨?_, ?_⟩
  · have : (0 : ℝ≥0∞) < (scalarGap (modelData hL ε) ρ : ℝ≥0∞) := by
      rw [hgap']; exact ENNReal.ofReal_pos.2 hH
    exact_mod_cast this
  · unfold scalarQuotient
    have h2e : (2 : ℝ≥0∞) * ENNReal.ofReal (firstHarmonicEntropy t) =
        ENNReal.ofReal (2 * firstHarmonicEntropy t) := by
      rw [ENNReal.ofReal_mul (by norm_num)]; simp
    rw [hD, hgap', h2e, ← ENNReal.ofReal_div_of_pos (by positivity)]
    congr 2
    rw [firstHarmonicFisher_of_lt ht]

/-- **RUF033.** For the rough product model `W_{L,ε}` (`ε ≠ 0`) with the exact free-energy
decomposition and every weak-drift provider `b`: the scalar rate is `r_* = a0 = 4π²`; the
first-harmonic densities `ρ_t = 1 + t cos 2πx`, `0 < |t| ≤ 1/2`, have `M(ρ_t) = 0` and positive
gap, and their quotient `D/(2G)` tends to `a0` as `t → 0`. -/
theorem exact_scalar_rate_of_the_rough_example {L : ℝ} (hL : 0 < L) {ε : ℝ} (hε : ε ≠ 0)
    (hdec : FreeEnergyDecomposition L ε) (b : AbsoluteDrift (modelData hL ε)) :
    scalarRate (modelData hL ε) b = ENNReal.ofReal (4 * π ^ 2) ∧
    (∀ (t : ℝ) (ht : |t| < 1), t ≠ 0 → |t| ≤ 1 / 2 →
      featureMean L ε (firstHarmonicDensity t ht) = 0 ∧
        0 < scalarGap (modelData hL ε) (firstHarmonicDensity t ht)) ∧
    Tendsto (fun t : ℝ => if ht : |t| < 1 then
        scalarQuotient (modelData hL ε) b (firstHarmonicDensity t ht) else 0)
      (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (4 * π ^ 2))) := by
  obtain ⟨-, C, -, -, hlim⟩ := circle_first_harmonic_estimates
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| < 1 / 2 ∧ t ≠ 0 := by
    have hb : Metric.ball (0 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hb, self_mem_nhdsWithin] with t ht ht0
    exact ⟨by simpa [Metric.mem_ball, Real.dist_eq] using ht, ht0⟩
  have hT : Tendsto (fun t : ℝ => if ht : |t| < 1 then
        scalarQuotient (modelData hL ε) b (firstHarmonicDensity t ht) else 0)
      (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (4 * π ^ 2))) := by
    have h1 : Tendsto (fun t : ℝ => ENNReal.ofReal (firstHarmonicFisher t /
        (2 * firstHarmonicEntropy t))) (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (4 * π ^ 2))) :=
      (ENNReal.tendsto_ofReal hlim)
    refine h1.congr' ?_
    filter_upwards [hev] with t ⟨h1, h0⟩
    have ht1 : |t| < 1 := by linarith
    simp only [ht1, ↓reduceDIte]
    rw [(scalarQuotient_firstHarmonic hL hε hdec b ht1 h0 h1.le).2]
  refine ⟨?_, fun t ht ht0 hle => ⟨featureMean_firstHarmonic hL ε ht,
    (scalarQuotient_firstHarmonic hL hε hdec b ht ht0 hle).1⟩, hT⟩
  refine le_antisymm ?_ (le_iInf fun ρ => ofReal_a0_le_scalarQuotient hL hε hdec b ρ.1 ρ.2)
  have hle : ∀ᶠ t in 𝓝[≠] (0 : ℝ), scalarRate (modelData hL ε) b ≤ if ht : |t| < 1 then
        scalarQuotient (modelData hL ε) b (firstHarmonicDensity t ht) else 0 := by
    filter_upwards [hev] with t ⟨h1, h0⟩
    have ht1 : |t| < 1 := by linarith
    simp only [ht1, ↓reduceDIte]
    exact scalarRate_le_quotient _ b _ (scalarQuotient_firstHarmonic hL hε hdec b ht1 h0 h1.le).1
  exact ge_of_tendsto hT hle

end DGPS.Examples.RoughBoundary.Nonlinear
