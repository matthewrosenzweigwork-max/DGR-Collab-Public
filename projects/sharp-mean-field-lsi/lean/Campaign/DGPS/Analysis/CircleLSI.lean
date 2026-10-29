import DGPS.Circle.QuantitativeLSI
import DGPS.Analysis.LSITensorization
import DGPS.Analysis.CircleMoments

/-!
# Sharp Haar circle LSI and normalization (DEF024)

With `a0 = 4π²` and the Haar probability `m` on the unit torus:

* `DGPS.haar_circle_lsi`: for every absolute-admissible `ρ` on the circle,
  `I(ρ) = 4 ∫ |(√ρ)'|² ≥ 2 a0 H(ρ|m)` (entropies and gradients finite; from FOU016).
* `DGPS.haar_torus_lsi`: `HaarLSI d a0` for every `d` (the normalized LSI of rate `a0` for all
  `H¹` functions `f` on `𝕋^d`, nonnormalized `f` and zero entropy included). The circle case is
  the legacy sharp LSI imported in place; the case of general `d` is the tensorization FOU014.
* `DGPS.haar_lsi_sharp`: no rate `a > a0` is admissible (first-harmonic test `1 + t cos 2πx`,
  H1044), hence the optimal rate `haarLSIRate d` equals `a0` for every `d ≥ 1`, and also on the
  absolute domain.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS

/-- The circle entropy `H(ρ|m)` of an absolute-admissible density as a real number equals the
real part of the relative entropy of the associated probability measure. -/
theorem circleEntropy_eq_relativeEntropy (ρ : AbsoluteDensity 1) :
    Analysis.circleEntropy ρ = (relativeEntropy (densityMeasure ρ) (haar 1)).toReal := by
  have h1 : relativeEntropy (densityMeasure ρ) (haar 1) = homogeneousEntropy (haar 1) ρ.density :=
    relativeEntropy_withDensity (Filter.Eventually.of_forall ρ.density_nonneg)
      ρ.integrable_density.aestronglyMeasurable.aemeasurable
  rw [h1]
  rfl

/-- **Sharp Haar circle LSI** (DEF024): `I(ρ) = 4 ∫ |(√ρ)'|² ≥ 2 a0 H(ρ|m)` with `a0 = 4π²`,
on the whole absolute domain; entropy and gradient energy are finite. -/
theorem haar_circle_lsi (ρ : AbsoluteDensity 1) :
    homogeneousEntropy (haar 1) ρ.density ≠ ⊤ ∧
    Integrable (fun x => ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2) (haar 1) ∧
    2 * (4 * Real.pi ^ 2) * Analysis.circleEntropy ρ ≤ Analysis.circleFisherInformation ρ := by
  obtain ⟨hH, hint, hq, -⟩ := Analysis.circle_quantitative_lsi_on_the_absolute_domain ρ
  refine ⟨hH, hint, ?_⟩
  have h0 : 0 ≤ (4 * Real.pi ^ 2) / 6 * Analysis.circleEntropy ρ ^ 2 := by positivity
  linarith

/-- The sharp circle LSI in the `HaarLSI` form, for all `H¹` functions on `𝕋¹` (legacy sharp LSI
`SharpLSI.lsi_torus_H1`, imported in place). -/
theorem haarLSI_one_a0 : Analysis.HaarLSI 1 (4 * Real.pi ^ 2) := by
  intro f g h
  obtain ⟨hH, hae⟩ := Analysis.legacy_memH1 h
  have hi : Integrable (fun x => f x ^ 2) (haar 1) := h.memLp.integrable_sq
  rw [DGPS.FiniteN.Tools.Rothaus.homogeneousEntropy_eq_ent hi]
  have := SharpLSI.lsi_torus_H1 hH
  have ha : SharpLSI.aCos = 4 * Real.pi ^ 2 := rfl
  rw [ha] at this
  refine this.trans (le_of_eq ?_)
  unfold SharpLSI.dirichlet
  congr 1
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with x hx
  rw [hx, ← Analysis.norm_sq_eq_sqNorm]

/-- **Haar LSI on every torus** (DEF024): the rate `a0 = 4π²` holds on `𝕋^d` for every `d`,
by tensorization (FOU014) of the circle inequality. -/
theorem haar_torus_lsi (d : ℕ) : Analysis.HaarLSI d (4 * Real.pi ^ 2) :=
  Analysis.tensorization_of_normalized_lsi (by positivity) haarLSI_one_a0 d

/-- Sharpness on the circle: no rate `a > a0` is admissible. -/
theorem not_haarLSI_one_of_gt {a : ℝ} (ha : 4 * Real.pi ^ 2 < a) : ¬ Analysis.HaarLSI 1 a := by
  intro H
  have hapos : 0 < a := lt_trans (by positivity) ha
  obtain ⟨-, C, -, -, hlim⟩ := Analysis.CircleMoments.circle_first_harmonic_estimates
  open Analysis.CircleMoments in
  have key : ∀ t : ℝ, ∀ ht : |t| < 1, t ≠ 0 → |t| ≤ 1 / 2 →
      0 < firstHarmonicEntropy t ∧ 2 * a * firstHarmonicEntropy t ≤ firstHarmonicFisher t := by
    intro t ht ht0 hle
    obtain ⟨hp, hne, -⟩ := entropy_bounds hle ht0 ht
    have hEpos : 0 < firstHarmonicEntropy t := by
      rw [firstHarmonicEntropy_of_lt ht]
      exact ENNReal.toReal_pos hp.ne' hne
    refine ⟨hEpos, ?_⟩
    set ρ := firstHarmonicDensity t ht with hρ
    have hsm := isSmoothPeriodic_firstSqrt ht
    have hW := isWeakGradient_smooth hsm
    have h := H (firstSqrt t) (Analysis.CircleMoments.smoothGrad (firstSqrt t)) hW
    have hgi : Integrable (fun x => ‖Analysis.CircleMoments.smoothGrad (firstSqrt t) x‖ ^ 2) (haar 1) :=
      hW.memLp_grad.norm.integrable_sq
    have hR : ∫⁻ x, ENNReal.ofReal (‖Analysis.CircleMoments.smoothGrad (firstSqrt t) x‖ ^ 2) ∂haar 1 =
        ENNReal.ofReal (∫ x, ‖Analysis.CircleMoments.smoothGrad (firstSqrt t) x‖ ^ 2 ∂haar 1) :=
      (ofReal_integral_eq_lintegral_ofReal hgi
        (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
    set J := ∫ x, ‖Analysis.CircleMoments.smoothGrad (firstSqrt t) x‖ ^ 2 ∂haar 1 with hJ
    have hJ0 : 0 ≤ J := integral_nonneg fun x => sq_nonneg _
    rw [hR, ← ENNReal.ofReal_mul (by positivity)] at h
    have hE : homogeneousEntropy (haar 1) (fun x => firstSqrt t x ^ 2) =
        relativeEntropy (densityMeasure ρ) (haar 1) :=
      (relativeEntropy_withDensity (Filter.Eventually.of_forall ρ.density_nonneg)
        ρ.integrable_density.aestronglyMeasurable.aemeasurable).symm
    rw [hE] at h
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
    rw [ENNReal.toReal_ofReal (by positivity), ← firstHarmonicEntropy_of_lt ht] at h2
    have hF : firstHarmonicFisher t = 4 * J := by
      rw [firstHarmonicFisher_of_lt ht]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [weakGradient_ae_eq hW] with x hx
      have : weakGradient ρ.sqrt ρ.sqrt_mem x = Analysis.CircleMoments.smoothGrad (firstSqrt t) x := hx
      rw [this]
    rw [hF]
    have h3 : firstHarmonicEntropy t ≤ 2 / a * J := h2
    rw [div_mul_eq_mul_div, le_div_iff₀ hapos] at h3
    nlinarith
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| < 1 / 2 ∧ t ≠ 0 := by
    have hb : Metric.ball (0 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hb, self_mem_nhdsWithin] with t ht ht0
    exact ⟨by simpa [Metric.mem_ball, Real.dist_eq] using ht, ht0⟩
  have hge : ∀ᶠ t in 𝓝[≠] (0 : ℝ), a ≤ Analysis.CircleMoments.firstHarmonicFisher t /
      (2 * Analysis.CircleMoments.firstHarmonicEntropy t) := by
    filter_upwards [hev] with t ⟨h1, h0⟩
    obtain ⟨hpos, hle⟩ := key t (by linarith [abs_nonneg t]) h0 h1.le
    rw [le_div_iff₀ (by positivity)]
    linarith
  have := ge_of_tendsto hlim hge
  exact absurd ha (not_lt.2 this)

/-- **Sharpness and normalization** (DEF024): for every `d ≥ 1` the Haar LSI holds at rate
`a0 = 4π²`, no larger rate is admissible, and the optimal rate on `𝕋^d` equals `a0`. -/
theorem haar_lsi_sharp {d : ℕ} (hd : 0 < d) :
    Analysis.HaarLSI d (4 * Real.pi ^ 2) ∧
    (∀ a : ℝ, Analysis.HaarLSI d a → a ≤ 4 * Real.pi ^ 2) ∧
    Analysis.haarLSIRate d = ENNReal.ofReal (4 * Real.pi ^ 2) := by
  have hmax : ∀ a : ℝ, Analysis.HaarLSI d a → a ≤ 4 * Real.pi ^ 2 := fun a H => by
    by_contra hlt
    replace hlt := not_le.1 hlt
    have hapos : 0 < a := lt_trans (by positivity) hlt
    exact not_haarLSI_one_of_gt hlt ((Analysis.haarLSI_iff_of_pos hd hapos).1 H)
  refine ⟨haar_torus_lsi d, hmax, ?_⟩
  unfold Analysis.haarLSIRate
  refine le_antisymm (iSup₂_le fun a ⟨_, ha⟩ => ENNReal.ofReal_le_ofReal (hmax a ha)) ?_
  exact le_iSup₂_of_le (4 * Real.pi ^ 2) ⟨by positivity, haar_torus_lsi d⟩ le_rfl

/-- Sharpness on the absolute domain: if `2 a H(ρ|m) ≤ I(ρ)` for every circle absolute-admissible
`ρ`, then `a ≤ a0`; together with `haar_circle_lsi` the optimal constant is exactly `a0`. -/
theorem haar_circle_lsi_sharp {a : ℝ}
    (h : ∀ ρ : AbsoluteDensity 1, 2 * a * Analysis.circleEntropy ρ ≤ Analysis.circleFisherInformation ρ) :
    a ≤ 4 * Real.pi ^ 2 := by
  obtain ⟨-, C, -, hest, hlim⟩ := Analysis.CircleMoments.circle_first_harmonic_estimates
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| < 1 / 2 ∧ t ≠ 0 := by
    have hb : Metric.ball (0 : ℝ) (1 / 2) ∈ 𝓝 (0 : ℝ) :=
      Metric.ball_mem_nhds _ (by norm_num)
    filter_upwards [mem_nhdsWithin_of_mem_nhds hb, self_mem_nhdsWithin] with t ht ht0
    exact ⟨by simpa [Metric.mem_ball, Real.dist_eq] using ht, ht0⟩
  have hge : ∀ᶠ t in 𝓝[≠] (0 : ℝ), a ≤ Analysis.CircleMoments.firstHarmonicFisher t /
      (2 * Analysis.CircleMoments.firstHarmonicEntropy t) := by
    filter_upwards [hev] with t ⟨h1, h0⟩
    have ht1 : |t| < 1 := by linarith
    obtain ⟨-, -, -, -, hp, hne, -, -⟩ := hest t ht1 h0 h1.le
    have hEpos : 0 < Analysis.CircleMoments.firstHarmonicEntropy t := by
      rw [Analysis.CircleMoments.firstHarmonicEntropy_of_lt ht1]
      exact ENNReal.toReal_pos hp.ne' hne
    have := h (Analysis.CircleMoments.firstHarmonicDensity t ht1)
    have hE : Analysis.circleEntropy (Analysis.CircleMoments.firstHarmonicDensity t ht1) =
        Analysis.CircleMoments.firstHarmonicEntropy t := by
      rw [circleEntropy_eq_relativeEntropy, Analysis.CircleMoments.firstHarmonicEntropy_of_lt ht1]
    have hF : Analysis.circleFisherInformation
        (Analysis.CircleMoments.firstHarmonicDensity t ht1) =
        Analysis.CircleMoments.firstHarmonicFisher t := by
      rw [Analysis.CircleMoments.firstHarmonicFisher_of_lt ht1]; rfl
    rw [hE, hF] at this
    rw [le_div_iff₀ (by positivity)]
    linarith
  exact ge_of_tendsto hlim hge

end DGPS
