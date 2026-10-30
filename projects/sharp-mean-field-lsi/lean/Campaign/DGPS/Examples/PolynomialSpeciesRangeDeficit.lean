import DGPS.Examples.PolynomialSpeciesRangeGap

/-! The actual nonlocal deficit in independent reference coordinates. This is
needed for value Taylor estimates before selecting the actual root. The generator
and squared gradient are the true ones of the same normalized reference. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

/-- Actual independent-reference Fisher-plus-moment deficit with physical rate r. -/
def polynomialRangeDeficit (p : ℝ × ℝ) (r : ℝ) (u : PeriodicC2_STR02969) : ℝ :=
  let L := e0_STR02955 (polynomialRangeLogWeight p)
  let m := eulerMean L u (e0_STR02955 (polynomialRangeFeature p))
  let A := eulerMean L u (polynomialRangeGenerator p)
  let J := eulerMean L u (polynomialRangeGradientSq p)
  eulerFisher L u + 2 * eta * m * A + eta ^ 2 * m ^ 2 * J - 2 * r * polynomialRangeGap p u

private def valueI (x : PolynomialEulerInput) : ℝ :=
  eulerFisher (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2
private def valueM (x : PolynomialEulerInput) : ℝ :=
  eulerMean (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2 (e0_STR02955 (polynomialRangeFeature x.1))
private def valueA (x : PolynomialEulerInput) : ℝ :=
  eulerMean (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2 (polynomialRangeGenerator x.1)
private def valueJ (x : PolynomialEulerInput) : ℝ :=
  eulerMean (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2 (polynomialRangeGradientSq x.1)
private def valueG (x : PolynomialEulerInput) : ℝ := polynomialRangeGap x.1 x.2.2

private theorem density_smooth : ContDiff ℝ ∞ (fun x : PolynomialEulerInput =>
    eulerDensity (e0_STR02955 (polynomialRangeLogWeight x.1)) x.2.2) := by
  have hp : ContDiff ℝ ∞ (fun x : PolynomialEulerInput => x.1) := contDiff_fst
  have hu : ContDiff ℝ ∞ (fun x : PolynomialEulerInput => x.2.2) := contDiff_snd.comp contDiff_snd
  have hL := e0_STR02955.contDiff.comp (polynomialRange_data_smooth.1.comp hp)
  exact rho_smooth_STR02954.comp (contDiff_const.prodMk (hL.add (e0_STR02955.contDiff.comp hu)))

private theorem moments_smooth : ContDiff ℝ ∞ valueM ∧ ContDiff ℝ ∞ valueA ∧ ContDiff ℝ ∞ valueJ := by
  obtain ⟨_, _, _, hφ, hB, hj⟩ := polynomialRange_data_smooth
  have hp : ContDiff ℝ ∞ (fun x : PolynomialEulerInput => x.1) := contDiff_fst
  have hφ0 := e0_STR02955.contDiff.comp (hφ.comp hp)
  have hB0 := hB.comp hp
  have hj0 := hj.comp hp
  exact ⟨meanCLM_STR02954.contDiff.comp (hφ0.mul density_smooth),
    meanCLM_STR02954.contDiff.comp (hB0.mul density_smooth),
    meanCLM_STR02954.contDiff.comp (hj0.mul density_smooth)⟩

private theorem fisher_smooth : ContDiff ℝ ∞ valueI := by
  have hu : ContDiff ℝ ∞ (fun x : PolynomialEulerInput => e1_STR02955 x.2.2) :=
    e1_STR02955.contDiff.comp (contDiff_snd.comp contDiff_snd)
  exact contDiff_const.mul (meanCLM_STR02954.contDiff.comp ((hu.mul hu).mul density_smooth))

private def gapInput (x : PolynomialEulerInput) : (ℝ × ℝ) × PeriodicC2_STR02969 :=
  (x.1, x.2.2)
private def gapUncurried (x : (ℝ × ℝ) × PeriodicC2_STR02969) : ℝ :=
  polynomialRangeGap x.1 x.2
private theorem gapInput_smooth : ContDiff ℝ ∞ gapInput :=
  contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
private theorem gapUncurried_smooth : ContDiff ℝ ∞ gapUncurried :=
  polynomialRangeGap_smooth
private theorem valueG_eq : valueG = gapUncurried ∘ gapInput := rfl
private theorem gap_smooth : ContDiff ℝ ∞ valueG := by
  rw [valueG_eq]
  exact gapUncurried_smooth.comp gapInput_smooth

private theorem combine_smooth (I m A J r G : PolynomialEulerInput → ℝ)
    (hI : ContDiff ℝ ∞ I) (hm : ContDiff ℝ ∞ m) (hA : ContDiff ℝ ∞ A)
    (hJ : ContDiff ℝ ∞ J) (hr : ContDiff ℝ ∞ r) (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (fun x => I x + 2 * eta * m x * A x + eta ^ 2 * m x ^ 2 * J x - 2 * r x * G x) :=
  ((hI.add ((contDiff_const.mul hm).mul hA)).add
    ((contDiff_const.mul (hm.pow 2)).mul hJ)).sub ((contDiff_const.mul hr).mul hG)

private theorem value_eq : (fun x : PolynomialEulerInput => polynomialRangeDeficit x.1 x.2.1 x.2.2) =
    fun x => valueI x + 2 * eta * valueM x * valueA x + eta ^ 2 * valueM x ^ 2 * valueJ x - 2 * x.2.1 * valueG x := rfl

/-- Genuine joint value smoothness; the selected root is never differentiated. -/
theorem polynomialRangeDeficit_smooth : ContDiff ℝ ∞ (fun x : PolynomialEulerInput =>
    polynomialRangeDeficit x.1 x.2.1 x.2.2) := by
  rw [value_eq]
  exact combine_smooth valueI valueM valueA valueJ (fun x => x.2.1) valueG
    fisher_smooth moments_smooth.1 moments_smooth.2.1 moments_smooth.2.2
    (contDiff_fst.comp contDiff_snd) gap_smooth

/-- The exact zero chart has zero actual deficit for every reference and rate. -/
theorem polynomialRangeDeficit_zero (p : ℝ × ℝ) (r : ℝ) : polynomialRangeDeficit p r 0 = 0 := by
  have hρ : eulerDensity (e0_STR02955 (polynomialRangeLogWeight p)) 0 = polynomialRangeReference p := by
    simp only [eulerDensity, map_zero, add_zero, polynomialRangeReference]
  have hm : eulerMean (e0_STR02955 (polynomialRangeLogWeight p)) 0
      (e0_STR02955 (polynomialRangeFeature p)) = 0 := by
    rw [eulerMean, hρ]
    exact polynomialRangeFeature_centered p
  simp only [polynomialRangeDeficit, hm, polynomialRangeGap_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    mul_zero, zero_mul, add_zero, sub_zero]
  simp [eulerFisher, eulerMean]

/-- Exact rate dependence at a FIXED chart point. For a moving graph one must
use the actual envelope theorem; this identity does not freeze graph motion. -/
theorem polynomialRangeDeficit_rate_affine (p : ℝ × ℝ) (γ : ℝ) (u : PeriodicC2_STR02969) :
    polynomialRangeDeficit p (DGPS.Circle.AngularNormalization.a0 * (1 + γ)) u =
      polynomialRangeDeficit p DGPS.Circle.AngularNormalization.a0 u -
        2 * DGPS.Circle.AngularNormalization.a0 * γ * polynomialRangeGap p u := by
  unfold polynomialRangeDeficit
  ring

/-- Exact selected-root value restriction to the original canonical chart deficit. -/
theorem polynomialRangeDeficit_actual (h r : ℝ) (u : PeriodicC2_STR02969) :
    polynomialRangeDeficit (h, root_EX054 h) r u = polynomialChartDeficit h r u := by
  have hI : eulerFisher (e0_STR02955 (polynomialRangeLogWeight (h, root_EX054 h))) u =
      eulerFisher (polynomialLogReference h) u := by
    unfold eulerFisher eulerMean
    rw [polynomialRangeDensity_actual]
  have hm : eulerMean (e0_STR02955 (polynomialRangeLogWeight (h, root_EX054 h))) u
      (e0_STR02955 (polynomialRangeFeature (h, root_EX054 h))) =
      eulerMean (polynomialLogReference h) u (polynomialEulerFeature h) := by
    unfold eulerMean
    rw [polynomialRangeFeature_actual, polynomialRangeDensity_actual]
  have hA : eulerMean (e0_STR02955 (polynomialRangeLogWeight (h, root_EX054 h))) u
      (polynomialRangeGenerator (h, root_EX054 h)) =
      eulerMean (polynomialLogReference h) u (polynomialEulerGenerator h) := by
    unfold eulerMean
    rw [polynomialRangeGenerator_actual, polynomialRangeDensity_actual]
  have hJ : eulerMean (e0_STR02955 (polynomialRangeLogWeight (h, root_EX054 h))) u
      (polynomialRangeGradientSq (h, root_EX054 h)) =
      eulerMean (polynomialLogReference h) u (polynomialEulerGradientSq h) := by
    unfold eulerMean
    rw [polynomialRangeGradientSq_actual, polynomialRangeDensity_actual]
  change eulerFisher (e0_STR02955 (polynomialRangeLogWeight (h, root_EX054 h))) u +
      2 * eta * _ * _ + eta ^ 2 * _ ^ 2 * _ - 2 * r * polynomialRangeGap (h, root_EX054 h) u = _
  rw [hI, hm, hA, hJ, polynomialRangeGap_actual]
  rfl

end DGPS.Examples.PolynomialSpecies
