import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarDeficitVariation
import DGPS.Examples.ThreeSpeciesCircle.InteractingForceFeedbackVariation

/-! The explicit physical weak Euler equation for EVERY actual original-H1
scalar minimizer. Both nonlinear changing-law feedbacks and the actual mass
multiplier are derived from the model; no smoothness or Euler premise is added. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

def elementaryEulerCorrection (h ε r : ℝ) (ρ : AbsoluteDensity 1) (x : Torus 1) : ℝ :=
  2 * ε * (elementaryAK h (densityMeasure ρ) x + elementaryGeneratorFeedback h ρ x -
    r * elementaryKernelMean h (densityMeasure ρ) x) +
    ε ^ 2 * ((elementaryKprime h (densityMeasure ρ) x) ^ 2 + 2 * elementaryForceFeedback h ρ x)

def elementaryEulerMultiplier (h ε r : ℝ) (ρ : AbsoluteDensity 1) : ℝ :=
  ε * elementaryC h r ρ + 2 * ε ^ 2 * elementaryJ h ρ

theorem isSmooth_elementaryAK (h : ℝ) (ν : Measure (Torus 1)) :
    IsSmoothPeriodic (elementaryAK h ν) := by
  have hk := (isSmooth_elementaryKernelMean h ν).isSmoothPeriodic_coordPartial 0
  have hkk := hk.isSmoothPeriodic_coordPartial 0
  have hs := (isSmoothPeriodic_ellT h).isSmoothPeriodic_coordPartial 0
  exact hkk.neg.sub (hs.mul hk)

theorem isSmooth_elementaryEulerCorrection (h ε r : ℝ) (ρ : AbsoluteDensity 1) :
    IsSmoothPeriodic (elementaryEulerCorrection h ε r ρ) := by
  have hA := isSmooth_elementaryAK h (densityMeasure ρ)
  have hL := isSmooth_elementaryGeneratorFeedback h ρ
  have hK := isSmooth_elementaryKernelMean h (densityMeasure ρ)
  have hκ := hK.isSmoothPeriodic_coordPartial 0
  have hP := isSmooth_elementaryForceFeedback h ρ
  have hC : IsSmoothPeriodic (fun x => elementaryAK h (densityMeasure ρ) x +
      elementaryGeneratorFeedback h ρ x - r * elementaryKernelMean h (densityMeasure ρ) x) :=
    (hA.add hL).sub (contDiff_const.mul hK)
  have hJ : IsSmoothPeriodic (fun x => (elementaryKprime h (densityMeasure ρ) x) ^ 2 +
      2 * elementaryForceFeedback h ρ x) := hκ.pow 2 |>.add (contDiff_const.mul hP)
  exact (contDiff_const.mul hC).add (contDiff_const.mul hJ)

/-- The genuine full-original-H1 weak equation. Its force correction includes
both changing-law feedbacks; its multiplier uses the independently proved
actual deficit-zero identity. No positive or smooth stored-root input. -/
theorem elementaryModel_scalarMinimizer_weakEuler {h : ℝ} (hh : 0 < h) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧
      ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
        ∀ ρ : AbsoluteDensity 1, 0 < scalarGap (modelData h ε) ρ →
          scalarQuotient (modelData h ε) b ρ = scalarRate (modelData h ε) b →
          ∀ (φ : Torus 1 → ℝ) (G : Torus 1 → Tangent 1) (hφ : IsWeakGradient φ G),
            let r := (scalarRate (modelData h ε) b).toReal
            (∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * logScore h x) *
                (2 * G x 0 - φ x * logScore h x) ∂haar 1) +
              (∫ x, ρ.sqrt x * φ x * elementaryEulerCorrection h ε r ρ x ∂haar 1) =
                2 * r * (∫ x, ρ.sqrt x * φ x *
                  (Real.log (ρ.sqrt x ^ 2) - Real.log (referenceDensity h x)) ∂haar 1) +
                elementaryEulerMultiplier h ε r ρ * (∫ x, ρ.sqrt x * φ x ∂haar 1) := by
  obtain ⟨εD, hεD, hεDmax, hdef⟩ := elementaryModel_scalarMinimizer_deficit_hasDerivAt_zero hh
  obtain ⟨εG, hεG, _, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  refine ⟨min εD εG, lt_min hεD hεG, (min_le_left _ _).trans hεDmax,
    fun ε hε hεsmall b ρ hGP hmin φ G hφ => ?_⟩
  have heD : ε < εD := hεsmall.trans_le (min_le_left _ _)
  have heG : ε < εG := hεsmall.trans_le (min_le_right _ _)
  have heMax : ε < epsMax h := heD.trans_le hεDmax
  have hHpos : 0 < ordinaryEntropy h ρ := by
    by_contra hn
    have hz : ordinaryEntropy h ρ = 0 := le_antisymm (not_lt.mp hn) zero_le
    have hg := (hgap ε hε heG (SpeciesFamily.single ρ)).2
    have hu : (scalarGap (modelData h ε) ρ : ℝ) ≤ 0 := by
      simpa only [speciesGap_single, sum_single_count, SpeciesFamily.single_weight,
        SpeciesFamily.single_density, one_mul, hz, ENNReal.toReal_zero, mul_zero] using hg
    have hp : (0 : ℝ) < scalarGap (modelData h ε) ρ := hGP
    linarith
  let r := (scalarRate (modelData h ε) b).toReal
  let m := ∫ x, ρ.sqrt x * φ x ∂haar 1
  let I := (ordinaryFisher h ρ).toReal
  let H := (ordinaryEntropy h ρ).toReal
  let C := elementaryC h r ρ
  let J := elementaryJ h ρ
  let FC := fun x => elementaryAK h (densityMeasure ρ) x + elementaryGeneratorFeedback h ρ x -
    r * elementaryKernelMean h (densityMeasure ρ) x
  let FJ := fun x => (elementaryKprime h (densityMeasure ρ) x) ^ 2 + 2 * elementaryForceFeedback h ρ x
  let PC := ∫ x, ρ.sqrt x * φ x * FC x ∂haar 1
  let PJ := ∫ x, ρ.sqrt x * φ x * FJ x ∂haar 1
  let A := ∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * logScore h x) *
    (2 * G x 0 - φ x * logScore h x) ∂haar 1
  let R := ∫ x, ρ.sqrt x * φ x *
    (Real.log (ρ.sqrt x ^ 2) - Real.log (referenceDensity h x)) ∂haar 1
  have hFC : Continuous FC :=
    ((continuous_elementaryAK h (densityMeasure ρ)).add
      (isSmooth_elementaryGeneratorFeedback h ρ).continuous_torus).sub
        ((isSmooth_elementaryKernelMean h (densityMeasure ρ)).continuous_torus.const_mul r)
  have hFJ : Continuous FJ :=
    (((isSmooth_elementaryKernelMean h (densityMeasure ρ)).continuous_coordPartial 0).pow 2).add
      ((isSmooth_elementaryForceFeedback h ρ).continuous_torus.const_mul 2)
  have hiPC := absoluteRootMixedMoment_integrable ρ hφ hFC
  have hiPJ := absoluteRootMixedMoment_integrable ρ hφ hFJ
  have hFCmean : (∫ x, FC x ∂(densityMeasure ρ : Measure (Torus 1))) = C :=
    elementaryC_feedback_mean h r ρ
  have hFJmean : (∫ x, FJ x ∂(densityMeasure ρ : Measure (Torus 1))) = 3 * J :=
    elementaryJ_feedback_mean h ρ
  have hMC : absoluteRootMomentDerivative ρ φ FC = 2 * PC - 2 * m * C := by
    unfold absoluteRootMomentDerivative
    change 2 * PC - (2 * m) * (∫ x, FC x ∂(densityMeasure ρ : Measure (Torus 1))) = _
    rw [hFCmean]
  have hMJ : absoluteRootMomentDerivative ρ φ FJ = 2 * PJ - 6 * m * J := by
    unfold absoluteRootMomentDerivative
    change 2 * PJ - (2 * m) * (∫ x, FJ x ∂(densityMeasure ρ : Measure (Torus 1))) = _
    rw [hFJmean]
    ring
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  have hiLog := integrable_mul_mul_log hw hφ
  have hLc : Continuous (fun x : Torus 1 => Real.log (referenceDensity h x)) :=
    (continuous_referenceDensity h).log (fun x => (referenceDensity_pos (h := h) x).ne')
  have hiQ := integrable_mul_bdd_two hLc.aestronglyMeasurable
    (abs_log_referenceDensity_le h) ρ.memLp_sqrt hφ.memLp
  have hiM : Integrable (fun x => ρ.sqrt x * φ x) (haar 1) :=
    ρ.memLp_sqrt.integrable_mul hφ.memLp
  have hEF : (∫ x, eulF' (ρ.sqrt x) * φ x ∂haar 1) =
      2 * (∫ x, ρ.sqrt x * φ x * Real.log (ρ.sqrt x ^ 2) ∂haar 1) + 2 * m := by
    have he : (fun x => eulF' (ρ.sqrt x) * φ x) = fun x =>
        2 * (ρ.sqrt x * φ x * Real.log (ρ.sqrt x ^ 2)) + 2 * (ρ.sqrt x * φ x) := by
      funext x
      unfold eulF'
      ring
    rw [he, integral_add (hiLog.const_mul 2) (hiM.const_mul 2),
      integral_const_mul, integral_const_mul]
  have hR : R = (∫ x, ρ.sqrt x * φ x * Real.log (ρ.sqrt x ^ 2) ∂haar 1) -
      ∫ x, ρ.sqrt x * φ x * Real.log (referenceDensity h x) ∂haar 1 := by
    dsimp only [R]
    rw [← integral_sub hiLog hiQ]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  have hI := absoluteRootVariation_fisher_hasDerivAt h ρ hφ
  change HasDerivAt (fun t : ℝ => (ordinaryFisher h (absoluteRootVariation ρ hφ t)).toReal)
    (2 * A - 2 * m * I) 0 at hI
  have hHraw := absoluteRootVariation_entropy_hasDerivAt h ρ hHpos hφ
  have hH : HasDerivAt (fun t : ℝ => (ordinaryEntropy h (absoluteRootVariation ρ hφ t)).toReal)
      (2 * R - 2 * m * H) 0 := by
    convert hHraw using 1
    rw [hEF, hR]
    dsimp only [m, H]
    ring
  have hC := absoluteRootVariation_elementaryC_feedback_hasDerivAt h r ρ hφ
  change HasDerivAt (fun t : ℝ => elementaryC h r (absoluteRootVariation ρ hφ t))
    (2 * absoluteRootMomentDerivative ρ φ FC) 0 at hC
  rw [hMC] at hC
  have hJ := absoluteRootVariation_elementaryJ_feedback_hasDerivAt h ρ hφ
  change HasDerivAt (fun t : ℝ => elementaryJ h (absoluteRootVariation ρ hφ t))
    (absoluteRootMomentDerivative ρ φ FJ) 0 at hJ
  rw [hMJ] at hJ
  have hF := (((hI.sub (hH.const_mul (2 * r))).add (hC.const_mul ε)).add (hJ.const_mul (ε ^ 2)))
  let δF := (2 * A - 2 * m * I) - 2 * r * (2 * R - 2 * m * H) +
    ε * (2 * (2 * PC - 2 * m * C)) + ε ^ 2 * (2 * PJ - 6 * m * J)
  have hδF : δF = 0 := hF.unique (hdef ε hε heD b ρ hGP hmin φ G hφ)
  have hbase : I - 2 * r * H + ε * C + ε ^ 2 * J = 0 :=
    elementaryModel_scalarMinimizer_deficit_zero hh hε heMax b ρ hGP hmin
  have halg : 2 * (A + 2 * ε * PC + ε ^ 2 * PJ - 2 * r * R -
      (ε * C + 2 * ε ^ 2 * J) * m) =
      δF + 2 * m * (I - 2 * r * H + ε * C + ε ^ 2 * J) := by
    dsimp only [δF]
    ring
  rw [hδF, hbase, mul_zero, add_zero] at halg
  have hXi : (∫ x, ρ.sqrt x * φ x * elementaryEulerCorrection h ε r ρ x ∂haar 1) =
      2 * ε * PC + ε ^ 2 * PJ := by
    have he : (fun x => ρ.sqrt x * φ x * elementaryEulerCorrection h ε r ρ x) =
        fun x => (2 * ε) * (ρ.sqrt x * φ x * FC x) +
          ε ^ 2 * (ρ.sqrt x * φ x * FJ x) := by
      funext x
      dsimp only [elementaryEulerCorrection, FC, FJ]
      ring
    rw [he, integral_add (hiPC.const_mul (2 * ε)) (hiPJ.const_mul (ε ^ 2)),
      integral_const_mul, integral_const_mul]
  change A + (∫ x, ρ.sqrt x * φ x * elementaryEulerCorrection h ε r ρ x ∂haar 1) =
    2 * r * R + (ε * C + 2 * ε ^ 2 * J) * m
  rw [hXi]
  linarith

end DGPS.Examples.ThreeSpeciesCircle
