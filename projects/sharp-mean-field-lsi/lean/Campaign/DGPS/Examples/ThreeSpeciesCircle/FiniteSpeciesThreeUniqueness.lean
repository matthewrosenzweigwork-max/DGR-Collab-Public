import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesProfileComparison
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesFeedbackPairing
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesFieldMonotonicity

/-! Genuine uniqueness of matched three-branch full-family minimizers. All
relative profile errors are supplied by the actual profile comparison theorem;
the signed ordinary-root quadratic and actual feedback pairing close the proof.
This does not yet classify arbitrary families or identify cyclic branch labels. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- Two actual full-rate minimizing triples near the SAME retained root chart
have equal weights and equal corresponding laws. No lower bound on their
positive weights, desired profile bound, or field monotonicity is assumed. -/
theorem elementaryModel_three_minimizers_unique (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∀ σ : Fin 3 → AbsoluteDensity 1,
      (∀ j θ, (σ j).density (angEquiv.symm θ) =
        rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) →
      ∀ A : ℝ, 0 < A → ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 → ∀ b : AbsoluteDrift (modelData h ε),
        ∀ p q : Fin 3 → ℝ, ∀ hp : ∀ j, 0 < p j, ∀ hq : ∀ j, 0 < q j,
        ∀ hps : ∑ j, p j = 1, ∀ hqs : ∑ j, q j = 1,
        ∀ ρ ν : Fin 3 → AbsoluteDensity 1,
        let F := SpeciesFamily.ofData 3 p hp hps ρ
        let G := SpeciesFamily.ofData 3 q hq hqs ν
        0 < speciesGap (modelData h ε) F →
        speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b →
        0 < speciesGap (modelData h ε) G →
        speciesQuotient (modelData h ε) b G = speciesRate (modelData h ε) b →
        (∀ j, ordinaryRootH1Deviation (σ j) (ρ j) (σ j).sqrt ≤ A * ε) →
        (∀ j, ordinaryRootH1Deviation (σ j) (ν j) (σ j).sqrt ≤ A * ε) →
        p = q ∧ ∀ j, densityMeasure (ρ j) = densityMeasure (ν j) := by
  obtain ⟨δP, hδP, hδPr, hProfiles⟩ := elementaryModel_three_minimizers_profile_comparison D
  obtain ⟨δQ, hδQ, _, hSigned⟩ := ordinarySignedRootMoment_lower D
  obtain ⟨δT, hδT, _, hTrials⟩ := elementaryModel_speciesRate_linear_trial_margin D
  let δ := min δP (min δQ δT)
  refine ⟨δ, lt_min hδP (lt_min hδQ hδT), (min_le_left _ _).trans hδPr,
    fun h hh hhd σ hσ A hA => ?_⟩
  obtain ⟨K, εP, hK, hεP, hεPmax, hProfile⟩ :=
    hProfiles h hh (hhd.trans_le (min_le_left _ _)) σ hσ A hA
  obtain ⟨d, εT, hd, hεT, _, hTrial⟩ :=
    hTrials h hh (hhd.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  obtain ⟨M, hM, hObs⟩ := elementaryCorrection_coordinates_bound h
  obtain ⟨L, hL, hPolynomial⟩ := elementarySixCorrectionPolynomial_error (a + 1) (by dsimp [a]; positivity)
  obtain ⟨B, hB, hPair⟩ := elementaryEulerCorrection_pairing_lower h
  let T := L * (2 * M * K + K ^ 2)
  let C := 2 * T + 4 * B
  have hT : 0 < T := by dsimp only [T]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  let ε0 := min εP (min εT (min 1 (1 / (C + 1))))
  have hε0 : 0 < ε0 := lt_min hεP (lt_min hεT (lt_min one_pos (by positivity)))
  refine ⟨ε0, hε0, (min_le_left _ _).trans hεPmax,
    fun ε hε hεsmall b p q hp hq hps hqs ρ ν hF hFm hG hGm hρ hν => ?_⟩
  let F := SpeciesFamily.ofData 3 p hp hps ρ
  let G := SpeciesFamily.ofData 3 q hq hqs ν
  let r := (speciesRate (modelData h ε) b).toReal
  let S := ∑ j, |p j - q j|
  let N := ∫ x, |(barycenter F).density x - (barycenter G).density x| ∂haar 1
  let v := fun i : Fin 6 =>
    (∫ x, elementarySixObservable h i x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) -
      ∫ x, elementarySixObservable h i x ∂(densityMeasure (barycenter G) : Measure (Torus 1))
  let w := ordinarySignedRootMoment h σ (fun j => p j - q j)
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => abs_nonneg _
  have hN : 0 ≤ N := integral_nonneg fun x => abs_nonneg _
  have heP : ε < εP := hεsmall.trans_le (min_le_left _ _)
  have heT : ε < εT := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have he1 : ε ≤ 1 := (hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))).le
  have heC : ε < 1 / (C + 1) := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hCε : C * ε ≤ 1 := by
    have he := (lt_div_iff₀ (by positivity : 0 < C + 1)).1 heC
    nlinarith only [he, hε]
  have heMax : ε < epsMax h := heP.trans_le hεPmax
  obtain ⟨hN2, hBranch, hMoment⟩ := hProfile ε hε heP b p q hp hq hps hqs ρ ν
    hF hFm hG hGm hρ hν
  obtain ⟨_, hRate⟩ := hTrial ε hε heT b
  have hr : 0 ≤ r := ENNReal.toReal_nonneg
  have hra : r ≤ a := by
    change r ≤ a - d * ε at hRate
    nlinarith only [hRate, mul_pos hd hε]
  have hrR : |r| ≤ a + 1 := by rw [abs_of_nonneg hr]; linarith
  have hZero : ∑ j, (p j - q j) = 0 := by rw [Finset.sum_sub_distrib, hps, hqs]; ring
  have hQ := hSigned h hh
    (hhd.trans_le ((min_le_right _ _).trans (min_le_left _ _))) σ hσ r hr hra
    (fun j => p j - q j) hZero
  change (7 / 2 : ℝ) * S ^ 2 ≤ elementarySixCorrectionPolynomial r w at hQ
  have hw (i : Fin 6) : |w i| ≤ M * S := by
    have hi (j : Fin 3) : |∫ x, elementarySixObservable h i x
        ∂(densityMeasure (σ j) : Measure (Torus 1))| ≤ M := by
      have he := norm_integral_le_of_norm_le_const
        (μ := (densityMeasure (σ j) : Measure (Torus 1)))
        (f := elementarySixObservable h i) (C := M)
        (Filter.Eventually.of_forall fun x => by
          simpa only [Real.norm_eq_abs, elementaryCorrectionObservable] using hObs (.inl i) x)
      simpa only [Real.norm_eq_abs, Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using he
    change |∑ j, (p j - q j) * _| ≤ _
    calc _ ≤ ∑ j, |(p j - q j) * _| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, |p j - q j| * M := by
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hi j) (abs_nonneg _)
      _ = M * S := by rw [← Finset.sum_mul]; ring
  have he := hPolynomial r hrR v w (M * S) (K * ε * S) (by positivity) (by positivity) hMoment hw
  have hSquare : ε ^ 2 ≤ ε := by nlinarith [mul_nonneg hε.le (sub_nonneg.mpr he1)]
  have hError : |elementarySixCorrectionPolynomial r v - elementarySixCorrectionPolynomial r w| ≤
      T * ε * S ^ 2 := by
    apply he.trans
    have hs := mul_le_mul_of_nonneg_left hSquare (show 0 ≤ L * K ^ 2 * S ^ 2 by positivity)
    dsimp only [T]
    nlinarith only [hs]
  have hQv : (7 / 2 : ℝ) * S ^ 2 - T * ε * S ^ 2 ≤ elementarySixCorrectionPolynomial r v := by
    have he := (abs_le.mp hError).1
    linarith only [hQ, he]
  have hPairing := hPair ε r (barycenter F) (barycenter G)
  change 2 * ε * elementarySixCorrectionPolynomial r v - B * ε ^ 2 * N ^ 2 ≤ _ at hPairing
  have hNonpos := elementaryModel_minimizers_feedback_pairing_nonpos hh hε heMax b F G hF hG hFm hGm
  have hNpow : N ^ 2 ≤ 4 * S ^ 2 := by
    have he := pow_le_pow_left₀ hN hN2 2
    nlinarith only [he]
  have hNe := mul_le_mul_of_nonneg_left hNpow (show 0 ≤ B * ε ^ 2 by positivity)
  have hQe := mul_le_mul_of_nonneg_left hQv (show 0 ≤ 2 * ε by positivity)
  have hFinal : (7 - C * ε) * ε * S ^ 2 ≤ 0 := by
    dsimp only [C]
    nlinarith only [hPairing, hNonpos, hNe, hQe]
  have hCoeff : 0 < (7 - C * ε) * ε := mul_pos (by linarith only [hCε]) hε
  have hSzero : S = 0 := by
    have hs : S ^ 2 ≤ 0 := by nlinarith only [hFinal, hCoeff, sq_nonneg S]
    nlinarith only [hs, hS]
  have hpq : p = q := by
    funext j
    have hj : |p j - q j| ≤ S :=
      Finset.single_le_sum (fun k _ => abs_nonneg (p k - q k)) (Finset.mem_univ j)
    rw [hSzero] at hj
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hj)
  refine ⟨hpq, fun j => ?_⟩
  have hIj : (∫ x, |(ρ j).density x - (ν j).density x| ∂haar 1) = 0 := by
    have he := hBranch j
    change (∫ x, |(ρ j).density x - (ν j).density x| ∂haar 1) ≤ K * ε * S at he
    rw [hSzero, mul_zero] at he
    exact le_antisymm he (integral_nonneg fun x => abs_nonneg _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => abs_nonneg ((ρ j).density x - (ν j).density x))
    ((ρ j).integrable_density.sub (ν j).integrable_density).abs).1 hIj
  apply Subtype.ext
  apply withDensity_congr_ae
  filter_upwards [hae] with x hx
  have he : (ρ j).density x = (ν j).density x := sub_eq_zero.mp (abs_eq_zero.mp hx)
  exact congrArg ENNReal.ofReal he

end DGPS.Examples.ThreeSpeciesCircle
