import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesWeightVariation
import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesActiveLocalization
import DGPS.Examples.ThreeSpeciesCircle.InteractingFeedbackBounds

/-! The actual common feedback has nonnegative reference mean. Together with
full-family weight stationarity this supports exclusion of a reference-near
active law, without treating that law as an individual scalar minimizer. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem integral_linear3_zero (ν : ProbabilityMeasure (Torus 1))
    (a b c : ℝ) {f g k : Torus 1 → ℝ} (hf : Continuous f) (hg : Continuous g) (hk : Continuous k)
    (hfi : (∫ x, f x ∂(ν : Measure (Torus 1))) = 0)
    (hgi : (∫ x, g x ∂(ν : Measure (Torus 1))) = 0)
    (hki : (∫ x, k x ∂(ν : Measure (Torus 1))) = 0) :
    (∫ x, a * f x + b * g x + c * k x ∂(ν : Measure (Torus 1))) = 0 := by
  have hi := hf.integrable_of_hasCompactSupport (μ := (ν : Measure (Torus 1)))
    (HasCompactSupport.of_compactSpace _)
  have hj := hg.integrable_of_hasCompactSupport (μ := (ν : Measure (Torus 1)))
    (HasCompactSupport.of_compactSpace _)
  have hl := hk.integrable_of_hasCompactSupport (μ := (ν : Measure (Torus 1)))
    (HasCompactSupport.of_compactSpace _)
  have e1 := integral_add ((hi.const_mul a).add (hj.const_mul b)) (hl.const_mul c)
  have e2 := integral_add (hi.const_mul a) (hj.const_mul b)
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2]
  simp only [integral_const_mul, hfi, hgi, hki, mul_zero, add_zero]

/-- The actual reference expectation of the full changing-law feedback field is
nonnegative. The true centered generator and feature terms vanish; the remaining
term is the actual squared force times the coupling squared. -/
theorem elementaryEulerCorrection_reference_mean_nonneg {h : ℝ} (hh : 0 < h)
    (ε r : ℝ) (τ : AbsoluteDensity 1) :
    0 ≤ ∫ x, elementaryEulerCorrection h ε r τ x
      ∂(densityMeasure (ordinaryReferenceAbsolute h) : Measure (Torus 1)) := by
  let ν := densityMeasure (ordinaryReferenceAbsolute h)
  have hs (i : Fin 6) : (∫ x, elementarySixObservable h i x ∂(ν : Measure (Torus 1))) = 0 := by
    rw [show (ν : Measure (Torus 1)) = threefoldReference h from ordinaryReferenceAbsolute_measure h]
    exact elementarySixObservable_reference_zero hh i
  have hAK : (∫ x, elementaryAK h (densityMeasure τ) x ∂(ν : Measure (Torus 1))) = 0 := by
    have he : elementaryAK h (densityMeasure τ) = fun x =>
        (kAlpha * momC h (densityMeasure τ)) * elementaryFeatureGenerator h (featureC h) x +
        (kAlpha * momS h (densityMeasure τ)) * elementaryFeatureGenerator h (featureS h) x +
        (-kBeta * momB h (densityMeasure τ)) * elementaryFeatureGenerator h (featureB h) x := by
      funext x
      rw [elementaryAK_moments]
      ring
    rw [he]
    exact integral_linear3_zero ν _ _ _
      (continuous_elementaryFeatureGenerator h _ (isSmooth_featureC h))
      (continuous_elementaryFeatureGenerator h _ (isSmooth_featureS h))
      (continuous_elementaryFeatureGenerator h _ (isSmooth_featureB h)) (hs 3) (hs 4) (hs 5)
  have hlinear (a b c : ℝ) : (∫ x, a * featureC h x + b * featureS h x + c * featureB h x
      ∂(ν : Measure (Torus 1))) = 0 :=
    integral_linear3_zero ν a b c (isSmooth_featureC h).continuous_torus
      (isSmooth_featureS h).continuous_torus (isSmooth_featureB h).continuous_torus (hs 0) (hs 1) (hs 2)
  have hK : (∫ x, elementaryKernelMean h (densityMeasure τ) x ∂(ν : Measure (Torus 1))) = 0 := by
    have he : elementaryKernelMean h (densityMeasure τ) = fun x =>
        (kAlpha * momC h (densityMeasure τ)) * featureC h x +
        (kAlpha * momS h (densityMeasure τ)) * featureS h x +
        (-kBeta * momB h (densityMeasure τ)) * featureB h x := by
      funext x
      unfold elementaryKernelMean
      ring
    rw [he]
    exact hlinear _ _ _
  have hL : (∫ x, elementaryGeneratorFeedback h τ x ∂(ν : Measure (Torus 1))) = 0 := by
    have he : elementaryGeneratorFeedback h τ = fun x =>
        (kAlpha * ∫ y, elementaryFeatureGenerator h (featureC h) y ∂(densityMeasure τ : Measure (Torus 1))) * featureC h x +
        (kAlpha * ∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure τ : Measure (Torus 1))) * featureS h x +
        (-kBeta * ∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure τ : Measure (Torus 1))) * featureB h x := by
      funext x
      unfold elementaryGeneratorFeedback
      ring
    rw [he]
    exact hlinear _ _ _
  have hF : (∫ x, elementaryForceFeedback h τ x ∂(ν : Measure (Torus 1))) = 0 := by
    have he : elementaryForceFeedback h τ = fun x =>
        (kAlpha * ∫ y, elementaryKprime h (densityMeasure τ) y * coordPartial 0 (featureC h) y
          ∂(densityMeasure τ : Measure (Torus 1))) * featureC h x +
        (kAlpha * ∫ y, elementaryKprime h (densityMeasure τ) y * coordPartial 0 (featureS h) y
          ∂(densityMeasure τ : Measure (Torus 1))) * featureS h x +
        (-kBeta * ∫ y, elementaryKprime h (densityMeasure τ) y * coordPartial 0 (featureB h) y
          ∂(densityMeasure τ : Measure (Torus 1))) * featureB h x := by
      funext x
      unfold elementaryForceFeedback
      ring
    rw [he]
    exact hlinear _ _ _
  have hAi := (continuous_elementaryAK h (densityMeasure τ)).integrable_of_hasCompactSupport
    (μ := (ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hLi := (isSmooth_elementaryGeneratorFeedback h τ).continuous_torus.integrable_of_hasCompactSupport
    (μ := (ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hKi := (isSmooth_elementaryKernelMean h (densityMeasure τ)).continuous_torus.integrable_of_hasCompactSupport
    (μ := (ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hFi := (isSmooth_elementaryForceFeedback h τ).continuous_torus.integrable_of_hasCompactSupport
    (μ := (ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hκi := (((isSmooth_elementaryKernelMean h (densityMeasure τ)).continuous_coordPartial 0).pow 2).integrable_of_hasCompactSupport
    (μ := (ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  change 0 ≤ ∫ x, elementaryEulerCorrection h ε r τ x ∂(ν : Measure (Torus 1))
  unfold elementaryEulerCorrection
  have e1 := integral_add (((hAi.add hLi).sub (hKi.const_mul r)).const_mul (2 * ε))
      ((hκi.add (hFi.const_mul 2)).const_mul (ε ^ 2))
  have e2 := integral_sub (hAi.add hLi) (hKi.const_mul r)
  have e3 := integral_add hAi hLi
  have e4 := integral_add hκi (hFi.const_mul 2)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.pow_apply] at e1 e2 e3 e4
  simp only [elementaryKprime]
  rw [e1, integral_const_mul, integral_const_mul, e2, e3,
    integral_const_mul, e4, integral_const_mul, hAK, hL, hK, hF]
  simp only [add_zero, mul_zero, sub_zero, zero_add]
  exact mul_nonneg (sq_nonneg ε) (integral_nonneg fun x => sq_nonneg _)

/-- EVERY active law of an actual full-family minimizer is close to a genuine
nonreference ordinary branch. Reference exclusion is derived from the actual
common value, not imposed as an entry or positive-weight premise. -/
theorem elementaryModel_speciesRate_active_nonreference_localization (D : OrdinaryRootGraphData) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ D.radius ∧ ∀ h : ℝ, 0 < h → h < δ →
      ∃ σ : Fin 3 → AbsoluteDensity 1,
        (∀ j θ, (σ j).density (angEquiv.symm θ) =
          rhoT_STR02901 h (chartU_STR02924 D.ψ h (D.Z j h)) (angSec θ)) ∧
        ∃ K ε0 : ℝ, 0 < K ∧ 0 < ε0 ∧ ε0 ≤ epsMax h ∧
          ∀ ε : ℝ, 0 < ε → ε < ε0 →
            ∀ (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1),
              0 < speciesGap (modelData h ε) F →
              speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b →
              ∀ s : Fin F.count, ∃ j : Fin 3,
                ordinaryRootH1Deviation (σ j) (F.density s) (σ j).sqrt ≤ K * ε ∧
                  (ordinaryFisher h (F.density s)).toReal -
                    2 * (ordinaryLSRate (ordinaryReference h)).toReal *
                      (ordinaryEntropy h (F.density s)).toReal ≤ K * ε ^ 2 := by
  obtain ⟨δA, hδA, hδAr, hActive⟩ := elementaryModel_speciesRate_active_root_localization D
  obtain ⟨δT, hδT, _, hTrial⟩ := elementaryModel_speciesRate_linear_trial_margin D
  obtain ⟨δG, hδG, _, hGap⟩ := elementaryModel_speciesRate_minimizer_uniform_gap D
  let δ := min δA (min δT δG)
  refine ⟨δ, lt_min hδA (lt_min hδT hδG), (min_le_left _ _).trans hδAr,
    fun h hh hhd => ?_⟩
  obtain ⟨σ, hσ, K, εA, hK, hεA, hεAmax, hlocal⟩ :=
    hActive h hh (hhd.trans_le (min_le_left _ _))
  obtain ⟨c, εT, hc, hεT, _, hmargin⟩ :=
    hTrial h hh (hhd.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨η, εG, hη, hεG, _, hgap⟩ :=
    hGap h hh (hhd.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨L, εL, hL, hεL, _, hlower⟩ := elementaryModel_quotient_lower_ordinary_linear hh
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  have ha : 0 ≤ a := ENNReal.toReal_nonneg
  obtain ⟨B, hB, hfield⟩ := elementaryEulerCorrection_uniform_bound h (a + 1) (by positivity)
  have hr0 : |(0 : ℝ)| ≤ a + 1 := by simpa using (show 0 ≤ a + 1 by positivity)
  have hr1 : |(1 : ℝ)| ≤ a + 1 := by simpa using (show 1 ≤ a + 1 by linarith)
  have hQJ (τ : AbsoluteDensity 1) :
      |elementaryQ h (densityMeasure τ)| ≤ 2 * B ∧ elementaryJ h τ ≤ 2 * B := by
    have h01 := (hfield τ 0 hr0 1 (by norm_num) le_rfl).2
    have h11 := (hfield τ 1 hr1 1 (by norm_num) le_rfl).2
    have h0h := (hfield τ 0 hr0 (1 / 2) (by norm_num) (by norm_num)).2
    have hQi : elementaryQ h (densityMeasure τ) =
        elementaryEulerMultiplier h 1 0 τ - elementaryEulerMultiplier h 1 1 τ := by
      unfold elementaryEulerMultiplier elementaryC
      ring
    have hJi : elementaryJ h τ = elementaryEulerMultiplier h 1 0 τ -
        2 * elementaryEulerMultiplier h (1 / 2) 0 τ := by
      unfold elementaryEulerMultiplier
      ring
    constructor
    · rw [hQi]
      calc _ ≤ |elementaryEulerMultiplier h 1 0 τ| + |elementaryEulerMultiplier h 1 1 τ| := abs_sub _ _
        _ ≤ 2 * B := by nlinarith only [h01, h11]
    · rw [hJi]
      have hl := (abs_le.mp h0h).1
      have hu := (abs_le.mp h01).2
      nlinarith only [hl, hu]
  let A := 2 * B * L + 4 * B
  let T := A + 2 * B * K + 1
  have hT : 0 < T := by dsimp only [T, A]; positivity
  let ε0 := min εA (min εT (min εG (min εL (min 1 ((c * η) / T)))))
  have hε0 : 0 < ε0 := lt_min hεA
    (lt_min hεT (lt_min hεG (lt_min hεL (lt_min one_pos (div_pos (mul_pos hc hη) hT)))))
  refine ⟨σ, hσ, K, ε0, hK, hε0, (min_le_left _ _).trans hεAmax,
    fun ε hε hεsmall b F hF hmin s => ?_⟩
  have heA : ε < εA := hεsmall.trans_le (min_le_left _ _)
  have heT : ε < εT := hεsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have heG : ε < εG := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have heL : ε < εL := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have he1 : ε ≤ 1 := (hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))))).le
  have heSmall : ε < (c * η) / T := hεsmall.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))))
  have heMax : ε < epsMax h := heA.trans_le hεAmax
  obtain ⟨i, hi⟩ := hlocal ε hε heA b F hF hmin s
  by_cases hi0 : i = 0
  · exfalso
    let r := (speciesRate (modelData h ε) b).toReal
    let τ := barycenter F
    let V := elementaryEulerCorrection h ε r τ
    let G : ℝ := speciesGap (modelData h ε) F
    have hG : 0 < G := hF
    have hr := (hmargin ε hε heT b).2
    change r ≤ a - c * ε at hr
    have hra : r ≤ a := by nlinarith only [hr, mul_pos hc hε]
    have hrp : 0 ≤ r := ENNReal.toReal_nonneg
    have hrabs : |r| ≤ a + 1 := by rw [abs_of_nonneg hrp]; linarith only [hra]
    have hLin := hlower ε hε heL b F hF
    rw [hmin] at hLin
    change a - L * ε ≤ r at hLin
    have hdiff : 0 ≤ a - r := sub_nonneg.mpr hra
    have hdiffup : a - r ≤ L * ε := by linarith only [hLin]
    have hηG : η ≤ G := hgap ε hε heG b F hF hmin
    obtain ⟨hD0, hJ, _, _, hdef⟩ := elementaryModel_exactDeficitExpansion hh hε heMax b F
    have hz := elementaryModel_speciesRate_cost_eq_zero h ε b F hF hmin
    change (speciesDissipation (modelData h ε) b F).toReal - 2 * r * G = 0 at hz
    change (speciesDissipation (modelData h ε) b F).toReal - 2 * a * G = _ at hdef
    have hrG := mul_le_mul_of_nonneg_right hr (by positivity : 0 ≤ 2 * G)
    have hηG' := mul_le_mul_of_nonneg_left hηG (by positivity : 0 ≤ 2 * c * ε)
    have hJ' := mul_nonneg (sq_nonneg ε) hJ
    have hCε : ε * elementaryC h a τ ≤ -2 * c * ε * η := by
      nlinarith only [hdef, hz, hD0, hJ', hrG, hηG']
    have hQup : (a - r) * elementaryQ h (densityMeasure τ) ≤ (L * ε) * (2 * B) := by
      calc _ ≤ (a - r) * |elementaryQ h (densityMeasure τ)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hdiff
        _ ≤ (L * ε) * (2 * B) :=
          mul_le_mul hdiffup (hQJ τ).1 (abs_nonneg _) (mul_pos hL hε).le
    have hQε := mul_le_mul_of_nonneg_left hQup hε.le
    have hJε := mul_le_mul_of_nonneg_left (hQJ τ).2
      (show 0 ≤ 2 * ε ^ 2 by positivity)
    have hcId : elementaryEulerMultiplier h ε r τ = ε * elementaryC h a τ +
        ε * ((a - r) * elementaryQ h (densityMeasure τ)) + 2 * ε ^ 2 * elementaryJ h τ := by
      unfold elementaryEulerMultiplier elementaryC
      ring
    have hcUpper : elementaryEulerMultiplier h ε r τ ≤ -2 * c * η * ε + A * ε ^ 2 := by
      dsimp only [A]
      nlinarith only [hcId, hCε, hQε, hJε]
    have hdist : Real.sqrt (rootDistanceSq (F.density s) (ordinaryReferenceAbsolute h)) ≤ K * ε := by
      have hd := Real.sqrt_le_sqrt (rootDistanceSq_le_originalH1 (ordinaryReferenceAbsolute h) (F.density s))
      have hx : 0 ≤ ordinaryRootH1Deviation (ordinaryReferenceAbsolute h) (F.density s)
          (ordinaryReferenceAbsolute h).sqrt := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
      rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hx] at hd
      have hs := hi.1
      rw [hi0] at hs
      exact hd.trans hs
    have hVcont : Continuous V := (isSmooth_elementaryEulerCorrection h ε r τ).continuous_torus
    have hVbound : ∀ x, |V x| ≤ B * ε := (hfield τ r hrabs ε hε.le he1).1
    have hMoment := absolute_moment_error_le_root_distance (F.density s) (ordinaryReferenceAbsolute h)
      hVcont (mul_pos hB hε).le hVbound
    have hMoment' : |(∫ x, V x ∂(densityMeasure (F.density s) : Measure (Torus 1))) -
        ∫ x, V x ∂(densityMeasure (ordinaryReferenceAbsolute h) : Measure (Torus 1))| ≤
        (2 * B * K) * ε ^ 2 := by
      calc _ ≤ 2 * (B * ε) * Real.sqrt (rootDistanceSq (F.density s) (ordinaryReferenceAbsolute h)) := hMoment
        _ ≤ 2 * (B * ε) * (K * ε) := mul_le_mul_of_nonneg_left hdist (by positivity)
        _ = _ := by ring
    have hVref : 0 ≤ ∫ x, V x ∂(densityMeasure (ordinaryReferenceAbsolute h) : Measure (Torus 1)) :=
      elementaryEulerCorrection_reference_mean_nonneg hh ε r τ
    have hPhi : 0 ≤ (ordinaryFisher h (F.density s)).toReal -
        2 * r * (ordinaryEntropy h (F.density s)).toReal := by
      have hd := elementary_ordinary_deficit_nonneg h (F.density s)
      have he := mul_nonneg hdiff (ENNReal.toReal_nonneg (a := ordinaryEntropy h (F.density s)))
      nlinarith only [hd, he]
    have hvalue := elementaryModel_speciesRate_common_value hh hε heMax b F hF hmin s
    change (ordinaryFisher h (F.density s)).toReal - 2 * r * (ordinaryEntropy h (F.density s)).toReal +
      (∫ x, V x ∂(densityMeasure (F.density s) : Measure (Torus 1))) =
        elementaryEulerMultiplier h ε r τ at hvalue
    have hcLower : -(2 * B * K) * ε ^ 2 ≤ elementaryEulerMultiplier h ε r τ := by
      have he := (abs_le.mp hMoment').1
      linarith only [he, hVref, hPhi, hvalue]
    have hfinal : (2 * c * η) * ε ≤ ((A + 2 * B * K) * ε) * ε := by
      nlinarith only [hcUpper, hcLower]
    have hcancel := (mul_le_mul_iff_left₀ hε).1 hfinal
    have hthreshold := (lt_div_iff₀ hT).1 heSmall
    have hstrict : (A + 2 * B * K) * ε < c * η := by
      dsimp only [T] at hthreshold
      nlinarith only [hthreshold, hε]
    nlinarith only [hcancel, hstrict, mul_pos hc hη]
  · obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hi0
    exact ⟨j, hi⟩

end DGPS.Examples.ThreeSpeciesCircle
