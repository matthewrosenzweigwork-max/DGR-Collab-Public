import DGPS.Examples.ThreeSpeciesCircle.NearestRootMomentError
import DGPS.Examples.ThreeSpeciesCircle.InteractingEntropyComparison
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootGraphData
import DGPS.Examples.ThreeSpeciesCircle.OrdinaryReferenceLocalStability
import DGPS.Examples.PositiveH1.Transfer
import DGPS.Variational.SpeciesInclusion

/-! Genuine count-two families formed from an ordinary absolute root and the
actual reference. Their exact polynomial corrections do not require smooth
competitors, positive stored roots, a lower weight bound or a synthetic carrier. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal
open DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

/-- An original two-species family, with vanishing weight on the ordinary root. -/
def ordinaryBinaryFamily (h : ℝ) (σ : AbsoluteDensity 1) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) : SpeciesFamily 1 :=
  SpeciesFamily.twoSpecies θ hθ0 hθ1 σ (ordinaryReferenceAbsolute h)

theorem ordinaryBinary_integral (h : ℝ) (σ : AbsoluteDensity 1) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (f : Torus 1 → ℝ) (hf : Continuous f) :
    (∫ x, f x ∂(densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1)) : Measure (Torus 1))) =
      θ * (∫ x, f x ∂(densityMeasure σ : Measure (Torus 1))) +
        (1 - θ) * ∫ x, f x ∂threefoldReference h := by
  rw [Structural.budget_integral_barycenter _ hf]
  change (∑ s : Fin 2, (if s.val = 0 then θ else 1 - θ) *
    ∫ x, f x ∂(densityMeasure (if s.val = 0 then σ else ordinaryReferenceAbsolute h) : Measure (Torus 1))) = _
  simp [Fin.sum_univ_two, ordinaryReferenceAbsolute_measure]

/-- All six centered feature and true-generator moments scale exactly by theta. -/
theorem ordinaryBinary_six_moments {h : ℝ} (hh : 0 < h) (σ : AbsoluteDensity 1) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (i : Fin 6) :
    (∫ x, elementarySixObservable h i x
      ∂(densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1)) : Measure (Torus 1))) =
      θ * ∫ x, elementarySixObservable h i x ∂(densityMeasure σ : Measure (Torus 1)) := by
  rw [ordinaryBinary_integral h σ θ hθ0 hθ1 _ (continuous_elementarySixObservable h i),
    elementarySixObservable_reference_zero hh i, mul_zero, add_zero]

/-- The genuine kernel quadratic is exactly of second order in the small weight. -/
theorem ordinaryBinary_Q {h : ℝ} (hh : 0 < h) (σ : AbsoluteDensity 1) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    elementaryQ h (densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1))) =
      θ ^ 2 * elementaryQ h (densityMeasure σ) := by
  have hc : momC h (densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1))) =
      θ * momC h (densityMeasure σ) := ordinaryBinary_six_moments hh σ θ hθ0 hθ1 0
  have hs : momS h (densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1))) =
      θ * momS h (densityMeasure σ) := ordinaryBinary_six_moments hh σ θ hθ0 hθ1 1
  have hb : momB h (densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1))) =
      θ * momB h (densityMeasure σ) := ordinaryBinary_six_moments hh σ θ hθ0 hθ1 2
  rw [elementaryQ_moments, elementaryQ_moments, hc, hs, hb]
  ring

/-- The genuine cross correction also has exact second order, retaining independent
feature and generator moments. -/
theorem ordinaryBinary_C {h : ℝ} (hh : 0 < h) (a : ℝ) (σ : AbsoluteDensity 1) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    elementaryC h a (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1)) =
      θ ^ 2 * elementaryC h a σ := by
  have hm := ordinaryBinary_six_moments hh σ θ hθ0 hθ1
  rw [elementaryC_moments, elementaryC_moments]
  change 2 * kAlpha *
    ((∫ x, elementarySixObservable h 0 x ∂(densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1)) : Measure (Torus 1))) *
      (∫ x, elementarySixObservable h 3 x ∂(densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1)) : Measure (Torus 1))) +
     (∫ x, elementarySixObservable h 1 x ∂(densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1)) : Measure (Torus 1))) *
      (∫ x, elementarySixObservable h 4 x ∂(densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1)) : Measure (Torus 1)))) -
    2 * kBeta * (∫ x, elementarySixObservable h 2 x ∂(densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1)) : Measure (Torus 1))) *
      (∫ x, elementarySixObservable h 5 x ∂(densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1)) : Measure (Torus 1))) -
    a * (kAlpha * ((∫ x, elementarySixObservable h 0 x ∂(densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1)) : Measure (Torus 1))) ^ 2 +
      (∫ x, elementarySixObservable h 1 x ∂(densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1)) : Measure (Torus 1))) ^ 2) -
      kBeta * (∫ x, elementarySixObservable h 2 x ∂(densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1)) : Measure (Torus 1))) ^ 2) = _
  rw [hm 0, hm 1, hm 2, hm 3, hm 4, hm 5]
  simp only [elementarySixObservable, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val, momC, momS, momB]
  ring

private theorem ordinaryBinary_Kprime {h : ℝ} (hh : 0 < h) (σ : AbsoluteDensity 1) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (x : Torus 1) :
    elementaryKprime h (densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1))) x =
      θ * elementaryKprime h (densityMeasure σ) x := by
  have hc : momC h (densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1))) =
      θ * momC h (densityMeasure σ) := ordinaryBinary_six_moments hh σ θ hθ0 hθ1 0
  have hs : momS h (densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1))) =
      θ * momS h (densityMeasure σ) := ordinaryBinary_six_moments hh σ θ hθ0 hθ1 1
  have hb : momB h (densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1))) =
      θ * momB h (densityMeasure σ) := ordinaryBinary_six_moments hh σ θ hθ0 hθ1 2
  have hU : elementaryKernelMean h (densityMeasure (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1))) =
      fun y => θ * elementaryKernelMean h (densityMeasure σ) y := by
    funext y
    unfold elementaryKernelMean
    rw [hc, hs, hb]
    ring
  unfold elementaryKprime
  rw [hU, DGPS.Examples.PositiveH1.Transfer.coordPartial_const_mul
    (isSmooth_elementaryKernelMean h (densityMeasure σ)) θ 0 x]

/-- Exact finite J polynomial. The reference integral uses the FIXED root kernel
gradient; it is not elementaryJ of the reference law. -/
theorem ordinaryBinary_J {h : ℝ} (hh : 0 < h) (σ : AbsoluteDensity 1) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    elementaryJ h (barycenter (ordinaryBinaryFamily h σ θ hθ0 hθ1)) =
      θ ^ 2 * (θ * elementaryJ h σ + (1 - θ) *
        ∫ x, (elementaryKprime h (densityMeasure σ) x) ^ 2 ∂threefoldReference h) := by
  have hc : Continuous (fun x => (elementaryKprime h (densityMeasure σ) x) ^ 2) :=
    ((isSmooth_elementaryKernelMean h (densityMeasure σ)).continuous_coordPartial 0).pow 2
  have he (τ : AbsoluteDensity 1) : elementaryJ h τ =
      ∫ x, (elementaryKprime h (densityMeasure τ) x) ^ 2 ∂(densityMeasure τ : Measure (Torus 1)) := by
    rw [Structural.budget_integral_densityMeasure]
    rfl
  rw [he]
  simp_rw [ordinaryBinary_Kprime hh σ θ hθ0 hθ1, mul_pow]
  rw [integral_const_mul, ordinaryBinary_integral h σ θ hθ0 hθ1 _ hc, ← he σ]


private theorem reference_entropy_zero (h : ℝ) : ordinaryEntropy h (ordinaryReferenceAbsolute h) = 0 := by
  unfold ordinaryEntropy
  rw [ordinaryReferenceAbsolute_measure]
  letI : IsProbabilityMeasure (threefoldReference h) := by
    change IsProbabilityMeasure (ordinaryReference h).measure
    infer_instance
  exact relativeEntropy_self _

private theorem ordinaryBinary_entropy (h : ℝ) (σ : AbsoluteDensity 1) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∑ s, (ordinaryBinaryFamily h σ θ hθ0 hθ1).weight s *
      (ordinaryEntropy h ((ordinaryBinaryFamily h σ θ hθ0 hθ1).density s)).toReal) =
        θ * (ordinaryEntropy h σ).toReal := by
  change (∑ s : Fin 2, (if s.val = 0 then θ else 1 - θ) *
    (ordinaryEntropy h (if s.val = 0 then σ else ordinaryReferenceAbsolute h)).toReal) = _
  simp [Fin.sum_univ_two, reference_entropy_zero]

private theorem ordinary_optimizer_deficit_zero (h : ℝ) (σ : AbsoluteDensity 1)
    (hH : 0 < ordinaryEntropy h σ) (hq : str025_quot h σ = ordinaryLSRate (ordinaryReference h)) :
    (ordinaryFisher h σ).toReal -
      2 * (ordinaryLSRate (ordinaryReference h)).toReal * (ordinaryEntropy h σ).toReal = 0 := by
  have hHr : 0 < (ordinaryEntropy h σ).toReal :=
    ENNReal.toReal_pos hH.ne' (str025_entropy_ne_top h σ)
  have hqr := congrArg ENNReal.toReal hq
  change (ordinaryFisher h σ / (2 * ordinaryEntropy h σ)).toReal = _ at hqr
  rw [ENNReal.toReal_div, ENNReal.toReal_mul] at hqr
  norm_num only [ENNReal.toReal_ofNat] at hqr
  have he := (div_eq_iff (by positivity : (2 : ℝ) * (ordinaryEntropy h σ).toReal ≠ 0)).mp hqr
  nlinarith

private theorem ordinaryBinary_D0_zero (h : ℝ) (σ : AbsoluteDensity 1)
    (hH : 0 < ordinaryEntropy h σ) (hq : str025_quot h σ = ordinaryLSRate (ordinaryReference h))
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (∑ s, (ordinaryBinaryFamily h σ θ hθ0 hθ1).weight s *
      ((ordinaryFisher h ((ordinaryBinaryFamily h σ θ hθ0 hθ1).density s)).toReal -
        2 * (ordinaryLSRate (ordinaryReference h)).toReal *
          (ordinaryEntropy h ((ordinaryBinaryFamily h σ θ hθ0 hθ1).density s)).toReal)) = 0 := by
  have hIref := ordinaryFisher_eq_zero_of_entropy_zero_STR02901 h (ordinaryReferenceAbsolute h)
    (reference_entropy_zero h)
  have hσ := ordinary_optimizer_deficit_zero h σ hH hq
  change (∑ s : Fin 2, (if s.val = 0 then θ else 1 - θ) *
    ((ordinaryFisher h (if s.val = 0 then σ else ordinaryReferenceAbsolute h)).toReal -
      2 * (ordinaryLSRate (ordinaryReference h)).toReal *
        (ordinaryEntropy h (if s.val = 0 then σ else ordinaryReferenceAbsolute h)).toReal)) = 0
  simp [Fin.sum_univ_two, hσ, hIref, reference_entropy_zero]

private theorem canceled_binary_ratio (a θ P T : ℝ) (hθ : θ ≠ 0) (hT : T ≠ 0) :
    (a * (θ * T) + θ ^ 2 * P) / (θ * T) = a + θ * P / T := by
  field_simp [hθ, hT]

/-- Exact real quotient of the original family. Finiteness is supplied by the
actual deficit expansion before the real conversion. -/
theorem ordinaryBinary_quotient_real {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε))
    (σ : AbsoluteDensity 1) (hH : 0 < ordinaryEntropy h σ)
    (hq : str025_quot h σ = ordinaryLSRate (ordinaryReference h)) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hG : 0 < speciesGap (modelData h ε) (ordinaryBinaryFamily h σ θ hθ0 hθ1)) :
    (speciesQuotient (modelData h ε) b (ordinaryBinaryFamily h σ θ hθ0 hθ1)).toReal =
      (ordinaryLSRate (ordinaryReference h)).toReal +
        θ * (ε * elementaryC h (ordinaryLSRate (ordinaryReference h)).toReal σ +
          ε ^ 2 * (θ * elementaryJ h σ + (1 - θ) *
            ∫ x, (elementaryKprime h (densityMeasure σ) x) ^ 2 ∂threefoldReference h)) /
        (2 * (ordinaryEntropy h σ).toReal + ε * θ * elementaryQ h (densityMeasure σ)) := by
  let F := ordinaryBinaryFamily h σ θ hθ0 hθ1
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  let H := (ordinaryEntropy h σ).toReal
  let G : ℝ := speciesGap (modelData h ε) F
  let P := ε * elementaryC h a σ + ε ^ 2 * (θ * elementaryJ h σ + (1 - θ) *
    ∫ x, (elementaryKprime h (densityMeasure σ) x) ^ 2 ∂threefoldReference h)
  let Q := elementaryQ h (densityMeasure σ)
  obtain ⟨_, _, hDfinite, hgap, hdef⟩ := elementaryModel_exactDeficitExpansion hh hε hεmax b F
  rw [ordinaryBinary_entropy] at hgap
  rw [ordinaryBinary_D0_zero h σ hH hq θ hθ0 hθ1,
    ordinaryBinary_C hh a σ θ hθ0 hθ1, ordinaryBinary_J hh σ θ hθ0 hθ1] at hdef
  rw [ordinaryBinary_Q hh σ θ hθ0 hθ1] at hgap
  have hgap' : 2 * G = θ * (2 * H + ε * θ * Q) := by
    change 2 * G = 2 * (θ * H) + ε * (θ ^ 2 * Q) at hgap
    nlinarith
  have hdef' : (speciesDissipation (modelData h ε) b F).toReal = 2 * a * G + θ ^ 2 * P := by
    change (speciesDissipation (modelData h ε) b F).toReal - 2 * a * G =
      0 + ε * (θ ^ 2 * elementaryC h a σ) + ε ^ 2 *
        (θ ^ 2 * (θ * elementaryJ h σ + (1 - θ) *
          ∫ x, (elementaryKprime h (densityMeasure σ) x) ^ 2 ∂threefoldReference h)) at hdef
    dsimp only [P]
    nlinarith
  have hGr : 0 < G := hG
  have hden : 2 * H + ε * θ * Q ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hgap'
    linarith
  have hquot : (speciesQuotient (modelData h ε) b F).toReal =
      (speciesDissipation (modelData h ε) b F).toReal / (2 * G) := by
    unfold speciesQuotient
    rw [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.coe_toReal]
  change (speciesQuotient (modelData h ε) b F).toReal = a + θ * P / (2 * H + ε * θ * Q)
  have hnum : 2 * a * G = a * (θ * (2 * H + ε * θ * Q)) := by
    linear_combination a * hgap'
  rw [hquot, hdef', hnum, hgap']
  exact canceled_binary_ratio a θ P (2 * H + ε * θ * Q) hθ0.ne' hden

/-- A concrete sequence of strictly positive native two-species weights. -/
def ordinaryDilutionWeight (n : ℕ) : ℝ := 1 / ((n : ℝ) + 2)

private theorem ordinaryDilutionWeight_pos (n : ℕ) : 0 < ordinaryDilutionWeight n := by
  unfold ordinaryDilutionWeight
  positivity

private theorem ordinaryDilutionWeight_lt_one (n : ℕ) : ordinaryDilutionWeight n < 1 := by
  unfold ordinaryDilutionWeight
  apply (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mpr
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private theorem ordinaryDilutionWeight_tendsto :
    Tendsto ordinaryDilutionWeight atTop (𝓝 (0 : ℝ)) := by
  change Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ))
  simpa only [Function.comp_def, one_div] using
    (tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (2 : ℝ)
        (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)))


/-- The approaching sequence consists of original genuine count-two families. -/
def ordinaryBinarySequence (h : ℝ) (σ : AbsoluteDensity 1) (n : ℕ) : SpeciesFamily 1 :=
  ordinaryBinaryFamily h σ (ordinaryDilutionWeight n) (ordinaryDilutionWeight_pos n)
    (ordinaryDilutionWeight_lt_one n)

/-- Exact two-species approaching sequence at every actual ordinary optimizer.
The positive coupling threshold depends on h and precedes all weights. -/
theorem ordinaryBinary_approaching_sequence {h : ℝ} (hh : 0 < h) (σ : AbsoluteDensity 1)
    (hH : 0 < ordinaryEntropy h σ) (hq : str025_quot h σ = ordinaryLSRate (ordinaryReference h)) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ b : AbsoluteDrift (modelData h ε),
        (∀ n, (ordinaryBinarySequence h σ n).count = 2 ∧
          0 < speciesGap (modelData h ε) (ordinaryBinarySequence h σ n)) ∧
        Tendsto (fun n => speciesQuotient (modelData h ε) b (ordinaryBinarySequence h σ n))
          atTop (𝓝 (ordinaryLSRate (ordinaryReference h))) := by
  obtain ⟨ε0, hε0, hε0max, hgap⟩ := elementaryModel_speciesGap_entropy_comparable hh
  refine ⟨ε0, hε0, hε0max, fun ε hε hεε0 b => ?_⟩
  have hεmax : ε < epsMax h := hεε0.trans_le hε0max
  have hHr : 0 < (ordinaryEntropy h σ).toReal :=
    ENNReal.toReal_pos hH.ne' (str025_entropy_ne_top h σ)
  have hG (n : ℕ) : 0 < speciesGap (modelData h ε) (ordinaryBinarySequence h σ n) := by
    have he := (hgap ε hε hεε0 (ordinaryBinarySequence h σ n)).1
    have hEn : (∑ s, (ordinaryBinarySequence h σ n).weight s *
        (ordinaryEntropy h ((ordinaryBinarySequence h σ n).density s)).toReal) =
        ordinaryDilutionWeight n * (ordinaryEntropy h σ).toReal :=
      ordinaryBinary_entropy h σ (ordinaryDilutionWeight n) (ordinaryDilutionWeight_pos n)
        (ordinaryDilutionWeight_lt_one n)
    rw [hEn] at he
    change (0 : ℝ) < (speciesGap (modelData h ε) (ordinaryBinarySequence h σ n) : ℝ)
    exact lt_of_lt_of_le (mul_pos (by norm_num) (mul_pos (ordinaryDilutionWeight_pos n) hHr)) he
  refine ⟨fun n => ⟨rfl, hG n⟩, ?_⟩
  let a := (ordinaryLSRate (ordinaryReference h)).toReal
  let H := (ordinaryEntropy h σ).toReal
  let C := elementaryC h a σ
  let Q := elementaryQ h (densityMeasure σ)
  let J := elementaryJ h σ
  let M := ∫ x, (elementaryKprime h (densityMeasure σ) x) ^ 2 ∂threefoldReference h
  let f : ℝ → ℝ := fun t => a + t * (ε * C + ε ^ 2 * (t * J + (1 - t) * M)) /
    (2 * H + ε * t * Q)
  have hfc : ContinuousAt f 0 := by
    apply ContinuousAt.add continuousAt_const
    apply ContinuousAt.div
    · fun_prop
    · fun_prop
    · change 2 * H + ε * 0 * Q ≠ 0
      simpa only [mul_zero, zero_mul, add_zero] using
        (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hHr.ne')
  have hreal : Tendsto (fun n => (speciesQuotient (modelData h ε) b
      (ordinaryBinarySequence h σ n)).toReal) atTop (𝓝 a) := by
    have ht := hfc.tendsto.comp ordinaryDilutionWeight_tendsto
    have he (n : ℕ) : (speciesQuotient (modelData h ε) b (ordinaryBinarySequence h σ n)).toReal =
        f (ordinaryDilutionWeight n) :=
      ordinaryBinary_quotient_real hh hε hεmax b σ hH hq _
        (ordinaryDilutionWeight_pos n) (ordinaryDilutionWeight_lt_one n) (hG n)
    simpa only [Function.comp_def, ← he, f, mul_zero, zero_mul, zero_div, add_zero] using ht
  have hfinite (n : ℕ) : speciesQuotient (modelData h ε) b (ordinaryBinarySequence h σ n) ≠ ⊤ := by
    unfold speciesQuotient
    apply ENNReal.div_ne_top (elementaryModel_speciesDissipation_expansion h ε b _).1
    have hg0 : (speciesGap (modelData h ε) (ordinaryBinarySequence h σ n) : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast (hG n).ne'
    exact mul_ne_zero (by norm_num) hg0
  have hRateFinite : ordinaryLSRate (ordinaryReference h) ≠ ⊤ := by
    rw [← hq]
    exact quot_ne_top_STR02932 h σ hH
  have hlim := ENNReal.tendsto_ofReal hreal
  simpa only [ENNReal.ofReal_toReal (hfinite _), a, ENNReal.ofReal_toReal hRateFinite] using hlim

/-- The actual at-most-two-species infimum is bounded above by the actual
ordinary rate, using a genuine count-two approaching sequence selected internally. -/
theorem ordinaryBinary_rate_upper_same_graph (D : OrdinaryRootGraphData) {h : ℝ}
    (hh : 0 < h) (hhr : h < D.radius) :
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 ≤ epsMax h ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
      ∀ b : AbsoluteDrift (modelData h ε),
        speciesRateAtMost (modelData h ε) b 2 ≤ ordinaryLSRate (ordinaryReference h) := by
  obtain ⟨σ, _, hH, hq, _⟩ := D.roots h hh hhr
  obtain ⟨ε0, hε0, hε0max, hseq⟩ := ordinaryBinary_approaching_sequence hh (σ 0) (hH 0) (hq 0)
  refine ⟨ε0, hε0, hε0max, fun ε hε hεε0 b => ?_⟩
  obtain ⟨hG, hlim⟩ := hseq ε hε hεε0 b
  apply ge_of_tendsto hlim
  exact Eventually.of_forall fun n => speciesRateAtMost_le (modelData h ε) b 2
    (ordinaryBinarySequence h (σ 0) n) (by change Nat.le 2 2; exact Nat.le_refl 2) (hG n).2

end DGPS.Examples.ThreeSpeciesCircle
