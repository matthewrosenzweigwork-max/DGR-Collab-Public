import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesFeedbackLipschitz

/-! Exact quadratic signed-moment contribution and a true second-order bound
for the cubic feedback pairing. No optimizer, profile matching or charged
coercivity assumption is used in this independent analytic leaf. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The genuine signed six-moment quadratic, with actual generator moments. -/
def elementaryCorrectionDifference (h r : ℝ) (ρ σ : AbsoluteDensity 1) : ℝ :=
  let x := fun i : Fin 6 =>
    (∫ y, elementarySixObservable h i y ∂(densityMeasure ρ : Measure (Torus 1))) -
      ∫ y, elementarySixObservable h i y ∂(densityMeasure σ : Measure (Torus 1))
  2 * kAlpha * (x 0 * x 3 + x 1 * x 4) - 2 * kBeta * x 2 * x 5 -
    r * (kAlpha * (x 0 ^ 2 + x 1 ^ 2) - kBeta * x 2 ^ 2)

private def fc (h r : ℝ) (ρ : AbsoluteDensity 1) (y : Torus 1) : ℝ :=
  elementaryAK h (densityMeasure ρ) y + elementaryGeneratorFeedback h ρ y -
    r * elementaryKernelMean h (densityMeasure ρ) y
private def fj (h : ℝ) (ρ : AbsoluteDensity 1) (y : Torus 1) : ℝ :=
  elementaryKprime h (densityMeasure ρ) y ^ 2 + 2 * elementaryForceFeedback h ρ y

private theorem fc_continuous (h r : ℝ) (ρ : AbsoluteDensity 1) : Continuous (fc h r ρ) :=
  ((continuous_elementaryAK h (densityMeasure ρ)).add
    (isSmooth_elementaryGeneratorFeedback h ρ).continuous_torus).sub
      ((isSmooth_elementaryKernelMean h (densityMeasure ρ)).continuous_torus.const_mul r)
private theorem fj_continuous (h : ℝ) (ρ : AbsoluteDensity 1) : Continuous (fj h ρ) :=
  (((isSmooth_elementaryKernelMean h (densityMeasure ρ)).continuous_coordPartial 0).pow 2).add
    ((isSmooth_elementaryForceFeedback h ρ).continuous_torus.const_mul 2)

private def signedIntegral (ρ σ : AbsoluteDensity 1) (f : Torus 1 → ℝ) : ℝ :=
  (∫ y, f y ∂(densityMeasure ρ : Measure (Torus 1))) -
    ∫ y, f y ∂(densityMeasure σ : Measure (Torus 1))

private theorem integral_linear3 (ν : ProbabilityMeasure (Torus 1)) (a b c : ℝ)
    (f g k : Torus 1 → ℝ) (hf : Continuous f) (hg : Continuous g) (hk : Continuous k) :
    (∫ y, a * f y + b * g y + c * k y ∂(ν : Measure (Torus 1))) =
      a * (∫ y, f y ∂(ν : Measure (Torus 1))) + b * (∫ y, g y ∂(ν : Measure (Torus 1))) +
        c * (∫ y, k y ∂(ν : Measure (Torus 1))) := by
  have hi := hf.integrable_of_hasCompactSupport (μ := (ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hj := hg.integrable_of_hasCompactSupport (μ := (ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hl := hk.integrable_of_hasCompactSupport (μ := (ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have h₁ := integral_add ((hi.const_mul a).add (hj.const_mul b)) (hl.const_mul c)
  have h₂ := integral_add (hi.const_mul a) (hj.const_mul b)
  simp only [Pi.add_apply, Pi.add_def] at h₁ h₂
  rw [h₁, h₂]
  simp only [integral_const_mul]

private theorem fc_integral (h r : ℝ) (ρ ν : AbsoluteDensity 1) :
    (∫ y, fc h r ρ y ∂(densityMeasure ν : Measure (Torus 1))) =
      kAlpha *
        (momC h (densityMeasure ρ) * (∫ y, elementaryFeatureGenerator h (featureC h) y ∂(densityMeasure ν : Measure (Torus 1))) +
          momS h (densityMeasure ρ) * (∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure ν : Measure (Torus 1))) +
          (∫ y, elementaryFeatureGenerator h (featureC h) y ∂(densityMeasure ρ : Measure (Torus 1))) * momC h (densityMeasure ν) +
          (∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure ρ : Measure (Torus 1))) * momS h (densityMeasure ν)) -
      kBeta *
        (momB h (densityMeasure ρ) * (∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure ν : Measure (Torus 1))) +
          (∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure ρ : Measure (Torus 1))) * momB h (densityMeasure ν)) -
      r * (kAlpha * (momC h (densityMeasure ρ) * momC h (densityMeasure ν) +
        momS h (densityMeasure ρ) * momS h (densityMeasure ν)) - kBeta * momB h (densityMeasure ρ) * momB h (densityMeasure ν)) := by
  have hA : (∫ y, elementaryAK h (densityMeasure ρ) y ∂(densityMeasure ν : Measure (Torus 1))) =
      (kAlpha * momC h (densityMeasure ρ)) * (∫ y, elementaryFeatureGenerator h (featureC h) y ∂(densityMeasure ν : Measure (Torus 1))) +
      (kAlpha * momS h (densityMeasure ρ)) * (∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure ν : Measure (Torus 1))) +
      (-kBeta * momB h (densityMeasure ρ)) * (∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure ν : Measure (Torus 1))) := by
    have he : elementaryAK h (densityMeasure ρ) = fun y =>
        (kAlpha * momC h (densityMeasure ρ)) * elementaryFeatureGenerator h (featureC h) y +
        (kAlpha * momS h (densityMeasure ρ)) * elementaryFeatureGenerator h (featureS h) y +
        (-kBeta * momB h (densityMeasure ρ)) * elementaryFeatureGenerator h (featureB h) y := by
      funext y
      rw [elementaryAK_moments]
      ring
    rw [he]
    exact integral_linear3 (densityMeasure ν) _ _ _ _ _ _
      (continuous_elementaryFeatureGenerator h _ (isSmooth_featureC h))
      (continuous_elementaryFeatureGenerator h _ (isSmooth_featureS h))
      (continuous_elementaryFeatureGenerator h _ (isSmooth_featureB h))
  have hL : (∫ y, elementaryGeneratorFeedback h ρ y ∂(densityMeasure ν : Measure (Torus 1))) =
      (kAlpha * ∫ y, elementaryFeatureGenerator h (featureC h) y ∂(densityMeasure ρ : Measure (Torus 1))) * momC h (densityMeasure ν) +
      (kAlpha * ∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure ρ : Measure (Torus 1))) * momS h (densityMeasure ν) +
      (-kBeta * ∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure ρ : Measure (Torus 1))) * momB h (densityMeasure ν) := by
    have he : elementaryGeneratorFeedback h ρ = fun y =>
        (kAlpha * ∫ y, elementaryFeatureGenerator h (featureC h) y ∂(densityMeasure ρ : Measure (Torus 1))) * featureC h y +
        (kAlpha * ∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure ρ : Measure (Torus 1))) * featureS h y +
        (-kBeta * ∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure ρ : Measure (Torus 1))) * featureB h y + 0 := by
      funext y
      unfold elementaryGeneratorFeedback
      ring
    rw [he, integral_affine3]
    ring
  have hK : (∫ y, elementaryKernelMean h (densityMeasure ρ) y ∂(densityMeasure ν : Measure (Torus 1))) =
      (kAlpha * momC h (densityMeasure ρ)) * momC h (densityMeasure ν) +
      (kAlpha * momS h (densityMeasure ρ)) * momS h (densityMeasure ν) +
      (-kBeta * momB h (densityMeasure ρ)) * momB h (densityMeasure ν) := by
    have he : elementaryKernelMean h (densityMeasure ρ) = fun y =>
        (kAlpha * momC h (densityMeasure ρ)) * featureC h y +
        (kAlpha * momS h (densityMeasure ρ)) * featureS h y +
        (-kBeta * momB h (densityMeasure ρ)) * featureB h y + 0 := by
      funext y
      unfold elementaryKernelMean
      ring
    rw [he, integral_affine3]
    ring
  have hi := (continuous_elementaryAK h (densityMeasure ρ)).integrable_of_hasCompactSupport
    (μ := (densityMeasure ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hj := (isSmooth_elementaryGeneratorFeedback h ρ).continuous_torus.integrable_of_hasCompactSupport
    (μ := (densityMeasure ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hk := (isSmooth_elementaryKernelMean h (densityMeasure ρ)).continuous_torus.integrable_of_hasCompactSupport
    (μ := (densityMeasure ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  unfold fc
  have h₁ := integral_sub (hi.add hj) (hk.const_mul r)
  have h₂ := integral_add hi hj
  simp only [Pi.add_apply, Pi.add_def] at h₁ h₂
  rw [h₁, h₂, integral_const_mul, hA, hL, hK]
  ring

private theorem signedIntegral_sub (ρ σ : AbsoluteDensity 1) {f g : Torus 1 → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    signedIntegral ρ σ (fun y => f y - g y) = signedIntegral ρ σ f - signedIntegral ρ σ g := by
  have hi (ν : AbsoluteDensity 1) := hf.integrable_of_hasCompactSupport
    (μ := (densityMeasure ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hj (ν : AbsoluteDensity 1) := hg.integrable_of_hasCompactSupport
    (μ := (densityMeasure ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  unfold signedIntegral
  rw [integral_sub (hi _) (hj _), integral_sub (hi _) (hj _)]
  ring

private theorem signedIntegral_linear2 (ρ σ : AbsoluteDensity 1) (a b : ℝ)
    {f g : Torus 1 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    signedIntegral ρ σ (fun y => a * f y + b * g y) =
      a * signedIntegral ρ σ f + b * signedIntegral ρ σ g := by
  have hi (ν : AbsoluteDensity 1) := hf.integrable_of_hasCompactSupport
    (μ := (densityMeasure ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hj (ν : AbsoluteDensity 1) := hg.integrable_of_hasCompactSupport
    (μ := (densityMeasure ν : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  unfold signedIntegral
  rw [integral_add ((hi _).const_mul a) ((hj _).const_mul b),
    integral_add ((hi _).const_mul a) ((hj _).const_mul b)]
  simp only [integral_const_mul]
  ring

private theorem signedIntegral_haar (ρ σ : AbsoluteDensity 1) {f : Torus 1 → ℝ} (hf : Continuous f) :
    signedIntegral ρ σ f = ∫ y, f y * (ρ.density y - σ.density y) ∂haar 1 := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
  have hi (τ : AbsoluteDensity 1) : Integrable (fun y => τ.density y * f y) (haar 1) :=
    τ.integrable_density.mul_bdd hf.aestronglyMeasurable (c := C)
      (Filter.Eventually.of_forall fun y => hC y (Set.mem_univ y))
  unfold signedIntegral
  rw [Structural.budget_integral_densityMeasure, Structural.budget_integral_densityMeasure,
    ← integral_sub (hi _) (hi _)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by ring

private theorem fc_pairing (h r : ℝ) (ρ σ : AbsoluteDensity 1) :
    signedIntegral ρ σ (fun y => fc h r ρ y - fc h r σ y) = elementaryCorrectionDifference h r ρ σ := by
  rw [signedIntegral_sub ρ σ (fc_continuous h r ρ) (fc_continuous h r σ)]
  unfold signedIntegral
  rw [fc_integral, fc_integral, fc_integral, fc_integral]
  simp only [elementaryCorrectionDifference, elementarySixObservable, momC, momS, momB,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.cons_val_succ]
  ring

/-- The native feedback pairing is its exact signed quadratic contribution plus
an error bounded by coupling squared times the ORIGINAL density L1 distance
squared. The constant precedes ALL original densities, rates and couplings. -/
theorem elementaryEulerCorrection_pairing_lower (h : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ε r : ℝ) (ρ σ : AbsoluteDensity 1),
      2 * ε * elementaryCorrectionDifference h r ρ σ -
        K * ε ^ 2 * (∫ y, |ρ.density y - σ.density y| ∂haar 1) ^ 2 ≤
      ∫ y, (elementaryEulerCorrection h ε r ρ y - elementaryEulerCorrection h ε r σ y) *
        (ρ.density y - σ.density y) ∂haar 1 := by
  obtain ⟨L, hL, hLip⟩ := elementaryEulerCorrection_density_lipschitz h 0 le_rfl
  refine ⟨4 * L, by positivity, fun ε r ρ σ => ?_⟩
  let N := ∫ y, |ρ.density y - σ.density y| ∂haar 1
  have hN : 0 ≤ N := integral_nonneg fun y => abs_nonneg _
  have hJdiff (y : Torus 1) : |fj h ρ y - fj h σ y| ≤ 4 * L * N := by
    have h1 := hLip 0 (by simp) 1 (by norm_num) le_rfl ρ σ y
    have hh := hLip 0 (by simp) (1 / 2) (by norm_num) (by norm_num) ρ σ y
    have he : fj h ρ y - fj h σ y =
        2 * (elementaryEulerCorrection h 1 0 ρ y - elementaryEulerCorrection h 1 0 σ y) -
        4 * (elementaryEulerCorrection h (1 / 2) 0 ρ y - elementaryEulerCorrection h (1 / 2) 0 σ y) := by
      unfold elementaryEulerCorrection fj
      ring
    rw [he]
    calc _ ≤ 2 * |elementaryEulerCorrection h 1 0 ρ y - elementaryEulerCorrection h 1 0 σ y| +
        4 * |elementaryEulerCorrection h (1 / 2) 0 ρ y - elementaryEulerCorrection h (1 / 2) 0 σ y| := by
          have hp := abs_sub
            (2 * (elementaryEulerCorrection h 1 0 ρ y - elementaryEulerCorrection h 1 0 σ y))
            (4 * (elementaryEulerCorrection h (1 / 2) 0 ρ y - elementaryEulerCorrection h (1 / 2) 0 σ y))
          norm_num only [abs_mul] at hp
          exact hp
      _ ≤ 4 * L * N := by nlinarith only [h1, hh]
  have hJpair : -(4 * L * N ^ 2) ≤ signedIntegral ρ σ (fun y => fj h ρ y - fj h σ y) := by
    have hhaar := signedIntegral_haar ρ σ ((fj_continuous h ρ).sub (fj_continuous h σ))
    simp only [Pi.sub_def] at hhaar
    rw [hhaar]
    have hi : Integrable (fun y => (4 * L * N) * |ρ.density y - σ.density y|) (haar 1) :=
      (ρ.integrable_density.sub σ.integrable_density).abs.const_mul _
    have he : |∫ y, (fj h ρ y - fj h σ y) * (ρ.density y - σ.density y) ∂haar 1| ≤ 4 * L * N ^ 2 := by
      calc _ ≤ ∫ y, |(fj h ρ y - fj h σ y) * (ρ.density y - σ.density y)| ∂haar 1 := abs_integral_le_integral_abs
        _ ≤ ∫ y, (4 * L * N) * |ρ.density y - σ.density y| ∂haar 1 := by
          apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _) hi
          exact Filter.Eventually.of_forall fun y => by
            dsimp only
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_right (hJdiff y) (abs_nonneg _)
        _ = _ := by rw [integral_const_mul]; dsimp only [N]; ring
    exact (abs_le.mp he).1
  have he (y : Torus 1) : elementaryEulerCorrection h ε r ρ y - elementaryEulerCorrection h ε r σ y =
      (2 * ε) * (fc h r ρ y - fc h r σ y) + ε ^ 2 * (fj h ρ y - fj h σ y) := by
    unfold elementaryEulerCorrection fc fj
    ring
  have hhaar := signedIntegral_haar ρ σ
    ((isSmooth_elementaryEulerCorrection h ε r ρ).continuous_torus.sub
      (isSmooth_elementaryEulerCorrection h ε r σ).continuous_torus)
  simp only [Pi.sub_def] at hhaar
  rw [← hhaar]
  simp_rw [he]
  have hlin := signedIntegral_linear2 ρ σ (2 * ε) (ε ^ 2)
    ((fc_continuous h r ρ).sub (fc_continuous h r σ))
    ((fj_continuous h ρ).sub (fj_continuous h σ))
  simp only [Pi.sub_def] at hlin
  rw [hlin, fc_pairing]
  have hm := mul_le_mul_of_nonneg_left hJpair (sq_nonneg ε)
  change 2 * ε * elementaryCorrectionDifference h r ρ σ - 4 * L * ε ^ 2 * N ^ 2 ≤ _
  nlinarith only [hm]

end DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The true homogeneous signed six-moment polynomial. -/
def elementarySixCorrectionPolynomial (r : ℝ) (x : Fin 6 → ℝ) : ℝ :=
  2 * kAlpha * (x 0 * x 3 + x 1 * x 4) - 2 * kBeta * x 2 * x 5 -
    r * (kAlpha * (x 0 ^ 2 + x 1 ^ 2) - kBeta * x 2 ^ 2)

private theorem product_error {x y u v m e : ℝ} (hm : 0 ≤ m) (he : 0 ≤ e)
    (hx : |x - u| ≤ e) (hy : |y - v| ≤ e) (hu : |u| ≤ m) (hv : |v| ≤ m) :
    |x * y - u * v| ≤ 2 * m * e + e ^ 2 := by
  have hh : x * y - u * v = u * (y - v) + v * (x - u) + (x - u) * (y - v) := by ring
  rw [hh]
  calc _ ≤ |u * (y - v)| + |v * (x - u)| + |(x - u) * (y - v)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ = |u| * |y - v| + |v| * |x - u| + |x - u| * |y - v| := by simp only [abs_mul]
    _ ≤ m * e + m * e + e * e := by gcongr
    _ = _ := by ring

private theorem sixPolynomial_error_coeff (a : ℝ) (v w : Fin 6 → ℝ) {m e : ℝ}
    (hm : 0 ≤ m) (he : 0 ≤ e) (hd : ∀ i, |v i - w i| ≤ e) (hw : ∀ i, |w i| ≤ m) :
    |elementarySixCorrectionPolynomial a v - elementarySixCorrectionPolynomial a w| ≤
      (4 * |kAlpha| + 2 * |kBeta| + |a| * (2 * |kAlpha| + |kBeta|)) * (2 * m * e + e ^ 2) := by
  let L := 2 * m * e + e ^ 2
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hp (i j : Fin 6) : |v i * v j - w i * w j| ≤ L :=
    product_error hm he (hd i) (hd j) (hw i) (hw j)
  have hs (i : Fin 6) : |v i ^ 2 - w i ^ 2| ≤ L := by simpa only [sq] using hp i i
  have hexp : elementarySixCorrectionPolynomial a v - elementarySixCorrectionPolynomial a w =
      2 * kAlpha * ((v 0 * v 3 - w 0 * w 3) + (v 1 * v 4 - w 1 * w 4)) -
      2 * kBeta * (v 2 * v 5 - w 2 * w 5) -
      a * (kAlpha * ((v 0 ^ 2 - w 0 ^ 2) + (v 1 ^ 2 - w 1 ^ 2)) - kBeta * (v 2 ^ 2 - w 2 ^ 2)) := by
    unfold elementarySixCorrectionPolynomial
    ring
  rw [hexp]
  have h1 : |2 * kAlpha * ((v 0 * v 3 - w 0 * w 3) + (v 1 * v 4 - w 1 * w 4))| ≤
      2 * |kAlpha| * (2 * L) := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    gcongr
    exact (abs_add_le _ _).trans (by linarith [hp 0 3, hp 1 4])
  have h2 : |2 * kBeta * (v 2 * v 5 - w 2 * w 5)| ≤ 2 * |kBeta| * L := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    gcongr
    exact hp 2 5
  have h3 : |a * (kAlpha * ((v 0 ^ 2 - w 0 ^ 2) + (v 1 ^ 2 - w 1 ^ 2)) -
      kBeta * (v 2 ^ 2 - w 2 ^ 2))| ≤ |a| * (|kAlpha| * (2 * L) + |kBeta| * L) := by
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg a)
    calc _ ≤ |kAlpha * ((v 0 ^ 2 - w 0 ^ 2) + (v 1 ^ 2 - w 1 ^ 2))| +
          |kBeta * (v 2 ^ 2 - w 2 ^ 2)| := abs_sub _ _
      _ ≤ _ := by
        simp only [abs_mul]
        gcongr
        · exact (abs_add_le _ _).trans (by linarith [hs 0, hs 1])
        · exact hs 2
  calc _ ≤ |2 * kAlpha * ((v 0 * v 3 - w 0 * w 3) + (v 1 * v 4 - w 1 * w 4))| +
        |2 * kBeta * (v 2 * v 5 - w 2 * w 5)| +
        |a * (kAlpha * ((v 0 ^ 2 - w 0 ^ 2) + (v 1 ^ 2 - w 1 ^ 2)) - kBeta * (v 2 ^ 2 - w 2 ^ 2))| :=
      (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ 2 * |kAlpha| * (2 * L) + 2 * |kBeta| * L + |a| * (|kAlpha| * (2 * L) + |kBeta| * L) :=
      add_le_add (add_le_add h1 h2) h3
    _ = _ := by dsimp only [L]; ring


/-- Quantitative quadratic perturbation with a constant before every bounded
rate and every moment scale/error. Both the linear-scale and quadratic-error
terms are retained for comparison of close signed weight differences. -/
theorem elementarySixCorrectionPolynomial_error (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, |r| ≤ R → ∀ (v w : Fin 6 → ℝ) (m e : ℝ),
      0 ≤ m → 0 ≤ e → (∀ i, |v i - w i| ≤ e) → (∀ i, |w i| ≤ m) →
        |elementarySixCorrectionPolynomial r v - elementarySixCorrectionPolynomial r w| ≤
          K * (2 * m * e + e ^ 2) := by
  let K := 4 * |kAlpha| + 2 * |kBeta| + R * (2 * |kAlpha| + |kBeta|) + 1
  have hK : 0 < K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun r hr v w m e hm he hd hw => ?_⟩
  have hbound := sixPolynomial_error_coeff r v w hm he hd hw
  have hcoef : 4 * |kAlpha| + 2 * |kBeta| + |r| * (2 * |kAlpha| + |kBeta|) ≤ K := by
    have hs := mul_le_mul_of_nonneg_right hr (show 0 ≤ 2 * |kAlpha| + |kBeta| by positivity)
    dsimp only [K]
    linarith only [hs]
  exact hbound.trans (mul_le_mul_of_nonneg_right hcoef (by positivity))

end DGPS.Examples.ThreeSpeciesCircle
