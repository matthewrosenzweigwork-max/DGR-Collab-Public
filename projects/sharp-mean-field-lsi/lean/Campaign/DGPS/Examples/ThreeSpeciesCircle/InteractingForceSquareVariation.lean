import DGPS.Examples.ThreeSpeciesCircle.InteractingCorrectionVariation

/-! Actual cubic force-square moment differentiation on normalized original H1
paths. The finite-sum identities adapt the actual three-feature expansion in
`InteractingScalarLimits`; no convergence or derivative conclusion is assumed. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

private def forceFeatures (h : ℝ) : Fin 3 → Torus 1 → ℝ :=
  ![featureC h, featureS h, featureB h]
private def forceSigns : Fin 3 → ℝ := ![kAlpha, kAlpha, -kBeta]
private def forceFeatureGrad (h : ℝ) (i : Fin 3) := coordPartial 0 (forceFeatures h i)

private theorem feature_smooth (h : ℝ) (i : Fin 3) : IsSmoothPeriodic (forceFeatures h i) := by
  fin_cases i
  · exact smooth_featureC h
  · exact smooth_featureS h
  · exact smooth_featureB h

private theorem grad_continuous (h : ℝ) (i : Fin 3) : Continuous (forceFeatureGrad h i) :=
  (feature_smooth h i).continuous_coordPartial 0

private theorem partial_linear3 (a b c : ℝ) (f g k : Torus 1 → ℝ)
    (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) (hk : IsSmoothPeriodic k) :
    coordPartial 0 (fun x => a * f x + b * g x + c * k x) =
      fun x => a * coordPartial 0 f x + b * coordPartial 0 g x + c * coordPartial 0 k x := by
  have hsm : IsSmoothPeriodic (fun x => a * f x + b * g x + c * k x) :=
    ((contDiff_const.mul hf).add (contDiff_const.mul hg)).add (contDiff_const.mul hk)
  have hw := ((hf.isWeakGradient.smul a).add (hg.isWeakGradient.smul b)).add
    (hk.isWeakGradient.smul c)
  have he := hsm.isWeakGradient.ae_eq hw
  have hae : coordPartial 0 (fun x => a * f x + b * g x + c * k x) =ᵐ[haar 1]
      fun x => a * coordPartial 0 f x + b * coordPartial 0 g x + c * coordPartial 0 k x := by
    filter_upwards [he] with x hx
    have h0 := congrArg (fun z : Tangent 1 => z 0) hx
    simpa only [smoothGrad_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using h0
  exact ((hsm.continuous_coordPartial 0).ae_eq_iff_eq (haar 1)
    (((hf.continuous_coordPartial 0).const_mul a).add
      ((hg.continuous_coordPartial 0).const_mul b) |>.add
        ((hk.continuous_coordPartial 0).const_mul c))).1 hae

private theorem kprime_linear (h : ℝ) (τ : AbsoluteDensity 1) :
    elementaryKprime h (densityMeasure τ) = fun x =>
      ∑ i, (forceSigns i * ∫ y, forceFeatures h i y ∂(densityMeasure τ : Measure (Torus 1))) *
        forceFeatureGrad h i x := by
  have he : elementaryKernelMean h (densityMeasure τ) = fun x =>
      (kAlpha * momC h (densityMeasure τ)) * featureC h x +
      (kAlpha * momS h (densityMeasure τ)) * featureS h x +
      (-kBeta * momB h (densityMeasure τ)) * featureB h x := by
    funext x
    unfold elementaryKernelMean
    ring
  unfold elementaryKprime
  rw [he, partial_linear3 (kAlpha * momC h (densityMeasure τ))
    (kAlpha * momS h (densityMeasure τ)) (-kBeta * momB h (densityMeasure τ))
    (featureC h) (featureS h) (featureB h)
    (isSmooth_featureC h) (isSmooth_featureS h) (isSmooth_featureB h)]
  funext x
  simp [forceSigns, forceFeatureGrad, forceFeatures, momC, momS, momB,
    Fin.sum_univ_succ, add_assoc]

private theorem integral_sq_sum3 (ν : ProbabilityMeasure (Torus 1)) (a : Fin 3 → ℝ)
    (f : Fin 3 → Torus 1 → ℝ) (hf : ∀ i, Continuous (f i)) :
    (∫ x, (∑ i, a i * f i x) ^ 2 ∂(ν : Measure (Torus 1))) =
      ∑ i, ∑ j, (a i * a j) * ∫ x, f i x * f j x ∂(ν : Measure (Torus 1)) := by
  have hi (i j : Fin 3) : Integrable (fun x => (a i * a j) * (f i x * f j x))
      (ν : Measure (Torus 1)) :=
    (((hf i).mul (hf j)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)).const_mul _
  have he (x : Torus 1) : (∑ i, a i * f i x) ^ 2 =
      ∑ i, ∑ j, (a i * a j) * (f i x * f j x) := by
    rw [sq, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => hi i j)]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_const_mul _ _

private theorem J_moments (h : ℝ) (τ : AbsoluteDensity 1) :
    elementaryJ h τ = ∑ i : Fin 3, ∑ j : Fin 3,
      (forceSigns i * forceSigns j) *
        ((∫ x, forceFeatures h i x ∂(densityMeasure τ : Measure (Torus 1))) *
          ∫ x, forceFeatures h j x ∂(densityMeasure τ : Measure (Torus 1))) *
        ∫ x, forceFeatureGrad h i x * forceFeatureGrad h j x
          ∂(densityMeasure τ : Measure (Torus 1)) := by
  unfold elementaryJ
  rw [← Structural.budget_integral_densityMeasure, kprime_linear,
    integral_sq_sum3 (densityMeasure τ) _ _ (grad_continuous h)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Genuine differentiation of the ACTUAL force-square term. Its three moment
factors all vary with the density; no frozen-force shortcut is used. The displayed
finite basis is exactly the model's centered C/S/B features and signed coefficients. -/
theorem absoluteRootVariation_elementaryJ_hasDerivAt (h : ℝ) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    let f : Fin 3 → Torus 1 → ℝ := ![featureC h, featureS h, featureB h]
    let c : Fin 3 → ℝ := ![kAlpha, kAlpha, -kBeta]
    HasDerivAt (fun t : ℝ => elementaryJ h (absoluteRootVariation ρ hφ t))
      (∑ i : Fin 3, ∑ j : Fin 3, (c i * c j) *
        (((absoluteRootMomentDerivative ρ φ (f i) *
              (∫ x, f j x ∂(densityMeasure ρ : Measure (Torus 1))) +
            (∫ x, f i x ∂(densityMeasure ρ : Measure (Torus 1))) *
              absoluteRootMomentDerivative ρ φ (f j)) *
            (∫ x, coordPartial 0 (f i) x * coordPartial 0 (f j) x
              ∂(densityMeasure ρ : Measure (Torus 1)))) +
          ((∫ x, f i x ∂(densityMeasure ρ : Measure (Torus 1))) *
            (∫ x, f j x ∂(densityMeasure ρ : Measure (Torus 1)))) *
            absoluteRootMomentDerivative ρ φ
              (fun x => coordPartial 0 (f i) x * coordPartial 0 (f j) x))) 0 := by
  let m := fun i : Fin 3 => ∫ x, forceFeatures h i x ∂(densityMeasure ρ : Measure (Torus 1))
  let N := fun i j : Fin 3 => ∫ x, forceFeatureGrad h i x * forceFeatureGrad h j x
    ∂(densityMeasure ρ : Measure (Torus 1))
  have hd (g : Torus 1 → ℝ) (hg : Continuous g) :
      HasDerivAt (fun t : ℝ => ∫ x, g x
        ∂(densityMeasure (absoluteRootVariation ρ hφ t) : Measure (Torus 1)))
        (absoluteRootMomentDerivative ρ φ g) 0 :=
    absoluteRootVariation_moment_hasDerivAt ρ hφ g hg
  have hterm (i j : Fin 3) :
      HasDerivAt (fun t : ℝ => (forceSigns i * forceSigns j) *
        ((∫ x, forceFeatures h i x ∂(densityMeasure (absoluteRootVariation ρ hφ t) : Measure (Torus 1))) *
          ∫ x, forceFeatures h j x ∂(densityMeasure (absoluteRootVariation ρ hφ t) : Measure (Torus 1))) *
        ∫ x, forceFeatureGrad h i x * forceFeatureGrad h j x
          ∂(densityMeasure (absoluteRootVariation ρ hφ t) : Measure (Torus 1)))
        ((forceSigns i * forceSigns j) *
          ((absoluteRootMomentDerivative ρ φ (forceFeatures h i) * m j +
              m i * absoluteRootMomentDerivative ρ φ (forceFeatures h j)) * N i j +
            (m i * m j) * absoluteRootMomentDerivative ρ φ
              (fun x => forceFeatureGrad h i x * forceFeatureGrad h j x))) 0 := by
    have hi := hd (forceFeatures h i) (feature_smooth h i).continuous_torus
    have hj := hd (forceFeatures h j) (feature_smooth h j).continuous_torus
    have hN := hd (fun x => forceFeatureGrad h i x * forceFeatureGrad h j x)
      ((grad_continuous h i).mul (grad_continuous h j))
    have ht := (((hi.mul hj).mul hN).const_mul (forceSigns i * forceSigns j))
    convert ht using 1
    · funext t
      simp only [Pi.mul_apply]
      ring
    · simp only [Pi.mul_apply]
      simp_rw [absoluteRootVariation_moment_zero]
      dsimp only [m, N]
  have hsum := HasDerivAt.sum (u := Finset.univ) fun i _ =>
    HasDerivAt.sum (u := Finset.univ) fun j _ => hterm i j
  convert hsum using 1
  · funext t
    exact J_moments h (absoluteRootVariation ρ hφ t)
  · rfl

end DGPS.Examples.ThreeSpeciesCircle
