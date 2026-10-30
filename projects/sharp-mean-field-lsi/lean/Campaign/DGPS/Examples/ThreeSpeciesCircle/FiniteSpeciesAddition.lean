import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesWeightVariation
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! One-sided addition of ANY actual original-H1 species. Only a REAL finite
moment polynomial is extended to negative parameters; no zero-weight family
is used. Full-family minimality supplies the right first-variation inequality. -/

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


private theorem kprime_linear (h : ℝ) (τ : AbsoluteDensity 1) :
    elementaryKprime h (densityMeasure τ) = fun x =>
      ∑ i, (forceSigns i * ∫ y, forceFeatures h i y ∂(densityMeasure τ : Measure (Torus 1))) *
        forceFeatureGrad h i x := by
  funext x
  rw [elementaryKprime_three_features h τ x]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp only [forceSigns, forceFeatureGrad, forceFeatures, momC, momS, momB,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

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


private def correctionCPolynomial (a : ℝ)
    (x : (Fin 6 ⊕ (Fin 3 × Fin 3)) → ℝ) : ℝ :=
  2 * kAlpha * (x (.inl 0) * x (.inl 3) + x (.inl 1) * x (.inl 4)) -
    2 * kBeta * x (.inl 2) * x (.inl 5) -
      a * (kAlpha * (x (.inl 0) ^ 2 + x (.inl 1) ^ 2) - kBeta * x (.inl 2) ^ 2)

private def correctionJPolynomial
    (x : (Fin 6 ⊕ (Fin 3 × Fin 3)) → ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (forceSigns i * forceSigns j) *
      (x (.inl (Fin.castLE (by norm_num) i)) * x (.inl (Fin.castLE (by norm_num) j))) *
        x (.inr (i, j))

private def correctionCoordinates (h : ℝ) (ρ : AbsoluteDensity 1) :
    (Fin 6 ⊕ (Fin 3 × Fin 3)) → ℝ := fun i =>
  ∫ x, elementaryCorrectionObservable h i x ∂(densityMeasure ρ : Measure (Torus 1))

private theorem correctionC_coordinates (h a : ℝ) (ρ : AbsoluteDensity 1) :
    elementaryC h a ρ = correctionCPolynomial a (correctionCoordinates h ρ) := by
  rw [elementaryC_moments]
  rfl

private theorem correctionJ_coordinates (h : ℝ) (ρ : AbsoluteDensity 1) :
    elementaryJ h ρ = correctionJPolynomial (correctionCoordinates h ρ) := by
  rw [J_moments]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he (k : Fin 3) :
      elementaryCorrectionObservable h (Sum.inl (Fin.castLE (by norm_num) k)) = forceFeatures h k := by
    fin_cases k <;> rfl
  simp only [correctionJPolynomial, correctionCoordinates, he]
  rfl


private def additionMoment (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1)
    (g : Torus 1 → ℝ) : ℝ :=
  F.weight s * ((∫ x, g x ∂(densityMeasure τ : Measure (Torus 1))) -
    ∫ x, g x ∂(densityMeasure (F.density s) : Measure (Torus 1)))

private def additionCoordinates (h : ℝ) (F : SpeciesFamily 1) (s : Fin F.count)
    (τ : AbsoluteDensity 1) (t : ℝ) : (Fin 6 ⊕ (Fin 3 × Fin 3)) → ℝ := fun k =>
  correctionCoordinates h (barycenter F) k + t * additionMoment F s τ (elementaryCorrectionObservable h k)

private def additionC (h r : ℝ) (F : SpeciesFamily 1) (s : Fin F.count)
    (τ : AbsoluteDensity 1) (t : ℝ) : ℝ := correctionCPolynomial r (additionCoordinates h F s τ t)

private def additionJ (h : ℝ) (F : SpeciesFamily 1) (s : Fin F.count)
    (τ : AbsoluteDensity 1) (t : ℝ) : ℝ := correctionJPolynomial (additionCoordinates h F s τ t)

private theorem additionCoordinates_split (h : ℝ) (F : SpeciesFamily 1) (s : Fin F.count)
    (τ : AbsoluteDensity 1) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    correctionCoordinates h (barycenter (finiteSpeciesSplit F s τ t ht ht1)) =
      additionCoordinates h F s τ t := by
  funext k
  dsimp only [correctionCoordinates, additionCoordinates, additionMoment]
  rw [finiteSpeciesSplit_moment F s τ ht ht1 _ (continuous_elementaryCorrectionObservable h k)]
  ring

private theorem momentDifference_add (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1)
    {f g : Torus 1 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    additionMoment F s τ (fun x => f x + g x) =
      additionMoment F s τ f + additionMoment F s τ g := by
  have hi (ρ : AbsoluteDensity 1) := hf.integrable_of_hasCompactSupport
    (μ := (densityMeasure ρ : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hj (ρ : AbsoluteDensity 1) := hg.integrable_of_hasCompactSupport
    (μ := (densityMeasure ρ : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  unfold additionMoment
  rw [integral_add (hi _) (hj _), integral_add (hi _) (hj _)]
  ring

private theorem momentDifference_const_mul (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1)
    (g : Torus 1 → ℝ) (a : ℝ) :
    additionMoment F s τ (fun x => a * g x) = a * additionMoment F s τ g := by
  simp only [additionMoment, integral_const_mul]
  ring

private theorem momentDifference_sub (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1)
    {f g : Torus 1 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    additionMoment F s τ (fun x => f x - g x) =
      additionMoment F s τ f - additionMoment F s τ g := by
  have he : (fun x => f x - g x) = fun x => f x + (-1 : ℝ) * g x := by funext x; ring
  rw [he, momentDifference_add F s τ hf (hg.const_mul (-1)),
    momentDifference_const_mul]
  ring

private theorem momentDifference_sum {ι : Type*} (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1)
    (I : Finset ι) (g : ι → Torus 1 → ℝ) (hg : ∀ k ∈ I, Continuous (g k)) :
    additionMoment F s τ (fun x => ∑ k ∈ I, g k x) =
      ∑ k ∈ I, additionMoment F s τ (g k) := by
  classical
  have hi (ρ : AbsoluteDensity 1) (k : ι) (hk : k ∈ I) :=
    (hg k hk).integrable_of_hasCompactSupport
      (μ := (densityMeasure ρ : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  simp only [additionMoment]
  rw [integral_finsetSum _ (hi _), integral_finsetSum _ (hi _),
    ← Finset.sum_sub_distrib, Finset.mul_sum]

private theorem momentDifference_linear3 (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1)
    (a b c : ℝ) (f g k : Torus 1 → ℝ) (hf : Continuous f) (hg : Continuous g) (hk : Continuous k) :
    additionMoment F s τ (fun x => a * f x + b * g x + c * k x) =
      a * additionMoment F s τ f + b * additionMoment F s τ g +
        c * additionMoment F s τ k := by
  have h₁ := momentDifference_add F s τ
    ((hf.const_mul a).add (hg.const_mul b)) (hk.const_mul c)
  have h₂ := momentDifference_add F s τ (hf.const_mul a) (hg.const_mul b)
  simp only [Pi.add_apply] at h₁ h₂
  rw [h₁]
  simp only [Pi.add_def]
  rw [h₂]
  simp only [momentDifference_const_mul]


private theorem additionC_jet (h a : ℝ) (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1) :
    HasDerivAt (fun t : ℝ => additionC h a F s τ t)
      (2 * kAlpha *
        (additionMoment F s τ (featureC h) *
            (∫ x, elementaryFeatureGenerator h (featureC h) x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) +
          momC h (densityMeasure (barycenter F)) *
            additionMoment F s τ (elementaryFeatureGenerator h (featureC h)) +
          (additionMoment F s τ (featureS h) *
            (∫ x, elementaryFeatureGenerator h (featureS h) x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) +
          momS h (densityMeasure (barycenter F)) *
            additionMoment F s τ (elementaryFeatureGenerator h (featureS h)))) -
        2 * kBeta *
          (additionMoment F s τ (featureB h) *
            (∫ x, elementaryFeatureGenerator h (featureB h) x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) +
          momB h (densityMeasure (barycenter F)) *
            additionMoment F s τ (elementaryFeatureGenerator h (featureB h))) -
        a * (2 * kAlpha *
          (momC h (densityMeasure (barycenter F)) * additionMoment F s τ (featureC h) +
            momS h (densityMeasure (barycenter F)) * additionMoment F s τ (featureS h)) -
          2 * kBeta * momB h (densityMeasure (barycenter F)) *
            additionMoment F s τ (featureB h))) 0 := by
  have hd (g : Torus 1 → ℝ) (hg : Continuous g) :
      HasDerivAt
        (fun t : ℝ => (∫ x, g x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) + t * additionMoment F s τ g)
        (additionMoment F s τ g) 0 :=
    by simpa only [Pi.add_def, id_eq, zero_add, one_mul] using (hasDerivAt_const (0 : ℝ)
      (∫ x, g x ∂(densityMeasure (barycenter F) : Measure (Torus 1)))).add
        ((hasDerivAt_id (0 : ℝ)).mul_const (additionMoment F s τ g))
  have hC := hd (featureC h) (isSmooth_featureC h).continuous_torus
  have hS := hd (featureS h) (isSmooth_featureS h).continuous_torus
  have hB := hd (featureB h) (isSmooth_featureB h).continuous_torus
  have hAC := hd (elementaryFeatureGenerator h (featureC h))
    (continuous_elementaryFeatureGenerator h (featureC h) (smooth_featureC h))
  have hAS := hd (elementaryFeatureGenerator h (featureS h))
    (continuous_elementaryFeatureGenerator h (featureS h) (smooth_featureS h))
  have hAB := hd (elementaryFeatureGenerator h (featureB h))
    (continuous_elementaryFeatureGenerator h (featureB h) (smooth_featureB h))
  have hQ := (((hC.pow 2).add (hS.pow 2)).const_mul kAlpha).sub
    ((hB.pow 2).const_mul kBeta)
  have hpoly := ((((hC.mul hAC).add (hS.mul hAS)).const_mul (2 * kAlpha)).sub
    ((hB.mul hAB).const_mul (2 * kBeta))).sub (hQ.const_mul a)
  convert hpoly using 1
  · funext t
    simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
    dsimp only [additionC, correctionCPolynomial, additionCoordinates, correctionCoordinates,
      elementaryCorrectionObservable, elementarySixObservable]
    dsimp only [Matrix.vecCons, Matrix.vecHead, Matrix.vecTail, Fin.castLE]
    norm_num
    ring
  · simp only [momC, momS, momB]
    simp only [zero_mul, add_zero]
    ring



private theorem moment_kernel (h : ℝ) (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1) :
    additionMoment F s τ (elementaryKernelMean h (densityMeasure (barycenter F))) =
      kAlpha * (momC h (densityMeasure (barycenter F)) * additionMoment F s τ (featureC h) +
        momS h (densityMeasure (barycenter F)) * additionMoment F s τ (featureS h)) -
      kBeta * momB h (densityMeasure (barycenter F)) * additionMoment F s τ (featureB h) := by
  have he : elementaryKernelMean h (densityMeasure (barycenter F)) = fun x =>
      (kAlpha * momC h (densityMeasure (barycenter F))) * featureC h x +
      (kAlpha * momS h (densityMeasure (barycenter F))) * featureS h x +
      (-kBeta * momB h (densityMeasure (barycenter F))) * featureB h x := by
    funext x
    unfold elementaryKernelMean
    ring
  rw [he, momentDifference_linear3 F s τ _ _ _ _ _ _
    (isSmooth_featureC h).continuous_torus (isSmooth_featureS h).continuous_torus
    (isSmooth_featureB h).continuous_torus]
  ring

private theorem moment_generator (h : ℝ) (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1) :
    additionMoment F s τ (elementaryAK h (densityMeasure (barycenter F))) =
      kAlpha * (momC h (densityMeasure (barycenter F)) *
          additionMoment F s τ (elementaryFeatureGenerator h (featureC h)) +
        momS h (densityMeasure (barycenter F)) *
          additionMoment F s τ (elementaryFeatureGenerator h (featureS h))) -
      kBeta * momB h (densityMeasure (barycenter F)) *
        additionMoment F s τ (elementaryFeatureGenerator h (featureB h)) := by
  have he : elementaryAK h (densityMeasure (barycenter F)) = fun x =>
      (kAlpha * momC h (densityMeasure (barycenter F))) * elementaryFeatureGenerator h (featureC h) x +
      (kAlpha * momS h (densityMeasure (barycenter F))) * elementaryFeatureGenerator h (featureS h) x +
      (-kBeta * momB h (densityMeasure (barycenter F))) * elementaryFeatureGenerator h (featureB h) x := by
    funext x
    rw [elementaryAK_moments]
    ring
  rw [he, momentDifference_linear3 F s τ _ _ _ _ _ _
    (continuous_elementaryFeatureGenerator h _ (isSmooth_featureC h))
    (continuous_elementaryFeatureGenerator h _ (isSmooth_featureS h))
    (continuous_elementaryFeatureGenerator h _ (isSmooth_featureB h))]
  ring

private theorem moment_feedback (h : ℝ) (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1) :
    additionMoment F s τ (elementaryGeneratorFeedback h (barycenter F)) =
      kAlpha *
        ((∫ x, elementaryFeatureGenerator h (featureC h) x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) *
            additionMoment F s τ (featureC h) +
          (∫ x, elementaryFeatureGenerator h (featureS h) x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) *
            additionMoment F s τ (featureS h)) -
      kBeta *
        (∫ x, elementaryFeatureGenerator h (featureB h) x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) *
          additionMoment F s τ (featureB h) := by
  have he : elementaryGeneratorFeedback h (barycenter F) = fun x =>
      (kAlpha * ∫ y, elementaryFeatureGenerator h (featureC h) y ∂(densityMeasure (barycenter F) : Measure (Torus 1))) * featureC h x +
      (kAlpha * ∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure (barycenter F) : Measure (Torus 1))) * featureS h x +
      (-kBeta * ∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure (barycenter F) : Measure (Torus 1))) * featureB h x := by
    funext x
    unfold elementaryGeneratorFeedback
    ring
  rw [he, momentDifference_linear3 F s τ _ _ _ _ _ _
    (isSmooth_featureC h).continuous_torus (isSmooth_featureS h).continuous_torus
    (isSmooth_featureB h).continuous_torus]
  ring

/-- The actual signed correction has the compact generator-feedback derivative.
It is obtained from the full changing-moment formula, not assumed as Euler data. -/
private theorem additionC_hasDerivAt (h a : ℝ) (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1) :
    HasDerivAt (fun t : ℝ => additionC h a F s τ t)
      (2 * additionMoment F s τ (fun x =>
        elementaryAK h (densityMeasure (barycenter F)) x + elementaryGeneratorFeedback h (barycenter F) x -
          a * elementaryKernelMean h (densityMeasure (barycenter F)) x)) 0 := by
  have hA := continuous_elementaryAK h (densityMeasure (barycenter F))
  have hL := (isSmooth_elementaryGeneratorFeedback h (barycenter F)).continuous_torus
  have hK := (isSmooth_elementaryKernelMean h (densityMeasure (barycenter F))).continuous_torus
  have hd := additionC_jet h a F s τ
  convert hd using 1
  rw [momentDifference_sub F s τ
    (f := fun x => elementaryAK h (densityMeasure (barycenter F)) x + elementaryGeneratorFeedback h (barycenter F) x)
    (g := fun x => a * elementaryKernelMean h (densityMeasure (barycenter F)) x) (hA.add hL) (hK.const_mul a),
    momentDifference_add F s τ hA hL,
    momentDifference_const_mul F s τ _,
    moment_generator h F s τ, moment_feedback h F s τ, moment_kernel h F s τ]
  ring


private theorem additionJ_jet (h : ℝ) (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1) :
    let f : Fin 3 → Torus 1 → ℝ := ![featureC h, featureS h, featureB h]
    let c : Fin 3 → ℝ := ![kAlpha, kAlpha, -kBeta]
    HasDerivAt (fun t : ℝ => additionJ h F s τ t)
      (∑ i : Fin 3, ∑ j : Fin 3, (c i * c j) *
        (((additionMoment F s τ (f i) *
              (∫ x, f j x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) +
            (∫ x, f i x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) *
              additionMoment F s τ (f j)) *
            (∫ x, coordPartial 0 (f i) x * coordPartial 0 (f j) x
              ∂(densityMeasure (barycenter F) : Measure (Torus 1)))) +
          ((∫ x, f i x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) *
            (∫ x, f j x ∂(densityMeasure (barycenter F) : Measure (Torus 1)))) *
            additionMoment F s τ
              (fun x => coordPartial 0 (f i) x * coordPartial 0 (f j) x))) 0 := by
  let m := fun i : Fin 3 => ∫ x, forceFeatures h i x ∂(densityMeasure (barycenter F) : Measure (Torus 1))
  let N := fun i j : Fin 3 => ∫ x, forceFeatureGrad h i x * forceFeatureGrad h j x
    ∂(densityMeasure (barycenter F) : Measure (Torus 1))
  have hd (g : Torus 1 → ℝ) (hg : Continuous g) :
      HasDerivAt (fun t : ℝ =>
        (∫ x, g x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) + t * additionMoment F s τ g)
        (additionMoment F s τ g) 0 :=
    by simpa only [Pi.add_def, id_eq, zero_add, one_mul] using (hasDerivAt_const (0 : ℝ)
      (∫ x, g x ∂(densityMeasure (barycenter F) : Measure (Torus 1)))).add
        ((hasDerivAt_id (0 : ℝ)).mul_const (additionMoment F s τ g))
  have hterm (i j : Fin 3) :
      HasDerivAt (fun t : ℝ => (forceSigns i * forceSigns j) *
        ((m i + t * additionMoment F s τ (forceFeatures h i)) *
          (m j + t * additionMoment F s τ (forceFeatures h j))) *
        (N i j + t * additionMoment F s τ (fun x => forceFeatureGrad h i x * forceFeatureGrad h j x)))
        ((forceSigns i * forceSigns j) *
          ((additionMoment F s τ (forceFeatures h i) * m j +
              m i * additionMoment F s τ (forceFeatures h j)) * N i j +
            (m i * m j) * additionMoment F s τ
              (fun x => forceFeatureGrad h i x * forceFeatureGrad h j x))) 0 := by
    have hi := hd (forceFeatures h i) (feature_smooth h i).continuous_torus
    have hj := hd (forceFeatures h j) (feature_smooth h j).continuous_torus
    have hN := hd (fun x => forceFeatureGrad h i x * forceFeatureGrad h j x)
      ((grad_continuous h i).mul (grad_continuous h j))
    have ht := (((hi.mul hj).mul hN).const_mul (forceSigns i * forceSigns j))
    convert ht using 1
    · funext t
      simp only [Pi.mul_apply]
      dsimp only [m, N]
      ring
    · simp only [Pi.mul_apply, zero_mul, add_zero]
      dsimp only [m, N]
  have hsum := HasDerivAt.sum (u := Finset.univ) fun i _ =>
    HasDerivAt.sum (u := Finset.univ) fun j _ => hterm i j
  convert hsum using 1
  · funext t
    dsimp only [additionJ, correctionJPolynomial, additionCoordinates, correctionCoordinates, m, N]
    simp only [Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    have he (k : Fin 3) :
        elementaryCorrectionObservable h (Sum.inl (Fin.castLE (by norm_num) k)) = forceFeatures h k := by
      fin_cases k <;> rfl
    simp only [he]
    change (forceSigns i * forceSigns j) *
      ((m i + t * additionMoment F s τ (forceFeatures h i)) *
        (m j + t * additionMoment F s τ (forceFeatures h j))) *
      (N i j + t * additionMoment F s τ
        (fun x => forceFeatureGrad h i x * forceFeatureGrad h j x)) = _
    dsimp only [m, N]
  · rfl



private def f3 (h : ℝ) : Fin 3 → Torus 1 → ℝ := ![featureC h, featureS h, featureB h]
private def c3 : Fin 3 → ℝ := ![kAlpha, kAlpha, -kBeta]
private def g3 (h : ℝ) (i : Fin 3) := coordPartial 0 (f3 h i)

private theorem f3_smooth (h : ℝ) (i : Fin 3) : IsSmoothPeriodic (f3 h i) := by
  fin_cases i
  · exact isSmooth_featureC h
  · exact isSmooth_featureS h
  · exact isSmooth_featureB h

private theorem g3_continuous (h : ℝ) (i : Fin 3) : Continuous (g3 h i) :=
  (f3_smooth h i).continuous_coordPartial 0

private theorem additionJ_hasDerivAt (h : ℝ) (F : SpeciesFamily 1) (s : Fin F.count) (τ : AbsoluteDensity 1) :
    HasDerivAt (fun t : ℝ => additionJ h F s τ t)
      (additionMoment F s τ (fun x =>
        (elementaryKprime h (densityMeasure (barycenter F)) x) ^ 2 + 2 * elementaryForceFeedback h (barycenter F) x)) 0 := by
  classical
  let κ := elementaryKprime h (densityMeasure (barycenter F))
  let m := fun i : Fin 3 => ∫ x, f3 h i x ∂(densityMeasure (barycenter F) : Measure (Torus 1))
  let N := fun i j : Fin 3 => ∫ x, g3 h i x * g3 h j x ∂(densityMeasure (barycenter F) : Measure (Torus 1))
  let b := fun i : Fin 3 => ∫ x, κ x * g3 h i x ∂(densityMeasure (barycenter F) : Measure (Torus 1))
  let M := fun g : Torus 1 → ℝ => additionMoment F s τ g
  have hκ : Continuous κ :=
    (isSmooth_elementaryKernelMean h (densityMeasure (barycenter F))).continuous_coordPartial 0
  have hL := (isSmooth_elementaryForceFeedback h (barycenter F)).continuous_torus
  have hκsum : κ = fun x => ∑ i : Fin 3, (c3 i * m i) * g3 h i x := by
    funext x
    rw [show κ x = _ from elementaryKprime_three_features h (barycenter F) x]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp only [c3, m, f3, g3, momC, momS, momB, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    ring
  have hLsum : elementaryForceFeedback h (barycenter F) = fun x => ∑ i : Fin 3, (c3 i * b i) * f3 h i x := by
    funext x
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp only [elementaryForceFeedback, c3, b, κ, f3, g3, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    ring
  have hNsym (i j : Fin 3) : N i j = N j i := by
    apply integral_congr_ae
    exact Eventually.of_forall fun x => mul_comm _ _
  have hb (i : Fin 3) : b i = ∑ j : Fin 3, (c3 j * m j) * N i j := by
    have he : (fun x => κ x * g3 h i x) =
        fun x => ∑ j : Fin 3, (c3 j * m j) * (g3 h i x * g3 h j x) := by
      funext x
      rw [hκsum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hi (j : Fin 3) : Integrable
        (fun x => (c3 j * m j) * (g3 h i x * g3 h j x))
        (densityMeasure (barycenter F) : Measure (Torus 1)) :=
      (((g3_continuous h i).mul (g3_continuous h j)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul _
    dsimp only [b]
    rw [he, integral_finsetSum _ (fun j _ => hi j)]
    simp only [integral_const_mul]
    rfl
  have hMsq : M (fun x => κ x ^ 2) =
      ∑ i : Fin 3, ∑ j : Fin 3, ((c3 i * m i) * (c3 j * m j)) *
        M (fun x => g3 h i x * g3 h j x) := by
    have he : (fun x => κ x ^ 2) = fun x =>
        ∑ i : Fin 3, ∑ j : Fin 3, ((c3 i * m i) * (c3 j * m j)) *
          (g3 h i x * g3 h j x) := by
      funext x
      rw [hκsum, sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    have hc (i j : Fin 3) : Continuous (fun x =>
        ((c3 i * m i) * (c3 j * m j)) * (g3 h i x * g3 h j x)) :=
      ((g3_continuous h i).mul (g3_continuous h j)).const_mul _
    dsimp only [M]
    rw [he, momentDifference_sum F s τ Finset.univ _
      (fun i _ => continuous_finsetSum _ (fun j _ => hc i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [momentDifference_sum F s τ Finset.univ _ (fun j _ => hc i j)]
    apply Finset.sum_congr rfl
    intro j _
    exact momentDifference_const_mul F s τ _ _
  have hML : M (elementaryForceFeedback h (barycenter F)) =
      ∑ i : Fin 3, (c3 i * b i) * M (f3 h i) := by
    dsimp only [M]
    rw [hLsum, momentDifference_sum F s τ Finset.univ _
      (fun i _ => ((f3_smooth h i).continuous_torus).const_mul _)]
    apply Finset.sum_congr rfl
    intro i _
    exact momentDifference_const_mul F s τ _ _
  have hjet := additionJ_jet h F s τ
  convert hjet using 1
  rw [momentDifference_add F s τ
    (f := fun x => κ x ^ 2) (g := fun x => 2 * elementaryForceFeedback h (barycenter F) x)
    (hκ.pow 2) (hL.const_mul 2),
    momentDifference_const_mul F s τ _]
  change M (fun x => κ x ^ 2) + 2 * M (elementaryForceFeedback h (barycenter F)) = _
  rw [hMsq, hML]
  simp_rw [hb]
  change (∑ i : Fin 3, ∑ j : Fin 3,
      ((c3 i * m i) * (c3 j * m j)) * M (fun x => g3 h i x * g3 h j x)) +
      2 * (∑ i : Fin 3, (c3 i * (∑ j : Fin 3, (c3 j * m j) * N i j)) * M (f3 h i)) =
    ∑ i : Fin 3, ∑ j : Fin 3, (c3 i * c3 j) *
      ((M (f3 h i) * m j + m i * M (f3 h j)) * N i j +
        (m i * m j) * M (fun x => g3 h i x * g3 h j x))
  simp [Fin.sum_univ_succ, Fin.sum_univ_zero, hNsym (1 : Fin 3) 0,
    hNsym (2 : Fin 3) 0, hNsym (2 : Fin 3) 1]
  <;> ring


private theorem family_cost_expansion {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1) (r : ℝ) :
    (speciesDissipation (modelData h ε) b F).toReal -
      2 * r * (speciesGap (modelData h ε) F : ℝ) =
        (∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
          2 * r * (ordinaryEntropy h (F.density s)).toReal)) +
          ε * elementaryC h r (barycenter F) + ε ^ 2 * elementaryJ h (barycenter F) := by
  have hsum : (∑ s, F.weight s * ((ordinaryFisher h (F.density s)).toReal -
      2 * r * (ordinaryEntropy h (F.density s)).toReal)) =
      (∑ s, F.weight s * (ordinaryFisher h (F.density s)).toReal) -
        2 * r * (∑ s, F.weight s * (ordinaryEntropy h (F.density s)).toReal) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [(elementaryModel_speciesDissipation_expansion h ε b F).2,
    elementaryModel_speciesGap_expansion hh hε hεmax F, hsum]
  unfold elementaryC
  ring

private theorem feedback_integral (h ε r : ℝ) (τ ρ : AbsoluteDensity 1) :
    (∫ x, elementaryEulerCorrection h ε r τ x ∂(densityMeasure ρ : Measure (Torus 1))) =
      2 * ε * (∫ x, elementaryAK h (densityMeasure τ) x + elementaryGeneratorFeedback h τ x -
        r * elementaryKernelMean h (densityMeasure τ) x ∂(densityMeasure ρ : Measure (Torus 1))) +
      ε ^ 2 * (∫ x, (elementaryKprime h (densityMeasure τ) x) ^ 2 +
        2 * elementaryForceFeedback h τ x ∂(densityMeasure ρ : Measure (Torus 1))) := by
  have hA := continuous_elementaryAK h (densityMeasure τ)
  have hL := (isSmooth_elementaryGeneratorFeedback h τ).continuous_torus
  have hK := (isSmooth_elementaryKernelMean h (densityMeasure τ)).continuous_torus
  have hκ := (isSmooth_elementaryKernelMean h (densityMeasure τ)).continuous_coordPartial 0
  have hF := (isSmooth_elementaryForceFeedback h τ).continuous_torus
  have hC : Integrable (fun x => 2 * ε * (elementaryAK h (densityMeasure τ) x +
      elementaryGeneratorFeedback h τ x - r * elementaryKernelMean h (densityMeasure τ) x))
      (densityMeasure ρ : Measure (Torus 1)) :=
    (((hA.add hL).sub (hK.const_mul r)).const_mul _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hJ : Integrable (fun x => ε ^ 2 * ((elementaryKprime h (densityMeasure τ) x) ^ 2 +
      2 * elementaryForceFeedback h τ x)) (densityMeasure ρ : Measure (Torus 1)) :=
    (((hκ.pow 2).add (hF.const_mul 2)).const_mul _).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold elementaryEulerCorrection
  rw [integral_add hC hJ, integral_const_mul, integral_const_mul]


private def additionCost (h ε r : ℝ) (F : SpeciesFamily 1) (s : Fin F.count)
    (τ : AbsoluteDensity 1) (t : ℝ) : ℝ :=
  (∑ k, F.weight k * ((ordinaryFisher h (F.density k)).toReal -
    2 * r * (ordinaryEntropy h (F.density k)).toReal)) +
    t * (F.weight s * (((ordinaryFisher h τ).toReal - 2 * r * (ordinaryEntropy h τ).toReal) -
      ((ordinaryFisher h (F.density s)).toReal - 2 * r * (ordinaryEntropy h (F.density s)).toReal))) +
    ε * additionC h r F s τ t + ε ^ 2 * additionJ h F s τ t

private theorem additionCost_split {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1)
    (s : Fin F.count) (τ : AbsoluteDensity 1) (t : ℝ) (ht : 0 < t) (ht1 : t < 1) (r : ℝ) :
    additionCost h ε r F s τ t =
      (speciesDissipation (modelData h ε) b (finiteSpeciesSplit F s τ t ht ht1)).toReal -
        2 * r * (speciesGap (modelData h ε) (finiteSpeciesSplit F s τ t ht ht1) : ℝ) := by
  rw [family_cost_expansion hh hε hεmax,
    finiteSpeciesSplit_weighted_statistic F s τ ht ht1
      (fun ρ : AbsoluteDensity 1 => (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal),
    correctionC_coordinates, correctionJ_coordinates, additionCoordinates_split h F s τ t ht ht1]
  dsimp only [additionCost, additionC, additionJ]
  ring

private theorem additionCost_zero {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1)
    (s : Fin F.count) (τ : AbsoluteDensity 1) :
    additionCost h ε (speciesRate (modelData h ε) b).toReal F s τ 0 =
      (speciesDissipation (modelData h ε) b F).toReal -
        2 * (speciesRate (modelData h ε) b).toReal * (speciesGap (modelData h ε) F : ℝ) := by
  rw [family_cost_expansion hh hε hεmax]
  have hz : additionCoordinates h F s τ 0 = correctionCoordinates h (barycenter F) := by
    funext i
    simp [additionCoordinates]
  simp only [additionCost, additionC, additionJ, zero_mul, add_zero, hz]
  rw [← correctionC_coordinates, ← correctionJ_coordinates]

private theorem additionCost_hasDerivAt (h ε r : ℝ) (F : SpeciesFamily 1)
    (s : Fin F.count) (τ : AbsoluteDensity 1) :
    HasDerivAt (additionCost h ε r F s τ)
      (F.weight s *
        (((ordinaryFisher h τ).toReal - 2 * r * (ordinaryEntropy h τ).toReal +
          ∫ x, elementaryEulerCorrection h ε r (barycenter F) x ∂(densityMeasure τ : Measure (Torus 1))) -
         ((ordinaryFisher h (F.density s)).toReal - 2 * r * (ordinaryEntropy h (F.density s)).toReal +
          ∫ x, elementaryEulerCorrection h ε r (barycenter F) x
            ∂(densityMeasure (F.density s) : Measure (Torus 1))))) 0 := by
  let Φ := fun ρ : AbsoluteDensity 1 =>
    (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal
  have hlin := (hasDerivAt_const (0 : ℝ) (∑ k, F.weight k * Φ (F.density k))).add
    ((hasDerivAt_id (0 : ℝ)).mul_const (F.weight s * (Φ τ - Φ (F.density s))))
  have hd := (hlin.add ((additionC_hasDerivAt h r F s τ).const_mul ε)).add
    ((additionJ_hasDerivAt h F s τ).const_mul (ε ^ 2))
  convert hd using 1
  · funext t
    dsimp only [additionCost, Φ]
    simp only [Pi.add_apply, Pi.mul_apply, id_eq]
  · simp only [zero_add, one_mul]
    rw [feedback_integral, feedback_integral]
    dsimp only [additionMoment, Φ]
    ring

private theorem nonneg_right_derivative {P : ℝ → ℝ} {z : ℝ}
    (hP0 : P 0 = 0) (hP : ∀ t : ℝ, 0 < t → t < 1 → 0 ≤ P t)
    (hd : HasDerivAt P z 0) : 0 ≤ z := by
  have ht1 : ∀ᶠ t : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, t < 1 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
  have hm : IsLocalMinOn P (Set.Ici (0 : ℝ)) 0 := by
    change ∀ᶠ t : ℝ in 𝓝[Set.Ici (0 : ℝ)] 0, P 0 ≤ P t
    filter_upwards [self_mem_nhdsWithin, ht1] with t ht ht1'
    rw [hP0]
    by_cases ht0 : t = 0
    · simp only [ht0, hP0, le_refl]
    · exact hP t (lt_of_le_of_ne ht (Ne.symm ht0)) ht1'
  have hseg : segment ℝ (0 : ℝ) (0 + 1) ⊆ Set.Ici (0 : ℝ) :=
    (convex_Ici (0 : ℝ)).segment_subset (by simp) (by simp)
  have hcone : (1 : ℝ) ∈ posTangentConeAt (Set.Ici (0 : ℝ)) 0 :=
    mem_posTangentConeAt_of_segment_subset hseg
  simpa using hm.hasFDerivWithinAt_nonneg
    (hasDerivAt_iff_hasFDerivAt.1 hd).hasFDerivWithinAt hcone

/-- Every active species of an actual FULL-family minimizer is a GLOBAL
minimizer of the genuine fixed-field functional over ALL original H1 densities.
The assertion is derived by one-sided addition of an arbitrary new species;
common active values alone are not used as a substitute for this argument. -/
theorem elementaryModel_speciesRate_active_global_minimum {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1)
    (hG : 0 < speciesGap (modelData h ε) F)
    (hmin : speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b)
    (s : Fin F.count) (τ : AbsoluteDensity 1) :
    let r := (speciesRate (modelData h ε) b).toReal
    (ordinaryFisher h (F.density s)).toReal - 2 * r * (ordinaryEntropy h (F.density s)).toReal +
      (∫ x, elementaryEulerCorrection h ε r (barycenter F) x
        ∂(densityMeasure (F.density s) : Measure (Torus 1))) ≤
    (ordinaryFisher h τ).toReal - 2 * r * (ordinaryEntropy h τ).toReal +
      (∫ x, elementaryEulerCorrection h ε r (barycenter F) x ∂(densityMeasure τ : Measure (Torus 1))) := by
  dsimp only
  let r := (speciesRate (modelData h ε) b).toReal
  have hz : additionCost h ε r F s τ 0 = 0 := by
    rw [additionCost_zero hh hε hεmax b]
    exact elementaryModel_speciesRate_cost_eq_zero h ε b F hG hmin
  have hp (t : ℝ) (ht : 0 < t) (ht1 : t < 1) : 0 ≤ additionCost h ε r F s τ t := by
    rw [additionCost_split hh hε hεmax b F s τ t ht ht1 r]
    exact elementaryModel_speciesRate_cost_nonneg h ε b (finiteSpeciesSplit F s τ t ht ht1)
  have hright := nonneg_right_derivative hz hp (additionCost_hasDerivAt h ε r F s τ)
  have he := (mul_nonneg_iff_of_pos_left (F.weight_pos s)).1 hright
  exact sub_nonneg.mp he

end DGPS.Examples.ThreeSpeciesCircle
