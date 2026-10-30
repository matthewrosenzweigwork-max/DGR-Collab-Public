import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesMinimizerLocalization
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarWeakEuler
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Genuine two-sided variations of ORIGINAL positive species weights. The
neighborhood may depend on the family; no uniform lower weight is assumed.
Outside that neighborhood the curve remains a genuine family by returning F. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

private def weightTransfer (F : SpeciesFamily 1) (i j : Fin F.count) (k : Fin F.count) : ℝ :=
  (if k = j then F.weight i else 0) - (if k = i then F.weight i else 0)

private theorem weightTransfer_sum (F : SpeciesFamily 1) (i j : Fin F.count) :
    ∑ k, weightTransfer F i j k = 0 := by
  classical
  simp [weightTransfer, Finset.sum_sub_distrib]

/-- Transfer t times the original i-weight from i to j whenever all resulting
weights are positive. This uses only the original density laws. -/
def finiteSpeciesWeightCurve (F : SpeciesFamily 1) (i j : Fin F.count) (t : ℝ) :
    SpeciesFamily 1 := by
  classical
  exact if hp : ∀ k, 0 < F.weight k + t * weightTransfer F i j k then
    { count := F.count
      weight := fun k => F.weight k + t * weightTransfer F i j k
      weight_pos := hp
      weight_sum := by
        rw [Finset.sum_add_distrib, F.weight_sum, ← Finset.mul_sum, weightTransfer_sum]
        ring
      density := F.density }
    else F

private theorem weightCurve_positive_near_zero (F : SpeciesFamily 1)
    (i j : Fin F.count) :
    ∀ᶠ t : ℝ in 𝓝 0, ∀ k, 0 < F.weight k + t * weightTransfer F i j k := by
  apply Filter.eventually_all.2
  intro k
  have hc : Continuous (fun t : ℝ => F.weight k + t * weightTransfer F i j k) :=
    continuous_const.add (continuous_id.mul continuous_const)
  have hp : 0 < F.weight k + (0 : ℝ) * weightTransfer F i j k := by
    simpa using F.weight_pos k
  exact hc.continuousAt.eventually (lt_mem_nhds hp)

theorem finiteSpeciesWeightCurve_zero (F : SpeciesFamily 1) (i j : Fin F.count) :
    finiteSpeciesWeightCurve F i j 0 = F := by
  have hp : ∀ k, 0 < F.weight k + (0 : ℝ) * weightTransfer F i j k := by
    intro k
    simpa using F.weight_pos k
  unfold finiteSpeciesWeightCurve
  rw [dif_pos hp]
  simp only [zero_mul, add_zero]

/-- Every original-density statistic is affine on a genuine two-sided
neighborhood, with the full original weight retained in its slope. -/
theorem finiteSpeciesWeightCurve_statistic (F : SpeciesFamily 1) (i j : Fin F.count)
    (L : AbsoluteDensity 1 → ℝ) :
    (fun t : ℝ => ∑ k, (finiteSpeciesWeightCurve F i j t).weight k *
      L ((finiteSpeciesWeightCurve F i j t).density k)) =ᶠ[𝓝 0]
      fun t => (∑ k, F.weight k * L (F.density k)) +
        t * (F.weight i * (L (F.density j) - L (F.density i))) := by
  classical
  filter_upwards [weightCurve_positive_near_zero F i j] with t ht
  let Ft : SpeciesFamily 1 :=
    { count := F.count
      weight := fun k => F.weight k + t * weightTransfer F i j k
      weight_pos := ht
      weight_sum := by
        rw [Finset.sum_add_distrib, F.weight_sum, ← Finset.mul_sum, weightTransfer_sum]
        ring
      density := F.density }
  have hFt : finiteSpeciesWeightCurve F i j t = Ft := by
    unfold finiteSpeciesWeightCurve
    exact dif_pos ht
  rw [hFt]
  change (∑ k : Fin F.count, (F.weight k + t * weightTransfer F i j k) * L (F.density k)) = _
  have he (k : Fin F.count) :
      (F.weight k + t * weightTransfer F i j k) * L (F.density k) =
        F.weight k * L (F.density k) +
          t * ((if k = j then F.weight i * L (F.density j) else 0) -
            (if k = i then F.weight i * L (F.density i) else 0)) := by
    by_cases hij : i = j
    · subst j
      simp [weightTransfer]
    · by_cases hki : k = i
      · subst k
        simp only [weightTransfer, if_neg hij, if_pos rfl, ite_true]
        ring
      · by_cases hkj : k = j
        · subst k
          simp only [weightTransfer, if_pos rfl, if_neg (Ne.symm hij), ite_true]
          ring
        · simp only [weightTransfer, if_neg hki, if_neg hkj]
          ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-- Actual barycenter moments have their exact original-weight derivative. -/
theorem finiteSpeciesWeightCurve_moment_hasDerivAt (F : SpeciesFamily 1)
    (i j : Fin F.count) (g : Torus 1 → ℝ) (hg : Continuous g) :
    HasDerivAt (fun t : ℝ => ∫ x, g x
      ∂(densityMeasure (barycenter (finiteSpeciesWeightCurve F i j t)) : Measure (Torus 1)))
      (F.weight i * ((∫ x, g x ∂(densityMeasure (F.density j) : Measure (Torus 1))) -
        ∫ x, g x ∂(densityMeasure (F.density i) : Measure (Torus 1)))) 0 := by
  let L := fun ρ : AbsoluteDensity 1 => ∫ x, g x ∂(densityMeasure ρ : Measure (Torus 1))
  have he := finiteSpeciesWeightCurve_statistic F i j L
  have hd : HasDerivAt (fun t : ℝ => (∑ k, F.weight k * L (F.density k)) +
      t * (F.weight i * (L (F.density j) - L (F.density i))))
      (F.weight i * (L (F.density j) - L (F.density i))) 0 := by
    have hc := (hasDerivAt_const (0 : ℝ) (∑ k, F.weight k * L (F.density k))).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (F.weight i * (L (F.density j) - L (F.density i))))
    have hfun : ((fun _ : ℝ => ∑ k, F.weight k * L (F.density k)) +
        (fun t : ℝ => id t * (F.weight i * (L (F.density j) - L (F.density i))))) =
        (fun t : ℝ => (∑ k, F.weight k * L (F.density k)) +
          t * (F.weight i * (L (F.density j) - L (F.density i)))) := rfl
    rw [hfun] at hc
    convert hc using 1 <;> simp only [zero_add, one_mul]
  apply hd.congr_of_eventuallyEq
  filter_upwards [he] with t ht
  rw [Structural.budget_integral_barycenter _ hg]
  exact ht


private def weightMomentDifference (F : SpeciesFamily 1) (i j : Fin F.count)
    (g : Torus 1 → ℝ) : ℝ :=
  F.weight i * ((∫ x, g x ∂(densityMeasure (F.density j) : Measure (Torus 1))) -
    ∫ x, g x ∂(densityMeasure (F.density i) : Measure (Torus 1)))

private theorem momentDifference_add (F : SpeciesFamily 1) (i j : Fin F.count)
    {f g : Torus 1 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    weightMomentDifference F i j (fun x => f x + g x) =
      weightMomentDifference F i j f + weightMomentDifference F i j g := by
  have hi (ρ : AbsoluteDensity 1) := hf.integrable_of_hasCompactSupport
    (μ := (densityMeasure ρ : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  have hj (ρ : AbsoluteDensity 1) := hg.integrable_of_hasCompactSupport
    (μ := (densityMeasure ρ : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  unfold weightMomentDifference
  rw [integral_add (hi _) (hj _), integral_add (hi _) (hj _)]
  ring

private theorem momentDifference_const_mul (F : SpeciesFamily 1) (i j : Fin F.count)
    (g : Torus 1 → ℝ) (a : ℝ) :
    weightMomentDifference F i j (fun x => a * g x) = a * weightMomentDifference F i j g := by
  simp only [weightMomentDifference, integral_const_mul]
  ring

private theorem momentDifference_sub (F : SpeciesFamily 1) (i j : Fin F.count)
    {f g : Torus 1 → ℝ} (hf : Continuous f) (hg : Continuous g) :
    weightMomentDifference F i j (fun x => f x - g x) =
      weightMomentDifference F i j f - weightMomentDifference F i j g := by
  have he : (fun x => f x - g x) = fun x => f x + (-1 : ℝ) * g x := by funext x; ring
  rw [he, momentDifference_add F i j hf (hg.const_mul (-1)),
    momentDifference_const_mul]
  ring

private theorem momentDifference_sum {ι : Type*} (F : SpeciesFamily 1) (i j : Fin F.count)
    (s : Finset ι) (g : ι → Torus 1 → ℝ) (hg : ∀ k ∈ s, Continuous (g k)) :
    weightMomentDifference F i j (fun x => ∑ k ∈ s, g k x) =
      ∑ k ∈ s, weightMomentDifference F i j (g k) := by
  classical
  have hi (ρ : AbsoluteDensity 1) (k : ι) (hk : k ∈ s) :=
    (hg k hk).integrable_of_hasCompactSupport
      (μ := (densityMeasure ρ : Measure (Torus 1))) (HasCompactSupport.of_compactSpace _)
  simp only [weightMomentDifference]
  rw [integral_finsetSum _ (hi _), integral_finsetSum _ (hi _),
    ← Finset.sum_sub_distrib, Finset.mul_sum]

private theorem momentDifference_linear3 (F : SpeciesFamily 1) (i j : Fin F.count)
    (a b c : ℝ) (f g k : Torus 1 → ℝ) (hf : Continuous f) (hg : Continuous g) (hk : Continuous k) :
    weightMomentDifference F i j (fun x => a * f x + b * g x + c * k x) =
      a * weightMomentDifference F i j f + b * weightMomentDifference F i j g +
        c * weightMomentDifference F i j k := by
  rw [momentDifference_add F i j
    (f := fun x => a * f x + b * g x) (g := fun x => c * k x)
    ((hf.const_mul a).add (hg.const_mul b)) (hk.const_mul c),
    momentDifference_add F i j (f := fun x => a * f x) (g := fun x => b * g x)
      (hf.const_mul a) (hg.const_mul b)]
  simp only [momentDifference_const_mul]

private theorem weightCurve_C_jet (h a : ℝ) (F : SpeciesFamily 1) (i j : Fin F.count) :
    HasDerivAt (fun t : ℝ => elementaryC h a (barycenter (finiteSpeciesWeightCurve F i j t)))
      (2 * kAlpha *
        (weightMomentDifference F i j (featureC h) *
            (∫ x, elementaryFeatureGenerator h (featureC h) x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) +
          momC h (densityMeasure (barycenter F)) *
            weightMomentDifference F i j (elementaryFeatureGenerator h (featureC h)) +
          (weightMomentDifference F i j (featureS h) *
            (∫ x, elementaryFeatureGenerator h (featureS h) x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) +
          momS h (densityMeasure (barycenter F)) *
            weightMomentDifference F i j (elementaryFeatureGenerator h (featureS h)))) -
        2 * kBeta *
          (weightMomentDifference F i j (featureB h) *
            (∫ x, elementaryFeatureGenerator h (featureB h) x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) +
          momB h (densityMeasure (barycenter F)) *
            weightMomentDifference F i j (elementaryFeatureGenerator h (featureB h))) -
        a * (2 * kAlpha *
          (momC h (densityMeasure (barycenter F)) * weightMomentDifference F i j (featureC h) +
            momS h (densityMeasure (barycenter F)) * weightMomentDifference F i j (featureS h)) -
          2 * kBeta * momB h (densityMeasure (barycenter F)) *
            weightMomentDifference F i j (featureB h))) 0 := by
  have hd (g : Torus 1 → ℝ) (hg : Continuous g) :
      HasDerivAt
        (fun t : ℝ => ∫ x, g x ∂(densityMeasure (barycenter (finiteSpeciesWeightCurve F i j t)) : Measure (Torus 1)))
        (weightMomentDifference F i j g) 0 :=
    finiteSpeciesWeightCurve_moment_hasDerivAt F i j g hg
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
    rw [elementaryC_moments]
    simp only [momC, momS, momB] <;> ring
  · simp only [momC, momS, momB]
    simp only [finiteSpeciesWeightCurve_zero]
    ring


private theorem moment_kernel (h : ℝ) (F : SpeciesFamily 1) (i j : Fin F.count) :
    weightMomentDifference F i j (elementaryKernelMean h (densityMeasure (barycenter F))) =
      kAlpha * (momC h (densityMeasure (barycenter F)) * weightMomentDifference F i j (featureC h) +
        momS h (densityMeasure (barycenter F)) * weightMomentDifference F i j (featureS h)) -
      kBeta * momB h (densityMeasure (barycenter F)) * weightMomentDifference F i j (featureB h) := by
  have he : elementaryKernelMean h (densityMeasure (barycenter F)) = fun x =>
      (kAlpha * momC h (densityMeasure (barycenter F))) * featureC h x +
      (kAlpha * momS h (densityMeasure (barycenter F))) * featureS h x +
      (-kBeta * momB h (densityMeasure (barycenter F))) * featureB h x := by
    funext x
    unfold elementaryKernelMean
    ring
  rw [he, momentDifference_linear3 F i j _ _ _ _ _ _
    (isSmooth_featureC h).continuous_torus (isSmooth_featureS h).continuous_torus
    (isSmooth_featureB h).continuous_torus]
  ring

private theorem moment_generator (h : ℝ) (F : SpeciesFamily 1) (i j : Fin F.count) :
    weightMomentDifference F i j (elementaryAK h (densityMeasure (barycenter F))) =
      kAlpha * (momC h (densityMeasure (barycenter F)) *
          weightMomentDifference F i j (elementaryFeatureGenerator h (featureC h)) +
        momS h (densityMeasure (barycenter F)) *
          weightMomentDifference F i j (elementaryFeatureGenerator h (featureS h))) -
      kBeta * momB h (densityMeasure (barycenter F)) *
        weightMomentDifference F i j (elementaryFeatureGenerator h (featureB h)) := by
  have he : elementaryAK h (densityMeasure (barycenter F)) = fun x =>
      (kAlpha * momC h (densityMeasure (barycenter F))) * elementaryFeatureGenerator h (featureC h) x +
      (kAlpha * momS h (densityMeasure (barycenter F))) * elementaryFeatureGenerator h (featureS h) x +
      (-kBeta * momB h (densityMeasure (barycenter F))) * elementaryFeatureGenerator h (featureB h) x := by
    funext x
    rw [elementaryAK_moments]
    ring
  rw [he, momentDifference_linear3 F i j _ _ _ _ _ _
    (continuous_elementaryFeatureGenerator h _ (isSmooth_featureC h))
    (continuous_elementaryFeatureGenerator h _ (isSmooth_featureS h))
    (continuous_elementaryFeatureGenerator h _ (isSmooth_featureB h))]
  ring

private theorem moment_feedback (h : ℝ) (F : SpeciesFamily 1) (i j : Fin F.count) :
    weightMomentDifference F i j (elementaryGeneratorFeedback h (barycenter F)) =
      kAlpha *
        ((∫ x, elementaryFeatureGenerator h (featureC h) x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) *
            weightMomentDifference F i j (featureC h) +
          (∫ x, elementaryFeatureGenerator h (featureS h) x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) *
            weightMomentDifference F i j (featureS h)) -
      kBeta *
        (∫ x, elementaryFeatureGenerator h (featureB h) x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) *
          weightMomentDifference F i j (featureB h) := by
  have he : elementaryGeneratorFeedback h (barycenter F) = fun x =>
      (kAlpha * ∫ y, elementaryFeatureGenerator h (featureC h) y ∂(densityMeasure (barycenter F) : Measure (Torus 1))) * featureC h x +
      (kAlpha * ∫ y, elementaryFeatureGenerator h (featureS h) y ∂(densityMeasure (barycenter F) : Measure (Torus 1))) * featureS h x +
      (-kBeta * ∫ y, elementaryFeatureGenerator h (featureB h) y ∂(densityMeasure (barycenter F) : Measure (Torus 1))) * featureB h x := by
    funext x
    unfold elementaryGeneratorFeedback
    ring
  rw [he, momentDifference_linear3 F i j _ _ _ _ _ _
    (isSmooth_featureC h).continuous_torus (isSmooth_featureS h).continuous_torus
    (isSmooth_featureB h).continuous_torus]
  ring

/-- The actual signed correction has the compact generator-feedback derivative.
It is obtained from the full changing-moment formula, not assumed as Euler data. -/
private theorem weightCurve_C_hasDerivAt (h a : ℝ) (F : SpeciesFamily 1) (i j : Fin F.count) :
    HasDerivAt (fun t : ℝ => elementaryC h a (barycenter (finiteSpeciesWeightCurve F i j t)))
      (2 * weightMomentDifference F i j (fun x =>
        elementaryAK h (densityMeasure (barycenter F)) x + elementaryGeneratorFeedback h (barycenter F) x -
          a * elementaryKernelMean h (densityMeasure (barycenter F)) x)) 0 := by
  have hA := continuous_elementaryAK h (densityMeasure (barycenter F))
  have hL := (isSmooth_elementaryGeneratorFeedback h (barycenter F)).continuous_torus
  have hK := (isSmooth_elementaryKernelMean h (densityMeasure (barycenter F))).continuous_torus
  have hd := weightCurve_C_jet h a F i j
  convert hd using 1
  rw [momentDifference_sub F i j
    (f := fun x => elementaryAK h (densityMeasure (barycenter F)) x + elementaryGeneratorFeedback h (barycenter F) x)
    (g := fun x => a * elementaryKernelMean h (densityMeasure (barycenter F)) x) (hA.add hL) (hK.const_mul a),
    momentDifference_add F i j hA hL,
    momentDifference_const_mul F i j _,
    moment_generator h F i j, moment_feedback h F i j, moment_kernel h F i j]
  ring

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

private theorem weightCurve_J_jet (h : ℝ) (F : SpeciesFamily 1) (p q : Fin F.count) :
    let f : Fin 3 → Torus 1 → ℝ := ![featureC h, featureS h, featureB h]
    let c : Fin 3 → ℝ := ![kAlpha, kAlpha, -kBeta]
    HasDerivAt (fun t : ℝ => elementaryJ h (barycenter (finiteSpeciesWeightCurve F p q t)))
      (∑ i : Fin 3, ∑ j : Fin 3, (c i * c j) *
        (((weightMomentDifference F p q (f i) *
              (∫ x, f j x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) +
            (∫ x, f i x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) *
              weightMomentDifference F p q (f j)) *
            (∫ x, coordPartial 0 (f i) x * coordPartial 0 (f j) x
              ∂(densityMeasure (barycenter F) : Measure (Torus 1)))) +
          ((∫ x, f i x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) *
            (∫ x, f j x ∂(densityMeasure (barycenter F) : Measure (Torus 1)))) *
            weightMomentDifference F p q
              (fun x => coordPartial 0 (f i) x * coordPartial 0 (f j) x))) 0 := by
  let m := fun i : Fin 3 => ∫ x, forceFeatures h i x ∂(densityMeasure (barycenter F) : Measure (Torus 1))
  let N := fun i j : Fin 3 => ∫ x, forceFeatureGrad h i x * forceFeatureGrad h j x
    ∂(densityMeasure (barycenter F) : Measure (Torus 1))
  have hd (g : Torus 1 → ℝ) (hg : Continuous g) :
      HasDerivAt (fun t : ℝ => ∫ x, g x
        ∂(densityMeasure (barycenter (finiteSpeciesWeightCurve F p q t)) : Measure (Torus 1)))
        (weightMomentDifference F p q g) 0 :=
    finiteSpeciesWeightCurve_moment_hasDerivAt F p q g hg
  have hterm (i j : Fin 3) :
      HasDerivAt (fun t : ℝ => (forceSigns i * forceSigns j) *
        ((∫ x, forceFeatures h i x ∂(densityMeasure (barycenter (finiteSpeciesWeightCurve F p q t)) : Measure (Torus 1))) *
          ∫ x, forceFeatures h j x ∂(densityMeasure (barycenter (finiteSpeciesWeightCurve F p q t)) : Measure (Torus 1))) *
        ∫ x, forceFeatureGrad h i x * forceFeatureGrad h j x
          ∂(densityMeasure (barycenter (finiteSpeciesWeightCurve F p q t)) : Measure (Torus 1)))
        ((forceSigns i * forceSigns j) *
          ((weightMomentDifference F p q (forceFeatures h i) * m j +
              m i * weightMomentDifference F p q (forceFeatures h j)) * N i j +
            (m i * m j) * weightMomentDifference F p q
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
      simp only [finiteSpeciesWeightCurve_zero]
      dsimp only [m, N]
  have hsum := HasDerivAt.sum (u := Finset.univ) fun i _ =>
    HasDerivAt.sum (u := Finset.univ) fun j _ => hterm i j
  convert hsum using 1
  · funext t
    exact J_moments h (barycenter (finiteSpeciesWeightCurve F p q t))
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

private theorem weightCurve_J_hasDerivAt (h : ℝ) (F : SpeciesFamily 1) (p q : Fin F.count) :
    HasDerivAt (fun t : ℝ => elementaryJ h (barycenter (finiteSpeciesWeightCurve F p q t)))
      (weightMomentDifference F p q (fun x =>
        (elementaryKprime h (densityMeasure (barycenter F)) x) ^ 2 + 2 * elementaryForceFeedback h (barycenter F) x)) 0 := by
  classical
  let κ := elementaryKprime h (densityMeasure (barycenter F))
  let m := fun i : Fin 3 => ∫ x, f3 h i x ∂(densityMeasure (barycenter F) : Measure (Torus 1))
  let N := fun i j : Fin 3 => ∫ x, g3 h i x * g3 h j x ∂(densityMeasure (barycenter F) : Measure (Torus 1))
  let b := fun i : Fin 3 => ∫ x, κ x * g3 h i x ∂(densityMeasure (barycenter F) : Measure (Torus 1))
  let M := fun g : Torus 1 → ℝ => weightMomentDifference F p q g
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
    rw [he, momentDifference_sum F p q Finset.univ _
      (fun i _ => continuous_finsetSum _ (fun j _ => hc i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [momentDifference_sum F p q Finset.univ _ (fun j _ => hc i j)]
    apply Finset.sum_congr rfl
    intro j _
    exact momentDifference_const_mul F p q _ _
  have hML : M (elementaryForceFeedback h (barycenter F)) =
      ∑ i : Fin 3, (c3 i * b i) * M (f3 h i) := by
    dsimp only [M]
    rw [hLsum, momentDifference_sum F p q Finset.univ _
      (fun i _ => ((f3_smooth h i).continuous_torus).const_mul _)]
    apply Finset.sum_congr rfl
    intro i _
    exact momentDifference_const_mul F p q _ _
  have hjet := weightCurve_J_jet h F p q
  convert hjet using 1
  rw [momentDifference_add F p q
    (f := fun x => κ x ^ 2) (g := fun x => 2 * elementaryForceFeedback h (barycenter F) x)
    (hκ.pow 2) (hL.const_mul 2),
    momentDifference_const_mul F p q _]
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


private theorem weightCurve_statistic_hasDerivAt (F : SpeciesFamily 1) (i j : Fin F.count)
    (L : AbsoluteDensity 1 → ℝ) :
    HasDerivAt (fun t : ℝ => ∑ k, (finiteSpeciesWeightCurve F i j t).weight k *
      L ((finiteSpeciesWeightCurve F i j t).density k))
      (F.weight i * (L (F.density j) - L (F.density i))) 0 := by
  have hd : HasDerivAt (fun t : ℝ => (∑ k, F.weight k * L (F.density k)) +
      t * (F.weight i * (L (F.density j) - L (F.density i))))
      (F.weight i * (L (F.density j) - L (F.density i))) 0 := by
    have hc := (hasDerivAt_const (0 : ℝ) (∑ k, F.weight k * L (F.density k))).add
      ((hasDerivAt_id (0 : ℝ)).mul_const (F.weight i * (L (F.density j) - L (F.density i))))
    have hfun : ((fun _ : ℝ => ∑ k, F.weight k * L (F.density k)) +
        (fun t : ℝ => id t * (F.weight i * (L (F.density j) - L (F.density i))))) =
        (fun t : ℝ => (∑ k, F.weight k * L (F.density k)) +
          t * (F.weight i * (L (F.density j) - L (F.density i)))) := rfl
    rw [hfun] at hc
    convert hc using 1 <;> simp only [zero_add, one_mul]
  exact hd.congr_of_eventuallyEq (finiteSpeciesWeightCurve_statistic F i j L)

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

private theorem weightCurve_cost_hasDerivAt {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1)
    (i j : Fin F.count) (r : ℝ) :
    HasDerivAt (fun t : ℝ =>
      (speciesDissipation (modelData h ε) b (finiteSpeciesWeightCurve F i j t)).toReal -
        2 * r * (speciesGap (modelData h ε) (finiteSpeciesWeightCurve F i j t) : ℝ))
      (F.weight i *
        (((ordinaryFisher h (F.density j)).toReal - 2 * r * (ordinaryEntropy h (F.density j)).toReal +
          ∫ x, elementaryEulerCorrection h ε r (barycenter F) x
            ∂(densityMeasure (F.density j) : Measure (Torus 1))) -
        ((ordinaryFisher h (F.density i)).toReal - 2 * r * (ordinaryEntropy h (F.density i)).toReal +
          ∫ x, elementaryEulerCorrection h ε r (barycenter F) x
            ∂(densityMeasure (F.density i) : Measure (Torus 1))))) 0 := by
  let L := fun ρ : AbsoluteDensity 1 =>
    (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal
  have hd := ((weightCurve_statistic_hasDerivAt F i j L).add
    ((weightCurve_C_hasDerivAt h r F i j).const_mul ε)).add
      ((weightCurve_J_hasDerivAt h F i j).const_mul (ε ^ 2))
  have he : HasDerivAt (fun t : ℝ =>
      (speciesDissipation (modelData h ε) b (finiteSpeciesWeightCurve F i j t)).toReal -
        2 * r * (speciesGap (modelData h ε) (finiteSpeciesWeightCurve F i j t) : ℝ))
      (F.weight i * (L (F.density j) - L (F.density i)) +
        ε * (2 * weightMomentDifference F i j (fun x =>
          elementaryAK h (densityMeasure (barycenter F)) x + elementaryGeneratorFeedback h (barycenter F) x -
            r * elementaryKernelMean h (densityMeasure (barycenter F)) x)) +
        ε ^ 2 * weightMomentDifference F i j (fun x =>
          (elementaryKprime h (densityMeasure (barycenter F)) x) ^ 2 +
            2 * elementaryForceFeedback h (barycenter F) x)) 0 := by
    apply hd.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun t =>
      family_cost_expansion hh hε hεmax b (finiteSpeciesWeightCurve F i j t) r
  convert he using 1
  rw [feedback_integral, feedback_integral]
  dsimp only [L, weightMomentDifference]
  ring

/-- Actual full-family optimality makes the original active-species values equal.
Both changing-law feedbacks are derived, and no species is assumed to minimize
an individual scalar quotient. -/
theorem elementaryModel_speciesRate_weight_stationarity {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1)
    (hG : 0 < speciesGap (modelData h ε) F)
    (hmin : speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b)
    (i j : Fin F.count) :
    let r := (speciesRate (modelData h ε) b).toReal
    (ordinaryFisher h (F.density i)).toReal - 2 * r * (ordinaryEntropy h (F.density i)).toReal +
      (∫ x, elementaryEulerCorrection h ε r (barycenter F) x
        ∂(densityMeasure (F.density i) : Measure (Torus 1))) =
    (ordinaryFisher h (F.density j)).toReal - 2 * r * (ordinaryEntropy h (F.density j)).toReal +
      (∫ x, elementaryEulerCorrection h ε r (barycenter F) x
        ∂(densityMeasure (F.density j) : Measure (Torus 1))) := by
  dsimp only
  let r := (speciesRate (modelData h ε) b).toReal
  let cost := fun t : ℝ =>
    (speciesDissipation (modelData h ε) b (finiteSpeciesWeightCurve F i j t)).toReal -
      2 * r * (speciesGap (modelData h ε) (finiteSpeciesWeightCurve F i j t) : ℝ)
  have hz : cost 0 = 0 := by
    dsimp only [cost, r]
    rw [finiteSpeciesWeightCurve_zero]
    exact elementaryModel_speciesRate_cost_eq_zero h ε b F hG hmin
  have hm : IsLocalMin cost 0 := by
    apply Filter.Eventually.of_forall
    intro t
    rw [hz]
    exact elementaryModel_speciesRate_cost_nonneg h ε b (finiteSpeciesWeightCurve F i j t)
  have hder := weightCurve_cost_hasDerivAt hh hε hεmax b F i j r
  have he := hm.hasDerivAt_eq_zero hder
  have he' := (mul_eq_zero.mp he).resolve_left (ne_of_gt (F.weight_pos i))
  linarith only [he']

/-- Weight stationarity identifies the SAME actual common value for every active
species. Averaging uses the true C/J feedback means and zero full-rate cost. -/
theorem elementaryModel_speciesRate_common_value {h ε : ℝ} (hh : 0 < h) (hε : 0 < ε)
    (hεmax : ε < epsMax h) (b : AbsoluteDrift (modelData h ε)) (F : SpeciesFamily 1)
    (hG : 0 < speciesGap (modelData h ε) F)
    (hmin : speciesQuotient (modelData h ε) b F = speciesRate (modelData h ε) b)
    (s : Fin F.count) :
    let r := (speciesRate (modelData h ε) b).toReal
    (ordinaryFisher h (F.density s)).toReal - 2 * r * (ordinaryEntropy h (F.density s)).toReal +
      (∫ x, elementaryEulerCorrection h ε r (barycenter F) x
        ∂(densityMeasure (F.density s) : Measure (Torus 1))) =
      elementaryEulerMultiplier h ε r (barycenter F) := by
  dsimp only
  let r := (speciesRate (modelData h ε) b).toReal
  let Φ := fun ρ : AbsoluteDensity 1 =>
    (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal
  let V := elementaryEulerCorrection h ε r (barycenter F)
  let W := fun k : Fin F.count => Φ (F.density k) +
    ∫ x, V x ∂(densityMeasure (F.density k) : Measure (Torus 1))
  have he (k : Fin F.count) : W k = W s :=
    elementaryModel_speciesRate_weight_stationarity hh hε hεmax b F hG hmin k s
  have hsum : (∑ k, F.weight k * W k) = W s := by
    simp_rw [he]
    rw [← Finset.sum_mul, F.weight_sum, one_mul]
  have hsplit : (∑ k, F.weight k * W k) =
      (∑ k, F.weight k * Φ (F.density k)) +
        ∫ x, V x ∂(densityMeasure (barycenter F) : Measure (Torus 1)) := by
    simp only [W, mul_add, Finset.sum_add_distrib]
    congr 1
    exact (Structural.budget_integral_barycenter F
      (isSmooth_elementaryEulerCorrection h ε r (barycenter F)).continuous_torus).symm
  have hmean : (∫ x, V x ∂(densityMeasure (barycenter F) : Measure (Torus 1))) =
      2 * ε * elementaryC h r (barycenter F) + 3 * ε ^ 2 * elementaryJ h (barycenter F) := by
    dsimp only [V]
    rw [feedback_integral, elementaryC_feedback_mean, elementaryJ_feedback_mean]
    ring
  have hcost := family_cost_expansion hh hε hεmax b F r
  have hz := elementaryModel_speciesRate_cost_eq_zero h ε b F hG hmin
  change (speciesDissipation (modelData h ε) b F).toReal -
    2 * r * (speciesGap (modelData h ε) F : ℝ) = 0 at hz
  change (speciesDissipation (modelData h ε) b F).toReal -
    2 * r * (speciesGap (modelData h ε) F : ℝ) =
      (∑ k, F.weight k * Φ (F.density k)) +
        ε * elementaryC h r (barycenter F) + ε ^ 2 * elementaryJ h (barycenter F) at hcost
  change W s = elementaryEulerMultiplier h ε r (barycenter F)
  unfold elementaryEulerMultiplier
  linarith only [hsum, hsplit, hmean, hcost, hz]

end DGPS.Examples.ThreeSpeciesCircle
