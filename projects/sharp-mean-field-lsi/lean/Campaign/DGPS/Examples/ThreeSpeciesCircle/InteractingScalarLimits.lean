import DGPS.Examples.ThreeSpeciesCircle.InteractingDeficitExpansion

/-! Continuity of the actual finite-feature interaction corrections under bounded
continuous moment convergence. This leaf is independent of scalar and finite-species
compactness, so both can use precisely the same changing-reference corrections. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

namespace DGPS.Examples.ThreeSpeciesCircle

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

private def feature (h : ℝ) : Fin 3 → Torus 1 → ℝ := ![featureC h, featureS h, featureB h]
private def coefficient (h : ℝ) (ν : ProbabilityMeasure (Torus 1)) : Fin 3 → ℝ :=
  ![kAlpha * momC h ν, kAlpha * momS h ν, -kBeta * momB h ν]
private def featureGrad (h : ℝ) (i : Fin 3) := coordPartial 0 (feature h i)
private def featureGenerator (h : ℝ) (i : Fin 3) : Torus 1 → ℝ := fun x =>
  -coordPartial 0 (featureGrad h i) x - sigT h x * featureGrad h i x

private theorem feature_smooth (h : ℝ) (i : Fin 3) : IsSmoothPeriodic (feature h i) := by
  fin_cases i
  · exact isSmooth_featureC h
  · exact isSmooth_featureS h
  · exact isSmooth_featureB h

private theorem grad_continuous (h : ℝ) (i : Fin 3) : Continuous (featureGrad h i) :=
  (feature_smooth h i).continuous_coordPartial 0

private theorem generator_continuous (h : ℝ) (i : Fin 3) : Continuous (featureGenerator h i) :=
  (((feature_smooth h i).isSmoothPeriodic_coordPartial 0).continuous_coordPartial 0).neg.sub
    ((continuous_sigT h).mul (grad_continuous h i))

private theorem kprime_sum (h : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    elementaryKprime h ν = fun x => ∑ i, coefficient h ν i * featureGrad h i x := by
  have hfun : elementaryKernelMean h ν = fun x =>
      (kAlpha * momC h ν) * featureC h x + (kAlpha * momS h ν) * featureS h x +
        (-kBeta * momB h ν) * featureB h x := by
    funext x
    unfold elementaryKernelMean
    ring
  unfold elementaryKprime
  rw [hfun, partial_linear3 _ _ _ _ _ _ (isSmooth_featureC h) (isSmooth_featureS h) (isSmooth_featureB h)]
  funext x
  simp [coefficient, featureGrad, feature, Fin.sum_univ_succ, add_assoc]

private theorem ak_sum (h : ℝ) (ν : ProbabilityMeasure (Torus 1)) :
    elementaryAK h ν = fun x => ∑ i, coefficient h ν i * featureGenerator h i x := by
  have hg : elementaryKprime h ν = fun x =>
      (kAlpha * momC h ν) * coordPartial 0 (featureC h) x +
        (kAlpha * momS h ν) * coordPartial 0 (featureS h) x +
          (-kBeta * momB h ν) * coordPartial 0 (featureB h) x := by
    rw [kprime_sum]
    funext x
    simp [coefficient, featureGrad, feature, Fin.sum_univ_succ, add_assoc]
  unfold elementaryAK
  rw [hg, partial_linear3 _ _ _ _ _ _
    ((isSmooth_featureC h).isSmoothPeriodic_coordPartial 0)
    ((isSmooth_featureS h).isSmoothPeriodic_coordPartial 0)
    ((isSmooth_featureB h).isSmoothPeriodic_coordPartial 0)]
  funext x
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
  dsimp [coefficient, featureGenerator, featureGrad, feature]
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

/-- The two actual interaction corrections are continuous under convergence of
every bounded continuous moment of the same probabilities. No H1, positivity of
the gap, or convergence of the correction itself is a premise. -/
theorem elementary_correction_tendsto (h : ℝ)
    (ν : ℕ → ProbabilityMeasure (Torus 1)) (νL : ProbabilityMeasure (Torus 1))
    (hweak : ∀ g : Torus 1 →ᵇ ℝ,
      Tendsto (fun n => ∫ x, g x ∂(ν n : Measure (Torus 1))) atTop
        (𝓝 (∫ x, g x ∂(νL : Measure (Torus 1))))) :
    Tendsto (fun n => ∫ x, elementaryAK h (ν n) x ∂(ν n : Measure (Torus 1))) atTop
      (𝓝 (∫ x, elementaryAK h νL x ∂(νL : Measure (Torus 1)))) ∧
    Tendsto (fun n => ∫ x, (elementaryKprime h (ν n) x) ^ 2 ∂(ν n : Measure (Torus 1))) atTop
      (𝓝 (∫ x, (elementaryKprime h νL x) ^ 2 ∂(νL : Measure (Torus 1)))) := by
  have hw (f : Torus 1 → ℝ) (hf : Continuous f) :
      Tendsto (fun n => ∫ x, f x ∂(ν n : Measure (Torus 1))) atTop
        (𝓝 (∫ x, f x ∂(νL : Measure (Torus 1)))) :=
    hweak (BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩)
  have hm (i : Fin 3) : Tendsto (fun n => coefficient h (ν n) i) atTop
      (𝓝 (coefficient h νL i)) := by
    fin_cases i
    · exact (hw (featureC h) (isSmooth_featureC h).continuous_torus).const_mul kAlpha
    · exact (hw (featureS h) (isSmooth_featureS h).continuous_torus).const_mul kAlpha
    · exact (hw (featureB h) (isSmooth_featureB h).continuous_torus).const_mul (-kBeta)
  have hAK (μ : ProbabilityMeasure (Torus 1)) :
      (∫ x, elementaryAK h μ x ∂(μ : Measure (Torus 1))) =
        ∑ i, coefficient h μ i * ∫ x, featureGenerator h i x ∂(μ : Measure (Torus 1)) := by
    rw [ak_sum, integral_finsetSum _ (fun i _ =>
      ((generator_continuous h i).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul _)]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  constructor
  · simp_rw [hAK]
    exact tendsto_finsetSum _ fun i _ => (hm i).mul (hw _ (generator_continuous h i))
  · simp_rw [kprime_sum]
    simp_rw [integral_sq_sum3 _ _ _ (grad_continuous h)]
    exact tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
      ((hm i).mul (hm j)).mul (hw _ ((grad_continuous h i).mul (grad_continuous h j)))

/-- Shared changing-reference correction limit for scalar and finite-species
deficit expansions, on the actual absolute densities. -/
theorem elementary_deficit_correction_tendsto (h ε : ℝ)
    (τ : ℕ → AbsoluteDensity 1) (τL : AbsoluteDensity 1)
    (hweak : ∀ g : Torus 1 →ᵇ ℝ,
      Tendsto (fun n => ∫ x, g x ∂(densityMeasure (τ n) : Measure (Torus 1))) atTop
        (𝓝 (∫ x, g x ∂(densityMeasure τL : Measure (Torus 1))))) :
    Tendsto (fun n => 2 * ε *
      (∫ x, (τ n).density x * elementaryAK h (densityMeasure (τ n)) x ∂haar 1) +
        ε ^ 2 * elementaryJ h (τ n)) atTop
      (𝓝 (2 * ε * (∫ x, τL.density x * elementaryAK h (densityMeasure τL) x ∂haar 1) +
        ε ^ 2 * elementaryJ h τL)) := by
  obtain ⟨hAK, hJ⟩ := elementary_correction_tendsto h (fun n => densityMeasure (τ n)) (densityMeasure τL) hweak
  have hlim := (hAK.const_mul (2 * ε)).add (hJ.const_mul (ε ^ 2))
  simpa only [Structural.budget_integral_densityMeasure, elementaryJ] using hlim

end DGPS.Examples.ThreeSpeciesCircle
