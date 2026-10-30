import DGPS.Examples.ThreeSpeciesCircle.InteractingDeficitExpansion

/-! The actual reference generator acting on the centered kernel features.
The generator acts on the spatial kernel variable. No commutation with the
finite-rank kernel operator is asserted or used. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The physical generator associated with the actual threefold reference. -/
def elementaryFeatureGenerator (h : ℝ) (φ : Torus 1 → ℝ) (x : Torus 1) : ℝ :=
  -coordPartial 0 (fun y => coordPartial 0 φ y) x - sigT h x * coordPartial 0 φ x

private theorem partial_linear3 (f g k : Torus 1 → ℝ)
    (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) (hk : IsSmoothPeriodic k)
    (a b c : ℝ) (x : Torus 1) :
    coordPartial 0 (fun y => a * f y + b * g y + c * k y) x =
      a * coordPartial 0 f x + b * coordPartial 0 g x + c * coordPartial 0 k x := by
  have df : DifferentiableAt ℝ (f ∘ torusLift) (SharpLSI.secT x) := (hf.differentiable (by simp)) _
  have dg : DifferentiableAt ℝ (g ∘ torusLift) (SharpLSI.secT x) := (hg.differentiable (by simp)) _
  have dk : DifferentiableAt ℝ (k ∘ torusLift) (SharpLSI.secT x) := (hk.differentiable (by simp)) _
  unfold coordPartial
  rw [show ((fun y => a * f y + b * g y + c * k y) ∘ torusLift) =
    ((fun z => a * (f ∘ torusLift) z) + (fun z => b * (g ∘ torusLift) z)) +
      (fun z => c * (k ∘ torusLift) z) from rfl,
    fderiv_add ((df.const_mul a).add (dg.const_mul b)) (dk.const_mul c),
    fderiv_add (df.const_mul a) (dg.const_mul b),
    fderiv_const_mul df, fderiv_const_mul dg, fderiv_const_mul dk]
  simp only [ContinuousLinearMap.add_apply, smul_apply, smul_eq_mul]

/-- Linearity of the actual differential operator on smooth spatial functions. -/
theorem elementaryFeatureGenerator_linear3 (h : ℝ) (f g k : Torus 1 → ℝ)
    (hf : IsSmoothPeriodic f) (hg : IsSmoothPeriodic g) (hk : IsSmoothPeriodic k)
    (a b c : ℝ) (x : Torus 1) :
    elementaryFeatureGenerator h (fun y => a * f y + b * g y + c * k y) x =
      a * elementaryFeatureGenerator h f x + b * elementaryFeatureGenerator h g x +
        c * elementaryFeatureGenerator h k x := by
  have hd : (fun y => coordPartial 0 (fun z => a * f z + b * g z + c * k z) y) =
      fun y => a * coordPartial 0 f y + b * coordPartial 0 g y + c * coordPartial 0 k y :=
    funext (partial_linear3 f g k hf hg hk a b c)
  unfold elementaryFeatureGenerator
  rw [hd, partial_linear3 _ _ _ (hf.isSmoothPeriodic_coordPartial 0)
    (hg.isSmoothPeriodic_coordPartial 0) (hk.isSmoothPeriodic_coordPartial 0),
    partial_linear3 f g k hf hg hk]
  ring

/-- The generator of the kernel mean retains its three generator features. -/
theorem elementaryAK_moments (h : ℝ) (ν : Measure (Torus 1)) (x : Torus 1) :
    elementaryAK h ν x =
      kAlpha * (momC h ν * elementaryFeatureGenerator h (featureC h) x +
        momS h ν * elementaryFeatureGenerator h (featureS h) x) -
      kBeta * momB h ν * elementaryFeatureGenerator h (featureB h) x := by
  have he : elementaryKernelMean h ν = fun y =>
      (kAlpha * momC h ν) * featureC h y + (kAlpha * momS h ν) * featureS h y +
        (-kBeta * momB h ν) * featureB h y := by
    funext y
    unfold elementaryKernelMean
    ring
  change elementaryFeatureGenerator h (elementaryKernelMean h ν) x = _
  rw [he, elementaryFeatureGenerator_linear3 h (featureC h) (featureS h) (featureB h)
    (smooth_featureC h) (smooth_featureS h) (smooth_featureB h)]
  ring

private theorem generator_continuous (h : ℝ) {φ : Torus 1 → ℝ} (hφ : IsSmoothPeriodic φ) :
    Continuous (elementaryFeatureGenerator h φ) :=
  ((hφ.isSmoothPeriodic_coordPartial 0).continuous_coordPartial 0).neg.sub
    ((continuous_sigT h).mul (hφ.continuous_coordPartial 0))

/-- Six actual feature/generator moments determine the genuine correction C. -/
theorem elementaryC_moments (h a : ℝ) (τ : AbsoluteDensity 1) :
    elementaryC h a τ =
      2 * kAlpha * (momC h (densityMeasure τ) *
          (∫ x, elementaryFeatureGenerator h (featureC h) x ∂(densityMeasure τ : Measure (Torus 1))) +
        momS h (densityMeasure τ) *
          (∫ x, elementaryFeatureGenerator h (featureS h) x ∂(densityMeasure τ : Measure (Torus 1)))) -
      2 * kBeta * momB h (densityMeasure τ) *
        (∫ x, elementaryFeatureGenerator h (featureB h) x ∂(densityMeasure τ : Measure (Torus 1))) -
      a * (kAlpha * (momC h (densityMeasure τ) ^ 2 + momS h (densityMeasure τ) ^ 2) -
        kBeta * momB h (densityMeasure τ) ^ 2) := by
  have iC : Integrable (elementaryFeatureGenerator h (featureC h))
      (densityMeasure τ : Measure (Torus 1)) :=
    (generator_continuous h (φ := featureC h) (smooth_featureC h)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have iS : Integrable (elementaryFeatureGenerator h (featureS h))
      (densityMeasure τ : Measure (Torus 1)) :=
    (generator_continuous h (φ := featureS h) (smooth_featureS h)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have iB : Integrable (elementaryFeatureGenerator h (featureB h))
      (densityMeasure τ : Measure (Torus 1)) :=
    (generator_continuous h (φ := featureB h) (smooth_featureB h)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have he : elementaryAK h (densityMeasure τ) = fun x =>
      (kAlpha * momC h (densityMeasure τ)) * elementaryFeatureGenerator h (featureC h) x +
      (kAlpha * momS h (densityMeasure τ)) * elementaryFeatureGenerator h (featureS h) x +
      (-kBeta * momB h (densityMeasure τ)) * elementaryFeatureGenerator h (featureB h) x := by
    funext x
    rw [elementaryAK_moments]
    ring
  have hInt : (∫ x, elementaryAK h (densityMeasure τ) x ∂(densityMeasure τ : Measure (Torus 1))) =
      (kAlpha * momC h (densityMeasure τ)) *
        (∫ x, elementaryFeatureGenerator h (featureC h) x ∂(densityMeasure τ : Measure (Torus 1))) +
      (kAlpha * momS h (densityMeasure τ)) *
        (∫ x, elementaryFeatureGenerator h (featureS h) x ∂(densityMeasure τ : Measure (Torus 1))) +
      (-kBeta * momB h (densityMeasure τ)) *
        (∫ x, elementaryFeatureGenerator h (featureB h) x ∂(densityMeasure τ : Measure (Torus 1))) := by
    have iC' : Integrable (fun x => (kAlpha * momC h (densityMeasure τ)) *
        elementaryFeatureGenerator h (featureC h) x) (densityMeasure τ : Measure (Torus 1)) := iC.const_mul _
    have iS' : Integrable (fun x => (kAlpha * momS h (densityMeasure τ)) *
        elementaryFeatureGenerator h (featureS h) x) (densityMeasure τ : Measure (Torus 1)) := iS.const_mul _
    have iB' : Integrable (fun x => (-kBeta * momB h (densityMeasure τ)) *
        elementaryFeatureGenerator h (featureB h) x) (densityMeasure τ : Measure (Torus 1)) := iB.const_mul _
    have iCS : Integrable (fun x => (kAlpha * momC h (densityMeasure τ)) * elementaryFeatureGenerator h (featureC h) x +
        (kAlpha * momS h (densityMeasure τ)) * elementaryFeatureGenerator h (featureS h) x)
        (densityMeasure τ : Measure (Torus 1)) := iC'.add iS'
    rw [he]
    change (∫ x, (kAlpha * momC h (densityMeasure τ)) * elementaryFeatureGenerator h (featureC h) x +
      (kAlpha * momS h (densityMeasure τ)) * elementaryFeatureGenerator h (featureS h) x +
      (-kBeta * momB h (densityMeasure τ)) * elementaryFeatureGenerator h (featureB h) x
      ∂(densityMeasure τ : Measure (Torus 1))) = _
    rw [integral_add iCS iB', integral_add iC' iS']
    simp only [integral_const_mul]
  unfold elementaryC
  rw [← Structural.budget_integral_densityMeasure, hInt, elementaryQ_moments]
  ring

end DGPS.Examples.ThreeSpeciesCircle
