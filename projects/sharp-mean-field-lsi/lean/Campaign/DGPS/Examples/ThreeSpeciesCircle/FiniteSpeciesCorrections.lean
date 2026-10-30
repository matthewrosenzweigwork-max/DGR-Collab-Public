import DGPS.Examples.ThreeSpeciesCircle.NearestRootMomentError
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Quantitative actual correction control on the finite moment box. The
coordinates include the genuine generator moments and all derivative products;
no eigenfeature or kernel-generator commutation is used. -/

noncomputable section
open MeasureTheory
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

/-- The actual finite set of observables determining C and J. -/
def elementaryCorrectionObservable (h : ℝ) :
    Fin 6 ⊕ (Fin 3 × Fin 3) → Torus 1 → ℝ
  | Sum.inl i => elementarySixObservable h i
  | Sum.inr p => fun x => coordPartial 0 (forceFeatures h p.1) x *
      coordPartial 0 (forceFeatures h p.2) x

theorem continuous_elementaryCorrectionObservable (h : ℝ)
    (i : Fin 6 ⊕ (Fin 3 × Fin 3)) : Continuous (elementaryCorrectionObservable h i) := by
  cases i with
  | inl i => exact continuous_elementarySixObservable h i
  | inr p => exact (grad_continuous h p.1).mul (grad_continuous h p.2)

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

/-- All actual C/J coordinates lie in one compact moment box fixed before the
original absolute density. -/
theorem elementaryCorrection_coordinates_bound (h : ℝ) :
    ∃ M : ℝ, 0 < M ∧ ∀ (i : Fin 6 ⊕ (Fin 3 × Fin 3)) (x : Torus 1),
      |elementaryCorrectionObservable h i x| ≤ M := by
  have hb (i : Fin 6 ⊕ (Fin 3 × Fin 3)) : ∃ B : ℝ,
      ∀ x, ‖elementaryCorrectionObservable h i x‖ ≤ B := by
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_elementaryCorrectionObservable h i).continuousOn
    exact ⟨B, fun x => hB x (Set.mem_univ x)⟩
  choose B hB using hb
  refine ⟨1 + ∑ i, |B i|, by positivity, fun i x => ?_⟩
  have hx : |elementaryCorrectionObservable h i x| ≤ B i := by
    simpa only [Real.norm_eq_abs] using hB i x
  have hs : |B i| ≤ ∑ j, |B j| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (B j)) (Finset.mem_univ i)
  linarith [le_abs_self (B i)]

/-- Quantitative C and J control from their actual finite observable moments.
The constant is fixed before both original H1 densities and every moment error. -/
theorem elementaryCorrection_moment_lipschitz (h a : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ρ σ : AbsoluteDensity 1) (δ : ℝ), 0 ≤ δ →
      (∀ i : Fin 6 ⊕ (Fin 3 × Fin 3),
        |(∫ x, elementaryCorrectionObservable h i x ∂(densityMeasure ρ : Measure (Torus 1))) -
          (∫ x, elementaryCorrectionObservable h i x ∂(densityMeasure σ : Measure (Torus 1)))| ≤ δ) →
      |elementaryC h a ρ - elementaryC h a σ| ≤ K * δ ∧
        |elementaryJ h ρ - elementaryJ h σ| ≤ K * δ := by
  obtain ⟨M, hM, hbound⟩ := elementaryCorrection_coordinates_bound h
  have hcoord (ρ : AbsoluteDensity 1) : ‖correctionCoordinates h ρ‖ ≤ M := by
    apply (pi_norm_le_iff_of_nonneg hM.le).2
    intro i
    change ‖∫ x, elementaryCorrectionObservable h i x
      ∂(densityMeasure ρ : Measure (Torus 1))‖ ≤ M
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := (densityMeasure ρ : Measure (Torus 1)))
        (f := elementaryCorrectionObservable h i) (C := M)
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound i x))
  have hc : ContDiff ℝ 1 (correctionCPolynomial a) := by unfold correctionCPolynomial; fun_prop
  have hj : ContDiff ℝ 1 correctionJPolynomial := by unfold correctionJPolynomial; fun_prop
  obtain ⟨KC, hKC⟩ := hc.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : (Fin 6 ⊕ (Fin 3 × Fin 3)) → ℝ) M) (isCompact_closedBall 0 M)
  obtain ⟨KJ, hKJ⟩ := hj.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : (Fin 6 ⊕ (Fin 3 × Fin 3)) → ℝ) M) (isCompact_closedBall 0 M)
  refine ⟨(KC : ℝ) + KJ + 1, by positivity, fun ρ σ δ hδ hdiff => ?_⟩
  have hm (τ : AbsoluteDensity 1) : correctionCoordinates h τ ∈ Metric.closedBall 0 M := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hcoord τ
  have hd : dist (correctionCoordinates h ρ) (correctionCoordinates h σ) ≤ δ := by
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg hδ).2
    intro i
    simpa only [Pi.sub_apply, Real.norm_eq_abs, correctionCoordinates] using hdiff i
  have hC := (hKC.dist_le_mul _ (hm ρ) _ (hm σ)).trans (mul_le_mul_of_nonneg_left hd KC.coe_nonneg)
  have hJ := (hKJ.dist_le_mul _ (hm ρ) _ (hm σ)).trans (mul_le_mul_of_nonneg_left hd KJ.coe_nonneg)
  rw [correctionC_coordinates, correctionC_coordinates]
  rw [correctionJ_coordinates, correctionJ_coordinates]
  constructor
  · rw [Real.dist_eq] at hC
    exact hC.trans (by nlinarith [KJ.coe_nonneg])
  · rw [Real.dist_eq] at hJ
    exact hJ.trans (by nlinarith [KC.coe_nonneg])

end DGPS.Examples.ThreeSpeciesCircle
