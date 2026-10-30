import DGPS.Examples.ThreeSpeciesCircle.FiniteSpeciesCorrections
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarWeakEuler
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-! The ACTUAL feedback field is a finite polynomial with bounded continuous
coefficients. Coupling is factored out before taking the compact-box derivative
bound; all constants precede the original densities, rates and couplings. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

private abbrev FeedbackIndex := Fin 2 ⊕ (Fin 6 ⊕ (Fin 3 × Fin 3))
private def ff (h : ℝ) : Fin 3 → Torus 1 → ℝ := ![featureC h, featureS h, featureB h]
private def cc : Fin 3 → ℝ := ![kAlpha, kAlpha, -kBeta]
private def gi : Fin 3 → Fin 6 := ![3, 4, 5]

private theorem ff_smooth (h : ℝ) (i : Fin 3) : IsSmoothPeriodic (ff h i) := by
  fin_cases i
  · exact isSmooth_featureC h
  · exact isSmooth_featureS h
  · exact isSmooth_featureB h

private def bf (h : ℝ) (i : Fin 3) : BoundedContinuousFunction (Torus 1) ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨ff h i, (ff_smooth h i).continuous_torus⟩
private def bd (h : ℝ) (i : Fin 3) : BoundedContinuousFunction (Torus 1) ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨coordPartial 0 (ff h i), (ff_smooth h i).continuous_coordPartial 0⟩
private def ba (h : ℝ) (i : Fin 3) : BoundedContinuousFunction (Torus 1) ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨elementaryFeatureGenerator h (ff h i),
    continuous_elementaryFeatureGenerator h _ (ff_smooth h i)⟩

private theorem bf_apply (h : ℝ) (i : Fin 3) (y : Torus 1) :
    bf h i y = ff h i y := rfl
private theorem bd_apply (h : ℝ) (i : Fin 3) (y : Torus 1) :
    bd h i y = coordPartial 0 (ff h i) y := rfl
private theorem ba_apply (h : ℝ) (i : Fin 3) (y : Torus 1) :
    ba h i y = elementaryFeatureGenerator h (ff h i) y := rfl

private def mx (x : FeedbackIndex → ℝ) (i : Fin 3) : ℝ :=
  x (.inr (.inl (Fin.castLE (by norm_num) i)))
private def ax (x : FeedbackIndex → ℝ) (i : Fin 3) : ℝ := x (.inr (.inl (gi i)))
private def nx (x : FeedbackIndex → ℝ) (i j : Fin 3) : ℝ := x (.inr (.inr (i, j)))
private def feedbackK (h : ℝ) (x : FeedbackIndex → ℝ) : BoundedContinuousFunction (Torus 1) ℝ :=
  ∑ i : Fin 3, (cc i * mx x i) • bf h i
private def feedbackD (h : ℝ) (x : FeedbackIndex → ℝ) : BoundedContinuousFunction (Torus 1) ℝ :=
  ∑ i : Fin 3, (cc i * mx x i) • bd h i
private def feedbackA (h : ℝ) (x : FeedbackIndex → ℝ) : BoundedContinuousFunction (Torus 1) ℝ :=
  ∑ i : Fin 3, (cc i * mx x i) • ba h i
private def feedbackLA (h : ℝ) (x : FeedbackIndex → ℝ) : BoundedContinuousFunction (Torus 1) ℝ :=
  ∑ i : Fin 3, (cc i * ax x i) • bf h i
private def feedbackLP (h : ℝ) (x : FeedbackIndex → ℝ) : BoundedContinuousFunction (Torus 1) ℝ :=
  ∑ i : Fin 3, (cc i * ∑ j : Fin 3, (cc j * mx x j) * nx x i j) • bf h i

private def feedbackPolynomial (h : ℝ) (x : FeedbackIndex → ℝ) : BoundedContinuousFunction (Torus 1) ℝ :=
  (2 : ℝ) • (feedbackA h x + feedbackLA h x - x (.inl 0) • feedbackK h x) +
    x (.inl 1) • (feedbackD h x * feedbackD h x + (2 : ℝ) • feedbackLP h x)

private def feedbackCoordinates (h r ε : ℝ) (ρ : AbsoluteDensity 1) : FeedbackIndex → ℝ
  | .inl i => if i = 0 then r else ε
  | .inr k => ∫ y, elementaryCorrectionObservable h k y ∂(densityMeasure ρ : Measure (Torus 1))

private theorem mx_native (h r ε : ℝ) (ρ : AbsoluteDensity 1) (i : Fin 3) :
    mx (feedbackCoordinates h r ε ρ) i = ∫ y, ff h i y ∂(densityMeasure ρ : Measure (Torus 1)) := by
  fin_cases i <;> rfl
private theorem ax_native (h r ε : ℝ) (ρ : AbsoluteDensity 1) (i : Fin 3) :
    ax (feedbackCoordinates h r ε ρ) i =
      ∫ y, elementaryFeatureGenerator h (ff h i) y ∂(densityMeasure ρ : Measure (Torus 1)) := by
  fin_cases i <;> rfl
private theorem nx_native (h r ε : ℝ) (ρ : AbsoluteDensity 1) (i j : Fin 3) :
    nx (feedbackCoordinates h r ε ρ) i j =
      ∫ y, coordPartial 0 (ff h i) y * coordPartial 0 (ff h j) y
        ∂(densityMeasure ρ : Measure (Torus 1)) := by rfl

private theorem feedbackD_native (h r ε : ℝ) (ρ : AbsoluteDensity 1) (y : Torus 1) :
    feedbackD h (feedbackCoordinates h r ε ρ) y = elementaryKprime h (densityMeasure ρ) y := by
  rw [elementaryKprime_three_features]
  simp only [feedbackD, Fin.sum_univ_three, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.smul_apply, smul_eq_mul, bd_apply,
    mx_native, cc, ff, momC, momS, momB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  ring

private theorem force_moments (h r ε : ℝ) (ρ : AbsoluteDensity 1) (i : Fin 3) :
    (∫ y, elementaryKprime h (densityMeasure ρ) y * coordPartial 0 (ff h i) y
      ∂(densityMeasure ρ : Measure (Torus 1))) =
      ∑ j : Fin 3, (cc j * mx (feedbackCoordinates h r ε ρ) j) *
        nx (feedbackCoordinates h r ε ρ) i j := by
  have he (y : Torus 1) : elementaryKprime h (densityMeasure ρ) y * coordPartial 0 (ff h i) y =
      ∑ j : Fin 3, (cc j * mx (feedbackCoordinates h r ε ρ) j) *
        (coordPartial 0 (ff h i) y * coordPartial 0 (ff h j) y) := by
    rw [← feedbackD_native h r ε ρ y]
    simp only [feedbackD, Fin.sum_univ_three, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul, bd_apply]
    ring
  have hi (j : Fin 3) : Integrable
      (fun y => (cc j * mx (feedbackCoordinates h r ε ρ) j) *
        (coordPartial 0 (ff h i) y * coordPartial 0 (ff h j) y))
      (densityMeasure ρ : Measure (Torus 1)) :=
    ((((ff_smooth h i).continuous_coordPartial 0).mul
      ((ff_smooth h j).continuous_coordPartial 0)).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)).const_mul _
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => hi j)]
  simp only [integral_const_mul, nx_native]

private theorem feedbackPolynomial_native (h r ε : ℝ) (ρ : AbsoluteDensity 1) (y : Torus 1) :
    elementaryEulerCorrection h ε r ρ y = ε * feedbackPolynomial h (feedbackCoordinates h r ε ρ) y := by
  have hLP : feedbackLP h (feedbackCoordinates h r ε ρ) y = elementaryForceFeedback h ρ y := by
    have hcoeff : feedbackLP h (feedbackCoordinates h r ε ρ) =
        ∑ i : Fin 3, (cc i * ∫ z, elementaryKprime h (densityMeasure ρ) z * coordPartial 0 (ff h i) z
          ∂(densityMeasure ρ : Measure (Torus 1))) • bf h i := by
      unfold feedbackLP
      apply Finset.sum_congr rfl
      intro i _
      rw [force_moments h r ε ρ i]
    rw [hcoeff]
    simp only [Fin.sum_univ_three, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul, bf_apply]
    simp only [elementaryForceFeedback, cc, ff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hLA : feedbackLA h (feedbackCoordinates h r ε ρ) y = elementaryGeneratorFeedback h ρ y := by
    simp only [feedbackLA, Fin.sum_univ_three, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul, bf_apply,
      ax_native]
    simp only [elementaryGeneratorFeedback, cc, ff, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hA : feedbackA h (feedbackCoordinates h r ε ρ) y = elementaryAK h (densityMeasure ρ) y := by
    rw [elementaryAK_moments]
    simp only [feedbackA, Fin.sum_univ_three, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul, ba_apply,
      mx_native, cc, ff, momC, momS, momB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hK : feedbackK h (feedbackCoordinates h r ε ρ) y = elementaryKernelMean h (densityMeasure ρ) y := by
    simp only [feedbackK, Fin.sum_univ_three, BoundedContinuousFunction.add_apply,
      BoundedContinuousFunction.smul_apply, smul_eq_mul, bf_apply,
      mx_native, elementaryKernelMean, cc, ff, momC, momS, momB, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    ring
  have hr0 : feedbackCoordinates h r ε ρ (.inl 0) = r := by simp [feedbackCoordinates]
  have he1 : feedbackCoordinates h r ε ρ (.inl 1) = ε := by simp [feedbackCoordinates]
  simp only [feedbackPolynomial, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.sub_apply, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.mul_apply, smul_eq_mul, hr0, he1, hLP, hLA, hA, hK, feedbackD_native]
  unfold elementaryEulerCorrection
  ring

private theorem feedbackPolynomial_smooth (h : ℝ) : ContDiff ℝ 1 (feedbackPolynomial h) := by
  unfold feedbackPolynomial feedbackK feedbackD feedbackA feedbackLA feedbackLP mx ax nx
  fun_prop

/-- The actual field difference has a constant BEFORE all bounded rates,
couplings and original densities. The coupling factor is retained exactly. -/
theorem elementaryEulerCorrection_moment_lipschitz (h R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, |r| ≤ R → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ (ρ σ : AbsoluteDensity 1) (δ : ℝ), 0 ≤ δ →
        (∀ i : Fin 6 ⊕ (Fin 3 × Fin 3),
          |(∫ y, elementaryCorrectionObservable h i y ∂(densityMeasure ρ : Measure (Torus 1))) -
            (∫ y, elementaryCorrectionObservable h i y ∂(densityMeasure σ : Measure (Torus 1)))| ≤ δ) →
          ∀ y : Torus 1,
            |elementaryEulerCorrection h ε r ρ y - elementaryEulerCorrection h ε r σ y| ≤ K * ε * δ := by
  obtain ⟨M, hM, hobs⟩ := elementaryCorrection_coordinates_bound h
  let B := R + M + 1
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨L, hLip⟩ := (feedbackPolynomial_smooth h).contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0 : FeedbackIndex → ℝ) B) (isCompact_closedBall 0 B)
  have hmoment (ρ : AbsoluteDensity 1) (k : Fin 6 ⊕ (Fin 3 × Fin 3)) :
      ‖∫ y, elementaryCorrectionObservable h k y ∂(densityMeasure ρ : Measure (Torus 1))‖ ≤ M := by
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := (densityMeasure ρ : Measure (Torus 1)))
        (f := elementaryCorrectionObservable h k) (C := M)
        (Filter.Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hobs k y))
  refine ⟨(L : ℝ) + 1, by positivity, fun r hr ε hε he1 ρ σ δ hδ hdiff y => ?_⟩
  have hn (τ : AbsoluteDensity 1) : ‖feedbackCoordinates h r ε τ‖ ≤ B := by
    apply (pi_norm_le_iff_of_nonneg hB).2
    intro i
    cases i with
    | inl i =>
      fin_cases i
      · simpa [feedbackCoordinates, Real.norm_eq_abs] using
          hr.trans (show R ≤ B by dsimp only [B]; linarith only [hM])
      · simpa [feedbackCoordinates, Real.norm_eq_abs, abs_of_nonneg hε] using
          he1.trans (show (1 : ℝ) ≤ B by dsimp only [B]; linarith only [hM, hR])
    | inr k =>
      exact (hmoment τ k).trans (show M ≤ B by dsimp only [B]; linarith only [hR])
  have hm (τ : AbsoluteDensity 1) : feedbackCoordinates h r ε τ ∈ Metric.closedBall 0 B := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hn τ
  have hd : dist (feedbackCoordinates h r ε ρ) (feedbackCoordinates h r ε σ) ≤ δ := by
    rw [dist_eq_norm]
    apply (pi_norm_le_iff_of_nonneg hδ).2
    intro i
    cases i with
    | inl i => fin_cases i <;> simpa [feedbackCoordinates] using hδ
    | inr k => simpa only [feedbackCoordinates, Pi.sub_apply, Real.norm_eq_abs] using hdiff k
  have hpoly := (hLip.dist_le_mul _ (hm ρ) _ (hm σ)).trans
    (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
  rw [dist_eq_norm] at hpoly
  have hpoint : |feedbackPolynomial h (feedbackCoordinates h r ε ρ) y -
      feedbackPolynomial h (feedbackCoordinates h r ε σ) y| ≤ (L : ℝ) * δ := by
    have hp := (feedbackPolynomial h (feedbackCoordinates h r ε ρ) -
      feedbackPolynomial h (feedbackCoordinates h r ε σ)).norm_coe_le_norm y
    have hp' : |feedbackPolynomial h (feedbackCoordinates h r ε ρ) y -
        feedbackPolynomial h (feedbackCoordinates h r ε σ) y| ≤
          ‖feedbackPolynomial h (feedbackCoordinates h r ε ρ) - feedbackPolynomial h (feedbackCoordinates h r ε σ)‖ := by
      simpa only [BoundedContinuousFunction.sub_apply, Real.norm_eq_abs] using hp
    exact hp'.trans hpoly
  rw [feedbackPolynomial_native, feedbackPolynomial_native, ← mul_sub, abs_mul, abs_of_nonneg hε]
  calc _ ≤ ε * ((L : ℝ) * δ) := mul_le_mul_of_nonneg_left hpoint hε
    _ ≤ ((L : ℝ) + 1) * ε * δ := by nlinarith only [mul_nonneg hε hδ]

/-- Actual original-density L1 distance controls feedback differences, uniformly
before every density, bounded rate and coupling; no field-Lipschitz premise. -/
theorem elementaryEulerCorrection_density_lipschitz (h R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 < K ∧ ∀ r : ℝ, |r| ≤ R → ∀ ε : ℝ, 0 ≤ ε → ε ≤ 1 →
      ∀ (ρ σ : AbsoluteDensity 1) (y : Torus 1),
        |elementaryEulerCorrection h ε r ρ y - elementaryEulerCorrection h ε r σ y| ≤
          K * ε * (∫ x, |ρ.density x - σ.density x| ∂haar 1) := by
  obtain ⟨M, hM, hobs⟩ := elementaryCorrection_coordinates_bound h
  obtain ⟨K, hK, hLip⟩ := elementaryEulerCorrection_moment_lipschitz h R hR
  refine ⟨K * M, mul_pos hK hM, fun r hr ε hε he1 ρ σ y => ?_⟩
  let N := ∫ x, |ρ.density x - σ.density x| ∂haar 1
  have hN : 0 ≤ N := integral_nonneg fun x => abs_nonneg _
  have hΔ : Integrable (fun x => |ρ.density x - σ.density x|) (haar 1) :=
    (ρ.integrable_density.sub σ.integrable_density).abs
  have hmom (i : Fin 6 ⊕ (Fin 3 × Fin 3)) :
      |(∫ x, elementaryCorrectionObservable h i x ∂(densityMeasure ρ : Measure (Torus 1))) -
        (∫ x, elementaryCorrectionObservable h i x ∂(densityMeasure σ : Measure (Torus 1)))| ≤ M * N := by
    let g := elementaryCorrectionObservable h i
    have hg := continuous_elementaryCorrectionObservable h i
    have hiρ : Integrable (fun x => ρ.density x * g x) (haar 1) :=
      ρ.integrable_density.mul_bdd hg.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hobs i x)
    have hiσ : Integrable (fun x => σ.density x * g x) (haar 1) :=
      σ.integrable_density.mul_bdd hg.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hobs i x)
    rw [Structural.budget_integral_densityMeasure, Structural.budget_integral_densityMeasure,
      ← integral_sub hiρ hiσ]
    calc _ ≤ ∫ x, |ρ.density x * g x - σ.density x * g x| ∂haar 1 := abs_integral_le_integral_abs
      _ ≤ ∫ x, M * |ρ.density x - σ.density x| ∂haar 1 := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _) (hΔ.const_mul M)
        exact Filter.Eventually.of_forall fun x => by
          change |ρ.density x * g x - σ.density x * g x| ≤ M * |ρ.density x - σ.density x|
          rw [← sub_mul, abs_mul]
          exact (mul_le_mul_of_nonneg_left (hobs i x) (abs_nonneg _)).trans_eq (by ring)
      _ = M * N := integral_const_mul _ _
  have he := hLip r hr ε hε he1 ρ σ (M * N) (mul_nonneg hM.le hN) hmom y
  convert he using 1 <;> ring

end DGPS.Examples.ThreeSpeciesCircle
