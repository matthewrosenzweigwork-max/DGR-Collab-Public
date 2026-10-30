import DGPS.Examples.ThreeSpeciesCircle.InteractingHolderFeedback

/-! The factual finite expansion and uniformly bounded probability coefficients
of the actual common Euler field. This packet does not infer derivative bounds
from a Holder norm; derivatives of its fixed smooth basis remain explicit. -/

noncomputable section
open MeasureTheory Filter Topology
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

def elementaryFeedbackMoment (h : ℝ) (ρ : AbsoluteDensity 1) (i : Fin 3) : ℝ :=
  ∫ x, ![featureC h, featureS h, featureB h] i x ∂(densityMeasure ρ : Measure (Torus 1))

def elementaryFeedbackGeneratorMoment (h : ℝ) (ρ : AbsoluteDensity 1) (i : Fin 3) : ℝ :=
  ∫ x, elementaryFeatureGenerator h (![featureC h, featureS h, featureB h] i) x
    ∂(densityMeasure ρ : Measure (Torus 1))

def elementaryFeedbackForceMoment (h : ℝ) (ρ : AbsoluteDensity 1) (i : Fin 3) : ℝ :=
  ∫ x, elementaryKprime h (densityMeasure ρ) x *
    coordPartial 0 (![featureC h, featureS h, featureB h] i) x
      ∂(densityMeasure ρ : Measure (Torus 1))

/-- The physical finite expansion with genuine changing-law coefficients. -/
theorem elementaryEulerHolder_finite_expansion (h ε r : ℝ) (ρ : AbsoluteDensity 1) :
    let c : Fin 3 → ℝ := ![kAlpha, kAlpha, -kBeta]
    let K := ∑ i : Fin 3, (c i * elementaryFeedbackMoment h ρ i) • interactingHolderFeature h i
    let D := ∑ i : Fin 3, (c i * elementaryFeedbackMoment h ρ i) • interactingHolderDerivative h i
    let A := ∑ i : Fin 3, (c i * elementaryFeedbackMoment h ρ i) • interactingHolderGenerator h i
    let LA := ∑ i : Fin 3, (c i * elementaryFeedbackGeneratorMoment h ρ i) • interactingHolderFeature h i
    let LP := ∑ i : Fin 3, (c i * elementaryFeedbackForceMoment h ρ i) • interactingHolderFeature h i
    elementaryEulerHolder h ε r ρ = (2 * ε) • (A + LA - r • K) + ε ^ 2 • (D * D + (2 : ℝ) • LP) := by
  rfl

private theorem point_bound (F : PeriodicHolder_STR02968) (t : ℝ) : |F.val t| ≤ ‖F‖ := by
  rw [PeriodicHolder_STR02968.norm_def]
  exact (F.isPerHolder.abs_le_supNorm t).trans
    (le_add_of_nonneg_right (holderSemi_nonneg_STR02968 _ _))

private theorem native_bound {F : PeriodicHolder_STR02968} {f : Torus 1 → ℝ}
    (heq : ∀ t, F.val t = f (angEquiv.symm (t : AngCircle))) (x : Torus 1) : |f x| ≤ ‖F‖ := by
  have he := heq (angSec (angEquiv x))
  rw [coe_angSec_STR02962, angEquiv.symm_apply_apply] at he
  rw [← he]
  exact point_bound F _

private theorem probability_moment_bound (ν : ProbabilityMeasure (Torus 1)) {f : Torus 1 → ℝ}
    {B : ℝ} (hf : Continuous f) (hb : ∀ x, |f x| ≤ B) :
    |∫ x, f x ∂(ν : Measure (Torus 1))| ≤ B := by
  have hi := hf.integrable_of_hasCompactSupport (μ := (ν : Measure (Torus 1)))
    (HasCompactSupport.of_compactSpace _)
  calc
    _ ≤ ∫ x, |f x| ∂(ν : Measure (Torus 1)) := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := (ν : Measure (Torus 1))) f
    _ ≤ ∫ _ : Torus 1, B ∂(ν : Measure (Torus 1)) := integral_mono hi.abs (integrable_const B) hb
    _ = B := by simp

/-- Constants precede every density and coefficient. All three families are
actual probability moments of fixed features, generator images, and force
products. No information bound, minimizer, rate, or coupling is an input. -/
theorem elementaryEulerHolder_coefficient_bounds {h : ℝ} (hh : 0 < h) :
    ∃ B M : ℝ, 0 < B ∧ 0 ≤ M ∧ ∀ ρ : AbsoluteDensity 1, ∀ i : Fin 3,
      |elementaryFeedbackMoment h ρ i| ≤ B ∧
        |elementaryFeedbackGeneratorMoment h ρ i| ≤ B ∧
          |elementaryFeedbackForceMoment h ρ i| ≤ M * B := by
  let f : Fin 3 → Torus 1 → ℝ := ![featureC h, featureS h, featureB h]
  let c : Fin 3 → ℝ := ![kAlpha, kAlpha, -kBeta]
  let B := 1 + ∑ i : Fin 3,
    (‖interactingHolderFeature h i‖ + ‖interactingHolderDerivative h i‖ + ‖interactingHolderGenerator h i‖)
  have hB : 0 < B := by dsimp [B]; positivity
  have hb (i : Fin 3) : ‖interactingHolderFeature h i‖ ≤ B ∧
      ‖interactingHolderDerivative h i‖ ≤ B ∧ ‖interactingHolderGenerator h i‖ ≤ B := by
    have hi : ‖interactingHolderFeature h i‖ + ‖interactingHolderDerivative h i‖ +
        ‖interactingHolderGenerator h i‖ ≤ ∑ j : Fin 3,
          (‖interactingHolderFeature h j‖ + ‖interactingHolderDerivative h j‖ + ‖interactingHolderGenerator h j‖) :=
      Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin 3 => ‖interactingHolderFeature h j‖ +
          ‖interactingHolderDerivative h j‖ + ‖interactingHolderGenerator h j‖)
        (fun j _ => by positivity) (Finset.mem_univ i)
    dsimp only [B]
    constructor
    · linarith [norm_nonneg (interactingHolderDerivative h i), norm_nonneg (interactingHolderGenerator h i)]
    · constructor <;> linarith [norm_nonneg (interactingHolderFeature h i),
        norm_nonneg (interactingHolderDerivative h i), norm_nonneg (interactingHolderGenerator h i)]
  let M := (∑ i : Fin 3, |c i|) * B * B
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hs (i : Fin 3) : IsSmoothPeriodic (f i) := by
    fin_cases i
    · exact isSmooth_featureC h
    · exact isSmooth_featureS h
    · exact isSmooth_featureB h
  have hfB (i : Fin 3) (x : Torus 1) : |f i x| ≤ B :=
    (native_bound (fun t => (interactingHolderFeature_native hh i t).1) x).trans (hb i).1
  have hdB (i : Fin 3) (x : Torus 1) : |coordPartial 0 (f i) x| ≤ B :=
    (native_bound (fun t => (interactingHolderFeature_native hh i t).2.1) x).trans (hb i).2.1
  have haB (i : Fin 3) (x : Torus 1) : |elementaryFeatureGenerator h (f i) x| ≤ B :=
    (native_bound (fun t => (interactingHolderFeature_native hh i t).2.2) x).trans (hb i).2.2
  refine ⟨B, M, hB, hM, fun ρ i => ?_⟩
  have hmB (j : Fin 3) : |elementaryFeedbackMoment h ρ j| ≤ B :=
    probability_moment_bound (densityMeasure ρ) (hs j).continuous_torus (hfB j)
  have hκ (x : Torus 1) : |elementaryKprime h (densityMeasure ρ) x| ≤ M := by
    have he : elementaryKprime h (densityMeasure ρ) x =
        ∑ j : Fin 3, c j * elementaryFeedbackMoment h ρ j * coordPartial 0 (f j) x := by
      rw [elementaryKprime_three_features]
      simp only [Fin.sum_univ_three]
      dsimp only [c, f, elementaryFeedbackMoment, momC, momS, momB]
      simp only [Matrix.cons_val_zero', Matrix.cons_val_succ', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
      ring
    rw [he]
    calc
      _ ≤ ∑ j : Fin 3, |c j * elementaryFeedbackMoment h ρ j * coordPartial 0 (f j) x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin 3, |c j| * B * B := Finset.sum_le_sum fun j _ => by
        rw [abs_mul, abs_mul]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hmB j) (abs_nonneg _)) (hdB j x)
          (abs_nonneg _) (mul_nonneg (abs_nonneg _) hB.le)
      _ = M := by dsimp only [M]; rw [Finset.sum_mul, Finset.sum_mul]
  refine ⟨hmB i, probability_moment_bound (densityMeasure ρ)
    (continuous_elementaryFeatureGenerator h _ (hs i)) (haB i), ?_⟩
  apply probability_moment_bound (densityMeasure ρ)
    (((isSmooth_elementaryKernelMean h (densityMeasure ρ)).continuous_coordPartial 0).mul
      ((hs i).continuous_coordPartial 0))
  intro x
  change |elementaryKprime h (densityMeasure ρ) x * coordPartial 0 (f i) x| ≤ M * B
  rw [abs_mul]
  exact mul_le_mul (hκ x) (hdB i x) (abs_nonneg _) hM

end DGPS.Examples.ThreeSpeciesCircle
