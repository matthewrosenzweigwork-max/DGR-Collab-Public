import DGPS.Examples.ThreeSpeciesCircle.InteractingFeedbackMeans
import DGPS.Examples.ThreeSpeciesCircle.InteractingForceSquareVariation

/-! Compact ACTUAL force-feedback contraction of the full cubic J derivative.
The finite matrix entries below are genuine gradient-product moments. -/

noncomputable section
open MeasureTheory Filter Topology

namespace DGPS.Examples.ThreeSpeciesCircle

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

/-- All force moments and the actual law vary. This compact physical feedback
formula follows from the proved cubic moment jet, with symmetry of genuine
gradient-product integrals. No frozen force or desired contraction is a premise. -/
theorem absoluteRootVariation_elementaryJ_feedback_hasDerivAt (h : ℝ) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    HasDerivAt (fun t : ℝ => elementaryJ h (absoluteRootVariation ρ hφ t))
      (absoluteRootMomentDerivative ρ φ (fun x =>
        (elementaryKprime h (densityMeasure ρ) x) ^ 2 + 2 * elementaryForceFeedback h ρ x)) 0 := by
  classical
  let κ := elementaryKprime h (densityMeasure ρ)
  let m := fun i : Fin 3 => ∫ x, f3 h i x ∂(densityMeasure ρ : Measure (Torus 1))
  let N := fun i j : Fin 3 => ∫ x, g3 h i x * g3 h j x ∂(densityMeasure ρ : Measure (Torus 1))
  let b := fun i : Fin 3 => ∫ x, κ x * g3 h i x ∂(densityMeasure ρ : Measure (Torus 1))
  let M := fun g : Torus 1 → ℝ => absoluteRootMomentDerivative ρ φ g
  have hκ : Continuous κ :=
    (isSmooth_elementaryKernelMean h (densityMeasure ρ)).continuous_coordPartial 0
  have hL := (isSmooth_elementaryForceFeedback h ρ).continuous_torus
  have hκsum : κ = fun x => ∑ i : Fin 3, (c3 i * m i) * g3 h i x := by
    funext x
    rw [show κ x = _ from elementaryKprime_three_features h ρ x]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp only [c3, m, f3, g3, momC, momS, momB, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    ring
  have hLsum : elementaryForceFeedback h ρ = fun x => ∑ i : Fin 3, (c3 i * b i) * f3 h i x := by
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
        (densityMeasure ρ : Measure (Torus 1)) :=
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
    rw [he, absoluteRootMomentDerivative_sum ρ hφ Finset.univ _
      (fun i _ => continuous_finsetSum _ (fun j _ => hc i j))]
    apply Finset.sum_congr rfl
    intro i _
    rw [absoluteRootMomentDerivative_sum ρ hφ Finset.univ _ (fun j _ => hc i j)]
    apply Finset.sum_congr rfl
    intro j _
    exact absoluteRootMomentDerivative_const_mul ρ hφ
      ((g3_continuous h i).mul (g3_continuous h j)) _
  have hML : M (elementaryForceFeedback h ρ) =
      ∑ i : Fin 3, (c3 i * b i) * M (f3 h i) := by
    dsimp only [M]
    rw [hLsum, absoluteRootMomentDerivative_sum ρ hφ Finset.univ _
      (fun i _ => ((f3_smooth h i).continuous_torus).const_mul _)]
    apply Finset.sum_congr rfl
    intro i _
    exact absoluteRootMomentDerivative_const_mul ρ hφ (f3_smooth h i).continuous_torus _
  have hjet := absoluteRootVariation_elementaryJ_hasDerivAt h ρ hφ
  convert hjet using 1
  rw [absoluteRootMomentDerivative_add ρ hφ
    (f := fun x => κ x ^ 2) (g := fun x => 2 * elementaryForceFeedback h ρ x)
    (hκ.pow 2) (hL.const_mul 2),
    absoluteRootMomentDerivative_const_mul ρ hφ hL]
  change M (fun x => κ x ^ 2) + 2 * M (elementaryForceFeedback h ρ) = _
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

end DGPS.Examples.ThreeSpeciesCircle
