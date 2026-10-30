import DGPS.Examples.ThreeSpeciesCircle.OrdinaryRootFormDomain
import DGPS.Structural.AmplitudeComparison

/-!
# Haar centering preserves the original native form domain

Subtracting the genuine Haar mean preserves the chosen weak gradient, the weighted
variance, and the Dirichlet energy. Thus a Haar-centered form argument applies to every
original native weighted H1 test, without restricting the public Poincare domain.
-/

open MeasureTheory

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The actual Haar-centered native test, built by the existing full-domain shift. -/
noncomputable def ordinaryRoot_haarCenteredTest (σ : AbsoluteDensity 1)
    (f : WeakH1Test (densityMeasure σ)) : WeakH1Test (densityMeasure σ) :=
  Structural.shiftTest (densityMeasure σ) f (∫ x, f.fn x ∂haar 1)

@[simp] theorem ordinaryRoot_haarCenteredTest_fn (σ : AbsoluteDensity 1)
    (f : WeakH1Test (densityMeasure σ)) (x : Torus 1) :
    (ordinaryRoot_haarCenteredTest σ f).fn x = f.fn x - ∫ y, f.fn y ∂haar 1 := rfl

@[simp] theorem ordinaryRoot_haarCenteredTest_grad (σ : AbsoluteDensity 1)
    (f : WeakH1Test (densityMeasure σ)) :
    (ordinaryRoot_haarCenteredTest σ f).grad = f.grad := rfl

/-- The centering uses the original function's finite Haar integral. -/
theorem ordinaryRoot_haarCenteredTest_mean_zero (σ : AbsoluteDensity 1)
    (f : WeakH1Test (densityMeasure σ)) :
    (∫ x, (ordinaryRoot_haarCenteredTest σ f).fn x ∂haar 1) = 0 := by
  change (∫ x, (f.fn x - ∫ y, f.fn y ∂haar 1) ∂haar 1) = 0
  rw [integral_sub f.isWeak.integrable (integrable_const _)]
  simp

/-- Weighted variance is unchanged even though the subtracted mean is the Haar mean. -/
theorem ordinaryRoot_haarCenteredTest_variance (σ : AbsoluteDensity 1)
    (f : WeakH1Test (densityMeasure σ)) :
    weightedVariance (densityMeasure σ) (ordinaryRoot_haarCenteredTest σ f).fn =
      weightedVariance (densityMeasure σ) f.fn := by
  let c : ℝ := ∫ x, f.fn x ∂haar 1
  have hm : (∫ x, (f.fn x - c) ∂(densityMeasure σ : Measure (Torus 1))) =
      (∫ x, f.fn x ∂(densityMeasure σ : Measure (Torus 1))) - c := by
    rw [integral_sub (f.isWeak.memLp.integrable (by norm_num)) (integrable_const c)]
    simp
  unfold weightedVariance
  change (∫ x, (f.fn x - c - ∫ y, (f.fn y - c)
    ∂(densityMeasure σ : Measure (Torus 1))) ^ 2
    ∂(densityMeasure σ : Measure (Torus 1))) = _
  rw [hm]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by ring

/-- The original gradient, hence the actual ENNReal energy, is unchanged. -/
theorem ordinaryRoot_haarCenteredTest_energy (σ : AbsoluteDensity 1)
    (f : WeakH1Test (densityMeasure σ)) :
    dirichletEnergy (densityMeasure σ) (ordinaryRoot_haarCenteredTest σ f) =
      dirichletEnergy (densityMeasure σ) f := rfl

end DGPS.Examples.ThreeSpeciesCircle
