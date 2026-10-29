import FullLabeledLSI.Examples.E01h5_Pointwise
import FullLabeledLSI.Examples.E01h5_Reduce
import FullLabeledLSI.Examples.E01h3_QC

/-!
# Lane D, Task B: Lemma 9.11 `analytic_concavity` (frozen statement)
-/

open MeasureTheory Complex UnitAddTorus Filter Topology
open scoped Real ComplexConjugate ContDiff ENNReal

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

/-- Pointwise (Dirac) bound. -/
theorem pointwise_bound (α β : Measure (Torus 1)) [IsFiniteMeasure α] [IsFiniteMeasure β]
    (hm : α Set.univ = β Set.univ) {ℓ : ℝ} (hℓ1 : ℓ ≤ aCos) (y : Torus 1) :
    (4 * intS (convS (dT (dT poissonKernel)) α β) α β +
        2 * ℓ * intS (convS poissonKernel α β) α β) +
      (2 * (convS (dT poissonKernel) α β y) ^ 2 +
        4 * intS (fun z => dT poissonKernel (z - y) * convS (dT poissonKernel) α β z) α β) ≤
      -(19 / 250) * (512 * π ^ 2 * Nsum α β 0) := by
  have h1 := A_le α β hℓ1 y
  have h2 := E_le α β hm y
  rw [Nsum_inv α β y] at h1 h2
  nlinarith

/-- Lemma 9.11, frozen statement. -/
theorem analytic_concavity (ρ α₁ β₁ : Measure (Torus 1)) (hρ : IsProbabilityMeasure ρ)
    (hα : IsFiniteMeasure α₁) (hβ : IsFiniteMeasure β₁) (hm : α₁ Set.univ = β₁ Set.univ)
    {ℓ : ℝ} (hℓ0 : 0 ≤ ℓ) (hℓ1 : ℓ ≤ aCos) :
    UintHess poissonKernel ℓ ρ α₁ β₁ ≤ -(19 / 250) * QC poissonKernel α₁ β₁ := by
  have hs : IsSmoothT poissonKernel := poisson_good.smooth
  have h0 : Continuous poissonKernel := continuous_of_smooth hs
  have hs1 : IsSmoothT (dT poissonKernel) := isSmoothT_dT hs
  have h1 : Continuous (dT poissonKernel) := continuous_of_smooth hs1
  have h2 : Continuous (dT (dT poissonKernel)) := continuous_of_smooth (isSmoothT_dT hs1)
  rw [UintHess_formula ℓ h0 h1 h2 ρ α₁ β₁, (QC_poisson α₁ β₁).2]
  unfold u2
  have hQ1c : Continuous (convS (dT poissonKernel) α₁ β₁) := continuous_convS h1 α₁ β₁
  have hfub := intS_cvM_mul (g := dT poissonKernel) (h := convS (dT poissonKernel) α₁ β₁) h1 hQ1c ρ α₁ β₁
  set A : ℝ := 4 * intS (convS (dT (dT poissonKernel)) α₁ β₁) α₁ β₁ +
        2 * ℓ * intS (convS poissonKernel α₁ β₁) α₁ β₁ with hA
  set E : Torus 1 → ℝ := fun y => 2 * (convS (dT poissonKernel) α₁ β₁ y) ^ 2 +
        4 * intS (fun z => dT poissonKernel (z - y) * convS (dT poissonKernel) α₁ β₁ z) α₁ β₁ with hE
  have cA : Continuous (fun y : Torus 1 => 2 * (convS (dT poissonKernel) α₁ β₁ y) ^ 2) :=
    continuous_const.mul (hQ1c.pow 2)
  have cB : Continuous (fun y : Torus 1 =>
      4 * intS (fun z => dT poissonKernel (z - y) * convS (dT poissonKernel) α₁ β₁ z) α₁ β₁) :=
    continuous_const.mul (continuous_intS_param h1 hQ1c α₁ β₁)
  have hEc : Continuous E := cA.add cB
  have iE : ∫ y, E y ∂ρ = 2 * ∫ x, convS (dT poissonKernel) α₁ β₁ x ^ 2 ∂ρ +
      4 * ∫ y, intS (fun z => dT poissonKernel (z - y) * convS (dT poissonKernel) α₁ β₁ z) α₁ β₁ ∂ρ := by
    simp only [hE]
    rw [integral_add (cA.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (cB.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)),
      integral_const_mul, integral_const_mul]
  have hint : 2 * (2 * intS (convS (dT (dT poissonKernel)) α₁ β₁) α₁ β₁ +
        ∫ x, convS (dT poissonKernel) α₁ β₁ x ^ 2 ∂ρ +
        2 * intS (fun x => cvM ρ (dT poissonKernel) x * convS (dT poissonKernel) α₁ β₁ x) α₁ β₁ +
        ℓ * intS (convS poissonKernel α₁ β₁) α₁ β₁) = ∫ y, (A + E y) ∂ρ := by
    rw [integral_add (integrable_const _) (hEc.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)), integral_const, iE, ← hfub]
    simp only [hA, probReal_univ, one_smul]
    ring
  rw [hint]
  have hbound : ∀ y, A + E y ≤ -(19 / 250) * (512 * π ^ 2 * ∑' m : ℕ, (m : ℝ) ^ 2 * (1 / 100 : ℝ) ^ m *
      (cI α₁ β₁ 0 (2 * (m : ℤ)) ^ 2 + sI α₁ β₁ 0 (2 * (m : ℤ)) ^ 2)) := fun y =>
    pointwise_bound α₁ β₁ hm hℓ1 y
  calc ∫ y, (A + E y) ∂ρ ≤ ∫ _y, -(19 / 250) * (512 * π ^ 2 * ∑' m : ℕ, (m : ℝ) ^ 2 * (1 / 100 : ℝ) ^ m *
      (cI α₁ β₁ 0 (2 * (m : ℤ)) ^ 2 + sI α₁ β₁ 0 (2 * (m : ℤ)) ^ 2)) ∂ρ :=
        integral_mono ((integrable_const _).add (hEc.integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _))) (integrable_const _) hbound
    _ = _ := by simp

end SharpLSI.FL.Ex.LaneD
