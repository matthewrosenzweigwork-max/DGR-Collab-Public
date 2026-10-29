import LeanResearch.PeriodicAttractiveLogGas.GreenPointWeights
import LeanResearch.PeriodicAttractiveLogGas.LabelOccupations

/-! Actual Green point weights for a prescribed particle subfamily under the
source occupation cap. This is a point-law estimate for fixed sources;
conditional-version identification under the joint law is separate. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.CappedPointWeights

open MeshCells LabelOccupations GreenPointWeights ConditionalParameters

theorem sum_near_eq_sourceWeight {J N : ℕ} (η : LabelVector J N)
    (I : Finset (Fin N)) (S : Finset (MeshIndex J)) (w : Fin N → ℝ) :
    (∑ i : {i : I // η i ∈ S}, w i.1) = sourceWeight η I S w := by
  classical
  rw [← Finset.sum_subtype (p := fun i : I ↦ η i ∈ S)
    (Finset.univ.filter fun i : I ↦ η i ∈ S) (by simp) (fun i : I ↦ w i)]
  simp only [Finset.sum_filter]
  rw [Finset.sum_coe_sort I (fun i ↦ if η i ∈ S then w i else 0), sourceWeight_eq_sum_ite]

/-- Arbitrary nonnegative coefficients at most beta/N, including deletion of
any coefficient, and arbitrary prescribed source subfamilies. -/
theorem capped_pointWeight_bounds {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : LabelVector J N) (hη : OccupationCap (fixedDelta β₀ C₀ C₁) η)
    (I : Finset (Fin N)) (X : Configuration N)
    (hX : ∀ i ∈ I, X i ∈ closure (meshCell J hJ (η i)))
    (w : Fin N → ℝ) (hw₀ : ∀ i ∈ I, 0 ≤ w i) (hw : ∀ i ∈ I, w i ≤ β / N)
    (a : MeshIndex J) (b : Patch) :
    let μ := patchMeasure J hJ a b
    let y : I → Torus := fun i ↦ X i
    let v : I → ℝ := fun i ↦ w i
    Integrable (torusWeight y v) μ ∧ 0 < (∫ z, torusWeight y v z ∂μ) ∧
      IsProbabilityMeasure (pointLaw μ y v) ∧ MemLp (pointDensity μ y v) 4 μ ∧
      (∀ᵐ z ∂μ, fixedLower β₀ C₀ C₁ ≤ pointDensity μ y v z) ∧
      lpNorm (pointDensity μ y v) 4 μ ≤ fixedNorm β₀ C₀ C₁ := by
  classical
  have ht : ∑ i : I, w i ≤ β₀ := by
    rw [Finset.sum_coe_sort]
    exact total_source_weight_le hN hβ hβ₀ I hw
  have hn : ∑ i : {i : I // η i ∈ nearby J hJ (nearRadius β₀ C₁) a b},
      w i.1 ≤ 1 / 4 := by
    rw [sum_near_eq_sourceWeight]
    exact (sourceWeight_fixedDelta_le hN hβ hβ₀ hC₀ hη I _
      (card_nearby_le J hJ (nearRadius β₀ C₁) a b) hw).trans (by norm_num)
  exact pointWeight_bounds hJ (nearRadius_one_le β₀ C₁) hmesh a b
    (fun i : I ↦ X i) (fun i : I ↦ η i) (fun i ↦ hX i i.2)
    (fun i : I ↦ w i) (fun i ↦ hw₀ i i.2) hC₀ hC₁ hk₀ hk₁ ht hn

/-- When the distinguished particle is omitted, any valid completion
controls its fixed other-source family. This is not a definition of
two-endpoint admissibility, which still requires both completions. -/
theorem pointWeight_bounds_of_completion {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
    {β β₀ C₀ C₁ : ℝ} (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁)
    (hmesh : 8 * (nearRadius β₀ C₁ + 4) ≤ J)
    (η : LabelVector J N) (i : Fin N) (c : MeshIndex J)
    (hc : OccupationCap (fixedDelta β₀ C₀ C₁) (complete η i c))
    (I : Finset (Fin N)) (hi : i ∉ I) (X : Configuration N)
    (hX : ∀ k ∈ I, X k ∈ closure (meshCell J hJ (η k)))
    (w : Fin N → ℝ) (hw₀ : ∀ k ∈ I, 0 ≤ w k) (hw : ∀ k ∈ I, w k ≤ β / N)
    (a : MeshIndex J) (b : Patch) :
    let μ := patchMeasure J hJ a b
    let y : I → Torus := fun k ↦ X k
    let v : I → ℝ := fun k ↦ w k
    Integrable (torusWeight y v) μ ∧ 0 < (∫ z, torusWeight y v z ∂μ) ∧
      IsProbabilityMeasure (pointLaw μ y v) ∧ MemLp (pointDensity μ y v) 4 μ ∧
      (∀ᵐ z ∂μ, fixedLower β₀ C₀ C₁ ≤ pointDensity μ y v z) ∧
      lpNorm (pointDensity μ y v) 4 μ ≤ fixedNorm β₀ C₀ C₁ := by
  have hX' : ∀ k ∈ I, X k ∈ closure (meshCell J hJ (complete η i c k)) := by
    intro k hk
    have hki : k ≠ i := by intro he; subst k; exact hi hk
    rw [complete_of_ne η i k c hki]
    exact hX k hk
  exact capped_pointWeight_bounds hJ hN hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh
    (complete η i c) hc I X hX' w hw₀ hw a b

end PeriodicAttractiveLogGas.CappedPointWeights
