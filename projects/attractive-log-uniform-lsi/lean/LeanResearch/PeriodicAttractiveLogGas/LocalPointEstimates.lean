import LeanResearch.PeriodicAttractiveLogGas.TorusPatchDensity
import LeanResearch.PeriodicAttractiveLogGas.CappedPointWeights

/-! Functional inequalities for the actual Green point laws, completing
the analytic assembly in source Lemma 3.3. The capped specialization applies
to fixed-source one-coordinate and probe laws. The conditional-version
identity with the joint particle law is a separate assertion. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.LocalPointEstimates

open MeshCells GreenPointWeights ConditionalParameters PointWeightDensity LabelOccupations

def shape : Patch → TorusPatchDensity.Shape
  | .cell => .cell
  | .edge j => .edge j

theorem baseMeasure_shape (J : ℕ) (hJ : 0 < J) (a : MeshIndex J) (b : Patch) :
    TorusPatchDensity.baseMeasure (shape b) J hJ a = patchMeasure J hJ a b := by
  cases b <;> rfl

variable {ι : Type*} [Fintype ι]

theorem pointLaw_estimates {J : ℕ} (hJ : 0 < J) (a : MeshIndex J) (b : Patch)
    (y : ι → Torus) (w : ι → ℝ) {c K : ℝ} (hc : 0 < c)
    (hprob : IsProbabilityMeasure (pointLaw (patchMeasure J hJ a b) y w))
    (hlower : ∀ᵐ z ∂patchMeasure J hJ a b, c ≤ pointDensity (patchMeasure J hJ a b) y w z)
    (hmem : MemLp (pointDensity (patchMeasure J hJ a b) y w) 4 (patchMeasure J hJ a b))
    (hnorm : lpNorm (pointDensity (patchMeasure J hJ a b) y w) 4 (patchMeasure J hJ a b) ≤ K)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (TorusPatchDensity.domain (shape b) J hJ a))) :
    TorusPatchDensity.Estimates (RectangleDilation.sobolevConstant (TorusPatchDensity.kind (shape b)))
      J c 4 K (pointLaw (patchMeasure J hJ a b) y w) f := by
  let μ := patchMeasure J hJ a b
  let p := pointDensity μ y w
  have he : TorusPatchDensity.law (shape b) J hJ a p = pointLaw μ y w := by
    rw [TorusPatchDensity.law, baseMeasure_shape]
    rfl
  let : IsProbabilityMeasure (TorusPatchDensity.law (shape b) J hJ a p) := by
    rw [he]
    exact hprob
  have hl : ∀ᵐ z ∂TorusPatchDensity.baseMeasure (shape b) J hJ a, c ≤ p z := by
    simpa only [baseMeasure_shape] using hlower
  have hm : MemLp p (ENNReal.ofReal (4 : ℝ)) (TorusPatchDensity.baseMeasure (shape b) J hJ a) := by
    simpa only [baseMeasure_shape, ENNReal.ofReal_ofNat] using hmem
  have hn : lpNorm p (ENNReal.ofReal (4 : ℝ)) (TorusPatchDensity.baseMeasure (shape b) J hJ a) ≤ K := by
    simpa only [baseMeasure_shape, ENNReal.ofReal_ofNat] using hnorm
  have h := TorusPatchDensity.density_estimates (shape b) J hJ a p hc hl (by norm_num) hm hn hf
  simpa only [he] using h

/-- The functional-inequality sentence of source Lemma 3.3, with every
density and probability premise discharged by the actual Green weight. -/
theorem pointWeight_functional_estimates {J R : ℕ} (hJ : 0 < J) (hR : 1 ≤ R)
    (hmesh : 8 * (R + 4) ≤ J) (a : MeshIndex J) (b : Patch)
    (y : ι → Torus) (labels : ι → MeshIndex J)
    (hy : ∀ i, y i ∈ closure (meshCell J hJ (labels i))) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    {β₀ C₀ C₁ : ℝ} (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hk₀ : ∀ z : Torus, z ≠ 0 →
      |regularGreenRepresentative z + Real.log (torusEuclideanNorm z)| ≤ C₀)
    (hk₁ : GreenFarOscillation.KernelGradientBound C₁) (htotal : ∑ i, w i ≤ β₀)
    (hnear : ∑ i : {i // labels i ∈ nearby J hJ R a b}, w i ≤ 1 / 4)
    {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (TorusPatchDensity.domain (shape b) J hJ a))) :
    TorusPatchDensity.Estimates (RectangleDilation.sobolevConstant (TorusPatchDensity.kind (shape b))) J
      (sourceLowerConstant (distanceBound R) (oscillationBound β₀ C₁ R) C₀) 4
      (sourceNormConstant (distanceBound R) (oscillationBound β₀ C₁ R) C₀)
      (pointLaw (patchMeasure J hJ a b) y w) f := by
  have h := pointWeight_bounds hJ hR hmesh a b y labels hy w hw hC₀ hC₁ hk₀ hk₁ htotal hnear
  have hc := sourceLowerConstant_pos (lt_of_lt_of_le zero_lt_one (distanceBound_one_le hR))
    (oscillationBound β₀ C₁ R) C₀
  exact pointLaw_estimates hJ a b y w hc h.2.2.1 h.2.2.2.2.1 h.2.2.2.1 h.2.2.2.2.2 hf

/-- The same exact constants for arbitrary particle subfamilies under the
fixed source occupation cap. There is no positional separation hypothesis. -/
theorem capped_pointWeight_functional_estimates {J N : ℕ} (hJ : 0 < J) (hN : 0 < N)
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
    (a : MeshIndex J) (b : Patch) {f : Torus → ℝ} {L : ℝ≥0}
    (hf : PhysicalLipschitzOn L f (closure (TorusPatchDensity.domain (shape b) J hJ a))) :
    TorusPatchDensity.Estimates (RectangleDilation.sobolevConstant (TorusPatchDensity.kind (shape b)))
      J (fixedLower β₀ C₀ C₁) 4 (fixedNorm β₀ C₀ C₁)
      (pointLaw (patchMeasure J hJ a b) (fun i : I ↦ X i) (fun i : I ↦ w i)) f := by
  have h := CappedPointWeights.capped_pointWeight_bounds hJ hN hβ hβ₀ hC₀ hC₁ hk₀ hk₁ hmesh
    η hη I X hX w hw₀ hw a b
  have hc : 0 < fixedLower β₀ C₀ C₁ := sourceLowerConstant_pos
    (lt_of_lt_of_le zero_lt_one (distanceBound_one_le (nearRadius_one_le β₀ C₁))) _ _
  exact pointLaw_estimates hJ a b (fun i : I ↦ X i) (fun i : I ↦ w i)
    hc h.2.2.1 h.2.2.2.2.1 h.2.2.2.1 h.2.2.2.2.2 hf

end PeriodicAttractiveLogGas.LocalPointEstimates
