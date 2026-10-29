import DGRHS.Gaussian.SharpnessCompression
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {X : Type*} [MeasurableSpace X]

/-- Actual conditional law on a positive-mass atom. -/
def sharpnessNormalizedAtom (μ : Measure X) (A : Set X) : Measure X :=
  (μ A)⁻¹ • μ.restrict A

lemma sharpnessNormalizedAtom_probability (μ : Measure X) [IsFiniteMeasure μ]
    (A : Set X) (hm : 0 < (μ A).toReal) : IsProbabilityMeasure (sharpnessNormalizedAtom μ A) := by
  have hz : μ A ≠ 0 := by intro hz; simp [hz] at hm
  refine ⟨?_⟩
  unfold sharpnessNormalizedAtom
  rw [Measure.smul_apply,Measure.restrict_apply MeasurableSet.univ]
  simp only [univ_inter,smul_eq_mul]
  exact ENNReal.inv_mul_cancel hz (measure_ne_top μ A)

lemma sharpnessNormalizedAtom_ae_mem (μ : Measure X) [IsFiniteMeasure μ]
    (A : Set X) (hA : MeasurableSet A) :
    ∀ᵐ x ∂sharpnessNormalizedAtom μ A, x ∈ A := by
  rw [ae_iff]
  change sharpnessNormalizedAtom μ A Aᶜ = 0
  unfold sharpnessNormalizedAtom
  rw [Measure.smul_apply,Measure.restrict_apply hA.compl]
  simp

lemma sharpnessNormalizedAtom_pair_integrable (μ : Measure X) [IsFiniteMeasure μ]
    (H : X × X → ℝ) (hH : Integrable H (μ.prod μ))
    (A B : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hmA : 0 < (μ A).toReal) (hmB : 0 < (μ B).toReal) :
    Integrable H ((sharpnessNormalizedAtom μ A).prod (sharpnessNormalizedAtom μ B)) := by
  have hzA : μ A ≠ 0 := by intro hz; simp [hz] at hmA
  have hzB : μ B ≠ 0 := by intro hz; simp [hz] at hmB
  have hi : Integrable H ((μ.restrict A).prod (μ.restrict B)) := by
    rw [Measure.prod_restrict]
    exact hH.restrict
  unfold sharpnessNormalizedAtom
  rw [Measure.prod_smul_left,Measure.prod_smul_right]
  exact (hi.smul_measure (by simp [hzB])).smul_measure (by simp [hzA])

/-- Genuine conditional two-coordinate expectation equals the actual
block average, with both normalization and properness proved. -/
lemma sharpnessNormalizedAtom_pair_integral (μ : Measure X) [IsFiniteMeasure μ]
    (H : X × X → ℝ) (A B : Set X) :
    (∫ p,H p ∂(sharpnessNormalizedAtom μ A).prod (sharpnessNormalizedAtom μ B)) =
      sharpnessAtomAverage μ H A B := by
  unfold sharpnessNormalizedAtom
  rw [Measure.prod_smul_left,Measure.prod_smul_right,integral_smul_measure,integral_smul_measure]
  simp only [smul_eq_mul,ENNReal.toReal_inv,sharpnessAtomAverage,sharpnessAtomIntegral,div_eq_mul_inv,
    _root_.mul_inv_rev]
  ring

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpnessNormalizedAtom_probability
#print axioms DGRHS.Gaussian.sharpnessNormalizedAtom_pair_integrable
#print axioms DGRHS.Gaussian.sharpnessNormalizedAtom_pair_integral
#check @DGRHS.Gaussian.sharpnessNormalizedAtom_pair_integrable
