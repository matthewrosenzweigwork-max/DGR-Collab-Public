import DGRHS.Gaussian.FiniteEvaluation
import Mathlib.Probability.Moments.ComplexMGF

/-!
Actual finite iid standard Gaussian frequency characters for the Gaussian cutoff
permitted in arxiv2609.02743v1, lem:HCRStruncations. Source SHA256:
6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c.
This first unit proves the exact frequency integral; scale-mixture Hilbert
membership, centering, and identification with the physical truncated Riesz
kernel are subsequent obligations. No frequency law is assumed.
-/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def finiteGaussianFourierCharacter (a z : ι → ℝ) : ℂ :=
  Complex.exp (Complex.I * (finiteFeatureEvaluation (fun v : ι → ℝ => v) a z : ℝ))

lemma norm_finiteGaussianFourierCharacter (a z : ι → ℝ) :
    ‖finiteGaussianFourierCharacter a z‖ = 1 := by
  exact Complex.norm_exp_I_mul_ofReal _

lemma continuous_finiteGaussianFourierCharacter (a : ι → ℝ) :
    Continuous (finiteGaussianFourierCharacter a) := by
  classical
  unfold finiteGaussianFourierCharacter finiteFeatureEvaluation
  fun_prop

lemma integrable_finiteGaussianFourierCharacter (a : ι → ℝ) :
    Integrable (finiteGaussianFourierCharacter a) (finiteStandardGaussian ι) := by
  refine (integrable_const (1 : ℝ)).mono'
    (continuous_finiteGaussianFourierCharacter a).aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall (fun z => (norm_finiteGaussianFourierCharacter a z).le)

lemma integral_finiteGaussianFourierCharacter (a : ι → ℝ) :
    (∫ z, finiteGaussianFourierCharacter a z ∂finiteStandardGaussian ι) =
      (Real.exp (-(∑ i, (a i) ^ 2) / 2) : ℝ) := by
  classical
  have hmeas : Measurable (finiteFeatureEvaluation (fun v : ι → ℝ => v) a) := by
    unfold finiteFeatureEvaluation
    fun_prop
  have hLaw : HasLaw (finiteFeatureEvaluation (fun v : ι → ℝ => v) a)
      (gaussianReal 0 (Real.toNNReal (∑ i, (a i) ^ 2))) (finiteStandardGaussian ι) :=
    ⟨hmeas.aemeasurable, map_finiteFeatureEvaluation_eq_gaussianReal _ _⟩
  have hi := complexMGF_gaussianReal hLaw Complex.I
  have hnonneg : 0 ≤ ∑ i, (a i) ^ 2 := Finset.sum_nonneg (fun i hi => sq_nonneg _)
  have hvar : ((Real.toNNReal (∑ i, (a i) ^ 2) : ℝ) : ℂ) =
      ((∑ i, (a i) ^ 2 : ℝ) : ℂ) := by
    simp [Real.toNNReal_of_nonneg hnonneg]
  unfold complexMGF at hi
  unfold finiteGaussianFourierCharacter
  rw [hi, Complex.ofReal_exp]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, zero_add, Complex.I_sq]
  rw [hvar]
  push_cast
  ring

lemma integral_finiteGaussianFourierCharacter_scaled_difference
    (a b : ι → ℝ) (t : ℝ) :
    (∫ z, finiteGaussianFourierCharacter (fun i => (a i - b i) / t) z
      ∂finiteStandardGaussian ι) =
      (Real.exp (-(∑ i, (a i - b i) ^ 2) / (2 * t ^ 2)) : ℝ) := by
  rw [integral_finiteGaussianFourierCharacter]
  congr 2
  simp only [div_pow, ← Finset.sum_div]
  ring

end DGRHS.Gaussian
#check DGRHS.Gaussian.finiteGaussianFourierCharacter
#check DGRHS.Gaussian.norm_finiteGaussianFourierCharacter
#check DGRHS.Gaussian.continuous_finiteGaussianFourierCharacter
#check DGRHS.Gaussian.integrable_finiteGaussianFourierCharacter
#check DGRHS.Gaussian.integral_finiteGaussianFourierCharacter
#check DGRHS.Gaussian.integral_finiteGaussianFourierCharacter_scaled_difference
#print axioms DGRHS.Gaussian.finiteGaussianFourierCharacter
#print axioms DGRHS.Gaussian.norm_finiteGaussianFourierCharacter
#print axioms DGRHS.Gaussian.continuous_finiteGaussianFourierCharacter
#print axioms DGRHS.Gaussian.integrable_finiteGaussianFourierCharacter
#print axioms DGRHS.Gaussian.integral_finiteGaussianFourierCharacter
#print axioms DGRHS.Gaussian.integral_finiteGaussianFourierCharacter_scaled_difference
