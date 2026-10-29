import DGRHS.Gaussian.FiniteGaussianFourier
import Mathlib.MeasureTheory.Function.L2Space

/-! Actual Gaussian-frequency characters considered in a real Hilbert space.
This fixed-scale unit is not yet the scale-mixture truncated Riesz feature. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma real_inner_finiteGaussianFourierCharacter (a b z : ι → ℝ) :
    inner ℝ (finiteGaussianFourierCharacter a z) (finiteGaussianFourierCharacter b z) =
      (finiteGaussianFourierCharacter (fun i => b i - a i) z).re := by
  classical
  rw [Complex.inner]
  unfold finiteGaussianFourierCharacter
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal,
    finiteFeatureEvaluation, sub_mul, Finset.sum_sub_distrib, Complex.ofReal_sub]
  ring

lemma integral_real_inner_finiteGaussianFourierCharacter (a b : ι → ℝ) :
    (∫ z, inner ℝ (finiteGaussianFourierCharacter a z) (finiteGaussianFourierCharacter b z)
      ∂finiteStandardGaussian ι) = Real.exp (-(∑ i, (b i - a i) ^ 2) / 2) := by
  simp_rw [real_inner_finiteGaussianFourierCharacter]
  change (∫ z, RCLike.re (finiteGaussianFourierCharacter (fun i => b i - a i) z)
    ∂finiteStandardGaussian ι) = _
  rw [integral_re (integrable_finiteGaussianFourierCharacter (fun i => b i - a i)),
    integral_finiteGaussianFourierCharacter]
  rfl

lemma memLp_finiteGaussianFourierCharacter (a : ι → ℝ) (p : ℝ≥0∞) :
    MemLp (finiteGaussianFourierCharacter a) p (finiteStandardGaussian ι) := by
  apply (memLp_const (1 : ℝ)).of_le
    (continuous_finiteGaussianFourierCharacter a).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by
    simp [norm_finiteGaussianFourierCharacter])

def finiteGaussianFourierFeature (a : ι → ℝ) : Lp ℂ 2 (finiteStandardGaussian ι) :=
  (memLp_finiteGaussianFourierCharacter a 2).toLp (finiteGaussianFourierCharacter a)

lemma coeFn_finiteGaussianFourierFeature (a : ι → ℝ) :
    (finiteGaussianFourierFeature a : (ι → ℝ) → ℂ) =ᵐ[finiteStandardGaussian ι]
      finiteGaussianFourierCharacter a :=
  (memLp_finiteGaussianFourierCharacter a 2).coeFn_toLp

lemma inner_finiteGaussianFourierFeature (a b : ι → ℝ) :
    inner ℝ (finiteGaussianFourierFeature a) (finiteGaussianFourierFeature b) =
      Real.exp (-(∑ i, (b i - a i) ^ 2) / 2) := by
  rw [L2.inner_def]
  have he : (fun z => inner ℝ (finiteGaussianFourierFeature a z) (finiteGaussianFourierFeature b z))
      =ᵐ[finiteStandardGaussian ι] fun z =>
      inner ℝ (finiteGaussianFourierCharacter a z) (finiteGaussianFourierCharacter b z) := by
    filter_upwards [coeFn_finiteGaussianFourierFeature a, coeFn_finiteGaussianFourierFeature b]
      with z ha hb
    rw [ha, hb]
  rw [integral_congr_ae he, integral_real_inner_finiteGaussianFourierCharacter]

lemma norm_sq_finiteGaussianFourierFeature (a : ι → ℝ) :
    ‖finiteGaussianFourierFeature a‖ ^ 2 = 1 := by
  rw [← real_inner_self_eq_norm_sq, inner_finiteGaussianFourierFeature]
  simp

end DGRHS.Gaussian
#check DGRHS.Gaussian.real_inner_finiteGaussianFourierCharacter
#check DGRHS.Gaussian.integral_real_inner_finiteGaussianFourierCharacter
#check DGRHS.Gaussian.memLp_finiteGaussianFourierCharacter
#check DGRHS.Gaussian.finiteGaussianFourierFeature
#check DGRHS.Gaussian.coeFn_finiteGaussianFourierFeature
#check DGRHS.Gaussian.inner_finiteGaussianFourierFeature
#check DGRHS.Gaussian.norm_sq_finiteGaussianFourierFeature
#print axioms DGRHS.Gaussian.real_inner_finiteGaussianFourierCharacter
#print axioms DGRHS.Gaussian.integral_real_inner_finiteGaussianFourierCharacter
#print axioms DGRHS.Gaussian.memLp_finiteGaussianFourierCharacter
#print axioms DGRHS.Gaussian.finiteGaussianFourierFeature
#print axioms DGRHS.Gaussian.coeFn_finiteGaussianFourierFeature
#print axioms DGRHS.Gaussian.inner_finiteGaussianFourierFeature
#print axioms DGRHS.Gaussian.norm_sq_finiteGaussianFourierFeature
