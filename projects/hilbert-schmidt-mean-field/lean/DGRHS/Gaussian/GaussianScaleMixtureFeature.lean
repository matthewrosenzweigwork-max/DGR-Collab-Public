import DGRHS.Gaussian.GaussianFourierCorrelation
import Mathlib.MeasureTheory.Integral.Prod

/-! Constructed Fourier characters in the real Hilbert L2 of an actual finite
scale measure times the finite iid Gaussian frequency measure. The Gram kernel
is proved from that product law. The Riesz scale measure is constructed separately. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

def gaussianScaleMixtureCharacter (a : ι → ℝ) (p : ℝ × (ι → ℝ)) : ℂ :=
  finiteGaussianFourierCharacter (fun i => a i / p.1) p.2

lemma norm_gaussianScaleMixtureCharacter (a : ι → ℝ) (p : ℝ × (ι → ℝ)) :
    ‖gaussianScaleMixtureCharacter a p‖ = 1 := norm_finiteGaussianFourierCharacter _ _

lemma measurable_gaussianScaleMixtureCharacter (a : ι → ℝ) :
    Measurable (gaussianScaleMixtureCharacter a) := by
  classical
  unfold gaussianScaleMixtureCharacter finiteGaussianFourierCharacter finiteFeatureEvaluation
  fun_prop

lemma memLp_gaussianScaleMixtureCharacter (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a : ι → ℝ) (p : ℝ≥0∞) :
    MemLp (gaussianScaleMixtureCharacter a) p (ν.prod (finiteStandardGaussian ι)) := by
  apply (memLp_const (1 : ℝ)).of_le
    (measurable_gaussianScaleMixtureCharacter a).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by simp [norm_gaussianScaleMixtureCharacter])

def gaussianScaleMixtureFeature (ν : Measure ℝ) [IsFiniteMeasure ν] (a : ι → ℝ) :
    Lp ℂ 2 (ν.prod (finiteStandardGaussian ι)) :=
  (memLp_gaussianScaleMixtureCharacter ν a 2).toLp (gaussianScaleMixtureCharacter a)

lemma coeFn_gaussianScaleMixtureFeature (ν : Measure ℝ) [IsFiniteMeasure ν] (a : ι → ℝ) :
    (gaussianScaleMixtureFeature ν a : (ℝ × (ι → ℝ)) → ℂ)
      =ᵐ[ν.prod (finiteStandardGaussian ι)] gaussianScaleMixtureCharacter a :=
  (memLp_gaussianScaleMixtureCharacter ν a 2).coeFn_toLp

lemma ae_inner_gaussianScaleMixtureFeature (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b : ι → ℝ) :
    (fun p => inner ℝ (gaussianScaleMixtureFeature ν a p) (gaussianScaleMixtureFeature ν b p))
      =ᵐ[ν.prod (finiteStandardGaussian ι)] fun p =>
      inner ℝ (gaussianScaleMixtureCharacter a p) (gaussianScaleMixtureCharacter b p) := by
  filter_upwards [coeFn_gaussianScaleMixtureFeature ν a, coeFn_gaussianScaleMixtureFeature ν b]
    with p ha hb
  rw [ha, hb]

lemma integrable_inner_gaussianScaleMixtureCharacter (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b : ι → ℝ) :
    Integrable (fun p => inner ℝ (gaussianScaleMixtureCharacter a p)
      (gaussianScaleMixtureCharacter b p)) (ν.prod (finiteStandardGaussian ι)) :=
  (L2.integrable_inner (𝕜 := ℝ) (gaussianScaleMixtureFeature ν a)
    (gaussianScaleMixtureFeature ν b)).congr (ae_inner_gaussianScaleMixtureFeature ν a b)

lemma integral_inner_gaussianScaleMixtureCharacter (a b : ι → ℝ) (t : ℝ) :
    (∫ z, inner ℝ (gaussianScaleMixtureCharacter a (t,z)) (gaussianScaleMixtureCharacter b (t,z))
      ∂finiteStandardGaussian ι) = Real.exp (-(∑ i, (b i - a i) ^ 2) / (2 * t ^ 2)) := by
  unfold gaussianScaleMixtureCharacter
  simp only [Prod.fst, Prod.snd]
  rw [integral_real_inner_finiteGaussianFourierCharacter]
  congr 1
  simp only [← sub_div, div_pow, ← Finset.sum_div]
  ring

lemma inner_gaussianScaleMixtureFeature (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a b : ι → ℝ) :
    inner ℝ (gaussianScaleMixtureFeature ν a) (gaussianScaleMixtureFeature ν b) =
      ∫ t, Real.exp (-(∑ i, (b i - a i) ^ 2) / (2 * t ^ 2)) ∂ν := by
  rw [L2.inner_def, integral_congr_ae (ae_inner_gaussianScaleMixtureFeature ν a b),
    integral_prod _ (integrable_inner_gaussianScaleMixtureCharacter ν a b)]
  simp_rw [integral_inner_gaussianScaleMixtureCharacter]

lemma norm_sq_gaussianScaleMixtureFeature (ν : Measure ℝ) [IsFiniteMeasure ν]
    (a : ι → ℝ) :
    ‖gaussianScaleMixtureFeature ν a‖ ^ 2 = (ν Set.univ).toReal := by
  rw [← real_inner_self_eq_norm_sq, inner_gaussianScaleMixtureFeature]
  simp [Measure.real]

end DGRHS.Gaussian
#check DGRHS.Gaussian.gaussianScaleMixtureCharacter
#check DGRHS.Gaussian.norm_gaussianScaleMixtureCharacter
#check DGRHS.Gaussian.measurable_gaussianScaleMixtureCharacter
#check DGRHS.Gaussian.memLp_gaussianScaleMixtureCharacter
#check DGRHS.Gaussian.gaussianScaleMixtureFeature
#check DGRHS.Gaussian.coeFn_gaussianScaleMixtureFeature
#check DGRHS.Gaussian.ae_inner_gaussianScaleMixtureFeature
#check DGRHS.Gaussian.integrable_inner_gaussianScaleMixtureCharacter
#check DGRHS.Gaussian.integral_inner_gaussianScaleMixtureCharacter
#check DGRHS.Gaussian.inner_gaussianScaleMixtureFeature
#check DGRHS.Gaussian.norm_sq_gaussianScaleMixtureFeature
#print axioms DGRHS.Gaussian.gaussianScaleMixtureCharacter
#print axioms DGRHS.Gaussian.norm_gaussianScaleMixtureCharacter
#print axioms DGRHS.Gaussian.measurable_gaussianScaleMixtureCharacter
#print axioms DGRHS.Gaussian.memLp_gaussianScaleMixtureCharacter
#print axioms DGRHS.Gaussian.gaussianScaleMixtureFeature
#print axioms DGRHS.Gaussian.coeFn_gaussianScaleMixtureFeature
#print axioms DGRHS.Gaussian.ae_inner_gaussianScaleMixtureFeature
#print axioms DGRHS.Gaussian.integrable_inner_gaussianScaleMixtureCharacter
#print axioms DGRHS.Gaussian.integral_inner_gaussianScaleMixtureCharacter
#print axioms DGRHS.Gaussian.inner_gaussianScaleMixtureFeature
#print axioms DGRHS.Gaussian.norm_sq_gaussianScaleMixtureFeature
