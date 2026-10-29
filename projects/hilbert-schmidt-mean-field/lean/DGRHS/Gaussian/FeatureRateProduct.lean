import DGRHS.Gaussian.FeatureRateLaplace
import Mathlib.MeasureTheory.Integral.Pi
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Gaussian
variable {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
  {μ : Measure X} [IsProbabilityMeasure μ]

def featureParticleOscillatoryIntegrand (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (p : (Fin N → X) × (ℕ → ℝ)) : ℂ :=
  ∏ i : Fin N, featureOscillatoryIntegrand β k g N (p.1 i,p.2)

def featureParticleExponentialEnvelope (β : ℝ) (k : X → H) (N : ℕ) (x : Fin N → X) : ℝ :=
  ∏ i : Fin N, Real.exp (β * ‖k (x i)‖ ^ 2 / (2 * (N : ℝ)))

lemma norm_featureParticleOscillatoryIntegrand (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (p : (Fin N → X) × (ℕ → ℝ)) :
    ‖featureParticleOscillatoryIntegrand β k g N p‖ = featureParticleExponentialEnvelope β k N p.1 := by
  unfold featureParticleOscillatoryIntegrand featureParticleExponentialEnvelope
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact norm_featureOscillatoryIntegrand β k g N (p.1 i,p.2)

lemma stronglyMeasurable_featureParticleOscillatoryIntegrand (β : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (N : ℕ) : StronglyMeasurable (featureParticleOscillatoryIntegrand β k g N) := by
  unfold featureParticleOscillatoryIntegrand
  apply Finset.stronglyMeasurable_fun_prod
  intro i hi
  exact (stronglyMeasurable_featureOscillatoryIntegrand β k hk g hg N).comp_measurable
    (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)

lemma integrable_featureParticleExponentialEnvelope (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (N : ℕ) (hN : 1 ≤ N) :
    Integrable (featureParticleExponentialEnvelope β k N) (Measure.pi (fun _ : Fin N => μ)) :=
  Integrable.fintype_prod (fun _ => integrable_feature_small_exponential β hβ k hk hM N hN)

lemma integral_featureParticleExponentialEnvelope (β : ℝ) (k : X → H) (N : ℕ) :
    (∫ x, featureParticleExponentialEnvelope β k N x ∂Measure.pi (fun _ : Fin N => μ)) =
      featurePositiveFactor μ β k N ^ N := by
  simpa only [featureParticleExponentialEnvelope, featurePositiveFactor, Fintype.card_fin] using
    (integral_fintype_prod_eq_pow (ι := Fin N) (μ := μ)
      (fun x => Real.exp (β * ‖k x‖ ^ 2 / (2 * (N : ℝ)))))

lemma integrable_featureParticleOscillatoryIntegrand (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g) (N : ℕ) (hN : 1 ≤ N) :
    Integrable (featureParticleOscillatoryIntegrand β k g N)
      ((Measure.pi (fun _ : Fin N => μ)).prod IsonormalProcess.iidStdGaussian) := by
  have he := (measurePreserving_fst (μ := Measure.pi (fun _ : Fin N => μ))
    (ν := IsonormalProcess.iidStdGaussian)).integrable_comp_of_integrable
    (integrable_featureParticleExponentialEnvelope β hβ k hk hM N hN)
  apply he.mono' (stronglyMeasurable_featureParticleOscillatoryIntegrand β k hk g hg N).aestronglyMeasurable
  filter_upwards [] with p
  exact le_of_eq (norm_featureParticleOscillatoryIntegrand β k g N p)

lemma integral_featureParticleOscillatoryIntegrand_section (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (ω : ℕ → ℝ) :
    (∫ x, featureParticleOscillatoryIntegrand β k g N (x,ω) ∂Measure.pi (fun _ : Fin N => μ)) =
      featureOscillatoryFactor μ β k g N ω ^ N := by
  simpa only [featureParticleOscillatoryIntegrand, featureOscillatoryFactor, Fintype.card_fin] using
    (integral_fintype_prod_eq_pow (ι := Fin N) (μ := μ)
      (fun x => featureOscillatoryIntegrand β k g N (x,ω)))

lemma integral_featureParticleOscillatoryIntegrand (β : ℝ) (hβ : 0 ≤ β) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g) (N : ℕ) (hN : 1 ≤ N) :
    (∫ x, ∫ ω, featureParticleOscillatoryIntegrand β k g N (x,ω) ∂IsonormalProcess.iidStdGaussian
      ∂Measure.pi (fun _ : Fin N => μ)) =
      ∫ ω, featureOscillatoryFactor μ β k g N ω ^ N ∂IsonormalProcess.iidStdGaussian := by
  have hi := integrable_featureParticleOscillatoryIntegrand β hβ k hk hM g hg N hN
  rw [← integral_prod _ hi, integral_prod_symm _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (integral_featureParticleOscillatoryIntegrand_section β k g N)

end DGRHS.Gaussian

#check DGRHS.Gaussian.featureParticleOscillatoryIntegrand
#print axioms DGRHS.Gaussian.featureParticleOscillatoryIntegrand

#check DGRHS.Gaussian.featureParticleExponentialEnvelope
#print axioms DGRHS.Gaussian.featureParticleExponentialEnvelope

#check DGRHS.Gaussian.norm_featureParticleOscillatoryIntegrand
#print axioms DGRHS.Gaussian.norm_featureParticleOscillatoryIntegrand

#check DGRHS.Gaussian.stronglyMeasurable_featureParticleOscillatoryIntegrand
#print axioms DGRHS.Gaussian.stronglyMeasurable_featureParticleOscillatoryIntegrand

#check DGRHS.Gaussian.integrable_featureParticleExponentialEnvelope
#print axioms DGRHS.Gaussian.integrable_featureParticleExponentialEnvelope

#check DGRHS.Gaussian.integral_featureParticleExponentialEnvelope
#print axioms DGRHS.Gaussian.integral_featureParticleExponentialEnvelope

#check DGRHS.Gaussian.integrable_featureParticleOscillatoryIntegrand
#print axioms DGRHS.Gaussian.integrable_featureParticleOscillatoryIntegrand

#check DGRHS.Gaussian.integral_featureParticleOscillatoryIntegrand_section
#print axioms DGRHS.Gaussian.integral_featureParticleOscillatoryIntegrand_section

#check DGRHS.Gaussian.integral_featureParticleOscillatoryIntegrand
#print axioms DGRHS.Gaussian.integral_featureParticleOscillatoryIntegrand
