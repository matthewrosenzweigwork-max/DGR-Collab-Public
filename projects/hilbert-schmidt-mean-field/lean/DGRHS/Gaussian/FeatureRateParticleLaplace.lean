import DGRHS.Gaussian.FeatureRateProduct
import Mathlib.Probability.Moments.ComplexMGF
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DGRHS.Gaussian
variable {ι H X : Type*} [Countable ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma integral_indexedGaussianIsometry_phase (b : HilbertBasis ι ℝ H) (f : ι → ℕ)
    (hf : Function.Injective f) (v : H) (t : ℝ) :
    (∫ ω, Complex.exp (Complex.I * (t * indexedGaussianIsometry b f hf v ω : ℝ))
      ∂IsonormalProcess.iidStdGaussian) = (Real.exp (-t ^ 2 * ‖v‖ ^ 2 / 2) : ℝ) := by
  have hLaw : HasLaw (indexedGaussianIsometry b f hf v : (ℕ → ℝ) → ℝ)
      (gaussianReal 0 (Real.toNNReal (‖v‖ ^ 2))) IsonormalProcess.iidStdGaussian :=
    ⟨(Lp.aestronglyMeasurable _).aemeasurable, map_indexedGaussianIsometry_eq_gaussianReal b f hf v⟩
  have hi := complexMGF_gaussianReal hLaw (Complex.I * (t : ℂ))
  have hvar : ((Real.toNNReal (‖v‖ ^ 2) : ℝ) : ℂ) = (‖v‖ ^ 2 : ℝ) := by
    simp [Real.toNNReal_of_nonneg (sq_nonneg ‖v‖)]
  unfold complexMGF at hi
  have he : (fun ω => Complex.exp (Complex.I * (t * indexedGaussianIsometry b f hf v ω : ℝ))) =
      fun ω => Complex.exp ((Complex.I * (t : ℂ)) * indexedGaussianIsometry b f hf v ω) := by
    funext ω
    congr 1
    push_cast
    ring
  rw [he, hi]
  rw [Complex.ofReal_exp]
  congr 1
  simp only [Complex.ofReal_zero, mul_zero, zero_add, mul_pow, Complex.I_sq]
  rw [hvar]
  push_cast
  ring

lemma ae_feature_particle_sum_eq_same_process
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (k : X → H) (g : X × (ℕ → ℝ) → ℝ)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (N : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      (fun ω => ∑ i : Fin N, g (x i,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
        indexedGaussianIsometry b f hf (∑ i : Fin N, k (x i)) := by
  have hcoords : ∀ i : Fin N, ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      (fun ω => g (x i,ω)) =ᵐ[IsonormalProcess.iidStdGaussian] indexedGaussianIsometry b f hf (k (x i)) :=
    fun i => (measurePreserving_eval (fun _ : Fin N => μ) i).quasiMeasurePreserving.ae hW
  filter_upwards [ae_all_iff.2 hcoords] with x hx
  have hraw : (fun ω => ∑ i : Fin N, g (x i,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      fun ω => ∑ i : Fin N, indexedGaussianIsometry b f hf (k (x i)) ω := by
    filter_upwards [ae_all_iff.2 hx] with ω hω
    exact Finset.sum_congr rfl (fun i hi => hω i)
  have hsum : (indexedGaussianIsometry b f hf (∑ i : Fin N, k (x i)) : (ℕ → ℝ) → ℝ)
      =ᵐ[IsonormalProcess.iidStdGaussian] fun ω => ∑ i : Fin N, indexedGaussianIsometry b f hf (k (x i)) ω := by
    rw [map_sum]
    exact Lp.coeFn_fun_finsetSum Finset.univ _
  exact hraw.trans hsum.symm

def featureParticleExp (β : ℝ) (k : X → H) (N : ℕ) (x : Fin N → X) : ℝ :=
  Real.exp (β / (2 * (N : ℝ)) * ((∑ i : Fin N, ‖k (x i)‖ ^ 2) - ‖∑ i : Fin N, k (x i)‖ ^ 2))

lemma featureParticleOscillatoryIntegrand_eq_exp (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) (N : ℕ) (p : (Fin N → X) × (ℕ → ℝ)) :
    featureParticleOscillatoryIntegrand β k g N p =
      Complex.exp (((β / (2 * (N : ℝ)) * ∑ i : Fin N, ‖k (p.1 i)‖ ^ 2 : ℝ) : ℂ) +
        Complex.I * (Real.sqrt (β / (N : ℝ)) * ∑ i : Fin N, g (p.1 i,p.2) : ℝ)) := by
  unfold featureParticleOscillatoryIntegrand featureOscillatoryIntegrand
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [Finset.mul_sum, Finset.sum_add_distrib]
  apply congrArg₂ (fun a b : ℂ => a + b)
  · apply Finset.sum_congr rfl
    intro i hi
    ring
  · apply Finset.sum_congr rfl
    intro i hi
    ring

lemma ae_integral_featureParticleOscillatoryIntegrand_eq_exp
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (g : X × (ℕ → ℝ) → ℝ)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (N : ℕ) :
    ∀ᵐ x ∂Measure.pi (fun _ : Fin N => μ),
      (∫ ω, featureParticleOscillatoryIntegrand β k g N (x,ω) ∂IsonormalProcess.iidStdGaussian) =
        (featureParticleExp β k N x : ℝ) := by
  filter_upwards [ae_feature_particle_sum_eq_same_process b f hf k g hW N] with x hx
  have he : (fun ω => featureParticleOscillatoryIntegrand β k g N (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      fun ω => Complex.exp (((β / (2 * (N : ℝ)) * ∑ i : Fin N, ‖k (x i)‖ ^ 2 : ℝ) : ℂ) +
        Complex.I * (Real.sqrt (β / (N : ℝ)) * indexedGaussianIsometry b f hf (∑ i : Fin N, k (x i)) ω : ℝ)) := by
    filter_upwards [hx] with ω hω
    rw [featureParticleOscillatoryIntegrand_eq_exp, hω]
  rw [integral_congr_ae he]
  simp_rw [Complex.exp_add]
  rw [integral_const_mul, integral_indexedGaussianIsometry_phase]
  unfold featureParticleExp
  rw [← Complex.ofReal_exp, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  rw [Real.sq_sqrt (div_nonneg hβ (Nat.cast_nonneg N))]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

lemma integrable_featureParticleExp
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (N : ℕ) (hN : 1 ≤ N) :
    Integrable (featureParticleExp β k N) (Measure.pi (fun _ : Fin N => μ)) := by
  have hp := integrable_featureParticleOscillatoryIntegrand β hβ k hk hM g hg N hN
  have hc : Integrable (fun x => (featureParticleExp β k N x : ℂ)) (Measure.pi (fun _ : Fin N => μ)) :=
    hp.integral_prod_left.congr (ae_integral_featureParticleOscillatoryIntegrand_eq_exp b f hf β hβ k g hW N)
  have he : (fun x => ‖(featureParticleExp β k N x : ℂ)‖) = featureParticleExp β k N := by
    funext x
    unfold featureParticleExp
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [← he]
  exact hc.norm

lemma integral_featureParticleExp_eq_integral_featureOscillatoryFactor_pow
    (b : HilbertBasis ι ℝ H) (f : ι → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (N : ℕ) (hN : 1 ≤ N) :
    (∫ x, featureParticleExp β k N x ∂Measure.pi (fun _ : Fin N => μ) : ℝ) =
      ∫ ω, featureOscillatoryFactor μ β k g N ω ^ N ∂IsonormalProcess.iidStdGaussian := by
  rw [← integral_complex_ofReal]
  calc
    _ = ∫ x, ∫ ω, featureParticleOscillatoryIntegrand β k g N (x,ω) ∂IsonormalProcess.iidStdGaussian
        ∂Measure.pi (fun _ : Fin N => μ) :=
      by
        apply integral_congr_ae
        filter_upwards [ae_integral_featureParticleOscillatoryIntegrand_eq_exp b f hf β hβ k g hW N] with x hx
        exact hx.symm
    _ = _ := integral_featureParticleOscillatoryIntegrand β hβ k hk hM g hg N hN

end DGRHS.Gaussian

#check DGRHS.Gaussian.integral_indexedGaussianIsometry_phase
#print axioms DGRHS.Gaussian.integral_indexedGaussianIsometry_phase

#check DGRHS.Gaussian.ae_feature_particle_sum_eq_same_process
#print axioms DGRHS.Gaussian.ae_feature_particle_sum_eq_same_process

#check DGRHS.Gaussian.featureParticleExp
#print axioms DGRHS.Gaussian.featureParticleExp

#check DGRHS.Gaussian.featureParticleOscillatoryIntegrand_eq_exp
#print axioms DGRHS.Gaussian.featureParticleOscillatoryIntegrand_eq_exp

#check DGRHS.Gaussian.ae_integral_featureParticleOscillatoryIntegrand_eq_exp
#print axioms DGRHS.Gaussian.ae_integral_featureParticleOscillatoryIntegrand_eq_exp

#check DGRHS.Gaussian.integrable_featureParticleExp
#print axioms DGRHS.Gaussian.integrable_featureParticleExp

#check DGRHS.Gaussian.integral_featureParticleExp_eq_integral_featureOscillatoryFactor_pow
#print axioms DGRHS.Gaussian.integral_featureParticleExp_eq_integral_featureOscillatoryFactor_pow
