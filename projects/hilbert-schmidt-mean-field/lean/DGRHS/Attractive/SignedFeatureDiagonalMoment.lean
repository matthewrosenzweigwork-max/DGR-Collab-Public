import DGRHS.Attractive.SignedFeatureFactory

/-! The source diagonal exponential moment supplies actual proper feature
powers and feature L2. No additional feature-L2 assumption is retained by the
exponential-diagonal field factory. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DGRHS.Attractive
open DGRHS.Gaussian

lemma nonnegative_power_le_exponential (a D : ℝ) (ha : 0 < a) (hD : 0 ≤ D) (p : ℕ) :
    D^p ≤ ((p.factorial:ℝ)/a^p)*Real.exp (a*D) := by
  have h := Real.pow_div_factorial_le_exp (x := a*D) (mul_nonneg ha.le hD) p
  have hf : 0 < (p.factorial:ℝ) := by positivity
  have hh := (div_le_iff₀ hf).mp h
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (pow_pos ha p)).mpr
  simpa only [mul_pow, mul_comm, mul_left_comm, mul_assoc] using hh

variable {H X : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]

lemma feature_diagonal_power_integrable (k : X → H) (hk : StronglyMeasurable k)
    (a : ℝ) (ha : 0 < a)
    (hM : Integrable (fun x => Real.exp (a*‖k x‖^2)) μ) (p : ℕ) :
    Integrable (fun x => (‖k x‖^2)^p) μ := by
  apply (hM.const_mul ((p.factorial:ℝ)/a^p)).mono'
    ((hk.norm.pow 2).pow p).aestronglyMeasurable
  filter_upwards [] with x
  change ‖(‖k x‖^2)^p‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (‖k x‖^2)^p)]
  exact nonnegative_power_le_exponential a (‖k x‖^2) ha (sq_nonneg _) p

lemma feature_memLp_two_of_diagonal_exponential (k : X → H) (hk : StronglyMeasurable k)
    (a : ℝ) (ha : 0 < a)
    (hM : Integrable (fun x => Real.exp (a*‖k x‖^2)) μ) : MemLp k 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hk.aestronglyMeasurable).2
  simpa only [pow_one] using feature_diagonal_power_integrable k hk a ha hM 1

variable [CompleteSpace H] [TopologicalSpace.SeparableSpace H]
  [MeasurableSpace H] [BorelSpace H]

theorem exists_separable_positiveFeature_of_diagonal_exponential
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (a : ℝ) (ha : 0 < a) (hM : Integrable (fun x => Real.exp (a*‖k x‖^2)) μ)
    (hmean : (∫ x, k x ∂μ) = 0)
    (hp : ∀ N : ℕ, 1 ≤ N → Integrable (positiveFeatureParticleExp (2*β) k N)
      (Measure.pi (fun _ : Fin N => μ))) :
    ∃ g : X × (ℕ → ℝ) → ℝ, StronglyMeasurable g ∧
      MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian) ∧
      (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, Integrable (fun x => g (x,ω)) μ) ∧
      (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian, (∫ x, g (x,ω) ∂μ) = 0) ∧
      ∀ N : ℕ, 1 ≤ N →
        (∀ᵐ ω ∂IsonormalProcess.iidStdGaussian,
          Integrable (fun x => positiveFeatureWick β k g N (x,ω)) μ ∧
          0 < positiveFeatureFactor μ β k g N ω) ∧
        Integrable (positiveFeatureFactor μ β k g N) IsonormalProcess.iidStdGaussian ∧
        (∫ ω, positiveFeatureFactor μ β k g N ω ∂IsonormalProcess.iidStdGaussian) = 1 ∧
        Integrable (fun ω => positiveFeatureFactor μ β k g N ω ^ N)
          IsonormalProcess.iidStdGaussian ∧
        (∫ x, positiveFeatureParticleExp β k N x ∂Measure.pi (fun _ : Fin N => μ)) =
          (∫ ω, positiveFeatureFactor μ β k g N ω ^ N ∂IsonormalProcess.iidStdGaussian) ∧
        Integrable (fun ω => positiveFeatureFactor μ β k g N ω ^ (2*N))
          IsonormalProcess.iidStdGaussian ∧
        (∫ ω, positiveFeatureFactor μ β k g N ω ^ (2*N) ∂IsonormalProcess.iidStdGaussian) =
          (∫ x, positiveFeatureParticleExp (2*β) k (2*N) x
            ∂Measure.pi (fun _ : Fin (2*N) => μ)) := by
  exact exists_separable_positiveFeature_linearization β hβ k hk
    (feature_memLp_two_of_diagonal_exponential k hk a ha hM) hmean hp

end DGRHS.Attractive
#check DGRHS.Attractive.feature_diagonal_power_integrable
#print axioms DGRHS.Attractive.feature_diagonal_power_integrable
#check DGRHS.Attractive.feature_memLp_two_of_diagonal_exponential
#print axioms DGRHS.Attractive.feature_memLp_two_of_diagonal_exponential
#check DGRHS.Attractive.exists_separable_positiveFeature_of_diagonal_exponential
#print axioms DGRHS.Attractive.exists_separable_positiveFeature_of_diagonal_exponential
