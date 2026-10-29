import DGRHS.Attractive.SignedFeatureQuadraticCoefficientLaw
import DGRHS.Kernel.SpectralHilbertSchmidt
import DGRHS.Kernel.SignedDeterminantBound

/-! Proper exponential moments of the same actual quadratic coefficient,
with dependence on the true Hilbert--Schmidt square and operator margin.
No diagonal trace bound is substituted for the Hilbert--Schmidt control. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace DGRHS.Attractive
open DGRHS.Gaussian
universe u v
variable {X : Type u} {H : Type v} {j : Type*}
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] [MeasurableSpace H] [BorelSpace H]

lemma positiveQuadraticCoefficient_exponential_bound [Countable j]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace.CountablyGenerated X]
    (b : HilbertBasis j ℝ H) (f : j → ℕ) (hf : Function.Injective f)
    (β : ℝ) (k : X → H) (hk : StronglyMeasurable k)
    (a : ℝ) (ha : 0<a) (hM : Integrable (fun x => Real.exp (a*‖k x‖^2)) μ)
    (hmean : (∫ x,k x ∂μ)=0)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hg2 : MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian))
    (hW : ∀ᵐ x ∂μ,(fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) (θ : ℝ)
    (hgap : |θ*β| *‖DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk (feature_memLp_two_of_diagonal_exponential k hk a ha hM))‖<1) :
    Integrable (fun ω => Real.exp (θ*positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω))
      IsonormalProcess.iidStdGaussian ∧
    (∫ ω,Real.exp (θ*positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω)
      ∂IsonormalProcess.iidStdGaussian) ≤
      Real.exp ((θ*β)^2*(∫ p,featureKernel k p^2 ∂μ.prod μ)/
        (2*(1-|θ*β| *‖DGRHS.Kernel.integralOperator (featureKernel k)
          (memLp_featureKernel k hk (feature_memLp_two_of_diagonal_exponential k hk a ha hM))‖))) := by
  have hk2 := feature_memLp_two_of_diagonal_exponential k hk a ha hM
  let hkq := memLp_featureKernel k hk hk2
  obtain ⟨ι,eig,e,hi,he,_,_,_,hL⟩ := exists_positiveQuadraticCoefficient_laplace
    b f hf β k hk a ha hM hmean g hg hg2 hW
  letI : Countable ι := hi
  obtain ⟨hiL,heL⟩ := hL θ hgap
  refine ⟨hiL,?_⟩
  rw [heL]
  have hs := DGRHS.Kernel.summable_integralOperator_eigenvalue_sq (featureKernel k) hkq eig e he
  have hx : ∀ i,|-θ*β*eig i|≤|θ*β| *‖DGRHS.Kernel.integralOperator (featureKernel k) hkq‖ := by
    intro i
    rw [mul_assoc,show -θ*(β*eig i)=-(θ*β)*eig i by ring,abs_mul,abs_neg]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Real.norm_eq_abs] using
        DGRHS.Kernel.integralOperator_eigenvalue_norm_le (featureKernel k) hkq eig e he i)
      (abs_nonneg _)
  have hb := DGRHS.Kernel.inv_sqrt_regularizedDet_le_sq_margin
    (DGRHS.Kernel.summable_scaled_eigenvalue_sq eig hs (-θ*β)) hx hgap
  have hsum : (∑' i,(-θ*β*eig i)^2)=(θ*β)^2*(∫ p,featureKernel k p^2 ∂μ.prod μ) := by
    simp_rw [mul_pow]
    rw [tsum_mul_left,DGRHS.Kernel.tsum_integralOperator_eigenvalue_sq (featureKernel k) hkq eig e he]
    congr 1
    ring
  simpa only [hsum] using hb

end DGRHS.Attractive
#check DGRHS.Attractive.positiveQuadraticCoefficient_exponential_bound
#print axioms DGRHS.Attractive.positiveQuadraticCoefficient_exponential_bound
