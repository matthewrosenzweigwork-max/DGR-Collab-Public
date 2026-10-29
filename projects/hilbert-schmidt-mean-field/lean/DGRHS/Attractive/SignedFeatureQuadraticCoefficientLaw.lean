import DGRHS.Attractive.SignedFeatureCoefficients
import DGRHS.Attractive.SignedFeatureSpectral

/-! The actual positive quadratic coefficient has the signed Laplace law
of the same feature Gram operator and constructed Gaussian field. -/
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

lemma ae_exp_positiveQuadraticCoefficient (β θ : ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (a : ℝ) (ha : 0<a)
    (hM : Integrable (fun x => Real.exp (a*‖k x‖^2)) μ)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hg2 : MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian)) :
    (fun ω => Real.exp (θ*positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω))
      =ᵐ[IsonormalProcess.iidStdGaussian]
        featureQuadraticCenteredExp (μ := μ) (-θ*β) k g := by
  have hD : Integrable (fun x => ‖k x‖^2) μ := by
    simpa only [pow_one] using feature_diagonal_power_integrable k hk a ha hM 1
  have hG : Integrable (fun p => g p^2) (μ.prod IsonormalProcess.iidStdGaussian) := by
    simpa only [Real.norm_eq_abs,sq_abs] using
      (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg2
  filter_upwards [hG.prod_left_ae] with ω hω
  unfold positiveQuadraticCoefficient positiveQuadraticIntegrand featureQuadraticCenteredExp
  rw [integral_const_mul,integral_sub hω hD]
  congr 1
  ring

theorem exists_positiveQuadraticCoefficient_laplace [Countable j]
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace.CountablyGenerated X]
    (b : HilbertBasis j ℝ H) (f : j → ℕ) (hf : Function.Injective f)
    (β : ℝ) (k : X → H) (hk : StronglyMeasurable k)
    (a : ℝ) (ha : 0<a) (hM : Integrable (fun x => Real.exp (a*‖k x‖^2)) μ)
    (hmean : (∫ x,k x ∂μ)=0)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hg2 : MemLp g 2 (μ.prod IsonormalProcess.iidStdGaussian))
    (hW : ∀ᵐ x ∂μ,(fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    ∃ (ι : Type u) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ)),
      Countable ι ∧
      (∀ i,DGRHS.Kernel.integralOperator (featureKernel k)
        (memLp_featureKernel k hk (feature_memLp_two_of_diagonal_exponential k hk a ha hM)) (e i)=eig i • e i) ∧
      (∀ i,0≤eig i) ∧ Summable eig ∧ (∑' i,eig i)=∫ x,‖k x‖^2 ∂μ ∧
      ∀ θ : ℝ,|θ*β| *‖DGRHS.Kernel.integralOperator (featureKernel k)
        (memLp_featureKernel k hk (feature_memLp_two_of_diagonal_exponential k hk a ha hM))‖<1 →
        Integrable (fun ω => Real.exp (θ*positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω))
          IsonormalProcess.iidStdGaussian ∧
        (∫ ω,Real.exp (θ*positiveQuadraticCoefficient μ β (fun x => ‖k x‖^2) g ω)
          ∂IsonormalProcess.iidStdGaussian)=
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => -θ*β*eig i)))⁻¹ := by
  have hk2 := feature_memLp_two_of_diagonal_exponential k hk a ha hM
  obtain ⟨ι,eig,e,hi,he,hepos,hs,ht,hL⟩ := exists_feature_signed_quadratic_laplace
    b f hf k hk hk2 hmean g hg hg2 hW
  refine ⟨ι,eig,e,hi,he,hepos,hs,ht,fun θ hgap => ?_⟩
  have hmargin : |-θ*β| *‖DGRHS.Kernel.integralOperator (featureKernel k)
      (memLp_featureKernel k hk hk2)‖<1 := by
    simpa only [neg_mul,abs_neg] using hgap
  obtain ⟨hiL,heL⟩ := hL (-θ*β) hmargin
  have heq := ae_exp_positiveQuadraticCoefficient β θ k hk a ha hM g hg hg2
  refine ⟨hiL.congr heq.symm,?_⟩
  exact (integral_congr_ae heq).trans heL

end DGRHS.Attractive
#check DGRHS.Attractive.ae_exp_positiveQuadraticCoefficient
#print axioms DGRHS.Attractive.ae_exp_positiveQuadraticCoefficient
#check DGRHS.Attractive.exists_positiveQuadraticCoefficient_laplace
#print axioms DGRHS.Attractive.exists_positiveQuadraticCoefficient_laplace
