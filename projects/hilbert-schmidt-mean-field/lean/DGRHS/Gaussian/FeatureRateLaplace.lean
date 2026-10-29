import DGRHS.Gaussian.FeatureRateIntegrated
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGRHS.Gaussian
universe u v
variable {X : Type u} {H : Type v} {j : Type*}
  [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [Countable j]

lemma featureQuadraticCenteredExp_eq_exp_featureRateB (β : ℝ) (k : X → H)
    (g : X × (ℕ → ℝ) → ℝ) :
    featureQuadraticCenteredExp (μ := μ) β k g = fun ω => Real.exp (featureRateB μ β k g ω) := by
  funext ω
  unfold featureQuadraticCenteredExp featureRateB
  congr 1
  ring

/-- The eigenvalues here are obtained from the actual Gram integral operator.
The same supplied field and isometry witness are retained in every rate bound. -/
theorem exists_featureOscillatoryFactor_rate
    [TopologicalSpace.SeparableSpace H] [MeasurableSpace.CountablyGenerated X]
    (b : HilbertBasis j ℝ H) (f : j → ℕ) (hf : Function.Injective f)
    (β : ℝ) (hβ : 0 ≤ β) (k : X → H) (hk : StronglyMeasurable k)
    (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (hmean : (∫ x, k x ∂μ) = 0)
    (g : X × (ℕ → ℝ) → ℝ) (hg : StronglyMeasurable g)
    (hW : ∀ᵐ x ∂μ, (fun ω => g (x,ω)) =ᵐ[IsonormalProcess.iidStdGaussian]
      indexedGaussianIsometry b f hf (k x)) :
    ∃ (ι : Type u) (eig : ι → ℝ) (e : HilbertBasis ι ℝ (Lp ℝ 2 μ)),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator (featureKernel k)
        (memLp_featureKernel k hk (memLp_feature_of_exponential_moment β hβ k hk hM)) (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧ (∑' i, eig i) = ∫ x, ‖k x‖ ^ 2 ∂μ ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun ω => featureOscillatoryFactor μ β k g N ω ^ N) IsonormalProcess.iidStdGaussian ∧
        ‖(∫ ω, featureOscillatoryFactor μ β k g N ω ^ N ∂IsonormalProcess.iidStdGaussian) -
          ((Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹ : ℝ)‖ ≤
          (26 * β ^ 2 + 12 * β ^ 3) * (∫ x, featureExponentialMomentWeight β k x ∂μ) ^ 2 / (N : ℝ) := by
  have hk2 := memLp_feature_of_exponential_moment β hβ k hk hM
  have hg2 := memLp_featureGaussian_of_exponential_moment b f hf β hβ k hk hM g hg hW
  obtain ⟨ι, eig, e, hi, he, ha, hs, ht, hLaplace⟩ :=
    exists_feature_quadratic_laplace b f hf k hk.measurable hk hk2 hmean g hg hg2 hW
  refine ⟨ι, eig, e, hi, he, ha, hs, ht, fun N hN => ⟨?_, ?_⟩⟩
  · exact integrable_featureOscillatoryFactor_pow β hβ k hk hM g hg N hN
  · have hl : (∫ ω, Real.exp (featureRateB μ β k g ω) ∂IsonormalProcess.iidStdGaussian) =
        (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹ := by
      simpa only [featureQuadraticCenteredExp_eq_exp_featureRateB] using (hLaplace β hβ).2
    rw [← hl]
    exact norm_integral_featureOscillatoryFactor_pow_sub_laplace_le b f hf β hβ k hk hM hmean g hg hW N hN

lemma feature_rate_moment_sq_le_source_cube (M : ℝ) (hM : 0 ≤ M) :
    M ^ 2 ≤ (1 + M) ^ 3 := by
  nlinarith [pow_nonneg hM 3, sq_nonneg M]

end DGRHS.Gaussian

#check DGRHS.Gaussian.featureQuadraticCenteredExp_eq_exp_featureRateB
#print axioms DGRHS.Gaussian.featureQuadraticCenteredExp_eq_exp_featureRateB

#check DGRHS.Gaussian.exists_featureOscillatoryFactor_rate
#print axioms DGRHS.Gaussian.exists_featureOscillatoryFactor_rate

#check DGRHS.Gaussian.feature_rate_moment_sq_le_source_cube
#print axioms DGRHS.Gaussian.feature_rate_moment_sq_le_source_cube
