import DGRHS.Gaussian.FeatureRateBounded

/-! Original source export: arXiv:2609.02743v1, preserved
DGR_PFunc_Current_20260902_145019_UTC.tex SHA256
6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c,
prop:boundedFeatureQuadLaplace, source lines1801–1827.
Development semantic/protected acceptance is separate. The original source
kernel need only agree with the feature Gram kernel product-almost everywhere;
its L2 membership and actual full-source-operator spectral data are derived.
One explicit beta-only constant is used in BOTH source conclusions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace DGRHS.Gaussian
universe u v
variable {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsProbabilityMeasure μ]
variable {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [TopologicalSpace.SeparableSpace H]
  [MeasurableSpace.CountablyGenerated X]

lemma originalFeature_rate_source_constant (β M Z L : ℝ)
    (hβ : 0 ≤ β) (hM : 0 ≤ M) (N : ℕ) (hN : 1 ≤ N)
    (h : |Z - L| ≤ (26 * β ^ 2 + 12 * β ^ 3) * M ^ 2 / (N : ℝ)) :
    |Z - L| ≤ featureBoundedRateConstant β * (1 + M) ^ 3 / (N : ℝ) := by
  have hn : 0 < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 1) hN)
  have hcoef : 0 ≤ 26 * β ^ 2 + 12 * β ^ 3 := by positivity
  have hC : 26 * β ^ 2 + 12 * β ^ 3 ≤ featureBoundedRateConstant β := by
    have hd : 0 ≤ 2 / β := div_nonneg (by norm_num) hβ
    unfold featureBoundedRateConstant
    linarith
  apply (featureParticleInteraction_rate_source_form β M Z L hβ hM N hN h).trans
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hC (pow_nonneg (by linarith : 0 ≤ 1 + M) 3)) hn.le

/-- Original feature-space quadratic Laplace proposition. Source-kernel L2,
actual spectral eigenvalues/eigenbasis, trace, true product convergence and both
source rates are derived. No Gaussian/spectral/matching/rate/limit premise.
The constant featureBoundedRateConstant beta depends ONLY on beta. -/
theorem original_boundedFeatureQuadLaplace
    (β : ℝ) (hβ : 0 ≤ β) (h : X × X → ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (hM : Integrable (featureExponentialMomentWeight β k) μ)
    (hmean : (∫ x, k x ∂μ) = 0) (heq : h =ᵐ[μ.prod μ] featureKernel k) :
    ∃ (hh : MemLp h 2 (μ.prod μ)) (ι : Type u) (eig : ι → ℝ)
      (e : HilbertBasis ι ℝ (Lp ℝ 2 μ)),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧ (∑' i, eig i) = ∫ x, ‖k x‖ ^ 2 ∂μ ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      0 < featureBoundedRateConstant β ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (-β / 2 * sourceKernelParticleStatistic h N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |(∫ x, Real.exp (-β / 2 * sourceKernelParticleStatistic h N x)
          ∂Measure.pi (fun _ : Fin N => μ)) -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          featureBoundedRateConstant β * (1 + ∫ x, featureExponentialMomentWeight β k x ∂μ) ^ 3 / (N : ℝ) ∧
        (MemLp k ∞ μ →
          |(∫ x, Real.exp (-β / 2 * sourceKernelParticleStatistic h N x)
            ∂Measure.pi (fun _ : Fin N => μ)) -
            (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
            featureBoundedRateConstant β * Real.exp
              (featureBoundedRateConstant β * β * (lpNorm k ∞ μ) ^ 2) / (N : ℝ)) := by
  have hk2 := memLp_feature_of_exponential_moment β hβ k hk hM
  have hh : MemLp h 2 (μ.prod μ) := (memLp_congr_ae heq).2 (memLp_featureKernel k hk hk2)
  obtain ⟨ι, eig, e, hi, he, ha, hs, ht, hRate⟩ :=
    exists_sourceKernelParticleStatistic_feature_rate β hβ h hh k hk hM hmean heq
  obtain ⟨hP, hD, _⟩ := sourceKernel_eigenbasis_feature_rate β hβ h hh k hk hM hmean heq eig e he
  refine ⟨hh, ι, eig, e, hi, he, ha, hs, ht, hP, hD,
    featureBoundedRateConstant_pos β hβ, fun N hN => ⟨(hRate N hN).1, ?_, ?_⟩⟩
  · exact originalFeature_rate_source_constant β _ _ _ hβ
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_integral_featureExponentialMomentWeight β hβ k hM))
      N hN (hRate N hN).2
  · intro hkinf
    exact feature_bounded_rate_numeric β _ _ _ _ hβ
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) (one_le_integral_featureExponentialMomentWeight β hβ k hM))
      (integral_featureExponentialMomentWeight_le_bounded β hβ k hk hkinf) N hN (hRate N hN).2

/-- Original bounded-feature clause with NO supplied moment premise. Actual
source-kernel membership, spectral data and determinant product are constructed. -/
theorem original_boundedFeatureQuadLaplace_of_memLp_top
    (β : ℝ) (hβ : 0 ≤ β) (h : X × X → ℝ) (k : X → H)
    (hk : StronglyMeasurable k) (hkinf : MemLp k ∞ μ)
    (hmean : (∫ x, k x ∂μ) = 0) (heq : h =ᵐ[μ.prod μ] featureKernel k) :
    ∃ (hh : MemLp h 2 (μ.prod μ)) (ι : Type u) (eig : ι → ℝ)
      (e : HilbertBasis ι ℝ (Lp ℝ 2 μ)),
      Countable ι ∧
      (∀ i, DGRHS.Kernel.integralOperator h hh (e i) = eig i • e i) ∧
      (∀ i, 0 ≤ eig i) ∧ Summable eig ∧ (∑' i, eig i) = ∫ x, ‖k x‖ ^ 2 ∂μ ∧
      HasProd (fun i => (1 + β * eig i) * Real.exp (-(β * eig i)))
        (DGRHS.Kernel.regularizedDet (fun i => β * eig i)) ∧
      0 < DGRHS.Kernel.regularizedDet (fun i => β * eig i) ∧
      0 < featureBoundedRateConstant β ∧
      ∀ N : ℕ, 1 ≤ N →
        Integrable (fun x => Real.exp (-β / 2 * sourceKernelParticleStatistic h N x))
          (Measure.pi (fun _ : Fin N => μ)) ∧
        |(∫ x, Real.exp (-β / 2 * sourceKernelParticleStatistic h N x)
          ∂Measure.pi (fun _ : Fin N => μ)) -
          (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β * eig i)))⁻¹| ≤
          featureBoundedRateConstant β * Real.exp
            (featureBoundedRateConstant β * β * (lpNorm k ∞ μ) ^ 2) / (N : ℝ) := by
  obtain ⟨hh, ι, eig, e, hi, he, ha, hs, ht, hP, hD, hC, hRate⟩ :=
    original_boundedFeatureQuadLaplace β hβ h k hk
      (integrable_featureExponentialMomentWeight_of_memLp_top β hβ k hk hkinf) hmean heq
  exact ⟨hh, ι, eig, e, hi, he, ha, hs, ht, hP, hD, hC,
    fun N hN => ⟨(hRate N hN).1, (hRate N hN).2.2 hkinf⟩⟩

end DGRHS.Gaussian

#check DGRHS.Gaussian.originalFeature_rate_source_constant
#print axioms DGRHS.Gaussian.originalFeature_rate_source_constant
#check DGRHS.Gaussian.original_boundedFeatureQuadLaplace
#print axioms DGRHS.Gaussian.original_boundedFeatureQuadLaplace
#check DGRHS.Gaussian.original_boundedFeatureQuadLaplace_of_memLp_top
#print axioms DGRHS.Gaussian.original_boundedFeatureQuadLaplace_of_memLp_top
