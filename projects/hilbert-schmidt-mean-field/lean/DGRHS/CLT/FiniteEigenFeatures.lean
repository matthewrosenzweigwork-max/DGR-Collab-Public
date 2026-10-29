/- UNCHECKED draft. The covariance premise of the finite CLT is discharged
for actual mean-zero orthonormal L2 eigenfunctions. Nonzero spectral modes
obtain the mean-zero premise from Kernel.integral_eigenfunction_eq_zero. -/
import DGRHS.CLT.FiniteIIDFeaturesCLT
import DGRHS.Kernel.Spectrum
import Mathlib.Probability.Moments.Covariance

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology InnerProductSpace BigOperators
namespace DGRHS.CLT
variable {S E j : Type*} [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype j]
  {μ : Measure S} [IsProbabilityMeasure μ]

def finiteEigenFeature (b : HilbertBasis j ℝ E) (e : j → Lp ℝ 2 μ) (x : S) : E :=
  ∑ i, e i x • b i

lemma measurable_finiteEigenFeature (b : HilbertBasis j ℝ E) (e : j → Lp ℝ 2 μ) :
    Measurable (finiteEigenFeature b e) := by
  classical
  unfold finiteEigenFeature
  apply Finset.measurable_sum
  intro i _
  exact (Lp.stronglyMeasurable (e i)).measurable.smul measurable_const

lemma memLp_finiteEigenFeature (b : HilbertBasis j ℝ E) (e : j → Lp ℝ 2 μ) :
    MemLp (finiteEigenFeature b e) 2 μ := by
  classical
  apply memLp_finsetSum Finset.univ
  intro i _
  simpa only [Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply] using
    (Lp.memLp (e i)).continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ (b i))

lemma integral_finiteEigenFeature (b : HilbertBasis j ℝ E) (e : j → Lp ℝ 2 μ)
    (hm : ∀ i, (∫ x, e i x ∂μ) = 0) :
    (∫ x, finiteEigenFeature b e x ∂μ) = 0 := by
  classical
  unfold finiteEigenFeature
  rw [integral_finsetSum]
  · simp only [integral_smul_const, hm, zero_smul, Finset.sum_const_zero]
  · intro i _
    exact ((Lp.memLp (e i)).continuousLinearMap_comp (ContinuousLinearMap.toSpanSingleton ℝ (b i))).integrable
      (by norm_num)

attribute [local instance] Classical.propDecidable

lemma covariance_orthonormal_L2 (e : j → Lp ℝ 2 μ) (he : Orthonormal ℝ e)
    (hm : ∀ i, (∫ x, e i x ∂μ) = 0) (i l : j) :
    covariance (e i) (e l) μ = if i = l then 1 else 0 := by
  classical
  rw [covariance_eq_sub (Lp.memLp _) (Lp.memLp _), hm, hm]
  have hi : (∫ x, e i x * e l x ∂μ) = inner ℝ (e i) (e l) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by simp [mul_comm])
  simpa only [zero_mul, sub_zero, Pi.mul_apply] using hi.trans (orthonormal_iff_ite.mp he i l)

lemma variance_inner_finiteEigenFeature (b : HilbertBasis j ℝ E) (e : j → Lp ℝ 2 μ)
    (he : Orthonormal ℝ e) (hm : ∀ i, (∫ x, e i x ∂μ) = 0) (t : E) :
    variance (fun x => inner ℝ (finiteEigenFeature b e x) t) μ = ‖t‖ ^ 2 := by
  classical
  have hex : (fun x => inner ℝ (finiteEigenFeature b e x) t) =
      fun x => ∑ i, inner ℝ (b i) t * e i x := by
    funext x
    simp [finiteEigenFeature, sum_inner, real_inner_smul_left, mul_comm]
  rw [hex, variance_fun_sum (fun i => (Lp.memLp (e i)).const_mul _)]
  simp_rw [covariance_const_mul_left, covariance_const_mul_right,
    covariance_orthonormal_L2 e he hm]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, ← pow_two]
  simpa only [HilbertBasis.coe_toOrthonormalBasis] using
    b.toOrthonormalBasis.sum_sq_inner_right t

theorem iid_finite_eigenfeature_clt (b : HilbertBasis j ℝ E) (e : j → Lp ℝ 2 μ)
    (he : Orthonormal ℝ e) (hm : ∀ i, (∫ x, e i x ∂μ) = 0) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → S) => (Real.sqrt n)⁻¹ •
        ∑ i ∈ Finset.range n, finiteEigenFeature b e (ω i)) atTop
      (finiteStandardVector b) (fun _ => Measure.infinitePi (fun _ : ℕ => μ))
      (DGRHS.Gaussian.finiteStandardGaussian j) := by
  exact iid_finite_feature_isotropic_clt μ b (finiteEigenFeature b e)
    (measurable_finiteEigenFeature b e) (memLp_finiteEigenFeature b e)
    (integral_finiteEigenFeature b e hm) (variance_inner_finiteEigenFeature b e he hm)
end DGRHS.CLT

#print axioms DGRHS.CLT.measurable_finiteEigenFeature
#print axioms DGRHS.CLT.memLp_finiteEigenFeature
#print axioms DGRHS.CLT.integral_finiteEigenFeature
#print axioms DGRHS.CLT.covariance_orthonormal_L2
#print axioms DGRHS.CLT.variance_inner_finiteEigenFeature
#print axioms DGRHS.CLT.iid_finite_eigenfeature_clt
