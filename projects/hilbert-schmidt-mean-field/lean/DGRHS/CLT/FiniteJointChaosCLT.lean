/- UNCHECKED outside frozen proof. Joint finite arbitrary L2 readouts and
quadratic statistic on the SAME fixed indexed isonormal process. The particle
and diagonal laws are constructed. Arbitrary covariance, repeated observables,
zero/empty modes and L1-only diagonal integrability are retained. -/
import DGRHS.CLT.FiniteCovarianceCLT
import DGRHS.CLT.FiniteParticleChaosCLT
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology BigOperators InnerProductSpace
namespace DGRHS.CLT
variable {S E j : Type*} [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype j]
  {μ : Measure S} [IsProbabilityMeasure μ]

lemma integral_finiteSpectralDiagonal_arbitrary (a : j → ℝ) (e : j → Lp ℝ 2 μ) :
    (∫ x, finiteSpectralDiagonal a e x ∂μ) = ∑ i, a i * ‖e i‖^2 := by
  classical
  unfold finiteSpectralDiagonal
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
    congr 1
    simpa only [Lp.toLp_coeFn] using
      (DGRHS.Kernel.norm_toLp_sq (Lp.memLp (e i))).symm
  · intro i _
    exact (Lp.memLp (e i)).integrable_sq.const_mul (a i)

/-- Only integrability of the squared L2 observables is used. No spatial
fourth moments or orthogonality are required by this diagonal law. -/
lemma tendstoInMeasure_finiteSpectralDiagonal_average_arbitrary
    (a : j → ℝ) (e : j → Lp ℝ 2 μ) :
    TendstoInMeasure (Measure.infinitePi (fun _ : ℕ => μ))
      (fun (n : ℕ) (ω : ℕ → S) => (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, finiteSpectralDiagonal a e (ω i)) atTop
      (fun _ => ∑ i, a i * ‖e i‖^2) := by
  classical
  let P := Measure.infinitePi (fun _ : ℕ => μ)
  let D := finiteSpectralDiagonal a e
  have hm : Measurable D := by
    unfold D finiteSpectralDiagonal
    apply Finset.measurable_sum
    intro i _
    exact measurable_const.mul ((Lp.stronglyMeasurable (e i)).measurable.pow_const 2)
  have hid : ∀ n, IdentDistrib (fun ω : ℕ → S => D (ω n)) (fun ω => D (ω 0)) P P :=
    fun n => (iid_feature_identDistrib μ D hm n).trans
      (iid_feature_identDistrib μ D hm 0).symm
  have hi : iIndepFun (fun (n : ℕ) (ω : ℕ → S) => D (ω n)) P :=
    iIndepFun_infinitePi (X := fun _ : ℕ => D) (fun _ => hm)
  have hint : Integrable (fun ω : ℕ → S => D (ω 0)) P :=
    (measurePreserving_eval_infinitePi (fun _ : ℕ => μ) 0).integrable_comp_of_integrable
      (integrable_finiteSpectralDiagonal a e)
  have havg := strong_law_ae (fun (n : ℕ) (ω : ℕ → S) => D (ω n)) hint
    (fun i l hil => hi.indepFun hil) hid
  have hmean : (∫ ω : ℕ → S, D (ω 0) ∂P) = ∑ i, a i * ‖e i‖^2 := by
    rw [(iid_feature_identDistrib μ D hm 0).integral_eq]
    exact integral_finiteSpectralDiagonal_arbitrary a e
  rw [hmean] at havg
  have hmAvg : ∀ n : ℕ, Measurable (fun ω : ℕ → S => (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, finiteSpectralDiagonal a e (ω i)) := by
    intro n
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    exact (measurable_finiteSpectralDiagonal a e).comp (measurable_pi_apply i)
  apply tendstoInMeasure_of_tendsto_ae (fun n => (hmAvg n).aestronglyMeasurable)
  simpa only [smul_eq_mul] using havg

/-- This retains the full finite vector in the joint target, so later linear
observables may be correlated with the quadratic spectral coordinates. -/
theorem iid_finite_joint_Lp_chaos_clt {ι : Type*} [Countable ι]
    (a : j → ℝ) (b : HilbertBasis j ℝ E) (e : j → Lp ℝ 2 μ)
    (he : ∀ i, (∫ x, e i x ∂μ) = 0)
    (h : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (f : ι → ℕ) (hf : Function.Injective f) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → S) =>
        let v := (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, finiteEigenFeature b e (ω i)
        (v, finiteSpectralQuadratic a b v - (n : ℝ)⁻¹ *
          ∑ i ∈ Finset.range n, finiteSpectralDiagonal a e (ω i))) atTop
      (fun ω =>
        let v := finiteEigenFeature b
          (fun i => DGRHS.Gaussian.indexedGaussianIsometry h f hf (e i)) ω
        (v, finiteSpectralQuadratic a b v - ∑ i, a i * ‖e i‖^2))
      (fun _ => Measure.infinitePi (fun _ : ℕ => μ)) IsonormalProcess.iidStdGaussian := by
  have hclt := iid_finite_Lp_tuple_clt b e he h f hf
  apply hclt.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : E × ℝ => (p.1, finiteSpectralQuadratic a b p.1 - p.2))
    (Y := fun (n : ℕ) (ω : ℕ → S) => (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, finiteSpectralDiagonal a e (ω i))
    (c := ∑ i, a i * ‖e i‖^2)
    (by unfold finiteSpectralQuadratic; fun_prop)
  · exact tendstoInMeasure_finiteSpectralDiagonal_average_arbitrary a e
  · intro n
    apply Measurable.aemeasurable
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    exact (measurable_finiteSpectralDiagonal a e).comp (measurable_pi_apply i)

/-- The changing finite products and original index-off-diagonal statistic
are preserved. Prefix sampling is actual measure-preserving transport. -/
theorem finiteParticleJointChaosCLT {ι : Type*} [Countable ι]
    (a : j → ℝ) (b : HilbertBasis j ℝ E) (e : j → Lp ℝ 2 μ)
    (he : ∀ i, (∫ x, e i x ∂μ) = 0)
    (h : HilbertBasis ι ℝ (Lp ℝ 2 μ)) (f : ι → ℕ) (hf : Function.Injective f) :
    TendstoInDistribution
      (fun N (x : Fin N → S) =>
        ((Real.sqrt N)⁻¹ • ∑ i : Fin N, finiteEigenFeature b e (x i),
          DGRHS.CanonicalVariance.normalizedOffDiagonalSum (finiteSpectralKernel a e) x))
      atTop
      (fun ω =>
        let v := finiteEigenFeature b
          (fun i => DGRHS.Gaussian.indexedGaussianIsometry h f hf (e i)) ω
        (v, finiteSpectralQuadratic a b v - ∑ i, a i * ‖e i‖^2))
      (fun N => Measure.pi (fun _ : Fin N => μ)) IsonormalProcess.iidStdGaussian := by
  classical
  have hc := iid_finite_joint_Lp_chaos_clt a b e he h f hf
  apply tendstoInDistribution_transport_source
    (f := fun N (ω : ℕ → S) => fun i : Fin N => ω i)
    (hf := prefixSample_measurePreserving μ)
  · intro N
    exact (by
      apply Measurable.aemeasurable
      apply Measurable.prodMk
      · apply measurable_const.smul
        apply Finset.measurable_sum
        intro i _
        exact (measurable_finiteEigenFeature b e).comp (measurable_pi_apply i)
      · unfold DGRHS.CanonicalVariance.normalizedOffDiagonalSum
          DGRHS.CanonicalVariance.offDiagonalSum finiteSpectralKernel
        fun_prop)
  · convert hc using 1
    funext N ω
    dsimp only [Function.comp_apply]
    rw [normalizedFiniteKernel_eq_chaosStatistic a b e N]
    simp only [Function.comp_apply, Finset.sum_range]
end DGRHS.CLT
#print axioms DGRHS.CLT.integral_finiteSpectralDiagonal_arbitrary
#print axioms DGRHS.CLT.tendstoInMeasure_finiteSpectralDiagonal_average_arbitrary
#print axioms DGRHS.CLT.iid_finite_joint_Lp_chaos_clt
#print axioms DGRHS.CLT.finiteParticleJointChaosCLT
#check DGRHS.CLT.finiteParticleJointChaosCLT
