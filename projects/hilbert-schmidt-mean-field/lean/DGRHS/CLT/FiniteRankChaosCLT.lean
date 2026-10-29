/- UNCHECKED draft outside the submitted root proof snapshot. The diagonal
law of large numbers and finite chaos limit are derived from actual finite
mean-zero orthonormal eigenfunctions, with no fourth-moment hypothesis. -/
import DGRHS.CLT.FiniteEigenFeatures
import Mathlib.Probability.StrongLaw
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology InnerProductSpace BigOperators
namespace DGRHS.CLT
variable {S E j : Type*} [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype j]
  {μ : Measure S} [IsProbabilityMeasure μ]

def finiteSpectralDiagonal (a : j → ℝ) (e : j → Lp ℝ 2 μ) (x : S) : ℝ :=
  ∑ i, a i * (e i x)^2

lemma measurable_finiteSpectralDiagonal (a : j → ℝ) (e : j → Lp ℝ 2 μ) :
    Measurable (finiteSpectralDiagonal a e) := by
  classical
  unfold finiteSpectralDiagonal
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul ((Lp.stronglyMeasurable (e i)).measurable.pow_const 2)

lemma integrable_finiteSpectralDiagonal (a : j → ℝ) (e : j → Lp ℝ 2 μ) :
    Integrable (finiteSpectralDiagonal a e) μ := by
  classical
  apply integrable_finsetSum
  intro i _
  exact (Lp.memLp (e i)).integrable_sq.const_mul (a i)

lemma integral_finiteSpectralDiagonal (a : j → ℝ) (e : j → Lp ℝ 2 μ)
    (he : Orthonormal ℝ e) :
    (∫ x, finiteSpectralDiagonal a e x ∂μ) = ∑ i, a i := by
  classical
  unfold finiteSpectralDiagonal
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
    have hi : (∫ x, (e i x)^2 ∂μ) = 1 := by
      have hinner := orthonormal_iff_ite.mp he i i
      rw [L2.inner_def] at hinner
      simpa only [ite_true, RCLike.inner_apply', conj_trivial, ← sq] using hinner
    rw [hi,mul_one]
  · intro i _
    exact (Lp.memLp (e i)).integrable_sq.const_mul (a i)

lemma tendstoInMeasure_finiteSpectralDiagonal_average
    (a : j → ℝ) (e : j → Lp ℝ 2 μ) (he : Orthonormal ℝ e) :
    TendstoInMeasure (Measure.infinitePi (fun _ : ℕ => μ))
      (fun (n : ℕ) (ω : ℕ → S) => (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, finiteSpectralDiagonal a e (ω i)) atTop
      (fun _ => ∑ i, a i) := by
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
  have hmean : (∫ ω : ℕ → S, D (ω 0) ∂P) = ∑ i, a i := by
    rw [(iid_feature_identDistrib μ D hm 0).integral_eq]
    exact integral_finiteSpectralDiagonal a e he
  rw [hmean] at havg
  have hmAvg (n : ℕ) : Measurable (fun ω : ℕ → S => (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, finiteSpectralDiagonal a e (ω i)) := by
    apply measurable_const.mul
    apply Finset.measurable_sum
    intro i _
    exact (measurable_finiteSpectralDiagonal a e).comp (measurable_pi_apply i)
  apply tendstoInMeasure_of_tendsto_ae (fun n => (hmAvg n).aestronglyMeasurable)
  simpa only [smul_eq_mul] using havg

def finiteSpectralQuadratic (a : j → ℝ) (b : HilbertBasis j ℝ E) (v : E) : ℝ :=
  ∑ i, a i * (inner ℝ (b i) v)^2

/-- The concrete finite Gaussian chaos limit follows from the constructed
multivariate CLT and the actual diagonal LLN by pinned Slutsky. -/
theorem tendstoInDistribution_finiteSpectralChaos
    (a : j → ℝ) (b : HilbertBasis j ℝ E) (e : j → Lp ℝ 2 μ)
    (he : Orthonormal ℝ e) (hm : ∀ i, (∫ x, e i x ∂μ) = 0) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → S) =>
        finiteSpectralQuadratic a b ((Real.sqrt n)⁻¹ •
          ∑ i ∈ Finset.range n, finiteEigenFeature b e (ω i)) -
        (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, finiteSpectralDiagonal a e (ω i))
      atTop (fun z => finiteSpectralQuadratic a b (finiteStandardVector b z) - ∑ i, a i)
      (fun _ => Measure.infinitePi (fun _ : ℕ => μ))
      (DGRHS.Gaussian.finiteStandardGaussian j) := by
  have hclt := iid_finite_eigenfeature_clt b e he hm
  apply hclt.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun p : E × ℝ => finiteSpectralQuadratic a b p.1 - p.2)
    (Y := fun (n : ℕ) (ω : ℕ → S) => (n : ℝ)⁻¹ *
      ∑ i ∈ Finset.range n, finiteSpectralDiagonal a e (ω i))
    (c := ∑ i, a i)
  · unfold finiteSpectralQuadratic
    fun_prop
  · exact tendstoInMeasure_finiteSpectralDiagonal_average a e he
  · intro n
    have hmAvg : Measurable (fun ω : ℕ → S => (n : ℝ)⁻¹ *
        ∑ i ∈ Finset.range n, finiteSpectralDiagonal a e (ω i)) := by
      apply measurable_const.mul
      apply Finset.measurable_sum
      intro i _
      exact (measurable_finiteSpectralDiagonal a e).comp (measurable_pi_apply i)
    exact hmAvg.aemeasurable
end DGRHS.CLT
#print axioms DGRHS.CLT.integral_finiteSpectralDiagonal
#print axioms DGRHS.CLT.tendstoInMeasure_finiteSpectralDiagonal_average
#print axioms DGRHS.CLT.tendstoInDistribution_finiteSpectralChaos
