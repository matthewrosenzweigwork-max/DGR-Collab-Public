/- Unchecked preparation outside root proof. Constructed finite Gaussian target. -/
import DGRHS.CLT.FiniteDimensionalCLT
import DGRHS.Gaussian.FiniteHilbertEvaluation
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology InnerProductSpace BigOperators
namespace DGRHS.CLT
variable {E Ω j : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace Ω] [Fintype j]
  {P : Measure Ω} [IsProbabilityMeasure P]

def finiteStandardVector (b : HilbertBasis j ℝ E) (z : j → ℝ) : E :=
  ∑ i, z i • b i

lemma measurable_finiteStandardVector (b : HilbertBasis j ℝ E) :
    Measurable (finiteStandardVector b) := by
  classical
  unfold finiteStandardVector
  apply Finset.measurable_sum
  intro i _
  exact (measurable_pi_apply i).smul measurable_const

/-- The target projection law is derived from an actual finite Gaussian
product and a complete Hilbert basis, including dimension zero. -/
lemma hasLaw_inner_finiteStandardVector (b : HilbertBasis j ℝ E) (t : E) :
    HasLaw (fun z ↦ inner ℝ (finiteStandardVector b z) t)
      (gaussianReal 0 (Real.toNNReal (‖t‖^2)))
      (DGRHS.Gaussian.finiteStandardGaussian j) := by
  classical
  have he : (fun z ↦ inner ℝ (finiteStandardVector b z) t) =
      DGRHS.Gaussian.finiteHilbertEvaluation b (fun _ : Unit ↦ t) () := by
    funext z
    simp only [finiteStandardVector,sum_inner,inner_smul_left,
      DGRHS.Gaussian.finiteHilbertEvaluation,DGRHS.Gaussian.finiteFeatureEvaluation,
      conj_trivial]
    apply Finset.sum_congr rfl
    intro i _
    simp only [smul_eq_mul,mul_comm]
  have hm : Measurable (fun z ↦ inner ℝ (finiteStandardVector b z) t) := by
    have := measurable_finiteStandardVector b
    fun_prop
  rw [he] at hm
  rw [he]
  exact ⟨hm.aemeasurable,
    DGRHS.Gaussian.map_finiteHilbertEvaluation_eq_gaussianReal b (fun _ : Unit ↦ t) ()⟩

/-- No Gaussian target law or limiting distribution is assumed: every
projection law is proved for the concrete standard vector. -/
theorem finite_dimensional_isotropic_clt
    (b : HilbertBasis j ℝ E) (X : ℕ → Ω → E)
    (hX : MemLp (X 0) 2 P) (hmean : (∫ ω, X 0 ω ∂P) = 0)
    (hindep : iIndepFun X P) (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (hvariance : ∀ t : E, variance (fun ω ↦ inner ℝ (X 0 ω) t) P = ‖t‖^2) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, X i ω)
      atTop (finiteStandardVector b) (fun _ ↦ P)
      (DGRHS.Gaussian.finiteStandardGaussian j) := by
  apply finite_dimensional_centered_clt X (finiteStandardVector b) hX hmean hindep hident
    (measurable_finiteStandardVector b).aemeasurable
  intro t
  rw [hvariance]
  exact hasLaw_inner_finiteStandardVector b t
end DGRHS.CLT
#print axioms DGRHS.CLT.hasLaw_inner_finiteStandardVector
#print axioms DGRHS.CLT.finite_dimensional_isotropic_clt
