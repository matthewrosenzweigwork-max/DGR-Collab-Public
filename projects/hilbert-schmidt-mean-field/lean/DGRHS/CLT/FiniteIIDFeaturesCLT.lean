/- Unchecked preparation outside root proof. Actual iid feature sampling
on the preserved background law's infinite product; no iid law is assumed. -/
import DGRHS.CLT.FiniteStandardCLT
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.Independence.InfinitePi
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology InnerProductSpace BigOperators
namespace DGRHS.CLT
variable {S E j : Type*} [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [Fintype j]
  (μ : Measure S) [IsProbabilityMeasure μ]

lemma iid_feature_identDistrib (F : S → E) (hm : Measurable F) (n : ℕ) :
    IdentDistrib (fun ω : ℕ → S ↦ F (ω n)) F
      (Measure.infinitePi (fun _ : ℕ ↦ μ)) μ := by
  refine ⟨hm.aemeasurable.comp_aemeasurable
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) n).aemeasurable,
    hm.aemeasurable,?_⟩
  rw [← Function.comp_def,← Measure.map_map hm (measurable_pi_apply n),
    (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) n).map_eq]

/-- Product sampling, mutual independence, identical laws and the target
Gaussian projections are all constructed from actual feature data. -/
theorem iid_finite_feature_isotropic_clt
    (b : HilbertBasis j ℝ E) (F : S → E) (hm : Measurable F)
    (hF : MemLp F 2 μ) (hmean : (∫ x, F x ∂μ) = 0)
    (hvariance : ∀ t : E, variance (fun x ↦ inner ℝ (F x) t) μ = ‖t‖^2) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : ℕ → S) ↦ (Real.sqrt n)⁻¹ • ∑ i ∈ Finset.range n, F (ω i))
      atTop (finiteStandardVector b)
      (fun _ ↦ Measure.infinitePi (fun _ : ℕ ↦ μ))
      (DGRHS.Gaussian.finiteStandardGaussian j) := by
  let X := fun n (ω : ℕ → S) ↦ F (ω n)
  have hX0 : MemLp (X 0) 2 (Measure.infinitePi (fun _ : ℕ ↦ μ)) :=
    hF.comp_measurePreserving (measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) 0)
  have hmean0 : (∫ ω, X 0 ω ∂Measure.infinitePi (fun _ : ℕ ↦ μ)) = 0 := by
    rw [(iid_feature_identDistrib μ F hm 0).integral_eq,hmean]
  have hi : iIndepFun X (Measure.infinitePi (fun _ : ℕ ↦ μ)) :=
    iIndepFun_infinitePi (X := fun _ : ℕ ↦ F) (fun _ ↦ hm)
  have hid : ∀ n, IdentDistrib (X n) (X 0)
      (Measure.infinitePi (fun _ : ℕ ↦ μ)) (Measure.infinitePi (fun _ : ℕ ↦ μ)) :=
    fun n ↦ (iid_feature_identDistrib μ F hm n).trans
      (iid_feature_identDistrib μ F hm 0).symm
  apply finite_dimensional_isotropic_clt b X hX0 hmean0 hi hid
  intro t
  rw [(measurePreserving_eval_infinitePi (fun _ : ℕ ↦ μ) 0).variance_fun_comp
    (f := fun x ↦ inner ℝ (F x) t) (by fun_prop),hvariance]
end DGRHS.CLT
#print axioms DGRHS.CLT.iid_feature_identDistrib
#print axioms DGRHS.CLT.iid_finite_feature_isotropic_clt
