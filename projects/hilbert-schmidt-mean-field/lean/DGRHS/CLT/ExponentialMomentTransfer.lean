/- Actual exponential expectation transfer on changing particle spaces.
Higher exponential moments are actual integrals, not the desired limit. -/
import DGRHS.CLT.PositiveMomentTransfer
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace DGRHS.CLT

lemma exp_le_one_add_exp_mul (x p : ℝ) (hp : 1 ≤ p) :
    Real.exp x ≤ 1+Real.exp (p*x) := by
  by_cases hx : 0 ≤ x
  · have he : Real.exp x ≤ Real.exp (p*x) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  · have he : Real.exp x ≤ 1 := by
      simpa using Real.exp_le_exp.mpr (le_of_not_ge hx)
    linarith [Real.exp_pos (p*x)]

lemma integrable_exp_of_higher_exp {S : Type*} [MeasurableSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] {X : S → ℝ}
    (hX : AEMeasurable X μ) {p : ℝ} (hp : 1 ≤ p)
    (hpm : Integrable (fun x => Real.exp (p*X x)) μ) :
    Integrable (fun x => Real.exp (X x)) μ := by
  apply ((integrable_const (1:ℝ)).add hpm).mono'
    (Real.continuous_exp.measurable.comp_aemeasurable hX).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    change ‖Real.exp (X x)‖ ≤ 1+Real.exp (p*X x)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_le_one_add_exp_mul _ _ hp

variable {Ω : ℕ → Type*} {Ω' : Type*}
  [∀ n, MeasurableSpace (Ω n)] [MeasurableSpace Ω']
  {μ : ∀ n, Measure (Ω n)} [∀ n, IsProbabilityMeasure (μ n)]
  {ν : Measure Ω'} [IsProbabilityMeasure ν]

lemma exponential_integral_tendsto_of_distribution_moment
    (X : ∀ n, Ω n → ℝ) (Z : Ω' → ℝ)
    (hweak : TendstoInDistribution X atTop Z μ ν)
    (hZ : Integrable (fun z => Real.exp (Z z)) ν)
    (p C : ℝ) (hp : 1 < p)
    (hmom : ∀ n, Integrable (fun x => Real.exp (p*X n x)) (μ n))
    (hC : ∀ n, (∫ x, Real.exp (p*X n x) ∂μ n) ≤ C) :
    Tendsto (fun n => ∫ x, Real.exp (X n x) ∂μ n) atTop
      (𝓝 (∫ z, Real.exp (Z z) ∂ν)) := by
  have heq : ∀ x : ℝ, (Real.exp x)^(1+(p-1)) = Real.exp (p*x) := by
    intro x
    rw [← Real.exp_mul]
    congr 1
    ring
  apply positive_integral_tendsto_of_distribution_moment
    (fun n x => Real.exp (X n x)) (fun z => Real.exp (Z z))
    (hweak.continuous_comp (g := Real.exp) Real.continuous_exp)
    (fun n => integrable_exp_of_higher_exp (hweak.forall_aemeasurable n) hp.le (hmom n)) hZ
    (fun n => ae_of_all _ fun x => (Real.exp_pos _).le)
    (ae_of_all _ fun z => (Real.exp_pos _).le) (p-1) C (by linarith)
  · intro n
    simpa only [heq] using hmom n
  · intro n
    simpa only [heq] using hC n

end DGRHS.CLT
#print axioms DGRHS.CLT.exp_le_one_add_exp_mul
#print axioms DGRHS.CLT.integrable_exp_of_higher_exp
#print axioms DGRHS.CLT.exponential_integral_tendsto_of_distribution_moment
#check @DGRHS.CLT.exponential_integral_tendsto_of_distribution_moment
