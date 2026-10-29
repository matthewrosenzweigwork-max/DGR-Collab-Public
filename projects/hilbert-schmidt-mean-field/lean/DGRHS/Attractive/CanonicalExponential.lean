import DGRHS.Attractive.CanonicalFactorialMoment
import DGRHS.Attractive.EvenMomentSeries

noncomputable section
open MeasureTheory
namespace DGRHS.Attractive
variable {Ω : Type*} [MeasurableSpace Ω]

lemma attractiveNormalizedStatistic_measurable (n : ℕ)
    (h : Ω × Ω → ℝ) (hh : Measurable h) : Measurable (attractiveNormalizedStatistic n h) := by
  have hm : Measurable (fun x : Fin n → Ω ↦
      DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (x i,x j))) := by
    unfold DGRHS.Decoupling.offDiagonalSum
    apply Finset.measurable_sum
    intro i hi
    apply Finset.measurable_sum
    intro j hj
    by_cases hij : i ≠ j
    · simp_rw [if_pos hij]
      exact hh.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
    · simp_rw [if_neg hij]
      exact measurable_const
  exact hm.neg.div_const (n : ℝ)

/-- Actual proper exponential moments from the source row hypothesis, with
no supplied whole-statistic moment, exponential properness, or partition bound.
The same finite constant applies to every particle number, including 0 and 1. -/
theorem attractiveCanonical_uniform_exponential (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (hs : ∀ x y, h (x,y) = h (y,x))
    (hc : ∀ᵐ y ∂μ, ∫ x, h (x,y) ∂μ = 0) (t : ℝ)
    (ht : |t| * (attractiveMomentConstant*C) < 1) :
    ∀ n : ℕ,
      Integrable (fun x : Fin n → Ω ↦ Real.exp (t*attractiveNormalizedStatistic n h x))
        (Measure.pi (fun _ : Fin n ↦ μ)) ∧
      (∫ x : Fin n → Ω, Real.exp (t*attractiveNormalizedStatistic n h x)
        ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤
        2/(1-(t*(attractiveMomentConstant*C))^2) := by
  intro n
  exact exponential_of_even_factorial_moments (Measure.pi (fun _ : Fin n ↦ μ))
    (attractiveNormalizedStatistic n h) (attractiveNormalizedStatistic_measurable n h hh).aemeasurable
    (attractiveMomentConstant*C) t (mul_nonneg attractiveMomentConstant_pos.le hC.nonneg) ht
    (attractiveNormalizedStatistic_even_integrable μ h hh C hC n)
    (attractiveNormalizedStatistic_even_factorial_moment μ h hh C hC hs hc n)

/-- Literal source Z_{N,2β}, for β nonnegative under the source smallness
condition. The denominator is strictly positive by the same smallness. -/
theorem attractiveCanonical_doubled_exponential (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω × Ω → ℝ) (hh : Measurable h) (C : ℝ) (hC : RowFactorialMoments μ h C)
    (hs : ∀ x y, h (x,y) = h (y,x))
    (hc : ∀ᵐ y ∂μ, ∫ x, h (x,y) ∂μ = 0) (β : ℝ) (hβ : 0 ≤ β)
    (hsmall : β*(attractiveMomentConstant*C) < 1) (n : ℕ) :
    Integrable (fun x : Fin n → Ω ↦ Real.exp (-β/(n : ℝ)*
      DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (x i,x j))))
      (Measure.pi (fun _ : Fin n ↦ μ)) ∧
    (∫ x : Fin n → Ω, Real.exp (-β/(n : ℝ)*
      DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (x i,x j)))
      ∂Measure.pi (fun _ : Fin n ↦ μ)) ≤
      2/(1-(β*(attractiveMomentConstant*C))^2) := by
  have ht : |β| * (attractiveMomentConstant*C) < 1 := by
    simpa only [abs_of_nonneg hβ] using hsmall
  have he (x : Fin n → Ω) : β*attractiveNormalizedStatistic n h x =
      -β/(n : ℝ)*DGRHS.Decoupling.offDiagonalSum (fun i j ↦ h (x i,x j)) := by
    unfold attractiveNormalizedStatistic
    ring
  simpa only [he] using attractiveCanonical_uniform_exponential μ h hh C hC hs hc β ht n

#check @DGRHS.Attractive.attractiveCanonical_uniform_exponential
#check @DGRHS.Attractive.attractiveCanonical_doubled_exponential
#print axioms DGRHS.Attractive.attractiveCanonical_uniform_exponential
#print axioms DGRHS.Attractive.attractiveCanonical_doubled_exponential
end DGRHS.Attractive
