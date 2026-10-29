import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Mul
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Integration

noncomputable section
open MeasureTheory ProbabilityTheory Finset

namespace DGRHS.Decoupling

def fairBool : Measure Bool := (PMF.uniformOfFintype Bool).toMeasure
instance : IsProbabilityMeasure fairBool := by unfold fairBool; infer_instance

def selectorLaw (ι : Type*) [Fintype ι] : Measure (ι → Bool) :=
  Measure.pi (fun _ ↦ fairBool)
instance (ι : Type*) [Fintype ι] : IsProbabilityMeasure (selectorLaw ι) := by
  unfold selectorLaw; infer_instance

def bit (b : Bool) : ℝ := if b then 1 else 0

lemma integral_bit : ∫ b, bit b ∂fairBool = 1 / 2 := by
  unfold fairBool
  rw [PMF.integral_eq_sum]
  norm_num [bit, PMF.uniformOfFintype_apply, Fintype.sum_bool]

lemma integral_one_sub_bit : ∫ b, (1 - bit b) ∂fairBool = 1 / 2 := by
  unfold fairBool
  rw [PMF.integral_eq_sum]
  norm_num [bit, PMF.uniformOfFintype_apply, Fintype.sum_bool]

lemma integral_selector_pair {ι : Type*} [Fintype ι] (i j : ι) (hij : i ≠ j) :
    ∫ s, bit (s i) * (1 - bit (s j)) ∂selectorLaw ι = 1 / 4 := by
  have hi : iIndepFun (fun i (s : ι → Bool) ↦ s i) (selectorLaw ι) :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have h := (hi.indepFun hij).comp (measurable_of_finite bit)
    (measurable_of_finite (fun b ↦ 1 - bit b))
  have he := h.integral_fun_mul_eq_mul_integral ((measurable_of_finite _).aestronglyMeasurable) ((measurable_of_finite _).aestronglyMeasurable)
  simp only [Function.comp_def] at he
  rw [he]
  change (∫ s, bit (s i) ∂Measure.pi (fun _ : ι ↦ fairBool)) *
    (∫ s, (1 - bit (s j)) ∂Measure.pi (fun _ : ι ↦ fairBool)) = _
  rw [integral_comp_eval (μ := fun _ : ι ↦ fairBool) (X := fun _ : ι ↦ Bool) (i := i) (f := bit) ((measurable_of_finite _).aestronglyMeasurable),
    integral_comp_eval (μ := fun _ : ι ↦ fairBool) (X := fun _ : ι ↦ Bool) (i := j) (f := fun b : Bool ↦ 1 - bit b) ((measurable_of_finite _).aestronglyMeasurable),
    integral_bit, integral_one_sub_bit]
  norm_num

/-- Ordered off-diagonal sum: distinct sample indices, not distinct positions. -/
def offDiagonalSum {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ι → ℝ) : ℝ :=
  ∑ i, ∑ j, if i ≠ j then a i j else 0

/-- One directed block of a fair partition of the sample indices. -/
def crossSum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ι → ℝ) (s : ι → Bool) : ℝ :=
  ∑ i, ∑ j, if i ≠ j then bit (s i) * (1 - bit (s j)) * a i j else 0

lemma integral_crossSum {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ι → ι → ℝ) :
    ∫ s, crossSum a s ∂selectorLaw ι = (1 / 4) * offDiagonalSum a := by
  unfold crossSum offDiagonalSum
  rw [integral_finsetSum _ (fun _ _ ↦ .of_finite)]
  simp_rw [integral_finsetSum _ (fun _ _ ↦ Integrable.of_finite)]
  rw [mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  by_cases hij : i ≠ j
  · simp_rw [if_pos hij]
    rw [integral_mul_const, integral_selector_pair i j hij]
  · simp [hij]

/-- The first, finite-selector Jensen step with the exact factor four. -/
theorem selector_even_moment {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ι → ℝ) (k : ℕ) :
    |offDiagonalSum a| ^ (2 * k) ≤
      4 ^ (2 * k) * ∫ s, |crossSum a s| ^ (2 * k) ∂selectorLaw ι := by
  have hj := ((even_two_mul k).convexOn_pow (𝕜 := ℝ)).map_integral_le
    (μ := selectorLaw ι) (f := fun s ↦ (4 : ℝ) * crossSum a s)
    (continuous_pow (2 * k)).continuousOn isClosed_univ
    (Filter.Eventually.of_forall (fun _ ↦ Set.mem_univ _))
    Integrable.of_finite Integrable.of_finite
  rw [integral_const_mul, integral_crossSum] at hj
  have heq : (4 : ℝ) * ((1 / 4) * offDiagonalSum a) = offDiagonalSum a := by ring
  rw [heq] at hj
  simpa only [pow_abs_two_mul, mul_pow, integral_const_mul] using hj

#print axioms DGRHS.Decoupling.integral_crossSum
#print axioms DGRHS.Decoupling.selector_even_moment

end DGRHS.Decoupling
