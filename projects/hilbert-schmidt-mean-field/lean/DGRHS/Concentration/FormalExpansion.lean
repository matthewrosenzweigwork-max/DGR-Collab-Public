import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.Analysis.SpecialFunctions.Exp

noncomputable section
open Finset

namespace DGRHS.Concentration

lemma formal_exp_sum_eq_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ) :
    PowerSeries.rescale (∑ i ∈ s, a i) (PowerSeries.exp ℝ) =
      ∏ i ∈ s, PowerSeries.rescale (a i) (PowerSeries.exp ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, Finset.prod_empty]
    rw [PowerSeries.rescale_zero]
    change PowerSeries.C (PowerSeries.constantCoeff (PowerSeries.exp ℝ)) = 1
    rw [PowerSeries.constantCoeff_exp]
    exact map_one _
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi,
      ← PowerSeries.exp_mul_exp_eq_exp_add, ih]


lemma coeff_rescaled_formal_exp (x : ℝ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.rescale x (PowerSeries.exp ℝ)) = x ^ n / (n.factorial : ℝ) := by
  simp [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, div_eq_mul_inv]

lemma sum_power_div_factorial_eq_coeff_prod {ι : Type*} (s : Finset ι) (a : ι → ℝ) (m : ℕ) :
    (∑ i ∈ s, a i) ^ m / (m.factorial : ℝ) =
      PowerSeries.coeff m (∏ i ∈ s, PowerSeries.rescale (a i) (PowerSeries.exp ℝ)) := by
  rw [← formal_exp_sum_eq_prod s a]
  exact (coeff_rescaled_formal_exp _ _).symm

#print axioms DGRHS.Concentration.formal_exp_sum_eq_prod
#print axioms DGRHS.Concentration.sum_power_div_factorial_eq_coeff_prod

end DGRHS.Concentration
