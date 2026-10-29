import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Algebra.Polynomial.Eval.Defs

noncomputable section
open Finset
namespace DGRHS.Concentration

lemma antidiagonal_degree_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (m : ℕ) (l : ι →₀ ℕ)
    (hl : l ∈ Finset.finsuppAntidiag s m) (i : ι) (hi : i ∈ s) : l i ≤ m := by
  have hs : ∑ j ∈ s, l j = m := (Finset.mem_finsuppAntidiag.mp hl).1
  rw [← hs]
  exact Finset.single_le_sum (fun j _ ↦ Nat.zero_le (l j)) hi

lemma polynomial_coe_prod {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℝ) :
    ((∏ i ∈ s, P i : Polynomial ℝ) : PowerSeries ℝ) =
      ∏ i ∈ s, (P i : PowerSeries ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Polynomial.coe_mul, ih]

lemma polynomial_coeff_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → Polynomial ℝ) (m : ℕ) :
    (∏ i ∈ s, P i).coeff m =
      ∑ l ∈ Finset.finsuppAntidiag s m, ∏ i ∈ s, (P i).coeff (l i) := by
  rw [← Polynomial.coeff_coe, polynomial_coe_prod, PowerSeries.coeff_prod]
  simp only [Polynomial.coeff_coe]

lemma polynomial_coeff_prod_nonneg {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P : ι → Polynomial ℝ)
    (hP : ∀ i ∈ s, ∀ n, 0 ≤ (P i).coeff n) (m : ℕ) :
    0 ≤ (∏ i ∈ s, P i).coeff m := by
  rw [polynomial_coeff_prod]
  exact Finset.sum_nonneg fun l _ ↦ Finset.prod_nonneg fun i hi ↦ hP i hi (l i)

lemma polynomial_coeff_prod_abs_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (P Q : ι → Polynomial ℝ)
    (hPQ : ∀ i ∈ s, ∀ n, |(P i).coeff n| ≤ (Q i).coeff n) (m : ℕ) :
    |(∏ i ∈ s, P i).coeff m| ≤ (∏ i ∈ s, Q i).coeff m := by
  rw [polynomial_coeff_prod, polynomial_coeff_prod]
  calc
    |∑ l ∈ Finset.finsuppAntidiag s m, ∏ i ∈ s, (P i).coeff (l i)| ≤
        ∑ l ∈ Finset.finsuppAntidiag s m, |∏ i ∈ s, (P i).coeff (l i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ l ∈ Finset.finsuppAntidiag s m, ∏ i ∈ s, |(P i).coeff (l i)| := by
      simp_rw [Finset.abs_prod]
    _ ≤ ∑ l ∈ Finset.finsuppAntidiag s m, ∏ i ∈ s, (Q i).coeff (l i) := by
      apply Finset.sum_le_sum
      intro l hl
      exact Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) (fun i hi ↦ hPQ i hi (l i))

lemma polynomial_coeff_le_eval_one (P : Polynomial ℝ)
    (hP : ∀ n, 0 ≤ P.coeff n) (m : ℕ) : P.coeff m ≤ P.eval 1 := by
  classical
  have heval : P.eval 1 = ∑ n ∈ P.support, P.coeff n := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    simp
  rw [heval]
  by_cases hm : m ∈ P.support
  · exact Finset.single_le_sum (fun n _ ↦ hP n) hm
  · rw [Polynomial.notMem_support_iff.mp hm]
    exact Finset.sum_nonneg fun n _ ↦ hP n

#print axioms DGRHS.Concentration.antidiagonal_degree_le
#print axioms DGRHS.Concentration.polynomial_coeff_prod_abs_le
#print axioms DGRHS.Concentration.polynomial_coeff_le_eval_one
end DGRHS.Concentration
