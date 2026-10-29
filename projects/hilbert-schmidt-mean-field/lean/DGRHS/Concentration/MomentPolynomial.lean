import DGRHS.Concentration.Arithmetic
import DGRHS.Concentration.FormalExpansion
import DGRHS.Concentration.Coefficients
import DGRHS.Concentration.Integrability

noncomputable section
open MeasureTheory ProbabilityTheory Finset
namespace DGRHS.Concentration

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

def rawMomentSeries (μ : Measure Ω) (f : Ω → ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun r ↦ (∫ ω, f ω ^ r ∂μ) / (r.factorial : ℝ)

def positiveMomentSeries (μ : Measure Ω) (f : Ω → ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun r ↦ if r = 1 then 0 else
    (∫ ω, |f ω| ^ r ∂μ) / (r.factorial : ℝ)

def rawMomentPolynomial (μ : Measure Ω) (f : Ω → ℝ) (m : ℕ) : Polynomial ℝ :=
  PowerSeries.trunc (m + 1) (rawMomentSeries μ f)

def positiveMomentPolynomial (μ : Measure Ω) (f : Ω → ℝ) (m : ℕ) : Polynomial ℝ :=
  PowerSeries.trunc (m + 1) (positiveMomentSeries μ f)

lemma positiveMomentPolynomial_coeff_nonneg (μ : Measure Ω) (f : Ω → ℝ) (m r : ℕ) :
    0 ≤ (positiveMomentPolynomial μ f m).coeff r := by
  simp only [positiveMomentPolynomial, PowerSeries.coeff_trunc]
  split_ifs with hr
  · simp only [positiveMomentSeries, PowerSeries.coeff_mk]
    split_ifs
    · exact le_refl 0
    · exact div_nonneg (integral_nonneg fun ω ↦ pow_nonneg (abs_nonneg (f ω)) r)
        (Nat.cast_nonneg _)
  · exact le_refl 0

lemma rawMomentPolynomial_abs_coeff_le (μ : Measure Ω) (f : Ω → ℝ)
    (hc : ∫ ω, f ω ∂μ = 0) (m r : ℕ) :
    |(rawMomentPolynomial μ f m).coeff r| ≤
      (positiveMomentPolynomial μ f m).coeff r := by
  simp only [rawMomentPolynomial, positiveMomentPolynomial, PowerSeries.coeff_trunc]
  split_ifs with hr
  · simp only [rawMomentSeries, positiveMomentSeries, PowerSeries.coeff_mk]
    by_cases hr1 : r = 1
    · subst r
      simp [hc]
    · rw [if_neg hr1, abs_div]
      have hfa : |(r.factorial : ℝ)| = (r.factorial : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
      rw [hfa]
      simpa only [abs_pow] using
        div_le_div_of_nonneg_right (abs_integral_le_integral_abs (f := fun ω ↦ f ω ^ r))
          (Nat.cast_nonneg r.factorial)
  · simp

lemma mixed_power_integrable [DecidableEq ι] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hX : iIndepFun X μ)
    (hXm : ∀ i, AEStronglyMeasurable (X i) μ) (m : ℕ)
    (hh : ∀ i, Integrable (fun ω ↦ |X i ω| ^ m) μ)
    (l : ι →₀ ℕ) (hl : l ∈ Finset.finsuppAntidiag Finset.univ m) :
    Integrable (fun ω ↦ ∏ i, X i ω ^ l i / ((l i).factorial : ℝ)) μ := by
  classical
  apply independent_mixed_product_integrable μ X hX (fun i ↦ (hXm i).aemeasurable)
    (fun i x ↦ x ^ l i / ((l i).factorial : ℝ))
  intro i
  apply (integrable_map_measure (by fun_prop) (hXm i).aemeasurable).2
  simpa only [Function.comp_def] using
    (lower_raw_power_integrable μ (X i) m (l i) (hXm i) (hh i)
      (antidiagonal_degree_le Finset.univ m l hl i (Finset.mem_univ i))).div_const
        ((l i).factorial : ℝ)

lemma moment_div_factorial_eq_coefficient (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hX : iIndepFun X μ)
    (hXm : ∀ i, AEStronglyMeasurable (X i) μ) (m : ℕ)
    (hh : ∀ i, Integrable (fun ω ↦ |X i ω| ^ m) μ) :
    (∫ ω, (∑ i, X i ω) ^ m ∂μ) / (m.factorial : ℝ) =
      (∏ i, rawMomentPolynomial μ (X i) m).coeff m := by
  classical
  have hx (ω : Ω) : (∑ i, X i ω) ^ m / (m.factorial : ℝ) =
      ∑ l ∈ Finset.finsuppAntidiag Finset.univ m,
        ∏ i, X i ω ^ l i / ((l i).factorial : ℝ) := by
    rw [sum_power_div_factorial_eq_coeff_prod Finset.univ (fun i ↦ X i ω) m,
      PowerSeries.coeff_prod]
    simp only [coeff_rescaled_formal_exp]
  rw [← integral_div]
  calc
    (∫ ω, (∑ i, X i ω) ^ m / (m.factorial : ℝ) ∂μ) =
        ∫ ω, ∑ l ∈ Finset.finsuppAntidiag Finset.univ m,
          ∏ i, X i ω ^ l i / ((l i).factorial : ℝ) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall hx)
    _ = ∑ l ∈ Finset.finsuppAntidiag Finset.univ m,
        ∫ ω, ∏ i, X i ω ^ l i / ((l i).factorial : ℝ) ∂μ := by
      apply integral_finsetSum
      exact fun l hl ↦ mixed_power_integrable μ X hX hXm m hh l hl
    _ = ∑ l ∈ Finset.finsuppAntidiag Finset.univ m,
        ∏ i, (∫ ω, X i ω ^ l i ∂μ) / ((l i).factorial : ℝ) := by
      apply Finset.sum_congr rfl
      intro l hl
      have heq := hX.integral_fun_prod_comp
        (f := fun i (x : ℝ) ↦ x ^ l i / ((l i).factorial : ℝ))
        (fun i ↦ (hXm i).aemeasurable) (fun i ↦ by fun_prop)
      simpa only [integral_div] using heq
    _ = (∏ i, rawMomentPolynomial μ (X i) m).coeff m := by
      rw [polynomial_coeff_prod]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.prod_congr rfl
      intro i hi
      have hli : l i < m + 1 := Nat.lt_succ_of_le
        (antidiagonal_degree_le Finset.univ m l hl i hi)
      simp only [rawMomentPolynomial, PowerSeries.coeff_trunc, if_pos hli,
        rawMomentSeries, PowerSeries.coeff_mk]

lemma positiveMomentPolynomial_eval_one (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (m : ℕ) (hm : 2 ≤ m) :
    (positiveMomentPolynomial μ f m).eval 1 =
      1 + ∑ q ∈ Finset.range (m - 1),
        (∫ ω, |f ω| ^ (q + 2) ∂μ) / ((q + 2).factorial : ℝ) := by
  classical
  have heval : (positiveMomentPolynomial μ f m).eval 1 =
      ∑ r ∈ Finset.range (m + 1),
        if r = 1 then 0 else (∫ ω, |f ω| ^ r ∂μ) / (r.factorial : ℝ) := by
    change (PowerSeries.trunc (m + 1) (positiveMomentSeries μ f)).eval₂
      (RingHom.id ℝ) 1 = _
    rw [PowerSeries.eval₂_trunc_eq_sum_range]
    simp only [RingHom.id_apply, one_pow, mul_one, positiveMomentSeries, PowerSeries.coeff_mk]
  rw [heval, show m + 1 = 2 + (m - 1) by omega, Finset.sum_range_add]
  have hfirst : (∑ r ∈ Finset.range 2,
      if r = 1 then 0 else (∫ ω, |f ω| ^ r ∂μ) / (r.factorial : ℝ)) = 1 := by
    simp [Finset.sum_range_succ]
  rw [hfirst]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hq1 : q + 2 ≠ 1 := by omega
  simp only [Nat.add_comm 2 q, if_neg hq1]

lemma even_moment_polynomial_majorant (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hX : iIndepFun X μ)
    (hXm : ∀ i, AEStronglyMeasurable (X i) μ) (k : ℕ) (hk : 1 ≤ k)
    (hh : ∀ i, Integrable (fun ω ↦ |X i ω| ^ (2 * k)) μ)
    (hc : ∀ i, ∫ ω, X i ω ∂μ = 0) :
    (∫ ω, |∑ i, X i ω| ^ (2 * k) ∂μ) ≤
      ((2 * k).factorial : ℝ) * ∏ i,
        (1 + ∑ q ∈ Finset.range (2 * k - 1),
          (∫ ω, |X i ω| ^ (q + 2) ∂μ) / ((q + 2).factorial : ℝ)) := by
  classical
  have hm : 2 ≤ 2 * k := by omega
  have hcoef : (∫ ω, |∑ i, X i ω| ^ (2 * k) ∂μ) / ((2 * k).factorial : ℝ) =
      (∏ i, rawMomentPolynomial μ (X i) (2 * k)).coeff (2 * k) := by
    simpa only [pow_abs_two_mul] using
      moment_div_factorial_eq_coefficient μ X hX hXm (2 * k) hh
  have hbound : (∫ ω, |∑ i, X i ω| ^ (2 * k) ∂μ) / ((2 * k).factorial : ℝ) ≤
      (∏ i, positiveMomentPolynomial μ (X i) (2 * k)).eval 1 := by
    rw [hcoef]
    calc
      _ ≤ |(∏ i, rawMomentPolynomial μ (X i) (2 * k)).coeff (2 * k)| := le_abs_self _
      _ ≤ (∏ i, positiveMomentPolynomial μ (X i) (2 * k)).coeff (2 * k) :=
        polynomial_coeff_prod_abs_le Finset.univ _ _
          (fun i _ r ↦ rawMomentPolynomial_abs_coeff_le μ (X i) (hc i) (2 * k) r) _
      _ ≤ (∏ i, positiveMomentPolynomial μ (X i) (2 * k)).eval 1 :=
        polynomial_coeff_le_eval_one _
          (polynomial_coeff_prod_nonneg Finset.univ _
            (fun i _ r ↦ positiveMomentPolynomial_coeff_nonneg μ (X i) (2 * k) r)) _
  have hprod : (∏ i, positiveMomentPolynomial μ (X i) (2 * k)).eval 1 =
      ∏ i, (1 + ∑ q ∈ Finset.range (2 * k - 1),
        (∫ ω, |X i ω| ^ (q + 2) ∂μ) / ((q + 2).factorial : ℝ)) := by
    change (Polynomial.evalRingHom 1) (∏ i, positiveMomentPolynomial μ (X i) (2 * k)) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro i hi
    exact positiveMomentPolynomial_eval_one μ (X i) (2 * k) hm
  rw [hprod] at hbound
  have hfac : 0 < ((2 * k).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos (2 * k)
  have hh' := (div_le_iff₀ hfac).mp hbound
  simpa only [mul_comm] using hh'


lemma normalized_even_moment_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ) (hX : iIndepFun X μ)
    (hXm : ∀ i, AEStronglyMeasurable (X i) μ) (k : ℕ) (hk : 1 ≤ k)
    (hh : ∀ i, Integrable (fun ω ↦ |X i ω| ^ (2 * k)) μ)
    (hc : ∀ i, ∫ ω, X i ω ∂μ = 0)
    (hv : (∑ i, ∫ ω, X i ω ^ 2 ∂μ) ≤ (2 * k : ℕ))
    (hM : (∑ i, ∫ ω, |X i ω| ^ (2 * k) ∂μ) ≤ 1) :
    (∫ ω, |∑ i, X i ω| ^ (2 * k) ∂μ) ≤
      ((2 * k).factorial : ℝ) * Real.exp (2 * k : ℕ) := by
  classical
  have hm : 2 ≤ 2 * k := by omega
  have hvabs : (∑ i, ∫ ω, |X i ω| ^ 2 ∂μ) ≤ (2 * k : ℕ) := by
    calc
      (∑ i, ∫ ω, |X i ω| ^ 2 ∂μ) = (∑ i, ∫ ω, X i ω ^ 2 ∂μ) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω ↦ by
          change |X i ω| ^ 2 = X i ω ^ 2
          rw [← abs_pow, abs_of_nonneg (sq_nonneg (X i ω))]
      _ ≤ _ := hv
  have hlower (q : ℕ) (hq : q ∈ Finset.range (2 * k - 1)) :
      (∑ i, ∫ ω, |X i ω| ^ (q + 2) ∂μ) ≤ (2 * k : ℕ) + 1 := by
    have hq' : q < 2 * k - 1 := Finset.mem_range.mp hq
    have hrm : q + 2 ≤ 2 * k := by omega
    calc
      _ ≤ ∑ i, ((∫ ω, |X i ω| ^ 2 ∂μ) + (∫ ω, |X i ω| ^ (2 * k) ∂μ)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hI2 := lower_abs_power_integrable μ (X i) (2 * k) 2 (hXm i) (hh i) hm
        have hIr := lower_abs_power_integrable μ (X i) (2 * k) (q + 2) (hXm i) (hh i) hrm
        rw [← integral_add hI2 (hh i)]
        apply integral_mono hIr (hI2.add (hh i))
        intro ω
        change |X i ω| ^ (q + 2) ≤ |X i ω| ^ 2 + |X i ω| ^ (2 * k)
        exact power_le_second_add_high |X i ω| (abs_nonneg (X i ω)) (2 * k) (q + 2)
          (by omega) hrm
      _ = (∑ i, ∫ ω, |X i ω| ^ 2 ∂μ) + (∑ i, ∫ ω, |X i ω| ^ (2 * k) ∂μ) :=
        Finset.sum_add_distrib
      _ ≤ _ := add_le_add hvabs hM
  let a : ι → ℝ := fun i ↦ ∑ q ∈ Finset.range (2 * k - 1),
    (∫ ω, |X i ω| ^ (q + 2) ∂μ) / ((q + 2).factorial : ℝ)
  have ha : ∀ i, 0 ≤ a i := by
    intro i
    exact Finset.sum_nonneg fun q hq ↦
      div_nonneg (integral_nonneg fun ω ↦ pow_nonneg (abs_nonneg (X i ω)) (q + 2))
        (Nat.cast_nonneg _)
  have hsum : (∑ i, a i) ≤ (2 * k : ℕ) := by
    calc
      (∑ i, a i) = ∑ q ∈ Finset.range (2 * k - 1),
          ∑ i, (∫ ω, |X i ω| ^ (q + 2) ∂μ) / ((q + 2).factorial : ℝ) :=
        Finset.sum_comm
      _ ≤ ∑ q ∈ Finset.range (2 * k - 1), ((2 * k : ℕ) + 1 : ℝ) / ((q + 2).factorial : ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        rw [← Finset.sum_div]
        exact div_le_div_of_nonneg_right (hlower q hq) (Nat.cast_nonneg _)
      _ = ((2 * k : ℕ) + 1 : ℝ) *
          ∑ q ∈ Finset.range (2 * k - 1), 1 / ((q + 2).factorial : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ _ := normalized_factorial_sum_bound (2 * k) hm
  have hprod : (∏ i, (1 + a i)) ≤ Real.exp (2 * k : ℕ) :=
    (Real.prod_one_add_le_exp_sum Finset.univ ha).trans (Real.exp_monotone hsum)
  have hmajor := even_moment_polynomial_majorant μ X hX hXm k hk hh hc
  exact hmajor.trans (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg _))

#print axioms DGRHS.Concentration.normalized_even_moment_bound

#print axioms DGRHS.Concentration.moment_div_factorial_eq_coefficient
#print axioms DGRHS.Concentration.even_moment_polynomial_majorant
end DGRHS.Concentration
