/- Development candidate; native polynomial evaluations bound the
actual no-singleton counts. No desired count bound is a premise. -/
import DGRHS.Attractive.SurvivingCount
import DGRHS.Concentration.Arithmetic
noncomputable section
open scoped BigOperators
namespace DGRHS.Attractive

lemma geometric_prefix_le_two (t : ℝ) (ht : 0≤t) (hhalf : t≤1/2) (n : ℕ) :
    (∑ r∈Finset.range n,t^r)≤2 := by
  have hstrong : ∀ n : ℕ,(∑ r∈Finset.range n,t^r)≤2*(1-t^n) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ,pow_succ]
      have hn := pow_nonneg ht n
      nlinarith
  have h := hstrong n
  have hn := pow_nonneg ht n
  nlinarith

lemma vectorCountPolynomial_eval (m : ℕ) (hm : 2≤m) (t : ℝ) :
    (vectorCountPolynomial m).eval t=1+t^2*∑ q∈Finset.range (m-1),t^q := by
  change (PowerSeries.trunc (m+1) (PowerSeries.mk
    (fun r => if r=1 then (0:ℝ) else 1))).eval₂ (RingHom.id ℝ) t=_
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  simp only [RingHom.id_apply,PowerSeries.coeff_mk]
  rw [show m+1=2+(m-1) by omega,Finset.sum_range_add]
  have hfirst : (∑ r∈Finset.range 2,(if r=1 then (0:ℝ) else 1)*t^r)=1 := by
    simp [Finset.sum_range_succ]
  rw [hfirst,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hq1 : 2+q≠1 := by omega
  simp only [if_neg hq1,one_mul,pow_add]

lemma wordCountPolynomial_eval (m : ℕ) (hm : 2≤m) (t : ℝ) :
    (wordCountPolynomial m).eval t=
      1+t^2*∑ q∈Finset.range (m-1),t^q/((q+2).factorial:ℝ) := by
  change (PowerSeries.trunc (m+1) (PowerSeries.mk
    (fun r => if r=1 then (0:ℝ) else 1/(r.factorial:ℝ)))).eval₂ (RingHom.id ℝ) t=_
  rw [PowerSeries.eval₂_trunc_eq_sum_range]
  simp only [RingHom.id_apply,PowerSeries.coeff_mk]
  rw [show m+1=2+(m-1) by omega,Finset.sum_range_add]
  have hfirst : (∑ r∈Finset.range 2,(if r=1 then (0:ℝ) else 1/(r.factorial:ℝ))*t^r)=1 := by
    simp [Finset.sum_range_succ]
  rw [hfirst,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro q hq
  have hq1 : 2+q≠1 := by omega
  have hq2 : q+2≠1 := by omega
  simp only [if_neg hq1,if_neg hq2,pow_add,Nat.add_comm 2 q]
  ring

lemma vectorCountPolynomial_eval_le (m : ℕ) (hm : 2≤m) (t : ℝ)
    (ht : 0≤t) (hhalf : t≤1/2) :
    (vectorCountPolynomial m).eval t≤1+2*t^2 := by
  rw [vectorCountPolynomial_eval m hm]
  have h := mul_le_mul_of_nonneg_left (geometric_prefix_le_two t ht hhalf (m-1)) (sq_nonneg t)
  nlinarith

lemma wordCountPolynomial_eval_le (m : ℕ) (hm : 2≤m) (t : ℝ)
    (ht : 0≤t) (hone : t≤1) :
    (wordCountPolynomial m).eval t≤1+t^2 := by
  rw [wordCountPolynomial_eval m hm]
  have hs : (∑ q∈Finset.range (m-1),t^q/((q+2).factorial:ℝ))≤1 := by
    calc
      _≤∑ q∈Finset.range (m-1),1/((q+2).factorial:ℝ) := by
        apply Finset.sum_le_sum
        intro q hq
        exact div_le_div_of_nonneg_right (pow_le_one₀ ht hone) (Nat.cast_nonneg _)
      _≤3/4 := DGRHS.Concentration.reciprocal_factorial_sum_le (m-1)
      _≤1 := by norm_num
  have h := mul_le_mul_of_nonneg_left hs (sq_nonneg t)
  nlinarith

lemma polynomial_power_coeff_nonneg (P : Polynomial ℝ) (hP : ∀ n,0≤P.coeff n)
    (N m : ℕ) : 0≤(P^N).coeff m := by
  have he : P^N=∏ _ : Fin N,P := by simp
  rw [he]
  exact DGRHS.Concentration.polynomial_coeff_prod_nonneg Finset.univ (fun _ : Fin N=>P)
    (fun _ _ n=>hP n) m

lemma polynomial_power_eval_le_exp (P : Polynomial ℝ) (N : ℕ) (t A : ℝ)
    (hP : 0≤P.eval t) (hA : 0≤A) (hPA : P.eval t≤1+A) :
    (P^N).eval t≤Real.exp ((N:ℝ)*A) := by
  have he : (P^N).eval t=(P.eval t)^N := by
    exact map_pow (Polynomial.evalRingHom t) P N
  rw [he]
  have hbase : P.eval t≤Real.exp A := hPA.trans (by simpa only [add_comm] using Real.add_one_le_exp A)
  calc
    _≤(Real.exp A)^N := pow_le_pow_left₀ hP hbase N
    _=Real.exp ((N:ℝ)*A) := by rw [←Real.exp_nat_mul]

lemma polynomial_eval_nonneg (P : Polynomial ℝ) (hP : ∀ n,0≤P.coeff n)
    (t : ℝ) (ht : 0≤t) : 0≤P.eval t := by
  rw [Polynomial.eval_eq_sum,Polynomial.sum_def]
  exact Finset.sum_nonneg (fun n _=>mul_nonneg (hP n) (pow_nonneg ht n))

lemma vector_count_scaled_bound {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (hm : 2≤m) (t : ℝ) (ht : 0≤t) (hhalf : t≤1/2) :
    ((noSingletonVectors (α:=α) m).card:ℝ)*t^m≤Real.exp (2*(Fintype.card α:ℝ)*t^2) := by
  rw [card_noSingletonVectors_eq_coefficient]
  have hcoef := polynomial_coeff_mul_pow_le_eval
    ((vectorCountPolynomial m)^(Fintype.card α))
    (polynomial_power_coeff_nonneg _ (vectorCountPolynomial_coeff_nonneg m) _) t ht m
  have hpow := polynomial_power_eval_le_exp (vectorCountPolynomial m) (Fintype.card α) t (2*t^2)
    (polynomial_eval_nonneg _ (vectorCountPolynomial_coeff_nonneg m) t ht) (by positivity)
    (vectorCountPolynomial_eval_le m hm t ht hhalf)
  exact hcoef.trans (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hpow)

lemma word_count_scaled_bound {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (hm : 2≤m) (t : ℝ) (ht : 0≤t) (hone : t≤1) :
    ((noSingletonWords (α:=α) m).card:ℝ)*t^m≤
      (m.factorial:ℝ)*Real.exp ((Fintype.card α:ℝ)*t^2) := by
  rw [card_noSingletonWords_eq_coefficient,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have hcoef := polynomial_coeff_mul_pow_le_eval
    ((wordCountPolynomial m)^(Fintype.card α))
    (polynomial_power_coeff_nonneg _ (wordCountPolynomial_coeff_nonneg m) _) t ht m
  exact hcoef.trans (polynomial_power_eval_le_exp (wordCountPolynomial m) (Fintype.card α) t (t^2)
    (polynomial_eval_nonneg _ (wordCountPolynomial_coeff_nonneg m) t ht) (sq_nonneg t)
    (wordCountPolynomial_eval_le m hm t ht hone))

end DGRHS.Attractive
#print axioms DGRHS.Attractive.geometric_prefix_le_two
#print axioms DGRHS.Attractive.vectorCountPolynomial_eval_le
#print axioms DGRHS.Attractive.wordCountPolynomial_eval_le
#print axioms DGRHS.Attractive.vector_count_scaled_bound
#print axioms DGRHS.Attractive.word_count_scaled_bound
