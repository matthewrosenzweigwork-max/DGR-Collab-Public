import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-! Pointwise real Wick expansion, an alternative to the source's integrated
fourth derivative. Gaussian and spatial domination remain separate obligations.
Native finite exponential-series remainder is used at its pinned declaration. -/
noncomputable section
open scoped BigOperators
namespace DGRHS.Attractive

def positiveCubicPolynomial (v : ℝ) : ℝ := 1+v+v^2/2+v^3/6

lemma abs_exp_sub_sum_le (v : ℝ) (n : ℕ) :
    |Real.exp v - ∑ j ∈ Finset.range n, v^j/(j.factorial:ℝ)| ≤
      |v|^n * Real.exp |v| := by
  convert Complex.norm_exp_sub_sum_le_norm_mul_exp (v:ℂ) n using 1 <;> norm_cast

lemma abs_positive_cubic_remainder (v : ℝ) :
    |Real.exp v-positiveCubicPolynomial v| ≤ v^4*Real.exp |v| := by
  have h := abs_exp_sub_sum_le v 4
  have hs : (∑ j ∈ Finset.range 4, v^j/(j.factorial:ℝ)) = positiveCubicPolynomial v := by
    norm_num [Finset.sum_range_succ, positiveCubicPolynomial]
  rw [hs] at h
  simpa only [show |v|^4=v^4 by rw [show (4:ℕ)=2*2 by rfl, pow_mul, sq_abs]; ring] using h

lemma abs_positive_linear_remainder (v : ℝ) :
    |Real.exp v-1-v| ≤ v^2*Real.exp |v| := by
  have h := abs_exp_sub_sum_le v 2
  norm_num [Finset.sum_range_succ] at h
  simpa only [sub_add_eq_sub_sub, sq_abs] using h

lemma abs_negative_linear_remainder (u : ℝ) (hu : 0 ≤ u) :
    |Real.exp (-u)-1+u| ≤ 2*u^2 := by
  by_cases hs : u ≤ 1
  · have h := Real.abs_exp_sub_one_sub_id_le (show |-u| ≤ 1 by simpa [abs_of_nonneg hu])
    have he : Real.exp (-u)-1-(-u) = Real.exp (-u)-1+u := by ring
    rw [he] at h
    nlinarith
  · have hu1 : 1 ≤ u := le_of_lt (lt_of_not_ge hs)
    have hl : 0 ≤ Real.exp (-u)-1+u := by linarith [Real.add_one_le_exp (-u)]
    have hh : Real.exp (-u) ≤ 1 := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr (show -u ≤ 0 by linarith)
    rw [abs_of_nonneg hl]
    nlinarith [sq_nonneg (u-1)]

lemma positive_wick_cubic_decomposition (u v : ℝ) :
    Real.exp (v-u)-(positiveCubicPolynomial v-u*(1+v)) =
      (Real.exp v-positiveCubicPolynomial v)-u*(Real.exp v-1-v)+
      (Real.exp (-u)-1+u)*Real.exp v := by
  rw [sub_eq_add_neg v u, Real.exp_add]
  ring

lemma abs_positive_wick_cubic_remainder (u v : ℝ) (hu : 0 ≤ u) :
    |Real.exp (v-u)-(positiveCubicPolynomial v-u*(1+v))| ≤
      Real.exp |v| * (4*v^4+3*u*v^2+2*u^2) := by
  have hc := abs_positive_cubic_remainder v
  have hl := abs_positive_linear_remainder v
  have hn := abs_negative_linear_remainder u hu
  have hev : Real.exp v ≤ Real.exp |v| := Real.exp_le_exp.mpr (le_abs_self v)
  have he0 := (Real.exp_pos |v|).le
  rw [positive_wick_cubic_decomposition]
  calc
    _ ≤ (|Real.exp v-positiveCubicPolynomial v|+|u*(Real.exp v-1-v)|)+
        |(Real.exp (-u)-1+u)*Real.exp v| := by
      have ht : |(Real.exp v-positiveCubicPolynomial v)-u*(Real.exp v-1-v)| ≤
          |Real.exp v-positiveCubicPolynomial v|+|u*(Real.exp v-1-v)| := by
        simpa only [sub_eq_add_neg, abs_neg] using
          abs_add_le (Real.exp v-positiveCubicPolynomial v) (-(u*(Real.exp v-1-v)))
      exact (abs_add_le _ _).trans (add_le_add ht (le_refl _))
    _ = (|Real.exp v-positiveCubicPolynomial v|+u*|Real.exp v-1-v|)+
        |Real.exp (-u)-1+u| * Real.exp v := by
      rw [abs_mul, abs_mul, abs_of_nonneg hu, abs_of_pos (Real.exp_pos _)]
    _ ≤ (v^4*Real.exp |v|+u*(v^2*Real.exp |v|))+2*u^2*Real.exp |v| := by
      gcongr
    _ ≤ Real.exp |v| * (4*v^4+3*u*v^2+2*u^2) := by
      have h4 : 0 ≤ v^4*Real.exp |v| := by positivity
      have h2 : 0 ≤ u*v^2*Real.exp |v| := by positivity
      nlinarith

lemma positive_wick_polynomial_coefficients (β D t y : ℝ) (hβ : 0 ≤ β) :
    positiveCubicPolynomial (t*Real.sqrt β*y)-
      (t^2*β*D/2)*(1+t*Real.sqrt β*y) =
    1+t*Real.sqrt β*y+t^2*(β/2*(y^2-D))+
      t^3*(β*Real.sqrt β/6*(y^3-3*D*y)) := by
  unfold positiveCubicPolynomial
  have hsq := Real.sq_sqrt hβ
  have hc : (Real.sqrt β)^3 = β*Real.sqrt β := by
    calc
      _ = (Real.sqrt β)^2*Real.sqrt β := by ring
      _ = _ := by rw [hsq]
  ring_nf
  rw [hsq, hc]
  ring

end DGRHS.Attractive
#check DGRHS.Attractive.abs_positive_wick_cubic_remainder
#print axioms DGRHS.Attractive.abs_positive_wick_cubic_remainder
#check DGRHS.Attractive.positive_wick_polynomial_coefficients
#print axioms DGRHS.Attractive.positive_wick_polynomial_coefficients
