/- Unchecked draft outside the proof tree. Scalar phase factorization for the
source remainder. No integrated differentiation and no assumed remainder law. -/
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace DGRHS.Gaussian

def cubicExpPolynomial (z : ℂ) : ℂ := 1 + z + z ^ 2 / 2 + z ^ 3 / 6

lemma norm_cubicExpPolynomial_le (z : ℂ) :
    ‖cubicExpPolynomial z‖ ≤ 1 + ‖z‖ + ‖z‖ ^ 2 / 2 + ‖z‖ ^ 3 / 6 := by
  unfold cubicExpPolynomial
  calc
    ‖1 + z + z ^ 2 / 2 + z ^ 3 / 6‖ ≤
        ‖1 + z + z ^ 2 / 2‖ + ‖z ^ 3 / 6‖ := norm_add_le _ _
    _ ≤ (‖1 + z‖ + ‖z ^ 2 / 2‖) + ‖z ^ 3 / 6‖ :=
      add_le_add (norm_add_le _ _) (le_refl _)
    _ ≤ ((‖(1 : ℂ)‖ + ‖z‖) + ‖z ^ 2 / 2‖) + ‖z ^ 3 / 6‖ := by
      gcongr
      exact norm_add_le _ _
    _ = 1 + ‖z‖ + ‖z‖ ^ 2 / 2 + ‖z‖ ^ 3 / 6 := by
      norm_num [norm_div, norm_pow]

lemma norm_exp_cubic_remainder_unit_modulus (z : ℂ) (hz : ‖Complex.exp z‖ = 1) :
    ‖Complex.exp z - cubicExpPolynomial z‖ ≤ 4 * ‖z‖ ^ 4 := by
  by_cases hs : ‖z‖ ≤ 1
  · have he := Complex.exp_bound (n := 4) hs (by norm_num)
    have hp : (∑ m ∈ Finset.range 4, z ^ m / (m.factorial : ℂ)) =
        cubicExpPolynomial z := by
      norm_num [Finset.sum_range_succ, cubicExpPolynomial]
    rw [hp] at he
    norm_num at he
    nlinarith [pow_nonneg (norm_nonneg z) 4]
  · have ht : 1 ≤ ‖z‖ := le_of_lt (lt_of_not_ge hs)
    have h2 : ‖z‖ ≤ ‖z‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - 1)]
    have h3 : ‖z‖ ^ 2 ≤ ‖z‖ ^ 3 := by
      have hm := mul_le_mul_of_nonneg_right h2 (norm_nonneg z)
      nlinarith
    have h4 : ‖z‖ ^ 3 ≤ ‖z‖ ^ 4 := by
      have hm := mul_le_mul_of_nonneg_right h3 (norm_nonneg z)
      nlinarith
    calc
      ‖Complex.exp z - cubicExpPolynomial z‖ ≤
          ‖Complex.exp z‖ + ‖cubicExpPolynomial z‖ := norm_sub_le _ _
      _ ≤ 1 + (1 + ‖z‖ + ‖z‖ ^ 2 / 2 + ‖z‖ ^ 3 / 6) := by
        rw [hz]
        exact add_le_add (le_refl 1) (norm_cubicExpPolynomial_le z)
      _ ≤ 4 * ‖z‖ ^ 4 := by nlinarith

lemma norm_exp_linear_remainder_unit_modulus (z : ℂ) (hz : ‖Complex.exp z‖ = 1) :
    ‖Complex.exp z - 1 - z‖ ≤ 3 * ‖z‖ ^ 2 := by
  by_cases hs : ‖z‖ ≤ 1
  · have he := Complex.norm_exp_sub_one_sub_id_le hs
    nlinarith [sq_nonneg ‖z‖]
  · have ht : 1 ≤ ‖z‖ := le_of_lt (lt_of_not_ge hs)
    calc
      ‖Complex.exp z - 1 - z‖ ≤ ‖Complex.exp z - 1‖ + ‖z‖ := norm_sub_le _ _
      _ ≤ (‖Complex.exp z‖ + ‖(1 : ℂ)‖) + ‖z‖ :=
        add_le_add (norm_sub_le _ _) (le_refl _)
      _ = 2 + ‖z‖ := by rw [hz, norm_one]; ring
      _ ≤ 3 * ‖z‖ ^ 2 := by nlinarith [sq_nonneg (‖z‖ - 1)]

lemma abs_real_exp_linear_remainder (u : ℝ) (hu : 0 ≤ u) :
    |Real.exp u - 1 - u| ≤ 2 * u ^ 2 * Real.exp u := by
  have he : 1 ≤ Real.exp u := Real.one_le_exp hu
  by_cases hs : u ≤ 1
  · have hb := Real.abs_exp_sub_one_sub_id_le (show |u| ≤ 1 by rwa [abs_of_nonneg hu])
    have hm := mul_le_mul_of_nonneg_left he (sq_nonneg u)
    nlinarith
  · have ht : 1 ≤ u := le_of_lt (lt_of_not_ge hs)
    have hn : 0 ≤ Real.exp u - 1 - u := by linarith [Real.add_one_le_exp u]
    rw [abs_of_nonneg hn]
    have hs2 : 1 ≤ u ^ 2 := by nlinarith [sq_nonneg (u - 1)]
    have hm := mul_le_mul_of_nonneg_right hs2 (Real.exp_pos u).le
    nlinarith

lemma exp_real_phase_cubic_decomposition (u : ℝ) (z : ℂ) :
    Complex.exp ((u : ℂ) + z) - (cubicExpPolynomial z + u * (1 + z)) =
      (Complex.exp z - cubicExpPolynomial z) +
      u * (Complex.exp z - 1 - z) +
      (Complex.exp (u : ℂ) - 1 - u) * Complex.exp z := by
  rw [Complex.exp_add]
  ring

lemma norm_exp_real_phase_cubic_remainder (u : ℝ) (hu : 0 ≤ u) (z : ℂ)
    (hz : ‖Complex.exp z‖ = 1) :
    ‖Complex.exp ((u : ℂ) + z) - (cubicExpPolynomial z + u * (1 + z))‖ ≤
      4 * ‖z‖ ^ 4 + 3 * u * ‖z‖ ^ 2 + 2 * u ^ 2 * Real.exp u := by
  have hr : ‖Complex.exp (u : ℂ) - 1 - u‖ ≤ 2 * u ^ 2 * Real.exp u := by
    simpa only [← Complex.ofReal_exp, ← Complex.ofReal_one, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs] using abs_real_exp_linear_remainder u hu
  rw [exp_real_phase_cubic_decomposition]
  calc
    ‖(Complex.exp z - cubicExpPolynomial z) + u * (Complex.exp z - 1 - z) +
        (Complex.exp (u : ℂ) - 1 - u) * Complex.exp z‖ ≤
        (‖Complex.exp z - cubicExpPolynomial z‖ + ‖u * (Complex.exp z - 1 - z)‖) +
        ‖(Complex.exp (u : ℂ) - 1 - u) * Complex.exp z‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ 4 * ‖z‖ ^ 4 + 3 * u * ‖z‖ ^ 2 + 2 * u ^ 2 * Real.exp u := by
      rw [norm_mul, norm_mul, hz, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg hu]
      have hm := mul_le_mul_of_nonneg_left (norm_exp_linear_remainder_unit_modulus z hz) hu
      have hc := norm_exp_cubic_remainder_unit_modulus z hz
      nlinarith

lemma norm_exp_real_phase_cubic_remainder_weighted (u U v : ℝ) (hu : 0 ≤ u)
    (huU : u ≤ U) :
    ‖Complex.exp ((u : ℂ) + Complex.I * v) -
      (cubicExpPolynomial (Complex.I * v) + u * (1 + Complex.I * v))‖ ≤
      Real.exp U * (4 * v ^ 4 + 3 * u * v ^ 2 + 2 * u ^ 2) := by
  have hc := norm_exp_real_phase_cubic_remainder u hu (Complex.I * v)
    (Complex.norm_exp_I_mul_ofReal v)
  have hn : ‖Complex.I * (v : ℂ)‖ = |v| := by
    simp [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [hn, show |v| ^ 4 = v ^ 4 by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, sq_abs]
    ring, sq_abs] at hc
  have hE : 1 ≤ Real.exp U := Real.one_le_exp (hu.trans huU)
  have hreal := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr huU)
    (show 0 ≤ 2 * u ^ 2 by positivity)
  have hphase := mul_le_mul_of_nonneg_right hE
    (show 0 ≤ 4 * v ^ 4 + 3 * u * v ^ 2 by positivity)
  nlinarith

lemma norm_feature_scalar_remainder (β D t y : ℝ) (hβ : 0 ≤ β) (hD : 0 ≤ D)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖Complex.exp (((t ^ 2 * β * D / 2 : ℝ) : ℂ) +
        Complex.I * (t * Real.sqrt β * y : ℝ)) -
      (cubicExpPolynomial (Complex.I * (t * Real.sqrt β * y : ℝ)) +
        (t ^ 2 * β * D / 2 : ℝ) * (1 + Complex.I * (t * Real.sqrt β * y : ℝ)))‖ ≤
      t ^ 4 * β ^ 2 * Real.exp (β * D / 2) *
        (4 * y ^ 4 + (3 / 2 : ℝ) * D * y ^ 2 + (1 / 2 : ℝ) * D ^ 2) := by
  have ht2 : t ^ 2 ≤ 1 := by
    have hm := mul_le_mul ht1 ht1 ht0 (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hu : 0 ≤ t ^ 2 * β * D / 2 := by positivity
  have huU : t ^ 2 * β * D / 2 ≤ β * D / 2 := by
    have hm := mul_le_mul_of_nonneg_right ht2 (mul_nonneg hβ hD)
    nlinarith
  have hsq : (t * Real.sqrt β * y) ^ 2 = t ^ 2 * β * y ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hβ]
  have hfour : (t * Real.sqrt β * y) ^ 4 = t ^ 4 * β ^ 2 * y ^ 4 := by
    calc
      _ = ((t * Real.sqrt β * y) ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsq]; ring
  have hb := norm_exp_real_phase_cubic_remainder_weighted
    (t ^ 2 * β * D / 2) (β * D / 2) (t * Real.sqrt β * y) hu huU
  rw [hsq, hfour] at hb
  convert hb using 1 <;> ring

end DGRHS.Gaussian

#check DGRHS.Gaussian.norm_exp_cubic_remainder_unit_modulus
#print axioms DGRHS.Gaussian.norm_exp_cubic_remainder_unit_modulus
#check DGRHS.Gaussian.norm_exp_linear_remainder_unit_modulus
#print axioms DGRHS.Gaussian.norm_exp_linear_remainder_unit_modulus
#check DGRHS.Gaussian.abs_real_exp_linear_remainder
#print axioms DGRHS.Gaussian.abs_real_exp_linear_remainder
#check DGRHS.Gaussian.exp_real_phase_cubic_decomposition
#print axioms DGRHS.Gaussian.exp_real_phase_cubic_decomposition
#check DGRHS.Gaussian.norm_exp_real_phase_cubic_remainder
#print axioms DGRHS.Gaussian.norm_exp_real_phase_cubic_remainder

#check DGRHS.Gaussian.cubicExpPolynomial
#print axioms DGRHS.Gaussian.cubicExpPolynomial
#check DGRHS.Gaussian.norm_cubicExpPolynomial_le
#print axioms DGRHS.Gaussian.norm_cubicExpPolynomial_le
#check DGRHS.Gaussian.norm_exp_real_phase_cubic_remainder_weighted
#print axioms DGRHS.Gaussian.norm_exp_real_phase_cubic_remainder_weighted
#check DGRHS.Gaussian.norm_feature_scalar_remainder
#print axioms DGRHS.Gaussian.norm_feature_scalar_remainder
