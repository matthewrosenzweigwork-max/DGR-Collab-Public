import DGPS.Examples.PolynomialSpecies

/-! Exact classification of the finite coefficient computed from the actual
polynomial Fourier expansion. This file is only coefficient algebra: identifying
the actual reduced value with that expansion and proving its uniform remainder
remain separate analytic obligations. No global optimizer conclusion is asserted. -/

noncomputable section

namespace DGPS.Examples.PolynomialSpecies

/-- The scaled quotient coefficient from the actual finite Fourier calculation.
Its analytic identification with the true reduced quotient is not a definition. -/
def polynomialScaledQuotientCoefficient (a b : ℝ) : ℝ :=
  1 / 6 + a / 6 + (a ^ 4 + b ^ 4) / (12 * (a ^ 2 + b ^ 2))

private theorem sqrt_relations :
    let k := (1 + Real.sqrt 2) / 2
    let l := Real.sqrt 2 - 1
    0 < k ∧ 0 < l ∧ l ^ 2 + 2 * l = 1 ∧ 2 * l * k = 1 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  dsimp only
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

/-- Exact nonnegative polynomial identity, including the degenerate origin. -/
theorem polynomialScaledCoefficient_sos (a b : ℝ) :
    a ^ 4 + b ^ 4 + 2 * a * (a ^ 2 + b ^ 2) +
        ((1 + Real.sqrt 2) / 2) * (a ^ 2 + b ^ 2) =
      (b ^ 2 - (Real.sqrt 2 - 1) * a ^ 2) ^ 2 +
        2 * (Real.sqrt 2 - 1) * (a ^ 2 + b ^ 2) * (a + (1 + Real.sqrt 2) / 2) ^ 2 := by
  let k := (1 + Real.sqrt 2) / 2
  let l := Real.sqrt 2 - 1
  obtain ⟨_, _, hl, hkl⟩ := sqrt_relations
  change l ^ 2 + 2 * l = 1 at hl
  change 2 * l * k = 1 at hkl
  change a ^ 4 + b ^ 4 + 2 * a * (a ^ 2 + b ^ 2) + k * (a ^ 2 + b ^ 2) = _
  calc
    _ = (l ^ 2 + 2 * l) * a ^ 4 + b ^ 4 +
        2 * (2 * l * k) * a * (a ^ 2 + b ^ 2) + (2 * l * k) * k * (a ^ 2 + b ^ 2) := by
      rw [hl, hkl]
      ring
    _ = _ := by ring

private theorem coefficient_defect (a b : ℝ) (hr : 0 < a ^ 2 + b ^ 2) :
    polynomialScaledQuotientCoefficient a b - (3 - Real.sqrt 2) / 24 =
      (a ^ 4 + b ^ 4 + 2 * a * (a ^ 2 + b ^ 2) +
        ((1 + Real.sqrt 2) / 2) * (a ^ 2 + b ^ 2)) / (12 * (a ^ 2 + b ^ 2)) := by
  unfold polynomialScaledQuotientCoefficient
  field_simp [ne_of_gt hr]
  ring

/-- Global minimum of the computed coefficient, with the zero-amplitude
singularity excluded explicitly. This is not an actual-model rate bound. -/
theorem polynomialScaledCoefficient_global_lower (a b : ℝ) (hr : 0 < a ^ 2 + b ^ 2) :
    (3 - Real.sqrt 2) / 24 ≤ polynomialScaledQuotientCoefficient a b := by
  apply sub_nonneg.mp
  rw [coefficient_defect a b hr, polynomialScaledCoefficient_sos]
  obtain ⟨_, hl, _, _⟩ := sqrt_relations
  exact div_nonneg (add_nonneg (sq_nonneg _) (by positivity)) (by positivity)

/-- The coefficient has precisely two minimizer coordinates: the first is
fixed, and the second has the displayed strictly positive square. The actual
global optimizer classification still needs the analytic graph/remainder bridge. -/
theorem polynomialScaledCoefficient_minimum_iff (a b : ℝ) (hr : 0 < a ^ 2 + b ^ 2) :
    polynomialScaledQuotientCoefficient a b = (3 - Real.sqrt 2) / 24 ↔
      a = -(1 + Real.sqrt 2) / 2 ∧ b ^ 2 = (1 + Real.sqrt 2) / 4 := by
  let k := (1 + Real.sqrt 2) / 2
  let l := Real.sqrt 2 - 1
  obtain ⟨hk, hl, _, hkl⟩ := sqrt_relations
  change 0 < k at hk
  change 0 < l at hl
  change 2 * l * k = 1 at hkl
  have hlk : l * k ^ 2 = k / 2 := by nlinarith [congrArg (fun x : ℝ => x * k) hkl]
  have hgap := coefficient_defect a b hr
  rw [polynomialScaledCoefficient_sos] at hgap
  change polynomialScaledQuotientCoefficient a b - (3 - Real.sqrt 2) / 24 =
    ((b ^ 2 - l * a ^ 2) ^ 2 + 2 * l * (a ^ 2 + b ^ 2) * (a + k) ^ 2) /
      (12 * (a ^ 2 + b ^ 2)) at hgap
  constructor
  · intro he
    have hz : (b ^ 2 - l * a ^ 2) ^ 2 + 2 * l * (a ^ 2 + b ^ 2) * (a + k) ^ 2 = 0 := by
      rw [he, sub_self] at hgap
      exact (div_eq_zero_iff.mp hgap.symm).resolve_right (by positivity)
    have hc : 0 < 2 * l * (a ^ 2 + b ^ 2) := by positivity
    have ht : 2 * l * (a ^ 2 + b ^ 2) * (a + k) ^ 2 = 0 := by
      exact le_antisymm (by linarith [sq_nonneg (b ^ 2 - l * a ^ 2)])
        (mul_nonneg hc.le (sq_nonneg (a + k)))
    have ha : a = -k := by
      have hs := (mul_eq_zero.mp ht).resolve_left hc.ne'
      have hh := (sq_eq_zero_iff).mp hs
      linarith
    have hb : b ^ 2 = k / 2 := by
      have hs : (b ^ 2 - l * a ^ 2) ^ 2 = 0 := by rw [ht, add_zero] at hz; exact hz
      have hh := (sq_eq_zero_iff).mp hs
      rw [ha, neg_sq] at hh
      linarith
    exact ⟨by simpa only [k, neg_div] using ha, by simpa only [k, div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hb⟩
  · rintro ⟨ha, hb⟩
    have ha' : a = -k := by simpa only [k, neg_div] using ha
    have hb' : b ^ 2 = k / 2 := by simpa only [k, div_div, show (2 : ℝ) * 2 = 4 by norm_num] using hb
    apply sub_eq_zero.mp
    rw [hgap, ha', hb', neg_sq, hlk]
    simp

end DGPS.Examples.PolynomialSpecies
