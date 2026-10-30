import DGPS.Examples.PolynomialSpeciesScaledQuartic
import DGPS.Examples.PolynomialSpeciesScaledCoefficient

/-! Finite limiting capture algebra. Its premises are explicitly zero value
and variational nonnegativity of the limiting polynomial, not an assumed
optimizer classification. The actual-factor limit supplies these premises. -/
noncomputable section
open DGPS.Circle.AngularNormalization
namespace DGPS.Examples.PolynomialSpecies

/-- Away from zero amplitude, the undivided quartic is the positive physical
quadratic gap factor times the exact coefficient defect. -/
theorem polynomialScaledQuartic_coefficient_identity (a b α σ : ℝ)
    (hr : 0 < a ^ 2 + b ^ 2) :
    polynomialScaledQuartic (a, b, α, σ) =
      (a0 / 2 * (a ^ 2 + b ^ 2)) * (polynomialScaledQuotientCoefficient a b - α) := by
  unfold polynomialScaledQuartic polynomialScaledQuotientCoefficient
  field_simp [hr.ne']
  <;> ring

/-- A nonzero zero of the globally nonnegative limiting factor must have the
sharp coefficient and one of exactly the two explicit amplitude coordinates.
Nonnegativity may come from all original competitors, even zero-gap ones. -/
theorem polynomialScaledQuartic_variational_capture (a b α σ : ℝ)
    (hr : 0 < a ^ 2 + b ^ 2)
    (hz : polynomialScaledQuartic (a, b, α, σ) = 0)
    (hn : ∀ x y : ℝ, 0 ≤ polynomialScaledQuartic (x, y, α, σ)) :
    α = (3 - Real.sqrt 2) / 24 ∧
      a = -(1 + Real.sqrt 2) / 2 ∧ b ^ 2 = (1 + Real.sqrt 2) / 4 := by
  let m := (3 - Real.sqrt 2) / 24
  let x := -(1 + Real.sqrt 2) / 2
  let y := Real.sqrt ((1 + Real.sqrt 2) / 4)
  have hyarg : 0 < (1 + Real.sqrt 2) / 4 := by positivity
  have hy : y ^ 2 = (1 + Real.sqrt 2) / 4 := Real.sq_sqrt hyarg.le
  have hxy : 0 < x ^ 2 + y ^ 2 := by nlinarith only [sq_nonneg x, hy, hyarg]
  have hcoef : polynomialScaledQuotientCoefficient x y = m :=
    (polynomialScaledCoefficient_minimum_iff x y hxy).2 ⟨rfl, hy⟩
  have hmul : 0 < a0 / 2 * (x ^ 2 + y ^ 2) := mul_pos (div_pos a0_pos (by norm_num)) hxy
  have ht := hn x y
  rw [polynomialScaledQuartic_coefficient_identity x y α σ hxy, hcoef] at ht
  have hupper : α ≤ m := by
    have hdiff : 0 ≤ m - α :=
      (mul_le_mul_iff_right₀ hmul).1 (by simpa only [mul_zero] using ht)
    linarith only [hdiff]
  rw [polynomialScaledQuartic_coefficient_identity a b α σ hr] at hz
  have hpos : 0 < a0 / 2 * (a ^ 2 + b ^ 2) := mul_pos (div_pos a0_pos (by norm_num)) hr
  have he : polynomialScaledQuotientCoefficient a b = α :=
    sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hpos.ne')
  have hlower := polynomialScaledCoefficient_global_lower a b hr
  have hα : α = m := by rw [he] at hlower; exact le_antisymm hupper hlower
  exact ⟨hα, (polynomialScaledCoefficient_minimum_iff a b hr).1 (he.trans hα)⟩

end DGPS.Examples.PolynomialSpecies
