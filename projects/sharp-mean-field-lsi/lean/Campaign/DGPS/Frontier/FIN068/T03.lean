import DGPS.FiniteN.QuarticSaddle

/-!
# FIN068.03: Constants and exact cancellation

Provides:
* `DGPS.Frontier.FIN068.quarticA_FIN06803`: `A = b/5 - g'(4)`, with `b = quarticB` and
  `g'(4) = deriv besselRatio 4` (the derivative value, not the coordinate variable).
* `DGPS.Frontier.FIN068.quarticD_FIN06803`: `d = b - 4 g'(4)`.
* `DGPS.Frontier.FIN068.fin068_03_constants_exact_cancellation`: `b`, `κ`, `A`, `d` are strictly
  positive; `1/κ = b/5`; `4A - d = -b/5`; and `c₄ = bd/(10240 A) > 0` (stated as the explicit
  quotient, not as a named object).

R5 notes:
* No hypotheses are added. The theorem is closed; every quantity is a concrete real number.
* Domain of the inputs: `quarticB = besselRatio 4` and `quarticKappa = 5 / quarticB` (FIN065,
  `DGPS.Models`). Positivity of `b` rests on the FIN065 rational certificate
  `b > 889110/1029889`, proved there from exact series bounds for `I₀(4)` and `I₁(4)`.
* `g'(4)` is read as Mathlib's `deriv besselRatio 4`. The FIN065 Riccati identity
  `deriv besselRatio 4 = 1 - b/4 - b²` is used only through the FIN065 positivity facts; this
  file does not re-derive it.
* `A` and `d` are introduced as the defining expressions of the node (`A = b/5 - g'(4)`,
  `d = b - 4 g'(4)`), not as `1/κ - g'(4)`. The identity `1/κ = b/5` is then proved, so both
  readings agree.
* `c₄` is not a separate definition. It is the explicit quotient `b * d / (10240 * A)`, and
  its positivity is stated for that quotient.
* Non-literal reading: the specification's "`A = 1/κ - g'(4)`" in the Proof paragraph is
  replaced by the Statement-level definition `A = b/5 - g'(4)`; the two coincide by
  `1/κ = b/5`.
* No assumption from the FIN068.37/.38 gates (Bessel definition identifications) is used.
-/

open DGPS.Models DGPS.Circle.BesselMoments

namespace DGPS.Frontier.FIN068

/-- `A = b/5 - g'(4)`, where `g'(4) = deriv besselRatio 4`. -/
noncomputable def quarticA_FIN06803 : ℝ := quarticB / 5 - deriv besselRatio 4

/-- `d = b - 4 g'(4)`, where `g'(4) = deriv besselRatio 4`. -/
noncomputable def quarticD_FIN06803 : ℝ := quarticB - 4 * deriv besselRatio 4

/-- Constants and exact cancellation: `b, κ, A, d > 0`, `1/κ = b/5`, `4A - d = -b/5`, and
`c₄ = bd/(10240 A) > 0`. -/
theorem fin068_03_constants_exact_cancellation :
    0 < quarticB ∧ 0 < quarticKappa ∧ 0 < quarticA_FIN06803 ∧ 0 < quarticD_FIN06803 ∧
    1 / quarticKappa = quarticB / 5 ∧
    4 * quarticA_FIN06803 - quarticD_FIN06803 = -(quarticB / 5) ∧
    0 < quarticB * quarticD_FIN06803 / (10240 * quarticA_FIN06803) := by
  obtain ⟨_, _, _, _, hcert, hκpos, _, ⟨_, _, hApos⟩, hDpos, _⟩ :=
    DGPS.FiniteN.quartic_explicit_model_rational_certificate
  have hbpos : 0 < quarticB := by
    have h1 : (889110 / 1029889 : ℝ) < quarticB := hcert.1
    have h2 : (0 : ℝ) < 889110 / 1029889 := by norm_num
    linarith
  have hA : 0 < quarticA_FIN06803 := hApos
  have hD : 0 < quarticD_FIN06803 := hDpos
  have hinv : 1 / quarticKappa = quarticB / 5 := by
    unfold quarticKappa
    rw [one_div_div]
  have hcancel : 4 * quarticA_FIN06803 - quarticD_FIN06803 = -(quarticB / 5) := by
    unfold quarticA_FIN06803 quarticD_FIN06803
    ring
  have hc4 : 0 < quarticB * quarticD_FIN06803 / (10240 * quarticA_FIN06803) :=
    div_pos (mul_pos hbpos hD) (mul_pos (by norm_num) hA)
  exact ⟨hbpos, hκpos, hA, hD, hinv, hcancel, hc4⟩

end DGPS.Frontier.FIN068
