import DGPS.Frontier.EX049.T13
import DGPS.Frontier.EX049.T55

/-!
# EX049.24: Frozen conclusion with explicit witnesses

Task id: EX049.24. Title: Frozen conclusion with explicit witnesses. Node EX049, leaf
formalization, size S, prerequisites EX049.13 and EX049.55, verification level V1.

Let `C0 > 0` be the absolute witness selected from the EX037 lower bound on `groundPot`. Put
`h0 = 2` and `C = max 1 C0 + log (2 + 8π²) + 9`. Then `C > 0`, `h0 > 0`, and for every real
`h ≥ h0`, every angular `H¹` function `v` and every weak angular derivative `v'` of `v`,
`Ent_{μ_h}(v²) ≤ (2 + C h^(-1/2)) ∫ (v')² dμ_h + C √h ∫ v² dμ_h`.

The proof adds the estimate of EX049.13 (with `K = max 1 C0`) and the estimate of EX049.55. The
energy coefficient becomes `2 + (√h)⁻¹`, which is at most `2 + C h^(-1/2)` because `C ≥ 1`. The
mass coefficient becomes `(max 1 C0 + log (2 + 8π²) + 1) + 8 = C`, exactly.

## Provides

* `DGPS.Frontier.EX049.ex049_24_frozen_conclusion_explicit_witnesses`: the main statement, with
  `C0` existentially quantified together with its EX037 bound, and the explicit witnesses
  `h0 = 2` and `C = max 1 C0 + log (2 + 8π²) + 9` written in the conclusion.
* `DGPS.Frontier.EX049.ex049_24_frozen_conclusion_explicit_witnesses_exists`: the frozen
  conclusion in its existential form `∃ C h0, 0 < C ∧ 0 < h0 ∧ ...`.
* `DGPS.Frontier.EX049.ex049_24_frozen_conclusion_explicit_witnesses_of_witness`: the same
  conclusion for an arbitrary real `C0` that satisfies the EX037 bound.
* `DGPS.Frontier.EX049.rpow_neg_half_EX04924`: `h ^ (-(1/2)) = (√h)⁻¹` for `h > 0`.
* `DGPS.Frontier.EX049.uang_eq_angSec_EX04924`: `Uang θ = 1 - cos (angSec θ)` on the circle.

## R5 notes

* Hypotheses. The only hypotheses of the conclusion are `2 ≤ h` (the frozen `h ≥ h0` with
  `h0 = 2`), `AngularH1 v` and `IsAngularWeakDeriv v v'`. Nothing is assumed about positivity,
  mass or entropy of `v`, boundedness of `v`, or a constant. The EX037 bound is not a hypothesis:
  it is a conjunct of the main statement, recording that `C0` is the witness selected from EX037.
* Witnesses. In the main statement `C0` is existentially quantified. The constants `h0 = 2` and
  `C = max 1 C0 + log (2 + 8π²) + 9` are literal formulas in that one `C0`. No numeral value of
  `C0` is given, since the source does not supply one. The conjuncts `0 < C` and `0 < h0` are
  part of the statement.
* Main statement versus frozen conclusion. The main statement is stronger than the frozen
  conclusion, because it names the witnesses and carries the EX037 bound. The literal frozen form
  `∃ C h0, 0 < C ∧ 0 < h0 ∧ ...` is `ex049_24_frozen_conclusion_explicit_witnesses_exists`, which
  follows from the main statement with the same witnesses.
* Exponent. The frozen coefficient `h^{-1/2}` is read as the real power `h ^ (-(1/2 : ℝ))`.
  For `h > 0` it equals `(√h)⁻¹`, the coefficient used by EX049.13 (`rpow_neg_half_EX04924`).
* Weak derivative. `∫ (v')²` is taken for every weak derivative `v'` of `v`
  (`IsAngularWeakDeriv v v'`). Weak derivatives agree almost everywhere, so this is the
  single-derivative reading.
* Potential. EX049.13 is stated with `Uang θ = 1 - Real.Angle.cos θ`, and EX049.55 with
  `1 - Real.cos (angSec θ)`. `uang_eq_angSec_EX04924` identifies them pointwise on the circle, and
  the proof rewrites with it. No other identity is used.
* Binding. `μ_h = circleReference h`, the entropy `entEX04910`, `groundPot`, `corr` and `Uang`
  are the campaign objects of the prerequisite files. Their identity with the source objects is
  the open task EX049.25. This file inherits that status and does not claim the binding.
* Constants. The energy estimate uses `C ≥ 1` and `∫ (v')² ≥ 0`. The mass coefficient is exact:
  `B + 8 = C` with `B = max 1 C0 + log (2 + 8π²) + 1` from EX049.13 and `8` from EX049.55.
  No step divides by entropy or by mass.
-/

namespace DGPS.Frontier.EX049

open MeasureTheory Real
open DGPS.Circle.AngularNormalization DGPS.Examples.EngineeredRankOne
  DGPS.Examples.EngineeredGroundState

/-- The real power `h ^ (-(1/2))` equals `(√h)⁻¹` for `h > 0`, so the frozen coefficient
`h^{-1/2}` is the coefficient `(√h)⁻¹` used by EX049.13. -/
theorem rpow_neg_half_EX04924 (h : ℝ) (hh : 0 < h) : h ^ (-(1 / 2 : ℝ)) = (Real.sqrt h)⁻¹ := by
  rw [Real.rpow_neg hh.le, Real.sqrt_eq_rpow]

/-- On the circle the campaign potential `Uang` agrees with `1 - cos (angSec θ)`, the form used
by EX049.55. -/
theorem uang_eq_angSec_EX04924 (θ : AngCircle) : Uang θ = 1 - Real.cos (angSec θ) := by
  have hθ : ((angSec θ : ℝ) : Real.Angle) = θ := angSec_coe_EX04904 θ
  calc Uang θ = Uang ((angSec θ : ℝ) : Real.Angle) := by rw [hθ]
    _ = 1 - Real.cos (angSec θ) := drift_Uang (angSec θ)

/-- The explicit-witness conclusion for an arbitrary real `C0` satisfying the EX037 lower bound on
`groundPot`. For `h ≥ 2`, every angular `H¹` function `v` and every weak angular derivative `v'`,
the entropy is bounded with `h0 = 2` and `C = max 1 C0 + log (2 + 8π²) + 9`. -/
theorem ex049_24_frozen_conclusion_explicit_witnesses_of_witness (C0 : ℝ)
    (hC0 : ∀ h : ℝ, 2 ≤ h → ∀ t : ℝ, h ^ 2 * Real.sin t ^ 2 / 4 - C0 * h ≤ groundPot h t)
    (h : ℝ) (hh : 2 ≤ h) (v : AngCircle → ℝ) (hv : AngularH1 v)
    (v' : AngCircle → ℝ) (hv' : IsAngularWeakDeriv v v') :
    entEX04910 (circleReference h) (fun θ => v θ ^ 2) ≤
      (2 + (max 1 C0 + Real.log (2 + 8 * π ^ 2) + 9) * h ^ (-(1 / 2 : ℝ))) *
          (∫ θ, v' θ ^ 2 ∂circleReference h) +
        (max 1 C0 + Real.log (2 + 8 * π ^ 2) + 9) * Real.sqrt h *
          (∫ θ, v θ ^ 2 ∂circleReference h) := by
  have hh0 : (0:ℝ) < h := by linarith
  have h13 := ex049_13_global_entropy_reduction_h_least_two_of_witness C0 hC0 h hh v hv v' hv'
  have h55 := ex049_55_global_entropy_potential_bound h hh v v' hv'
  have hPot : (∫ θ, (h * Uang θ + corr h (Uang θ)) * v θ ^ 2 ∂circleReference h) ≤
      2 * (∫ θ, v' θ ^ 2 ∂circleReference h) +
        8 * Real.sqrt h * (∫ θ, v θ ^ 2 ∂circleReference h) := by
    simp only [uang_eq_angSec_EX04924]
    exact h55
  have hE0 : 0 ≤ ∫ θ, v' θ ^ 2 ∂circleReference h := integral_nonneg fun θ => sq_nonneg _
  have hs0 : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh0
  have hinv0 : 0 ≤ (Real.sqrt h)⁻¹ := (inv_pos.mpr hs0).le
  have hD : (0:ℝ) ≤ Real.log (2 + 8 * π ^ 2) :=
    Real.log_nonneg (by linarith [sq_nonneg π])
  have hC1 : 1 ≤ max 1 C0 + Real.log (2 + 8 * π ^ 2) + 9 := by
    have := le_max_left 1 C0
    linarith
  have hkey : (Real.sqrt h)⁻¹ * (∫ θ, v' θ ^ 2 ∂circleReference h) ≤
      (max 1 C0 + Real.log (2 + 8 * π ^ 2) + 9) * (Real.sqrt h)⁻¹ *
        (∫ θ, v' θ ^ 2 ∂circleReference h) :=
    mul_le_mul_of_nonneg_right (le_mul_of_one_le_left hinv0 hC1) hE0
  rw [rpow_neg_half_EX04924 h hh0]
  linarith [h13, hPot, hkey]

/-- EX049.24: frozen conclusion with explicit witnesses. There is `C0 > 0` with the EX037 lower
bound on `groundPot`, and for it the explicit values `C = max 1 C0 + log (2 + 8π²) + 9 > 0` and
`h0 = 2 > 0` satisfy, for every real `h ≥ h0`, every angular `H¹` function `v` and every weak
angular derivative `v'` of `v`, the entropy bound
`Ent_{μ_h}(v²) ≤ (2 + C h^(-1/2)) ∫ (v')² dμ_h + C √h ∫ v² dμ_h`. -/
theorem ex049_24_frozen_conclusion_explicit_witnesses :
    ∃ C0 : ℝ, 0 < C0 ∧
      (∀ h : ℝ, 2 ≤ h → ∀ t : ℝ, h ^ 2 * Real.sin t ^ 2 / 4 - C0 * h ≤ groundPot h t) ∧
      0 < max 1 C0 + Real.log (2 + 8 * π ^ 2) + 9 ∧ (0:ℝ) < 2 ∧
      ∀ h : ℝ, 2 ≤ h → ∀ v : AngCircle → ℝ, AngularH1 v →
        ∀ v' : AngCircle → ℝ, IsAngularWeakDeriv v v' →
          entEX04910 (circleReference h) (fun θ => v θ ^ 2) ≤
            (2 + (max 1 C0 + Real.log (2 + 8 * π ^ 2) + 9) * h ^ (-(1 / 2 : ℝ))) *
                (∫ θ, v' θ ^ 2 ∂circleReference h) +
              (max 1 C0 + Real.log (2 + 8 * π ^ 2) + 9) * Real.sqrt h *
                (∫ θ, v θ ^ 2 ∂circleReference h) := by
  obtain ⟨C0, hC0pos, hbound, -⟩ := ex049_13_global_entropy_reduction_h_least_two
  refine ⟨C0, hC0pos, hbound, ?_, by norm_num, ?_⟩
  · have := le_max_left 1 C0
    have := Real.log_nonneg (show (1:ℝ) ≤ 2 + 8 * π ^ 2 by linarith [sq_nonneg π])
    linarith
  · intro h hh v hv v' hv'
    exact ex049_24_frozen_conclusion_explicit_witnesses_of_witness C0 hbound h hh v hv v' hv'

/-- The frozen conclusion in its existential form: there are `C > 0` and `h0 > 0` such that for
every `h ≥ h0`, every angular `H¹` function `v` and every weak angular derivative `v'` of `v`,
the entropy bound holds with `C` and `h0`. The witnesses are the explicit values of the main
statement. -/
theorem ex049_24_frozen_conclusion_explicit_witnesses_exists :
    ∃ C h0 : ℝ, 0 < C ∧ 0 < h0 ∧
      ∀ h : ℝ, h0 ≤ h → ∀ v : AngCircle → ℝ, AngularH1 v →
        ∀ v' : AngCircle → ℝ, IsAngularWeakDeriv v v' →
          entEX04910 (circleReference h) (fun θ => v θ ^ 2) ≤
            (2 + C * h ^ (-(1 / 2 : ℝ))) * (∫ θ, v' θ ^ 2 ∂circleReference h) +
              C * Real.sqrt h * (∫ θ, v θ ^ 2 ∂circleReference h) := by
  obtain ⟨C0, -, -, hC, h2, hmain⟩ := ex049_24_frozen_conclusion_explicit_witnesses
  exact ⟨max 1 C0 + Real.log (2 + 8 * π ^ 2) + 9, 2, hC, h2, hmain⟩

end DGPS.Frontier.EX049
