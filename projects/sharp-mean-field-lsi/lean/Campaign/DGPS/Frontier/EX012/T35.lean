import DGPS.Frontier.EX012.T26
import DGPS.Frontier.EX012.T28

/-!
# EX012.35: Bounded coefficient extraction and reconstruction

Task id: EX012.35 (node EX012, one-site complementary range equation).
Title: Bounded coefficient extraction and reconstruction.

Provides:
* `DGPS.Frontier.EX012.ex012_35_bounded_coefficient_extraction_reconstruction`: the main
  statement, a conjunction of (i) there is a continuous linear map `E : PH α 2 →L[ℝ] ℝ × ℝ × PH.orthSub α 2`
  with `E v = (a v, b v, Q₂ v)` for every `v`, where `a v`, `b v` are the first cosine and sine
  coefficients and `Q₂` is the projection of EX012.26; (ii) for every mean-zero `v`
  (`∫₀¹ v = 0`), `v = a v • c₁ + b v • s₁ + Q₂ v` with `c₁ = cos (2π x)`, `s₁ = sin (2π x)` of
  EX012.28.
* `DGPS.Frontier.EX012.coefA_EX01235`: the first cosine coefficient `a v = modeWeight 1 * ∫₀¹ v cos (2π x)`
  (that is `2 ∫₀¹ v cos (2π x)`) on `PH α 2`.
* `DGPS.Frontier.EX012.coefB_EX01235`: the first sine coefficient `b v = modeWeight 1 * ∫₀¹ v sin (2π x)`
  on `PH α 2`.
* `DGPS.Frontier.EX012.extract_EX01235`: the bounded map `v ↦ (a v, b v, Q₂ v)` as a
  `ContinuousLinearMap` `PH α 2 →L[ℝ] ℝ × ℝ × PH.orthSub α 2`.
* Helper lemmas (all suffixed `_EX01235`): `modeWeight_one_EX01235` (`modeWeight 1 = 2`),
  `extract_apply_EX01235` (the pointwise description of `extract_EX01235`).

R5 notes:
* The only hypothesis is `[HolderExponent α]` (the campaign form of `0 < α < 1`). The mean-zero
  condition `PH.integral 2 v = 0` is a hypothesis of part (ii) only, as the specification states.
* "Exact FOU017 integrals" is read as the FOU017 mode normalization: the coefficient is
  `modeWeight 1 * PH.cosCoeff 2 1 v` (the same weight that `PH.modeCLM` and `PH.modeProj01_val`
  use), and `modeWeight 1 = 2`. The bare integral `∫ v cos (2π x)` is NOT used: with it the
  reconstruction identity would be false, since `∫₀¹ cos² (2π x) = 1/2` forces the factor `2`.
  This is a design choice, not a change of the statement.
* The boundedness is proved for the map on all of `PH α 2`, which is stronger than the
  specification's "for a mean-zero `v`": `Q₂` subtracts the mean anyway, and the restriction of a
  bounded linear map to a subspace is bounded. "Bounded" is the continuity of a
  `ContinuousLinearMap` (equivalently the norm bound `‖E v‖ ≤ ‖E‖ ‖v‖`); no separate constant is stated.
* The codomain of `Q₂` is the subtype `PH.orthSub α 2` (the codomain restriction of EX012.26),
  so the third component of `E` lies in that subspace, not merely in `PH α 2`.
* The reconstruction identity is stated with `PH α 2` on both sides, the subtype coercion applied
  to `Q₂ v`. The proof uses the pointwise formula of EX012.26
  (`ex012_26_projections_both_regularities_val`) together with `PH.ext`; the constant term
  disappears because `PH.integral 2 v = 0`. `Subtype.ext` is used only through `PH.ext`.
* The `ContinuousLinearMap.prod` construction and the pointwise formula for `E` are checked by
  `rfl` in `extract_apply_EX01235`; no property of the coefficient functionals beyond their
  definitions is assumed.
-/

open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.EX012

section Coefficients

variable {α : ℝ} [HolderExponent α]

theorem modeWeight_one_EX01235 : modeWeight 1 = 2 := by
  simp [modeWeight]

/-- First cosine coefficient `a v = modeWeight 1 * ∫₀¹ v cos (2π x)`, with `modeWeight 1 = 2`. -/
noncomputable def coefA_EX01235 (v : PH α 2) : ℝ := modeWeight 1 * PH.cosCoeff 2 1 v

/-- First sine coefficient `b v = modeWeight 1 * ∫₀¹ v sin (2π x)`, with `modeWeight 1 = 2`. -/
noncomputable def coefB_EX01235 (v : PH α 2) : ℝ := modeWeight 1 * PH.sinCoeff 2 1 v

/-- The bounded map `v ↦ (a v, b v, Q₂ v)`, assembled from the two coefficient functionals and
the projection `Q₂` of EX012.26 (`proj_EX01226 α 2`). -/
noncomputable def extract_EX01235 : PH α 2 →L[ℝ] ℝ × ℝ × PH.orthSub α 2 :=
  (modeWeight 1 • PH.cosCoeff 2 1).prod
    ((modeWeight 1 • PH.sinCoeff 2 1).prod (proj_EX01226 α 2))

theorem extract_apply_EX01235 (v : PH α 2) :
    extract_EX01235 (α := α) v =
      (coefA_EX01235 v, coefB_EX01235 v, proj_EX01226 α 2 v) := rfl

end Coefficients

section Reconstruction

variable {α : ℝ} [HolderExponent α]

/-- Extraction is bounded, and a mean-zero `v` is reconstructed from its first-harmonic
coefficients and its complementary component `Q₂ v`. -/
theorem ex012_35_bounded_coefficient_extraction_reconstruction :
    (∃ E : PH α 2 →L[ℝ] ℝ × ℝ × PH.orthSub α 2,
        ∀ v : PH α 2, E v = (coefA_EX01235 v, coefB_EX01235 v, proj_EX01226 α 2 v)) ∧
      ∀ v : PH α 2, PH.integral 2 v = 0 →
        v = coefA_EX01235 v • cosMode_EX01228 α 2 1 + coefB_EX01235 v • sinMode_EX01228 α 2 1 +
          ((proj_EX01226 α 2 v : PH.orthSub α 2) : PH α 2) := by
  refine ⟨⟨extract_EX01235, extract_apply_EX01235⟩, fun v hv => ?_⟩
  apply PH.ext
  funext x
  have hQ := ex012_26_projections_both_regularities_val (α := α) 2 v x
  simp only [PH.val_add, PH.val_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    cosMode_val_EX01228, sinMode_val_EX01228, Nat.cast_one, mul_one]
  rw [hQ, hv]
  unfold coefA_EX01235 coefB_EX01235
  rw [modeWeight_one_EX01235]
  ring

end Reconstruction

end DGPS.Frontier.EX012
