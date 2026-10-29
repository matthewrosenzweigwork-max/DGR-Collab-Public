import DGPS.Frontier.EX049.T07
import DGPS.Frontier.EX049.T25
import DGPS.Frontier.EX049.T54

/-!
# EX049.55: Global entropy-potential bound

Task id: EX049.55 (node EX049, leaf formalization, size S; prerequisites EX049.07 and EX049.54).
For every real `h ≥ 2` and every real angular `H¹` function `v` with weak derivative `v'`, put
`U = 1 - cos θ`, `R_h = corr h`, `Φ_h = h U + R_h(U)`, `μ_h = circleReference h`,
`M_h(v) = ∫ v² dμ_h` and `E_h(v) = ∫ (v')² dμ_h`. Then `∫ Φ_h v² dμ_h ≤ 2 E_h(v) + 8 √h M_h(v)`.

## Provides

- `DGPS.Frontier.EX049.ex049_55_global_entropy_potential_bound`: the main inequality, for every
  `h ≥ 2`, every `v`, and every weak derivative `v'` of `v` (`IsAngularWeakDeriv v v'`).
- `DGPS.Frontier.EX049.mem_U_EX04955`: the potential `1 - cos (angSec θ)` lies in `[0, 2]`.
- `DGPS.Frontier.EX049.corr_bounds_EX04955`: `0 ≤ corr h u ≤ 6 √h` for `u ∈ [0, 2]` and `h ≥ 2`.
- `DGPS.Frontier.EX049.continuous_corrU_EX04955`: `θ ↦ corr h (1 - cos (angSec θ))` is continuous.
- `DGPS.Frontier.EX049.norm_corr_le_EX04955`: `‖corr h (1 - cos (angSec θ))‖ ≤ 6 √h`.

## R5 notes

- Hypotheses. The statement has exactly the hypotheses `2 ≤ h` (the specification's `h ≥ 2`) and
  `IsAngularWeakDeriv v v'`. Nothing else is assumed: no positivity, mass or entropy condition on
  `v`, no boundedness of `v`, and no constant. Integrability of every term is proved inside the
  proof, from the weak-derivative hypothesis, the `L²` description of EX049.25 and the boundedness
  of the two potential factors.
- Angular `H¹` function. The pair `(v, v')` with `IsAngularWeakDeriv v v'` is the reading used in
  EX049.54. Weak derivatives are unique up to almost everywhere equality, and the statement uses
  `v'` only through an integral, so this covers every angular `H¹` function.
- The derivative `(v')²`. It is the circle weak derivative of EX049.02, not a derivative on
  `[0, 2π)`.
- `R_h`. The correction is the campaign function `corr h` of `DGPS.Examples.EngineeredRankOne`.
  Its bound `0 ≤ R_h ≤ 6 √h` on `[0, 2]` is obtained from EX049.07 applied to the smooth extension
  `integrand h` on the whole line, using EX049.25 (`integrand_eq_rsrc_EX04925`) to identify the
  extension with the quotient on `(0, 2)`. Only the values of `corr h` on `[0, 2]` enter, because
  `1 - cos` takes values in `[0, 2]`.
- The potential `U`. The statement writes `1 - Real.cos (angSec θ)`, the same form as in EX049.54,
  rather than the campaign `Uang`. The two agree at each representative, and the proof does not need
  an identity between them.
- Integrals. All integrals are Bochner integrals against `circleReference h`, the campaign measure
  of EX049.25. Every integrand is integrable under the stated hypotheses, so no zero convention for
  non-integrable functions is used.
- Constants. The coefficient `8` is `2 + 6`. The `2` comes from EX049.54 for the term `h U`, and the
  `6 √h` comes from the correction bound. The remaining mass term `2 M_h(v) ≤ 2 √h M_h(v)` uses
  `√h ≥ 1`, which follows from `h ≥ 2`. No other constant appears.
- Route. The proof is the global square-completion route, through EX049.54 and EX049.07. It uses no
  spatial localization and no entropy step.
-/

open MeasureTheory
open scoped ContDiff
open Set
open DGPS.Circle.AngularNormalization DGPS.Examples.EngineeredRankOne
  DGPS.Examples.EngineeredGroundState

namespace DGPS.Frontier.EX049

/-- The potential `1 - cos θ` lies in `[0, 2]` at every point of the circle. -/
theorem mem_U_EX04955 (θ : AngCircle) : 1 - Real.cos (angSec θ) ∈ Set.Icc (0:ℝ) 2 :=
  ⟨by linarith [Real.cos_le_one (angSec θ)], by linarith [Real.neg_one_le_cos (angSec θ)]⟩

/-- For `h ≥ 2` and `u ∈ [0,2]`, the correction satisfies `0 ≤ corr h u ≤ 6 √h`. -/
theorem corr_bounds_EX04955 (h : ℝ) (hh : 2 ≤ h) (u : ℝ) (hu : u ∈ Set.Icc (0:ℝ) 2) :
    0 ≤ corr h u ∧ corr h u ≤ 6 * Real.sqrt h := by
  have hpos : 0 < h := by linarith
  have hc : ContDiffOn ℝ ∞ (integrand h) univ := (contDiff_integrand h hpos).contDiffOn
  have hQg : ∀ x ∈ Set.Ioo (0:ℝ) 2, integrand h x = quot_EX04906 h x :=
    fun x hx => (integrand_eq_rsrc_EX04925 h hpos hx.1.ne' hx.2.ne).trans rfl
  obtain ⟨hc0, hc1⟩ :=
    integral_bounds_EX04907 h hh (integrand h) univ (subset_univ _) hc hQg u hu
  exact ⟨hc0, hc1.trans (sqrt_chain_EX04907 h hh)⟩

/-- The map `θ ↦ corr h (1 - cos (angSec θ))` is continuous, since `corr h` is continuous on `[0,2]`
and `1 - cos (angSec θ)` lies in `[0, 2]`. -/
theorem continuous_corrU_EX04955 (h : ℝ) (hh : 2 ≤ h) :
    Continuous (fun θ : AngCircle => corr h (1 - Real.cos (angSec θ))) :=
  (continuousOn_corr h (by linarith)).comp_continuous continuous_U_EX04954 mem_U_EX04955

/-- Pointwise bound `‖corr h (1 - cos (angSec θ))‖ ≤ 6 √h` for `h ≥ 2`. -/
theorem norm_corr_le_EX04955 (h : ℝ) (hh : 2 ≤ h) (θ : AngCircle) :
    ‖corr h (1 - Real.cos (angSec θ))‖ ≤ 6 * Real.sqrt h := by
  obtain ⟨h0, h1⟩ := corr_bounds_EX04955 h hh _ (mem_U_EX04955 θ)
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [Real.sqrt_nonneg h]

/-- Global entropy-potential bound (EX049.55). For every `h ≥ 2` and every real angular `H¹`
function `v` with weak derivative `v'`,
`∫ (h U + R_h(U)) v² dμ_h ≤ 2 ∫ (v')² dμ_h + 8 √h ∫ v² dμ_h`,
with `U = 1 - cos θ`, `R_h = corr h` and `μ_h = circleReference h`. -/
theorem ex049_55_global_entropy_potential_bound (h : ℝ) (hh : 2 ≤ h)
    (v v' : AngCircle → ℝ) (hv : IsAngularWeakDeriv v v') :
    (∫ θ, (h * (1 - Real.cos (angSec θ)) + corr h (1 - Real.cos (angSec θ))) * v θ ^ 2
        ∂circleReference h) ≤
      2 * (∫ θ, v' θ ^ 2 ∂circleReference h) +
        8 * Real.sqrt h * (∫ θ, v θ ^ 2 ∂circleReference h) := by
  have hpos : (0:ℝ) < h := by linarith
  have hT54 := ex049_54_global_energy_controls_main_potential h hh v v' hv
  have hI_v : Integrable (fun θ => v θ ^ 2) (circleReference h) :=
    ((memLp_circleReference_iff_EX04925 h hpos v).2 hv.memLp).integrable_sq
  have hI_U : Integrable (fun θ => (1 - Real.cos (angSec θ)) * v θ ^ 2) (circleReference h) :=
    Integrable.bdd_mul hI_v continuous_U_EX04954.aestronglyMeasurable
      (ae_of_all _ fun θ => bound_U_EX04954 θ)
  have hI_R : Integrable (fun θ => corr h (1 - Real.cos (angSec θ)) * v θ ^ 2)
      (circleReference h) :=
    Integrable.bdd_mul hI_v (continuous_corrU_EX04955 h hh).aestronglyMeasurable
      (ae_of_all _ fun θ => norm_corr_le_EX04955 h hh θ)
  have hlin : (∫ θ, (h * (1 - Real.cos (angSec θ)) + corr h (1 - Real.cos (angSec θ))) * v θ ^ 2
        ∂circleReference h) =
      ∫ θ, (h * ((1 - Real.cos (angSec θ)) * v θ ^ 2) +
        corr h (1 - Real.cos (angSec θ)) * v θ ^ 2) ∂circleReference h :=
    integral_congr_ae (ae_of_all _ fun θ => by ring)
  have hR_le : (∫ θ, corr h (1 - Real.cos (angSec θ)) * v θ ^ 2 ∂circleReference h) ≤
      6 * Real.sqrt h * ∫ θ, v θ ^ 2 ∂circleReference h := by
    have hm : (∫ θ, corr h (1 - Real.cos (angSec θ)) * v θ ^ 2 ∂circleReference h) ≤
        ∫ θ, 6 * Real.sqrt h * v θ ^ 2 ∂circleReference h :=
      integral_mono hI_R (hI_v.const_mul (6 * Real.sqrt h)) fun θ =>
        mul_le_mul_of_nonneg_right (corr_bounds_EX04955 h hh _ (mem_U_EX04955 θ)).2
          (sq_nonneg (v θ))
    rw [integral_const_mul] at hm
    exact hm
  have hM0 : 0 ≤ ∫ θ, v θ ^ 2 ∂circleReference h := integral_nonneg fun θ => sq_nonneg _
  have hs1 : 1 ≤ Real.sqrt h := by
    nlinarith [Real.sq_sqrt hpos.le, Real.sqrt_nonneg h]
  have hMs : 1 * (∫ θ, v θ ^ 2 ∂circleReference h) ≤
      Real.sqrt h * ∫ θ, v θ ^ 2 ∂circleReference h :=
    mul_le_mul_of_nonneg_right hs1 hM0
  rw [hlin, integral_add (hI_U.const_mul h) hI_R, integral_const_mul]
  linarith

end DGPS.Frontier.EX049
