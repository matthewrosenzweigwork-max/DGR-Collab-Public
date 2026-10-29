import DGPS.Frontier.EX049.T09
import DGPS.Frontier.EX049.T52
import DGPS.Frontier.EX049.T53

/-!
# EX049.54: Global energy controls the main potential

Task id: EX049.54 (node EX049, leaf formalization, size S; prerequisites EX049.09, EX049.52 and
EX049.53). For every real `h ≥ 2` and every real angular `H¹` function `v`, with `U = 1 - cos θ`,
`μ_h = circleReference h`, `M_h(v) = ∫ v² dμ_h` and `E_h(v) = ∫ (v')² dμ_h`, the global bound
`h ∫ U v² dμ_h ≤ 2 E_h(v) + 2 M_h(v)` holds.

## Provides

- `DGPS.Frontier.EX049.ex049_54_global_energy_controls_main_potential`: the main inequality, for
  every `h ≥ 2`, every `v`, and every weak derivative `v'` of `v` (`IsAngularWeakDeriv v v'`).
- `DGPS.Frontier.EX049.core_EX04954`: for any weak derivative `W'` of any `w`,
  `(h/2) ∫ U w² dm - ∫ w² dm ≤ ∫ (W'² + groundPot h ∘ angSec · w²) dm`.
- `DGPS.Frontier.EX049.lower_EX04954` and `DGPS.Frontier.EX049.lower_circle_EX04954`: the pointwise
  bound `(h/2) U - 1 ≤ V - g² + g'` on the line and on the circle, from EX049.52.
- `DGPS.Frontier.EX049.gLift_EX04954` and `DGPS.Frontier.EX049.gCirc_EX04954`: the multiplier
  `g = -(driftB h · cos) / 2` on the line and on the circle.
- `DGPS.Frontier.EX049.gCirc_coe_EX04954`, `DGPS.Frontier.EX049.contDiff_gLift_EX04954`,
  `DGPS.Frontier.EX049.smooth_gCirc_EX04954`, `DGPS.Frontier.EX049.angDeriv_gCirc_EX04954`: the
  multiplier is smooth on the circle, and its circle derivative is the line derivative.
- `DGPS.Frontier.EX049.cos_angSec_EX04954`, `DGPS.Frontier.EX049.continuous_U_EX04954`,
  `DGPS.Frontier.EX049.bound_U_EX04954`, `DGPS.Frontier.EX049.sq_conj_EX04954`: bookkeeping for
  `cos ∘ angSec`, the bounded continuous potential `U`, and the square of the ground-state
  conjugate `groundStateConj h v`.

## R5 notes

- Hypotheses. The statement has exactly the hypotheses `2 ≤ h` (kept verbatim from the
  specification) and `IsAngularWeakDeriv v v'`. Nothing else is assumed: no positivity, mass or
  entropy condition on `v`, no boundedness of `v`, and no constant. Every integrability fact is
  proved inside the proof.
- Angular `H¹` function. The specification's "real angular `H¹` function `v`" is quantified as a
  pair `(v, v')` with `IsAngularWeakDeriv v v'`. Since `AngularH1 v` is `∃ v', IsAngularWeakDeriv v v'`,
  this covers every angular `H¹` function and every weak derivative of it. Weak derivatives are
  unique up to almost everywhere equality, and both sides depend on `v'` only through integrals,
  so this is at least as strong as the literal reading.
- The derivative `(v')²`. It is the circle weak derivative of EX049.02, not a derivative on
  `[0, 2π)`.
- `U`. On the circle `U θ = 1 - Real.cos (angSec θ)`, the cosine of the representative in
  `(0, 2π]`. Cosine is `2π`-periodic, so this is the value at every real representative.
- `μ_h` and the integrals. `μ_h` is `circleReference h`, the campaign measure of EX049.25 with
  density `qAng h` relative to `angHaar`. `M_h` and `E_h` are integrals against it, and
  `∫ F dμ_h = ∫ F · qAng h dm` is the change of density of EX049.25.
- Drift and potential binding. `V = groundPot h` and `b = driftB h` are bound through the
  conjuncts `driftB h = b` and `groundPot h = V` of EX049.52. The correction `R_h` enters only
  through EX049.52. No other campaign fact is used.
- Multiplier. The smooth `g` of the proof is `g = -(driftB h · cos) / 2`, read on the circle
  through `angSec`. Its circle derivative `angDeriv g` equals the line derivative at every
  representative (`angDeriv_gCirc_EX04954`).
- Proof route. Put `w = groundStateConj h v = v √q_h`. The energy identity and square completion of
  EX049.09 give `E = ∫ (W'² + V w²) dm`. The identity of EX049.53 with multiplier `g` gives
  `∫ (W' + g w)² dm = ∫ (W'² + (g² - g') w²) dm`. Since `∫ (W' + g w)² ≥ 0`, this gives
  `E ≥ ∫ (V - g² + g') w² dm`, and the pointwise bound of EX049.52 completes the estimate.
  No division by mass or entropy occurs.
-/

open MeasureTheory
open scoped ContDiff
open DGPS.Circle.AngularNormalization DGPS.Examples.EngineeredRankOne
  DGPS.Examples.EngineeredGroundState

namespace DGPS.Frontier.EX049

/-- The multiplier `g_h(t) = -(b_h(t) cos t) / 2` on the real line, with `b_h = driftB h`. -/
noncomputable def gLift_EX04954 (h t : ℝ) : ℝ := -(driftB h t * Real.cos t) / 2

/-- The multiplier `g_h` on the angular circle, read through the representative `angSec`. -/
noncomputable def gCirc_EX04954 (h : ℝ) (x : AngCircle) : ℝ := gLift_EX04954 h (angSec x)

/-- Cosine is `2π`-periodic, so `cos (angSec x)` equals `cos x` at every real representative. -/
theorem cos_angSec_EX04954 (s : ℝ) : Real.cos (angSec (s : AngCircle)) = Real.cos s := by
  obtain ⟨n, hn⟩ := exists_angSec_eq s
  rw [hn]
  exact (Real.cos_periodic.int_mul n) s

/-- The circle multiplier lifts back to the line multiplier `gLift_EX04954 h`. -/
theorem gCirc_coe_EX04954 (h : ℝ) (hh : 0 < h) :
    (fun s : ℝ => gCirc_EX04954 h (s : AngCircle)) = gLift_EX04954 h := by
  funext s
  unfold gCirc_EX04954 gLift_EX04954
  rw [driftB_angSec_EX04925 h hh s, cos_angSec_EX04954 s]

/-- The line multiplier is smooth. -/
theorem contDiff_gLift_EX04954 (h : ℝ) (hh : 0 < h) : ContDiff ℝ ∞ (gLift_EX04954 h) := by
  unfold gLift_EX04954
  exact (((contDiff_driftB h hh).mul Real.contDiff_cos).neg).div_const 2

/-- The circle multiplier is smooth in the sense of `IsSmoothAngular`. -/
theorem smooth_gCirc_EX04954 (h : ℝ) (hh : 0 < h) : IsSmoothAngular (gCirc_EX04954 h) := by
  unfold IsSmoothAngular
  rw [gCirc_coe_EX04954 h hh]
  exact contDiff_gLift_EX04954 h hh

/-- The circle derivative of `g_h` is the line derivative of `gLift_EX04954 h` at `angSec x`. -/
theorem angDeriv_gCirc_EX04954 (h : ℝ) (hh : 0 < h) (x : AngCircle) :
    angDeriv (gCirc_EX04954 h) x = deriv (gLift_EX04954 h) (angSec x) := by
  unfold angDeriv
  rw [gCirc_coe_EX04954 h hh]

/-- The potential `U = 1 - cos θ` is continuous on the circle. -/
theorem continuous_U_EX04954 : Continuous (fun θ : AngCircle => 1 - Real.cos (angSec θ)) := by
  refine continuous_of_coe_EX04935 ?_
  simp only [cos_angSec_EX04954]
  exact continuous_const.sub Real.continuous_cos

/-- The potential `U = 1 - cos θ` is bounded by `2` on the circle. -/
theorem bound_U_EX04954 (θ : AngCircle) : ‖1 - Real.cos (angSec θ)‖ ≤ 2 := by
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [Real.neg_one_le_cos (angSec θ), Real.cos_le_one (angSec θ)]

/-- Pointwise lower bound on the line, from EX049.52: `(h/2) U - 1 ≤ V - g² + g'`. -/
theorem lower_EX04954 (h : ℝ) (hh : 2 ≤ h) (t : ℝ) :
    h / 2 * (1 - Real.cos t) - 1 ≤
      groundPot h t - gLift_EX04954 h t ^ 2 + deriv (gLift_EX04954 h) t := by
  obtain ⟨-, -, ⟨hdrift, -⟩, -, hlow⟩ := ex049_52_exact_pointwise_square_completion h hh
  show h / 2 * (1 - Real.cos t) - 1 ≤
      groundPot h t - (-(driftB h t * Real.cos t) / 2) ^ 2 +
        deriv (fun s => -(driftB h s * Real.cos s) / 2) t
  unfold groundPot
  rw [hdrift]
  exact hlow t

/-- Pointwise lower bound on the circle: the line bound of `lower_EX04954` read at `angSec x`. -/
theorem lower_circle_EX04954 (h : ℝ) (hh : 2 ≤ h) (x : AngCircle) :
    h / 2 * (1 - Real.cos (angSec x)) - 1 ≤
      groundPot h (angSec x) - gCirc_EX04954 h x ^ 2 + angDeriv (gCirc_EX04954 h) x := by
  have hh0 : (0 : ℝ) < h := by linarith
  rw [angDeriv_gCirc_EX04954 h hh0 x]
  exact lower_EX04954 h hh (angSec x)

/-- The ground-state conjugate has square `v² q_h` pointwise. -/
theorem sq_conj_EX04954 (h : ℝ) (hh : 0 < h) (v : AngCircle → ℝ) (θ : AngCircle) :
    groundStateConj h v θ ^ 2 = v θ ^ 2 * qAng h θ := by
  show (v θ * Real.sqrt (qAng h θ)) ^ 2 = v θ ^ 2 * qAng h θ
  rw [mul_pow, Real.sq_sqrt (qAng_pos h hh θ).le]

/-- Core bound: for every weak derivative `W'` of `w`,
`(h/2) ∫ U w² dm - ∫ w² dm ≤ ∫ (W'² + V w²) dm`, with `V = groundPot h ∘ angSec`. -/
theorem core_EX04954 (h : ℝ) (hh : 2 ≤ h) {w W' : AngCircle → ℝ}
    (hW : IsAngularWeakDeriv w W') :
    h / 2 * (∫ θ, (1 - Real.cos (angSec θ)) * w θ ^ 2 ∂angHaar) - ∫ θ, w θ ^ 2 ∂angHaar ≤
      ∫ θ, (W' θ ^ 2 + groundPot h (angSec θ) * w θ ^ 2) ∂angHaar := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hgs : ContDiff ℝ ∞ (fun s : ℝ => gCirc_EX04954 h (s : AngCircle)) :=
    smooth_gCirc_EX04954 h hh0
  have ha : ContDiff ℝ 1 (fun s : ℝ => gCirc_EX04954 h (s : AngCircle)) :=
    hgs.of_le (by exact_mod_cast le_top)
  have hgc : Continuous (gCirc_EX04954 h) := continuous_of_coe_EX04935 ha.continuous
  obtain ⟨M, hM⟩ := bdd_EX04903 hgc
  obtain ⟨-, hI_dg, -⟩ := ibp_EX04903 (L := gCirc_EX04954 h) ha (fun _ => rfl) hW
    (sq_weak_EX04903 hW)
  have hI_W : Integrable (fun θ => W' θ ^ 2) angHaar := hW.memLp_deriv.integrable_sq
  have hI_w : Integrable (fun θ => w θ ^ 2) angHaar := hW.memLp.integrable_sq
  have hI_g : Integrable (fun θ => gCirc_EX04954 h θ ^ 2 * w θ ^ 2) angHaar :=
    (memLp_bdd_mul_EX04935 hgc hM hW.memLp).integrable_sq.congr
      (ae_of_all _ fun θ => by simp only [mul_pow])
  have hI_G : Integrable
      (fun θ => (gCirc_EX04954 h θ ^ 2 - angDeriv (gCirc_EX04954 h) θ) * w θ ^ 2) angHaar :=
    (hI_g.sub hI_dg).congr (ae_of_all _ fun θ => by simp only [Pi.sub_apply, sub_mul])
  have hI_UW : Integrable (fun θ => (1 - Real.cos (angSec θ)) * w θ ^ 2) angHaar :=
    Integrable.bdd_mul hI_w continuous_U_EX04954.aestronglyMeasurable
      (ae_of_all _ fun θ => bound_U_EX04954 θ)
  have hVw : Integrable (fun θ => groundPot h (angSec θ) * w θ ^ 2) angHaar :=
    (square_completion_EX04909 h hh0 hW).1
  have hLHS : Integrable (fun θ => (h / 2 * (1 - Real.cos (angSec θ)) - 1) * w θ ^ 2) angHaar :=
    ((hI_UW.const_mul (h / 2)).sub hI_w).congr
      (ae_of_all _ fun θ => by simp only [Pi.sub_apply]; ring)
  have hpt : ∀ θ, (h / 2 * (1 - Real.cos (angSec θ)) - 1) * w θ ^ 2 ≤
      groundPot h (angSec θ) * w θ ^ 2 -
        (gCirc_EX04954 h θ ^ 2 - angDeriv (gCirc_EX04954 h) θ) * w θ ^ 2 := by
    intro θ
    have e : (groundPot h (angSec θ) - gCirc_EX04954 h θ ^ 2 + angDeriv (gCirc_EX04954 h) θ) *
        w θ ^ 2 = groundPot h (angSec θ) * w θ ^ 2 -
          (gCirc_EX04954 h θ ^ 2 - angDeriv (gCirc_EX04954 h) θ) * w θ ^ 2 := by
      ring
    rw [← e]
    exact mul_le_mul_of_nonneg_right (lower_circle_EX04954 h hh θ) (sq_nonneg (w θ))
  have hmono : ∫ θ, (h / 2 * (1 - Real.cos (angSec θ)) - 1) * w θ ^ 2 ∂angHaar ≤
      ∫ θ, (groundPot h (angSec θ) * w θ ^ 2 -
        (gCirc_EX04954 h θ ^ 2 - angDeriv (gCirc_EX04954 h) θ) * w θ ^ 2) ∂angHaar :=
    integral_mono hLHS (hVw.sub hI_G) hpt
  have hsplitL : ∫ θ, (h / 2 * (1 - Real.cos (angSec θ)) - 1) * w θ ^ 2 ∂angHaar =
      h / 2 * (∫ θ, (1 - Real.cos (angSec θ)) * w θ ^ 2 ∂angHaar) - ∫ θ, w θ ^ 2 ∂angHaar := by
    have e : (fun θ => (h / 2 * (1 - Real.cos (angSec θ)) - 1) * w θ ^ 2) =
        fun θ => h / 2 * ((1 - Real.cos (angSec θ)) * w θ ^ 2) - w θ ^ 2 := by
      funext θ
      ring
    rw [e, integral_sub (hI_UW.const_mul (h / 2)) hI_w, integral_const_mul]
  have hsplitR : ∫ θ, (groundPot h (angSec θ) * w θ ^ 2 -
      (gCirc_EX04954 h θ ^ 2 - angDeriv (gCirc_EX04954 h) θ) * w θ ^ 2) ∂angHaar =
      (∫ θ, groundPot h (angSec θ) * w θ ^ 2 ∂angHaar) -
        ∫ θ, (gCirc_EX04954 h θ ^ 2 - angDeriv (gCirc_EX04954 h) θ) * w θ ^ 2 ∂angHaar :=
    integral_sub hVw hI_G
  have hId := ex049_53_periodic_integrated_square_identity (smooth_gCirc_EX04954 h hh0) hW
  have hsplitId : ∫ θ, (W' θ ^ 2 +
      (gCirc_EX04954 h θ ^ 2 - angDeriv (gCirc_EX04954 h) θ) * w θ ^ 2) ∂angHaar =
      (∫ θ, W' θ ^ 2 ∂angHaar) +
        ∫ θ, (gCirc_EX04954 h θ ^ 2 - angDeriv (gCirc_EX04954 h) θ) * w θ ^ 2 ∂angHaar :=
    integral_add hI_W hI_G
  have hnn : 0 ≤ ∫ θ, (W' θ + gCirc_EX04954 h θ * w θ) ^ 2 ∂angHaar :=
    integral_nonneg fun θ => sq_nonneg _
  have hsplitV : ∫ θ, (W' θ ^ 2 + groundPot h (angSec θ) * w θ ^ 2) ∂angHaar =
      (∫ θ, W' θ ^ 2 ∂angHaar) + ∫ θ, groundPot h (angSec θ) * w θ ^ 2 ∂angHaar :=
    integral_add hI_W hVw
  linarith [hmono, hsplitL, hsplitR, hId, hsplitId, hnn, hsplitV]

/-- Global energy controls the main potential (EX049.54). For every `h ≥ 2`, every real angular
`H¹` function `v` with weak derivative `v'`, `h ∫ U v² dμ_h ≤ 2 ∫ (v')² dμ_h + 2 ∫ v² dμ_h`,
with `U = 1 - cos θ` and `μ_h = circleReference h`. -/
theorem ex049_54_global_energy_controls_main_potential (h : ℝ) (hh : 2 ≤ h)
    (v v' : AngCircle → ℝ) (hv : IsAngularWeakDeriv v v') :
    h * (∫ θ, (1 - Real.cos (angSec θ)) * v θ ^ 2 ∂circleReference h) ≤
      2 * (∫ θ, v' θ ^ 2 ∂circleReference h) + 2 * (∫ θ, v θ ^ 2 ∂circleReference h) := by
  have hh0 : (0 : ℝ) < h := by linarith
  have hW := ex049_09_full_h1_ground_state_identity_weak h hh0 hv
  have hEV := (conj_energy_EX04909 h hh0 hv hW).trans (square_completion_EX04909 h hh0 hW).2
  have hcore := core_EX04954 h hh hW
  rw [mass_EX04909 h hh0 v] at hcore
  have hA : (∫ θ, (1 - Real.cos (angSec θ)) * groundStateConj h v θ ^ 2 ∂angHaar) =
      ∫ θ, (1 - Real.cos (angSec θ)) * v θ ^ 2 ∂circleReference h := by
    rw [integral_circleReference h hh0]
    refine integral_congr_ae (ae_of_all _ fun θ => ?_)
    show (1 - Real.cos (angSec θ)) * groundStateConj h v θ ^ 2 =
      (1 - Real.cos (angSec θ)) * v θ ^ 2 * qAng h θ
    rw [sq_conj_EX04954 h hh0 v θ]
    ring
  rw [hA] at hcore
  linarith [hcore, hEV]

end DGPS.Frontier.EX049
