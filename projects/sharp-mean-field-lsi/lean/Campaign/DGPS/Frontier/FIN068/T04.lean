import DGPS.Frontier.FIN068.T02
import DGPS.Frontier.FIN068.T38

/-!
Task id and title: FIN068.04, Lift to two ordinary variables (module
`DGPS.Frontier.FIN068.T04`).

Provides:
* `DGPS.Frontier.FIN068.liftPotential_FIN06804`: the two-variable function
  `J(u, z) = (-5 + u)^2 / (2 κ) + z / (2 κ η) - log I₀(√((-4 + u)^2 + z))`, with `κ = quarticKappa`
  and `η = quarticEta` (a helper definition, not a claim).
* `DGPS.Frontier.FIN068.fin068_04_lift_two_ordinary_variables`: (1) `J` is `C^∞` on the open
  rectangle `(-1, 1) × (-1, 1)` in `(u, z)`; (2) for all real `u`, `y` with `|u| < 1` and `y^2 < 1`,
  the named potential satisfies `quarticPsi_FIN066 !₂[-4 + u, y] = J(u, y^2)`.

Proof: on the rectangle `(-4 + u)^2 + z > 8`, so `Real.sqrt` is smooth at the argument. The log of
`besselI 0` is `C^∞` on `ℝ` by FIN068.02 (through FIN068.01 and FIN068.16), and composition with the
smooth square root and the polynomial and linear terms gives smoothness at each point of the
rectangle. For (2), the named-potential gate of FIN068.38 unfolds `quarticPsi_FIN066` to the
displayed formula, and the constants `quarticKappa = 5 / besselRatio 4` and `quarticEta = 4 / 5` are
unfolded in `J`; the only rewrite left is `(-4 + u - 1) = -5 + u`.

R5 notes:
* The two-variable function is read as a function of the pair `(u, z)` on `ℝ × ℝ`, and "smooth on
  `|u| < 1`, `|z| < 1`" is read as `ContDiffOn ℝ ∞` on the open rectangle `Set.Ioo (-1) 1 ×ˢ
  Set.Ioo (-1) 1` (real-variable `C^∞`). The statement does not claim smoothness on the closed
  rectangle or on a neighbourhood of it; the proof sketch's "smaller closed rectangle" device is
  not needed for the statement and is not stated.
* `z` is the signed variable of the specification. The conclusion uses it only at `z = y^2 ≥ 0`
  (through the hypothesis-free identity), so the signed reading is harmless; nothing requires
  `z ≥ 0` inside `J`.
* The logarithm `ℓ` of the specification is written out as `Real.log (besselI 0 …)` in the
  definition of `liftPotential_FIN06804`; this is the `ℓ` of FIN068.02, with `I₀` the campaign
  object `besselI 0` (the normalized Haar average). The identification of `besselI 0` with the
  interval integral and with `K_0` is FIN068.37's and FIN068.38's content; it is used only through
  the FIN068.38 gate lemma `gate_fin068_38_named_potential_definition_gate_besselI` and the
  FIN068.02 smoothness lemma `besselI_zero_contDiff_FIN06802`.
* The constants `κ` and `η` are the campaign constants `quarticKappa` and `quarticEta` (not
  re-expanded in the statement), so `J` and the potential use the same objects.
* The second conjunct carries the hypotheses `|u| < 1` and `y^2 < 1` exactly as the specification
  lists them. The identity itself holds for all real `u` and `y`, so these hypotheses are not used
  in its proof; they are kept so that the statement matches the specification literally.
* The potential `ψ` is `quarticPsi_FIN066` evaluated at the point with coordinates `(-4 + u, y)`,
  written `!₂[-4 + u, y]` in `EuclideanSpace ℝ (Fin 2)`. The specification's identity `ψ(-4 + u, y)`
  is read as this evaluation.
* No hypothesis is added beyond those in the specification, and no helper is a hypothesis.
-/

open MeasureTheory Real
open scoped ContDiff
open DGPS.Circle.BesselMoments DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066

namespace DGPS.Frontier.FIN068

/-- The lifted potential `J(u, z) = (-5 + u)^2/(2κ) + z/(2κη) - log I₀(√((-4 + u)^2 + z))`, with
`κ = quarticKappa` and `η = quarticEta`. -/
noncomputable def liftPotential_FIN06804 (u z : ℝ) : ℝ :=
  (-5 + u) ^ 2 / (2 * quarticKappa) + z / (2 * quarticKappa * quarticEta) -
    Real.log (besselI 0 (Real.sqrt ((-4 + u) ^ 2 + z)))

/-- Lift to two ordinary variables: `J` is smooth on `|u| < 1`, `|z| < 1`, and the named potential
at `(-4 + u, y)` equals `J(u, y^2)` whenever `|u| < 1` and `y^2 < 1`. -/
theorem fin068_04_lift_two_ordinary_variables :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => liftPotential_FIN06804 p.1 p.2)
      (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.Ioo (-1 : ℝ) 1) ∧
    ∀ u y : ℝ, |u| < 1 → y ^ 2 < 1 →
      quarticPsi_FIN066 !₂[-4 + u, y] = liftPotential_FIN06804 u (y ^ 2) := by
  refine ⟨?_, fun u y _ _ => ?_⟩
  · rintro p ⟨⟨h1, h2⟩, h3, h4⟩
    have hF : (-4 + p.1) ^ 2 + p.2 ≠ 0 := by
      have : (-4 + p.1) ^ 2 + p.2 > 8 := by nlinarith
      exact ne_of_gt (by linarith)
    have hsq : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => Real.sqrt ((-4 + q.1) ^ 2 + q.2)) p :=
      ((by fun_prop : ContDiff ℝ ∞ fun q : ℝ × ℝ => (-4 + q.1) ^ 2 + q.2).contDiffAt).sqrt hF
    have hlog : ContDiffAt ℝ ∞
        (fun q : ℝ × ℝ => Real.log (besselI 0 (Real.sqrt ((-4 + q.1) ^ 2 + q.2)))) p :=
      (besselI_zero_contDiff_FIN06802.log fun t => (besselI_zero_pos t).ne').comp_contDiffAt p hsq
    have hpoly : ContDiffAt ℝ ∞
        (fun q : ℝ × ℝ => (-5 + q.1) ^ 2 / (2 * quarticKappa) +
          q.2 / (2 * quarticKappa * quarticEta)) p :=
      ((by fun_prop : ContDiff ℝ ∞ fun q : ℝ × ℝ =>
        (-5 + q.1) ^ 2 / (2 * quarticKappa) +
          q.2 / (2 * quarticKappa * quarticEta))).contDiffAt
    have hJ : ContDiffAt ℝ ∞ (fun q : ℝ × ℝ => liftPotential_FIN06804 q.1 q.2) p := by
      unfold liftPotential_FIN06804
      exact hpoly.sub hlog
    exact hJ.contDiffWithinAt
  · rw [gate_fin068_38_named_potential_definition_gate_besselI]
    unfold liftPotential_FIN06804 quarticKappa quarticEta quarticB
    have hu : (-4 + u - 1 : ℝ) = -5 + u := by ring
    rw [hu]

end DGPS.Frontier.FIN068
