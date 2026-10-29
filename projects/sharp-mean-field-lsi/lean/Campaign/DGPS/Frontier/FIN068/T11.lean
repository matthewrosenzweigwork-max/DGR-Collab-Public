import DGPS.Frontier.FIN068.T31

/-!
Task id and title: FIN068.11, Factor the longitudinal square (module
`DGPS.Frontier.FIN068.T11`).

Provides:
* `DGPS.Frontier.FIN068.fin068_11_factor_longitudinal_square`: there are `δu, δz > 0` and a curve `a`
  with the critical-curve data of FIN068.24/FIN068.30 (`C^∞` on `Set.Ioo (-δz) δz`, `a 0 = 0`, the
  critical equation for `J_u`, uniqueness of its zero in the window), and `δx, δy > 0` such that,
  with `x₀ y = -4 + a (y^2)` and the open rectangle `P = (-4-δx, -4+δx) × (-δy, δy)`: the segments
  `(x₀ y + t (x - x₀ y), y)`, `t ∈ [0,1]`, over `(x, y) ∈ P` lie in `R = (-5,-3) × (-1,1)`; the
  first-order condition `ψ_x (x₀ y, y) = 0` holds on `P`; and there are maps `φ : ℝ → ℝ` and
  `a₂ : ℝ × ℝ → ℝ` with `φ y = ψ (x₀ y, y)`, `a₂ (x, y) = 2 ∫₀¹ (1 - t) ψ_xx(x₀ y + t h, y) dt`
  (`h = x - x₀ y`), such that `a₂` is `C^∞` on `P`, `A/2 ≤ a₂ ≤ 2A` on `P` (`A = quarticA_FIN06803`),
  and `ψ(x, y) - φ y = (1/2) h^2 a₂ (x, y)` on `P`.

Proof: pure assembly. FIN068.31 (which rests on FIN068.27 for the smooth patch, FIN068.28 and
FIN068.29 for smooth parameter integration, and FIN068.30 for the exact second-order factorization)
already delivers the curve, the patch, the segment containment, the critical equation, the factor
`a₂` with its smoothness and the bounds `A/2 ≤ a₂ ≤ 2A`, and the factorization with
`ψ(x₀ y, y)` in place of `φ y`. Here `φ` is introduced as the function `y ↦ ψ(x₀ y, y)` and the
factorization is rewritten with it.

R5 notes:
* No hypothesis is added. The statement is closed (existential in the curve, the patch, `φ` and `a₂`).
* Non-literal reading: "a neighborhood of `(-4, 0)`" is realised existentially, as the open
  rectangle `P` above (it contains `(-4, 0)` since `δx, δy > 0`). The patch is the one obtained in
  FIN068.31 by shrinking the FIN068.27/FIN068.30 patch; it is a patch of that kind, not literally the
  object chosen inside the earlier existentials. The segment-containment and critical-equation
  facts are restated so that the patch is pinned down.
* `ψ(x, y)` is `quarticPsi_FIN066 !₂[x, y]`. `ψ_xx` is read as the second derivative of the slice
  `s ↦ ψ(s, y)`, `deriv (deriv (fun s => quarticPsi_FIN066 !₂[s, y]))`. `x₀ y` is `-4 + a (y^2)`,
  the FIN068.24 curve (FIN068.23). `φ y` is `ψ(x₀ y, y)`, as in the frozen statement; it is a
  function on all of `ℝ`, given by its defining formula (`∀ y, φ y = ...`).
* `a₂` is given by its defining formula as a function on all of `ℝ × ℝ`
  (`∀ p, a₂ p = 2 * ∫ t in 0..1, (1 - t) * ψ_xx(...)`); smoothness, the bounds and the
  factorization are asserted on `P` only. The integral is the interval integral
  `∫ t in (0:ℝ)..1`; `a₂` carries the factor `2` of the displayed formula.
* `A` is `quarticA_FIN06803`, the campaign constant of FIN068.03. The additional base value
  `a₂ (-4, 0) = A` of FIN068.31 is not part of FIN068.11 and is not restated.
* Smoothness of `ψ` on `R` is inherited from FIN068.27, hence from FIN068.04 and the FIN068.37 and
  FIN068.38 identifications; this dependency is not repaired here.
-/

open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff Topology

namespace DGPS.Frontier.FIN068

/-- Factor the longitudinal square (FIN068.11). -/
theorem fin068_11_factor_longitudinal_square :
    ∃ δu δz : ℝ, 0 < δu ∧ 0 < δz ∧ ∃ a : ℝ → ℝ,
      ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz) ∧ a 0 = 0 ∧
      (∀ z : ℝ, |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) ∧
      (∀ u z : ℝ, |u| < δu → |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) u = 0 → u = a z) ∧
      ∃ δx δy : ℝ, 0 < δx ∧ 0 < δy ∧
        (∀ x y t : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
          t ∈ Set.Icc (0 : ℝ) 1 →
          (-4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2))), y) ∈
            Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) ∧
        (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
          deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, y]) (-4 + a (y ^ 2)) = 0) ∧
        ∃ (φ : ℝ → ℝ) (a₂ : ℝ × ℝ → ℝ),
          (∀ y : ℝ, φ y = quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y]) ∧
          (∀ p : ℝ × ℝ, a₂ p = 2 * ∫ t in (0 : ℝ)..1, (1 - t) *
            deriv (deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, p.2]))
              (-4 + a (p.2 ^ 2) + t * (p.1 - (-4 + a (p.2 ^ 2))))) ∧
          ContDiffOn ℝ ∞ a₂ (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) ∧
          (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
            quarticA_FIN06803 / 2 ≤ a₂ (x, y) ∧ a₂ (x, y) ≤ 2 * quarticA_FIN06803) ∧
          (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
            quarticPsi_FIN066 !₂[x, y] - φ y =
              (1 / 2) * (x - (-4 + a (y ^ 2))) ^ 2 * a₂ (x, y)) := by
  obtain ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, δx, δy, hδx, hδy, hseg, hcrit, a₂, ha₂, hsm, -, hbd,
    hfac⟩ := fin068_31_smoothness_positivity_factor
  refine ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, δx, δy, hδx, hδy, hseg, hcrit,
    fun y => quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y], a₂, fun _ => rfl, ha₂, hsm, hbd, ?_⟩
  exact hfac

end DGPS.Frontier.FIN068
