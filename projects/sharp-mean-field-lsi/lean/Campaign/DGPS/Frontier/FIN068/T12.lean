import DGPS.Frontier.FIN068.T34

/-!
Task id and title: FIN068.12, Coordinate and fixed image rectangle (module
`DGPS.Frontier.FIN068.T12`).

Provides:
* `DGPS.Frontier.FIN068.fin068_12_coordinate_fixed_image_rectangle`: the assembled conclusion of
  FIN068.32, FIN068.33 and FIN068.34. There are `δx, δy > 0`, a curve `a` (the critical curve
  `x₀ y = -4 + a (y ^ 2)`) and a factor `a₂` (the integral formula for half the second derivative
  of `ψ` along the segment from `x₀ y` to `x`), such that the signed coordinate
  `v p = (p.1 - x₀ p.2) * sqrt (a₂ p)` is `C^∞` on the patch `P = (-4-δx, -4+δx) × (-δy, δy)` and
  satisfies `ψ(x, y) = v (x, y) ^ 2 / 2 + φ(y)` on `P`, where `φ(y) = ψ(x₀ y, y)`. On an open
  neighborhood `U ⊆ P` of `(-4, 0)` one has `√A / 2 ≤ v_x ≤ 2√A` and `|v_y| ≤ 1`. Finally the
  map `(x, y) ↦ (v (x, y), y)` restricts to a smooth diffeomorphism of an open neighborhood `W` of
  `(-4, 0)` (with `W ⊆ U`, and `W` the preimage of the rectangle) onto a fixed open rectangle
  `Q = (-ε, ε) × (-δ, δ)` centred at zero, with smooth inverse `q ↦ (X q, q.2)` on `Q`.
* Helper declarations: none. The theorem is the FIN068.34 conclusion, obtained by the single term
  `fin068_34_smooth_inverse_fixed_image_rectangle`; no helper lemma is introduced.

R5 notes:
* No hypothesis is added. The statement is closed: every object of the specification (the curve
  `a`, the factor `a₂`, the coordinate `v`, the neighborhood `U`, the rectangle `Q`, the patch `W`,
  the inverse `X`) appears as an existential witness, with its defining equation or property
  stated inside the conclusion. Nothing is assumed from FIN068.37 or FIN068.38; those identifications
  enter only through the FIN068.32 to FIN068.34 chain, exactly as in those files.
* The statement is the FIN068.34 conclusion verbatim (same binder names and shape), so that the
  consuming tasks see the coordinate, the bounds and the diffeomorphism in one place. It is not
  weaker than the specification's Statement paragraph: the specification's extra objects
  (`x₀`, `a₂`, `φ`) are the explicit expressions above, and the rectangle and patch are existential.
* `x₀ y` is read as `-4 + a (y ^ 2)`, the critical-curve formula of FIN068.32. `φ(y)` is read as
  `quarticPsi_FIN066 !₂[x₀ y, y]`, and `ψ` as `quarticPsi_FIN066 !₂[x, y]` (the displayed formula
  equality is the FIN068.38 gate, not this task).
* `a₂` is not assumed to be `ψ_xx / 2`; it is defined by the integral formula
  `a₂ p = 2 ∫₀¹ (1 - t) ψ_xx(x₀ y + t (x - x₀ y), y) dt`, as in FIN068.32/33, and the identity
  `ψ(x, y) - φ(y) = (1/2) (x - x₀ y)² a₂(x, y)` is part of the conclusion.
* "Smooth" is `ContDiffOn ℝ ∞` (the campaign reading of `C^∞`), with `∞` from `open scoped ContDiff`.
* `v_x` and `v_y` are read as `fderiv ℝ v p (1, 0)` and `fderiv ℝ v p (0, 1)`. `√` is `Real.sqrt`,
  and `A` is `quarticA_FIN06803` (`b/5 - g'(4)`, FIN068.03). The bounds are non-strict, as written.
* "A fixed neighborhood" is read as an open set `U` with `(-4, 0) ∈ U ⊆ P` on which the derivative
  bounds hold. The bounds are required only on `U`, not on all of `P`; `U` is chosen by the
  existential, as the specification's "choose" permits.
* "A smooth diffeomorphism on a smaller patch onto a fixed open rectangle centred at zero" is read
  as: `W = N ∩ T ⁻¹' Q` is open, contains `(-4, 0)`, lies in `N ⊆ U`; `T = (v, y)` is `C^∞` on `W`
  and maps `W` bijectively onto `Q = (-ε, ε) × (-δ, δ)` (`Set.BijOn`); the map `q ↦ (X q, q.2)` is
  `C^∞` on `Q` with values in `W`; and the two composites are the identities. The rectangle is
  centred at `(0, 0)` because `T (-4, 0) = (0, 0)`.
* "Fixed" rectangle is read as existential `ε, δ > 0` with `closure Q ⊆ T '' N`, not as numerical
  constants; the specification does not fix them numerically.
* The inverse-function route is the smooth one (`ContDiffAt.toOpenPartialHomeomorph`), as in
  FIN068.34; the specification's alternative parameter implicit-function route is not used.
-/

open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff

namespace DGPS.Frontier.FIN068

/-- Coordinate and fixed image rectangle (FIN068.12): the FIN068.32 to FIN068.34 data, with the
signed coordinate `v = (x - x₀ y) √a₂`, the identity `ψ = v²/2 + φ(y)` on the patch, the bounds
`√A/2 ≤ v_x ≤ 2√A`, `|v_y| ≤ 1` on a fixed neighborhood, and a smooth diffeomorphism from a
smaller patch onto a fixed open rectangle centred at zero. -/
theorem fin068_12_coordinate_fixed_image_rectangle :
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
        ContDiffOn ℝ ∞ (fun y : ℝ => -4 + a (y ^ 2)) (Set.Ioo (-δy) δy) ∧
        deriv (fun y : ℝ => -4 + a (y ^ 2)) 0 = 0 ∧
        ContDiffOn ℝ ∞ (fun y : ℝ => quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y])
          (Set.Ioo (-δy) δy) ∧
        ∃ a₂ : ℝ × ℝ → ℝ,
          (∀ p : ℝ × ℝ, a₂ p = 2 * ∫ t in (0 : ℝ)..1, (1 - t) *
            deriv (deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, p.2]))
              (-4 + a (p.2 ^ 2) + t * (p.1 - (-4 + a (p.2 ^ 2))))) ∧
          ContDiffOn ℝ ∞ a₂ (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) ∧
          a₂ (-4, 0) = quarticA_FIN06803 ∧
          (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
            quarticA_FIN06803 / 2 ≤ a₂ (x, y) ∧ a₂ (x, y) ≤ 2 * quarticA_FIN06803) ∧
          (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
            quarticPsi_FIN066 !₂[x, y] - quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y] =
              (1 / 2) * (x - (-4 + a (y ^ 2))) ^ 2 * a₂ (x, y)) ∧
          ∃ v : ℝ × ℝ → ℝ,
            (∀ p : ℝ × ℝ, v p = (p.1 - (-4 + a (p.2 ^ 2))) * Real.sqrt (a₂ p)) ∧
            ContDiffOn ℝ ∞ v (Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy) ∧
            (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
              quarticPsi_FIN066 !₂[x, y] =
                v (x, y) ^ 2 / 2 + quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y]) ∧
            v (-4, 0) = 0 ∧
            fderiv ℝ v (-4, 0) (1, 0) = Real.sqrt quarticA_FIN06803 ∧
            fderiv ℝ v (-4, 0) (0, 1) = 0 ∧
            ∃ U : Set (ℝ × ℝ), IsOpen U ∧ (-4, 0) ∈ U ∧
              U ⊆ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy ∧
              (∀ p ∈ U, Real.sqrt quarticA_FIN06803 / 2 ≤ fderiv ℝ v p (1, 0) ∧
                fderiv ℝ v p (1, 0) ≤ 2 * Real.sqrt quarticA_FIN06803 ∧
                |fderiv ℝ v p (0, 1)| ≤ 1) ∧
              ∃ N : Set (ℝ × ℝ), IsOpen N ∧ (-4, 0) ∈ N ∧ N ⊆ U ∧
                Set.InjOn (fun p : ℝ × ℝ => (v p, p.2)) N ∧
                IsOpen ((fun p : ℝ × ℝ => (v p, p.2)) '' N) ∧
                ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
                  closure (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ⊆
                    (fun p : ℝ × ℝ => (v p, p.2)) '' N ∧
                  ∃ X : ℝ × ℝ → ℝ, ContDiffOn ℝ ∞ X (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
                    ∃ W : Set (ℝ × ℝ),
                      W = N ∩ (fun p : ℝ × ℝ => (v p, p.2)) ⁻¹'
                        (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
                      IsOpen W ∧ (-4, 0) ∈ W ∧ W ⊆ N ∧
                      (∀ p ∈ W, Real.sqrt quarticA_FIN06803 / 2 ≤ fderiv ℝ v p (1, 0) ∧
                        fderiv ℝ v p (1, 0) ≤ 2 * Real.sqrt quarticA_FIN06803 ∧
                        |fderiv ℝ v p (0, 1)| ≤ 1) ∧
                      Set.BijOn (fun p : ℝ × ℝ => (v p, p.2)) W
                        (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
                      ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => (v p, p.2)) W ∧
                      ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => (X q, q.2))
                        (Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ) ∧
                      (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ, (X q, q.2) ∈ W) ∧
                      (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ, v (X q, q.2) = q.1) ∧
                      (∀ p ∈ W, X (v p, p.2) = p.1) :=
  fin068_34_smooth_inverse_fixed_image_rectangle

end DGPS.Frontier.FIN068
