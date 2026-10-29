import DGPS.Frontier.FIN068.T35
import DGPS.Frontier.FIN068.T36

/-!
Task id and title: FIN068.13, Jacobian and energy metric (module
`DGPS.Frontier.FIN068.T13`).

Provides:
* `DGPS.Frontier.FIN068.fin068_13_jacobian_energy_metric`: the full conclusion of FIN068.35 (the
  curve `a`, the patch, the factor `a₂`, the signed coordinate `v`, the neighborhood `U`, the open
  set `N`, the rectangle `Q = (-ε, ε) × (-δ, δ)`, the inverse `X`, the restricted source patch `W`,
  the derivative identities and the density Jacobian bounds `1 / (2 sqrt A) ≤ X_v ≤ 2 / sqrt A`),
  exactly as stated there, together with one further conjunct on `Q`: for every `q ∈ Q` and every
  `ξ : Fin 2 → ℝ`, with `D = [[v_x, v_y], [0, 1]]` evaluated at the source point `p = (X q, q.2)`,
  `|ξ|^2 / (1 + 8 / A) ≤ |Dᵀ ξ|^2 ≤ (4 A + 2) |ξ|^2`, where `|·|^2` is the sum of the squares of the
  two coordinates.

Proof: the FIN068.35 conclusion is obtained and restated. For `q ∈ Q`, the point `p = (X q, q.2)`
lies in `W`, where FIN068.35 gives `sqrt A / 2 ≤ v_x p ≤ 2 sqrt A` and `|v_y p| ≤ 1`. These are the
hypotheses of FIN068.36 with `a = v_x p` and `b = v_y p`, so FIN068.36 gives the two energy bounds.

R5 notes:
* No hypothesis is added. The statement is closed (an existential over the FIN068.34 and FIN068.35
  data), in the same packaging as FIN068.35; the FIN068.35 conclusion is restated inline with the
  same binder names, and the new energy conjunct is appended after the Jacobian conjunct.
* "On the coordinate rectangle from Task 12" is read as: for every `q` in the fixed open rectangle
  `Q = (-ε, ε) × (-δ, δ)` of FIN068.34, with the corresponding source point `p = (X q, q.2)`, which
  lies in the restricted source patch `W` (FIN068.34/35). The pointwise bounds are evaluated there.
* The derivative matrix of the forward map `(x, y) ↦ (v(x, y), y)` at `p` is
  `[[v_x, v_y], [0, 1]]`; it is written `Matrix.of ![![v_x, v_y], ![0, 1]]`, as in FIN068.36. The
  vector `ξ ∈ ℝ²` is `Fin 2 → ℝ` and `|ξ|^2` is `ξ 0 ^ 2 + ξ 1 ^ 2`, as in FIN068.36.
* The density Jacobian `j = ∂x/∂v` is `X_v = fderiv ℝ X q (1, 0)`, unchanged from FIN068.35. Its
  bounds are not re-derived here; they are carried over as the penultimate conjunct.
* Bounds are non-strict, and `1 / (2 sqrt A)`, `2 / sqrt A`, `|ξ|^2 / (1 + 8 / A)` are real division
  with `A = quarticA_FIN06803`. Positivity of `A` (FIN068.03) is used inside FIN068.35 and FIN068.36.
* The closing sentence of the specification ("positive, finite, uniform comparison constants for the
  transformed Dirichlet energy") is not formalized as a separate object: no Dirichlet energy or
  measure is defined in the supplied specification. The two explicit constants are the content.
* Dependencies: FIN068.35 (module `DGPS.Frontier.FIN068.T35`) and FIN068.36 (module
  `DGPS.Frontier.FIN068.T36`).
-/

open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff

namespace DGPS.Frontier.FIN068

/-- Jacobian and energy metric (FIN068.13): the FIN068.35 data on the fixed rectangle `Q`, the
density Jacobian bounds `1 / (2 sqrt A) ≤ X_v ≤ 2 / sqrt A`, and, for every `q ∈ Q` and every
`ξ`, the energy-metric comparison `|ξ|^2 / (1 + 8 / A) ≤ |Dᵀ ξ|^2 ≤ (4 A + 2) |ξ|^2` with
`D = [[v_x, v_y], [0, 1]]` at the source point `(X q, q.2)`. -/
theorem fin068_13_jacobian_energy_metric :
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
                      (∀ p ∈ W, X (v p, p.2) = p.1) ∧
                      (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ,
                        fderiv ℝ X q (1, 0) = 1 / fderiv ℝ v (X q, q.2) (1, 0) ∧
                        fderiv ℝ X q (0, 1) =
                          (-fderiv ℝ v (X q, q.2) (0, 1)) / fderiv ℝ v (X q, q.2) (1, 0)) ∧
                      (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ,
                        1 / (2 * Real.sqrt quarticA_FIN06803) ≤ fderiv ℝ X q (1, 0) ∧
                        fderiv ℝ X q (1, 0) ≤ 2 / Real.sqrt quarticA_FIN06803) ∧
                      (∀ q ∈ Set.Ioo (-ε) ε ×ˢ Set.Ioo (-δ) δ, ∀ ξ : Fin 2 → ℝ,
                        sqnorm_FIN06836 ξ / (1 + 8 / quarticA_FIN06803) ≤
                          sqnorm_FIN06836 ((Matrix.transpose
                            (Matrix.of ![![fderiv ℝ v (X q, q.2) (1, 0),
                              fderiv ℝ v (X q, q.2) (0, 1)], ![0, 1]])).mulVec ξ) ∧
                        sqnorm_FIN06836 ((Matrix.transpose
                            (Matrix.of ![![fderiv ℝ v (X q, q.2) (1, 0),
                              fderiv ℝ v (X q, q.2) (0, 1)], ![0, 1]])).mulVec ξ) ≤
                          (4 * quarticA_FIN06803 + 2) * sqnorm_FIN06836 ξ) := by
  obtain ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, δx, δy, hδx, hδy, hseg, hcrit, hx0, hx0d, hφ, a₂,
    hdef, hsm, hbase, hbd, hfac, v, hvdef, hvsm, hen, hv0, hvx, hvy, U, hUo, hU0, hUP, hUb,
    N, hNo, hN0, hNU, hinj, himgo, ε, δ, hε, hδ, hcl, X, hX, W, hWdef, hWo, hW0, hWN, hWb,
    hbij, hTs, hXs, hXW, hXv, hXinv, hder, hjac⟩ := fin068_35_inverse_derivatives_jacobian
  refine ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, δx, δy, hδx, hδy, hseg, hcrit, hx0, hx0d, hφ, a₂,
    hdef, hsm, hbase, hbd, hfac, v, hvdef, hvsm, hen, hv0, hvx, hvy, U, hUo, hU0, hUP, hUb,
    N, hNo, hN0, hNU, hinj, himgo, ε, δ, hε, hδ, hcl, X, hX, W, hWdef, hWo, hW0, hWN, hWb,
    hbij, hTs, hXs, hXW, hXv, hXinv, hder, hjac, ?_⟩
  intro q hq ξ
  obtain ⟨h1', h2', h3'⟩ := hWb _ (hXW q hq)
  exact fin068_36_quantitative_energy_matrix_comparison _ _ h1' h2' h3' ξ

end DGPS.Frontier.FIN068
