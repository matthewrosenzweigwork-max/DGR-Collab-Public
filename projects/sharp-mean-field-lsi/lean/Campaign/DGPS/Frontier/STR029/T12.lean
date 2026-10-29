import DGPS.Frontier.STR029.T50

/-!
# STR029.12: Exact normalized variational gradient

Task id: STR029.12 (node STR029, frontier unit, leaf formalization).
Title: Exact normalized variational gradient.

For real `h` and `γ` and `2π`-periodic `u, v` of class `C^{2,1/2}` with Haar mean zero (`v` also),
let `ρ = ρ(h,u)`, `I = ∫ u'^2 ρ`, `E_ρ = ∫ u ρ`, where `∫` is the normalised Haar mean
`dm = dt/(2π)`. Put `J(h,γ,u) = I_h(ρ(h,u)) - 2 (1 + γ) H_h(ρ(h,u))` and
`G = ρ [-2 u'' + 6 h sin 3t u' - u'^2 - 2 r u - I + 2 r E_ρ]` with `r = 1 + γ`. Then
`D_u J [v] = ∫ G v dm` and `∫ G dm = 0`.

## Provides

* `DGPS.Frontier.STR029.str029_12_exact_normalized_variational_gradient`: one conjunction.
  (1) `s ↦ J(h,γ,u + s v)` has derivative `∫ G v` at `s = 0`. (2) `∫ G = 0`.
* `DGPS.Frontier.STR029.gradG_STR02912`: the expression `G` as a function of `t`, with the two
  integrals `I` and `E_ρ` passed as arguments.
* `DGPS.Frontier.STR029.gradG_eq_STR02912`: with the closed integrals substituted, `G` equals the
  expression `gradG_STR02950` of STR029.50.

The proof composes the normalized-density derivative (STR029.48), the information variations
(STR029.49) and the integration by parts identity with the mean-zero computation (STR029.50).
Here only the parameters `I` and `E` are identified, and STR029.50 is applied.

## R5 notes

* `D_u` is the directional (Gâteaux) derivative at `u` in the direction `v`, formalised as
  `HasDerivAt (fun s => J(h,γ,u + s v)) (∫ G v) 0`, as in STR029.49 and STR029.50. No Fréchet
  derivative on a bundled `C^{2,α}` space is claimed.
* The carrier is the concrete predicate `IsC2Alpha_STR02901 (1 / 2)` on `2π`-periodic functions
  of `t` (the variable `t = 2πx`), with `α = 1/2` fixed in the node preamble. The norm
  `‖u‖∞ + ‖u'‖∞ + ‖u''‖∞ + [u'']_α` is not used directly.
* The Haar-mean-zero hypotheses `∫ u dm = 0` and `∫ v dm = 0` are carried as listed in the
  specification, under the names `_hu0` and `_hv0` (underscore only to silence the unused-variable
  linter). They are not needed. The identity and the mean-zero conclusion hold for every
  `C^{2,α}` pair, since the proof uses periodicity and `∫ ρ = 1` only. Keeping them does not
  weaken the statement.
* `I` and `E` are arguments constrained by the defining equations `hI` and `hE`, which are the
  closed integrals `∫ u'^2 ρ dm` and `∫ u ρ dm`. Substituting them gives the specification's `G`.
* `r = 1 + γ` is written as `1 + γ` and no separate variable `r` is introduced. `h` and `γ` range
  over all reals. The restriction `0 < |h| < h0` of the node is not needed for this identity.
* `J` is the logarithmic-chart functional `fisherChart - 2 (1 + γ) entropyChart` of STR029.49.
  Its pieces are the angular quantities `4 ∫ g'^2 q_h dm` and `∫ g^2 log g^2 q_h dm` with
  `g^2 = ρ/q_h`, written in the chart. The chart identities are taken from STR029.49 and are not
  reproved here. This unit does not identify `J` with `ordinaryFisher` or `ordinaryEntropy`, and
  it applies no angular-to-physical factor (`ordinaryFisher = ofReal a₀ * angFisher`). Those
  identifications belong to STR029.01.
* The common optimizer chart, the weighted carriers of the node preamble and the Euler range map
  are not used. `G` is defined on the variational chart directly, with no assumed projected Euler
  equation.
-/

namespace DGPS.Frontier.STR029

/-- The expression `G = ρ [-2 u'' + 6 h sin 3t u' - u'^2 - 2 r u - I + 2 r E]` of STR029.12, with
`r = 1 + γ`, `ρ = ρ(h,u)`, and the normalised integrals `I` and `E` passed as arguments. -/
noncomputable def gradG_STR02912 (h γ I E : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  rhoT_STR02901 h u t *
    (-2 * deriv (deriv u) t + 6 * h * Real.sin (3 * t) * deriv u t - deriv u t ^ 2 -
      2 * (1 + γ) * u t - I + 2 * (1 + γ) * E)

/-- With `I = ∫ u'^2 ρ(h,u)` and `E = ∫ u ρ(h,u)` substituted, `gradG_STR02912` is the expression
`gradG_STR02950` of STR029.50. -/
theorem gradG_eq_STR02912 (h γ : ℝ) (u : ℝ → ℝ) :
    gradG_STR02912 h γ (meanT_STR02901 (fun r => deriv u r ^ 2 * rhoT_STR02901 h u r))
      (meanT_STR02901 (fun r => u r * rhoT_STR02901 h u r)) u = gradG_STR02950 h γ u :=
  rfl

/-- Exact normalized variational gradient. For `2π`-periodic `C^{2,1/2}` functions `u, v` with
Haar mean zero and `I = ∫ u'^2 ρ(h,u)`, `E = ∫ u ρ(h,u)`, the directional derivative of
`J(h,γ,·)` at `u` in the direction `v` is `∫ G v`, and `∫ G = 0`. -/
theorem str029_12_exact_normalized_variational_gradient (h γ : ℝ) {u v : ℝ → ℝ}
    (hu : IsC2Alpha_STR02901 (1 / 2) u) (_hu0 : meanT_STR02901 u = 0)
    (hv : IsC2Alpha_STR02901 (1 / 2) v) (_hv0 : meanT_STR02901 v = 0)
    (I E : ℝ)
    (hI : I = meanT_STR02901 (fun r => deriv u r ^ 2 * rhoT_STR02901 h u r))
    (hE : E = meanT_STR02901 (fun r => u r * rhoT_STR02901 h u r)) :
    HasDerivAt (fun s : ℝ => Jchart_STR02950 h γ (fun t => u t + s * v t))
        (meanT_STR02901 (fun t => gradG_STR02912 h γ I E u t * v t)) 0 ∧
      meanT_STR02901 (gradG_STR02912 h γ I E u) = 0 := by
  subst hI hE
  exact str029_50_integrate_variation_compute_mean h γ hu hv

end DGPS.Frontier.STR029
