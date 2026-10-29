import DGPS.Frontier.FIN068.T24

/-!
Task id and title: FIN068.08, Expansion of the critical curve (module
`DGPS.Frontier.FIN068.T08`).

Provides:
* `DGPS.Frontier.FIN068.fin068_08_expansion_critical_curve`: there are `δu, δz > 0` and a function
  `a`, `C^∞` on `Set.Ioo (-δz) δz`, with `a 0 = 0`, `J_u(a z, z) = 0` for `|z| < δz`, every zero
  `u` of `J_u(·, z)` with `|u| < δu`, `|z| < δz` equal to `a z`, and `a'(0) = d / (32 A)`. There
  are `r, M` with `0 < r < δz`, `0 ≤ M`, `|a''| ≤ M` on the closed interval `Set.Icc (-r) r`, and
  `|a z - d z / (32 A)| ≤ M z^2 / 2` for `|z| ≤ r`. For `x₀ y = -4 + a (y^2)`: `x₀` is `C^∞` on
  `|y| < √r`, even, satisfies the critical equation `ψ_x (x₀ y, y) = 0` for `|y| < √r`, and
  `|x₀ y - (-4 + d y^2 / (32 A))| ≤ M y^4 / 2` there. Here `A = b/5 - g'(4)` and
  `d = b - 4 g'(4)` are written out, with `b = quarticB`, `g = besselRatio`, and
  `ψ_x (x, y)` is `deriv (fun x => quarticPsi_FIN066 !₂[x, y]) x`.
* No helper declarations. The proof is the composition of FIN068.24
  (`DGPS.Frontier.FIN068.fin068_24_curve_taylor_bound_composition`), which packages FIN068.07 and
  FIN068.23 with the Taylor bound of FIN068.24.

R5 notes:
* Assembly only. The statement is the main statement of FIN068.24, copied verbatim (same
  binders, same conclusion, same names for the objects), and the proof is that theorem. No
  hypothesis is added or removed, and no conclusion is weakened.
* "Shrink to a closed interval on which `|a''| ≤ M_a`" is read as the existence of `r` with
  `0 < r < δz` and `M ≥ 0` such that `|deriv (deriv a) z| ≤ M` on `Set.Icc (-r) r`. The
  closed interval is symmetric, `[-r, r]`.
* The expansion `|a z - d z / (32 A)| ≤ M z^2 / 2` is stated for all `z` with `|z| ≤ r`, that is on
  both sides of `0`, as the symmetric interval requires.
* `x₀` is `-4 + a (y^2)`. Its smoothness is stated as `ContDiffOn` on `Set.Ioo (-√r) √r`, not
  globally, because `y^2 < r` is needed to stay in the domain of `a`. Evenness is stated for all
  real `y` as the identity `-4 + a ((-y)^2) = -4 + a (y^2)`. The critical equation and the quartic
  error bound are stated for `|y| < √r`.
* The `O(y^4)` of the informal statement is replaced by the explicit constant `M y^4 / 2`, with the
  same `M` as the second-derivative bound on `[-r, r]`.
* The informal "Taylor formula with bounded second derivative" is proved in FIN068.24 by a
  monotonicity argument (mean value inequality for `a'`), not by the integral remainder. The
  conclusion is the one specified.
* `A` and `d` are written out as `quarticB / 5 - deriv besselRatio 4` and
  `quarticB - 4 * deriv besselRatio 4`. `quarticB` is `besselRatio 4` (definition in
  `DGPS/FiniteN/QuarticSaddle.lean`), `quarticKappa = 5 / quarticB` and `quarticEta = 4 / 5`, as
  in the informal statement. `A > 0` is not a hypothesis here; it enters through FIN068.23.
* Bessel identification (node note, gates FIN068.37 and FIN068.38): `besselRatio t` is defined in
  `DGPS/Circle/BesselMoments.lean` as `besselI 1 t / besselI 0 t`, where
  `besselI n t = ∫ exp (t cos θ) cos (nθ) dm`. The statement uses these base definitions as they
  are. The identification of `besselI 0` and `besselI 1` with the named integrals `I_0`, `I_0'`
  is not established in this file and remains the open gate; the statement is in terms of the
  base objects.
* `ψ` is `quarticPsi_FIN066` on `EuclideanSpace ℝ (Fin 2)`, with point `!₂[x, y]`. Its body
  (`DGPS/FiniteN/QuarticSaddleGlobalFIN066.lean`) is
  `(w 0 - 1)^2 / (2 κ) + (w 1)^2 / (2 κ η) - log (besselI 0 (√(w 0^2 + w 1^2)))`, which is the
  displayed formula of the informal statement. `ψ_x` is the one-variable derivative of the slice
  `x ↦ ψ(x, y)`.
* `J_u` is `deriv (fun s => liftPotential_FIN06804 s z)`, inherited from FIN068.04 and FIN068.07.
-/

open DGPS.Models DGPS.Circle.BesselMoments DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff Topology

namespace DGPS.Frontier.FIN068

/-- Main declaration. Expansion of the critical curve: the critical curve `a` of FIN068.07 with
`a'(0) = d / (32 A)` (FIN068.23), a radius `r` and a bound `M ≥ 0` of `|a''|` on `[-r, r]`, the
bound `|a z - d z / (32 A)| ≤ M z^2 / 2` for `|z| ≤ r`, and, for `x₀ y = -4 + a (y^2)` on
`|y| < √r`: smoothness, evenness, the critical equation `ψ_x (x₀ y, y) = 0`, and the quartic error
bound `|x₀ y - (-4 + d y^2 / (32 A))| ≤ M y^4 / 2`. -/
theorem fin068_08_expansion_critical_curve :
    ∃ δu δz : ℝ, 0 < δu ∧ 0 < δz ∧ ∃ a : ℝ → ℝ,
      ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz) ∧ a 0 = 0 ∧
      (∀ z : ℝ, |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) ∧
      (∀ u z : ℝ, |u| < δu → |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) u = 0 → u = a z) ∧
      deriv a 0 =
        (quarticB - 4 * deriv besselRatio 4) / (32 * (quarticB / 5 - deriv besselRatio 4)) ∧
      ∃ r M : ℝ, 0 < r ∧ r < δz ∧ 0 ≤ M ∧
        (∀ z ∈ Set.Icc (-r) r, |deriv (deriv a) z| ≤ M) ∧
        (∀ z : ℝ, |z| ≤ r →
          |a z - (quarticB - 4 * deriv besselRatio 4) /
            (32 * (quarticB / 5 - deriv besselRatio 4)) * z| ≤ M * z ^ 2 / 2) ∧
        ContDiffOn ℝ ∞ (fun y : ℝ => -4 + a (y ^ 2)) (Set.Ioo (-Real.sqrt r) (Real.sqrt r)) ∧
        (∀ y : ℝ, -4 + a ((-y) ^ 2) = -4 + a (y ^ 2)) ∧
        (∀ y : ℝ, |y| < Real.sqrt r →
          deriv (fun x : ℝ => quarticPsi_FIN066 !₂[x, y]) (-4 + a (y ^ 2)) = 0) ∧
        (∀ y : ℝ, |y| < Real.sqrt r →
          |(-4 + a (y ^ 2)) - (-4 + (quarticB - 4 * deriv besselRatio 4) /
            (32 * (quarticB / 5 - deriv besselRatio 4)) * y ^ 2)| ≤ M * y ^ 4 / 2) :=
  fin068_24_curve_taylor_bound_composition

end DGPS.Frontier.FIN068
