import DGPS.Frontier.EX012.T15

/-!
# EX012.01: Positive smooth normalized logarithm

Task id: EX012.01 (node EX012, leaf formalization, assembly).
Title: Positive smooth normalized logarithm.

For every sufficiently small `h > 0` and every minimizing `ρ` of the ground functional
`ex010_ground h` (covered by EX011), choose its strictly positive smooth representative `r`.
Then `u = √r` is positive and smooth with `∫ u² = 1`, and `u` is given by the normalized
exponential `u = exp (v/2) / (∫ exp v)^(1/2)` with `v = log r - ∫ log r`. For every fixed
`α` (a `[HolderExponent α]`), the centered logarithm `v` is an element of `PH α 2`, has mean
zero, and its `PH` norm is at most any prescribed `ε > 0` uniformly over the minimizing set once
`h` is small. This module assembles EX012.13 (transfer of the smooth representative and its
mass), EX012.14 (normalized centered logarithm) and EX012.15 (bundling the captured logarithm).

## Provides

* `DGPS.Frontier.EX012.ex012_01_positive_smooth_normalized_logarithm (α : ℝ) [HolderExponent α]`:
  the uniform assertion `∀ ε > 0, ∃ h1 > 0, ∀ h ∈ (0, h1), ∀ minimizing ρ, ∃ r, ...`. The
  representative `r` is positive, smooth, the only smooth representative of `ρ.density`, and
  there is a one-periodic `u = √r` (lifted to `ℝ`) that is positive, smooth, has `∫₀¹ u² = 1`
  and equals the normalized exponential `exp (v/2) / (∫ exp v)^(1/2)` of `v = log r - ∫ log r`;
  there is `v : PH α 2` with `v.val` the centered logarithm, `∫ (log r - ∫ log r) = 0` on the
  torus, `∫₀¹ v.val = 0` on the period interval, and `‖v‖ ≤ ε`.

## R5 notes

* Hölder exponent: `α : ℝ` with `[HolderExponent α]` is a parameter of the main theorem, as in
  EX012.15. It is the campaign form of the preamble's `Fix 0 < α < 1`; it is not an added
  hypothesis (`HolderExponent` carries `pos : 0 < α` and `lt_one : α < 1`).
* Threshold and minimizers: `h1` is the threshold supplied by EX011 through EX012.15. The
  minimizing hypothesis `∀ ρ', ex010_ground h ρ ≤ ex010_ground h ρ'` is the one used by EX011.
  The phrase "for every sufficiently small positive `h`" is read as `∃ h1 > 0, ∀ h ∈ (0, h1)`.
  The uniform quantifier order (`∀ ε` outside `∃ h1` outside `∀ ρ`) is that of EX011's uniform
  capture clause, so "tends to zero uniformly over the minimizing set" is read as this order.
* Positivity and compactness: `min r > 0` is not stated separately; it is EX012.13's lower-bound
  conjunct and is not needed for this statement. The square root and logarithm are used on the
  positive values of `r`.
* Mass: `∫ u² = 1` is read as the period-interval integral `∫ t in 0..1, u t ^ 2 = 1` of the lift
  `u : ℝ → ℝ`, the form delivered by EX012.13. The torus mass `∫ r ∂haar 1 = 1` is used
  internally (through EX012.14) and is not restated.
* Formula for `u`: stated pointwise on the lift, `∀ t, u t = exp((log r(pt t) - ℓ)/2) /
  (∫ exp (log r - ℓ) ∂haar 1)^(1/2)` with `ℓ = ∫ log r ∂haar 1`, the real power `1/2` and
  `pt t = torusLift fun _ => t`. It is the lift of EX012.14's `sqrt_formula`, read through
  `u t = √(r (pt t))`. The specification's `v` and `u` are written out in full rather than named,
  because `v` is the function `s ↦ log (r (pt s)) - ℓ` bundled as `v.val` in `PH α 2`.
* Smoothness of `u`: read as `ContDiff ℝ ∞ u` on the lift, together with the one-periodicity
  `Function.Periodic u 1` (the torus form of "smooth"). Both come from EX012.13.
* Uniqueness conjunct (added, not in the specification's list, inherited from EX012.15):
  `∀ r', IsSmoothPeriodic r' → ρ.density =ᵐ[haar 1] r' → r' = r`. It makes "its strictly positive
  smooth representative" literal, so that `u` and `v` do not depend on which representative EX011
  supplied. It adds a conclusion and weakens nothing.
* Mean zero of `v`: read in two places, as the torus Haar mean `∫ (log r - ℓ) ∂haar 1 = 0`
  (EX012.14) and as the period-interval mean `∫ t in 0..1, v.val t = 0` (EX012.15).
* Norm: the `PH` norm `‖v‖` is `phNorm α 2 v.val` (`PH.norm_def`, by `rfl`); this is the norm of
  the uniform assertion. No regularity estimate or limiting argument is added here.
* Assembly only: no new mathematical argument is proved in this file. Every conjunct is the
  corresponding conjunct of EX012.13, EX012.14 or EX012.15 instantiated at the same `h`, `ρ` and
  `r`, with the same `α` and `ε`.
-/

open MeasureTheory
open scoped ContDiff
open DGPS.Circle.VonMisesSmallField
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.EX012

theorem ex012_01_positive_smooth_normalized_logarithm (α : ℝ) [HolderExponent α] :
    ∀ ε : ℝ, 0 < ε → ∃ h1 : ℝ, 0 < h1 ∧
      ∀ h : ℝ, 0 < h → h < h1 → ∀ ρ : AbsoluteDensity 1,
        (∀ ρ' : AbsoluteDensity 1, ex010_ground h ρ ≤ ex010_ground h ρ') →
        ∃ r : Torus 1 → ℝ, (∀ x, 0 < r x) ∧ IsSmoothPeriodic r ∧ ρ.density =ᵐ[haar 1] r ∧
          (∀ r' : Torus 1 → ℝ, IsSmoothPeriodic r' → ρ.density =ᵐ[haar 1] r' → r' = r) ∧
          ∃ u : ℝ → ℝ, (∀ t, u t = Real.sqrt (r (torusLift fun _ => t))) ∧
            ContDiff ℝ ∞ u ∧ Function.Periodic u 1 ∧ (∀ t, 0 < u t) ∧
            (∫ t in (0 : ℝ)..1, u t ^ 2 = 1) ∧
            (∀ t, u t = Real.exp ((Real.log (r (torusLift fun _ => t)) -
                ∫ y, Real.log (r y) ∂haar 1) / 2) /
              (∫ z, Real.exp (Real.log (r z) - ∫ y, Real.log (r y) ∂haar 1) ∂haar 1) ^
                (1 / 2 : ℝ)) ∧
          ∃ v : PH α 2,
            v.val = (fun s => Real.log (r (torusLift fun _ => s)) - ∫ y, Real.log (r y) ∂haar 1) ∧
            (∫ x, (Real.log (r x) - ∫ y, Real.log (r y) ∂haar 1) ∂haar 1 = 0) ∧
            (∫ t in (0 : ℝ)..1, v.val t = 0) ∧ ‖v‖ ≤ ε := by
  intro ε hε
  obtain ⟨h1, hh1, hT15⟩ := ex012_15_bundle_captured_logarithm α ε hε
  refine ⟨h1, hh1, fun h hpos hlt ρ hmin => ?_⟩
  obtain ⟨r, hr, hsm, hρ, huniq, hmean, w, hw, hnorm, hwmean⟩ := hT15 h hpos hlt ρ hmin
  obtain ⟨-, -, hmass, -, -, u, hu, hsmu, hper, hpos_u, hsq, -⟩ :=
    ex012_13_transfer_smooth_representative_mass ρ r hr hsm hρ
  refine ⟨r, hr, hsm, hρ, huniq, u, hu, hsmu, hper, hpos_u, hsq, ?_, w, hw, hmean, hwmean, hnorm⟩
  intro t
  rw [hu t]
  exact ex012_14_normalized_centered_logarithm_sqrt_formula hr hmass (torusLift fun _ => t)

end DGPS.Frontier.EX012
