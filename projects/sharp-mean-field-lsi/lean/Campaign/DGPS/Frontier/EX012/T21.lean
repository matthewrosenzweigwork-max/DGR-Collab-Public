import DGPS.Frontier.EX012.T14
import DGPS.Frontier.EX012.T20

/-!
# EX012.21: Logarithmic derivative identities

Task id: EX012.21 (node EX012, leaf formalization).
Title: Logarithmic derivative identities.

With `v = 2 log u - ∫ 2 log u` (the centered doubled logarithm; its mean is zero, as in
EX012.14) and `D = (2π)⁻¹ ∂ₓ`, the identities `D u / u = D v / 2` and
`D² u / u = D² v / 2 + (D v)² / 4` hold for every smooth positive `u`. For the ground state `u`
of EX012.20 (minimality among admissible densities), the pointwise Euler identity
`T = E_h(u²) u` turns `D² v + v + (D v)² / 2 + (τ/4) c₂` into a spatial constant, with `τ = h²`,
`c₂(x) = cos(2π · 2 · x)` and `s₁(x)² = (1 - c₂(x))/2`.

## Provides

* `DGPS.Frontier.EX012.centeredLog2_EX01221`: the function `x ↦ 2 log (u x) - ∫ 2 log u`.
* `DGPS.Frontier.EX012.ex012_21_logarithmic_derivative_identities_first`: `D u x / u x = D v x / 2`
  for every `x`, for smooth positive `u`.
* `DGPS.Frontier.EX012.ex012_21_logarithmic_derivative_identities_second`:
  `D² u x / u x = D² v x / 2 + (D v x)² / 4` for every `x`, for smooth positive `u`.
* `DGPS.Frontier.EX012.ex012_21_logarithmic_derivative_identities_of_euler`: from the pointwise
  Euler identity `T x = E * u x` (a real constant `E`), for every `x`,
  `D² v x + v x + (D v x)² / 2 + (h²/4) cos(2π · 2 · x) = h²/4 - E/2 - ∫ 2 log u`.
* `DGPS.Frontier.EX012.ex012_21_logarithmic_derivative_identities`: main statement. For an
  admissible `u` (`IsAdmSmooth_EX01236`) minimal among admissible densities (the hypothesis of
  EX012.20 part (ii)), the two derivative identities hold pointwise, and
  `D² v + v + (D v)²/2 + (h²/4) c₂` is a spatial constant `∃ K`.
* Helpers (suffix `_EX01221`): the derivative of `v`, the second derivative of `v`, and the
  trigonometric identity `sin² θ = (1 - cos 2θ)/2`.

## R5 notes

* Domain: `u : ℝ → ℝ`, smooth (`ContDiff ℝ ∞`) and positive. The two derivative identities use
  nothing else (no periodicity, no mass normalization). The main statement uses
  `IsAdmSmooth_EX01236 u`, which gives smoothness, one-periodicity, positivity and unit mass; only
  smoothness and positivity are used.
* `D` is `angD_EX01217 = (2π)⁻¹ • deriv`, i.e. the derivative of the specification divided by `2π`.
  The second angular derivative is `angD_EX01217 (angD_EX01217 ·)`.
* The integral `∫` of the specification is read as `∫ t in (0:ℝ)..1`, the period integral used by
  EX012.20 and EX012.14 (the Haar integral of the period cell).
* The specification's `v = 2 log u − ∫2 log u` is `centeredLog2_EX01221 u`. The constant
  `∫ 2 log u` is an interval integral over `[0,1]`, so `v` is a spatial constant shift of `2 log u`.
* `c₂(x) = cos(2π · 2 · x)` and `s₁(x) = sin(2π x)`. The identity `s₁² = (1 - c₂)/2` is proved
  from `cos 2θ = 1 - 2 sin² θ` (`Real.cos_two_mul`, `Real.sin_sq_add_cos_sq`).
* The Euler identity is NOT a hypothesis of the specification's text for EX012.21 (its statement
  says only "deduce"). It is the output of EX012.20 part (ii), which needs minimality of `u²`.
  The main statement therefore takes exactly the minimality hypothesis of EX012.20 part (ii),
  `∀ v admissible, E_h(u²) ≤ E_h(v²)`, in the admissible-density form (the weaker of the two
  EX012.20 variants; the `_ground` variant over all `AbsoluteDensity 1` is not used). The
  `_of_euler` lemma isolates the deduction from the pointwise Euler identity alone.
* `E_h(u²)` is `groundE_EX01236 h u`, the displayed expression of EX012.36 (the unfolding to
  `ex010_ground` is EX012.36's `ground_smoothDensity_EX01236`, used inside EX012.20).
* The constant is explicit: `K = h²/4 - E/2 - ∫ 2 log u`, with `E = groundE_EX01236 h u` in the
  main statement; the main statement quantifies `∃ K` to match "is a spatial constant".
* Nothing is assumed about `D²u` beyond smoothness: derivatives come from `hasDerivAt_angD_EX01217`.
-/

open MeasureTheory
open scoped ContDiff

namespace DGPS.Frontier.EX012

/-- The centered doubled logarithm `v = 2 log u - ∫ 2 log u` (interval integral over `[0,1]`). -/
noncomputable def centeredLog2_EX01221 (u : ℝ → ℝ) : ℝ → ℝ :=
  fun x => 2 * Real.log (u x) - ∫ t in (0:ℝ)..1, 2 * Real.log (u t)

theorem hasDerivAt_centeredLog2_EX01221 {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ x, 0 < u x) (x : ℝ) :
    HasDerivAt (centeredLog2_EX01221 u) (2 * (deriv u x / u x)) x := by
  have hd : HasDerivAt u (deriv u x) x := ((hu.differentiable (by simp)) x).hasDerivAt
  exact ((hd.log (hpos x).ne').const_mul 2).sub_const
    (∫ t in (0:ℝ)..1, 2 * Real.log (u t))

theorem angD_centeredLog2_EX01221 {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ x, 0 < u x) (x : ℝ) :
    angD_EX01217 (centeredLog2_EX01221 u) x = 2 * (angD_EX01217 u x / u x) := by
  simp only [angD_EX01217_apply]
  rw [(hasDerivAt_centeredLog2_EX01221 hu hpos x).deriv]
  ring

theorem angD_angD_centeredLog2_EX01221 {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ x, 0 < u x) (x : ℝ) :
    angD_EX01217 (angD_EX01217 (centeredLog2_EX01221 u)) x
      = 2 * (angD_EX01217 (angD_EX01217 u) x / u x - (angD_EX01217 u x / u x) ^ 2) := by
  have hfun : angD_EX01217 (centeredLog2_EX01221 u) = fun y => 2 * (angD_EX01217 u y / u y) :=
    funext (angD_centeredLog2_EX01221 hu hpos)
  have hd : HasDerivAt u (deriv u x) x := ((hu.differentiable (by simp)) x).hasDerivAt
  have hq : HasDerivAt (fun y => 2 * (angD_EX01217 u y / u y))
      (2 * ((2 * Real.pi * angD_EX01217 (angD_EX01217 u) x * u x
        - angD_EX01217 u x * deriv u x) / u x ^ 2)) x :=
    ((hasDerivAt_angD_EX01217 hu x).div hd (hpos x).ne').const_mul 2
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hdu : deriv u x = (2 * Real.pi) * angD_EX01217 u x := by
    rw [angD_EX01217_apply, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
  have hp : u x ≠ 0 := (hpos x).ne'
  rw [hfun, angD_EX01217_apply (fun y => 2 * (angD_EX01217 u y / u y)) x, hq.deriv, hdu]
  field_simp

theorem ex012_21_logarithmic_derivative_identities_first {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ x, 0 < u x) (x : ℝ) :
    angD_EX01217 u x / u x = angD_EX01217 (centeredLog2_EX01221 u) x / 2 := by
  rw [angD_centeredLog2_EX01221 hu hpos x]
  ring

theorem ex012_21_logarithmic_derivative_identities_second {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u)
    (hpos : ∀ x, 0 < u x) (x : ℝ) :
    angD_EX01217 (angD_EX01217 u) x / u x
      = angD_EX01217 (angD_EX01217 (centeredLog2_EX01221 u)) x / 2
        + (angD_EX01217 (centeredLog2_EX01221 u) x) ^ 2 / 4 := by
  rw [angD_angD_centeredLog2_EX01221 hu hpos x, angD_centeredLog2_EX01221 hu hpos x]
  ring

theorem sin_sq_eq_EX01221 (x : ℝ) :
    Real.sin (2 * Real.pi * x) ^ 2 = (1 - Real.cos (2 * Real.pi * 2 * x)) / 2 := by
  have e : 2 * Real.pi * 2 * x = 2 * (2 * Real.pi * x) := by ring
  rw [e, Real.cos_two_mul]
  have := Real.sin_sq_add_cos_sq (2 * Real.pi * x)
  linarith

theorem ex012_21_logarithmic_derivative_identities_of_euler (h E : ℝ) {u : ℝ → ℝ}
    (hu : ContDiff ℝ ∞ u) (hpos : ∀ x, 0 < u x)
    (hT : ∀ x, euler_T_EX01220 h u x = E * u x) (x : ℝ) :
    angD_EX01217 (angD_EX01217 (centeredLog2_EX01221 u)) x + centeredLog2_EX01221 u x
      + (angD_EX01217 (centeredLog2_EX01221 u) x) ^ 2 / 2
      + (h ^ 2 / 4) * Real.cos (2 * Real.pi * 2 * x)
      = h ^ 2 / 4 - E / 2 - ∫ t in (0:ℝ)..1, 2 * Real.log (u t) := by
  have hp : u x ≠ 0 := (hpos x).ne'
  have hx := hT x
  unfold euler_T_EX01220 at hx
  have hbp : angD_EX01217 (angD_EX01217 u) x / u x
      = (h ^ 2 * Real.sin (2 * Real.pi * x) ^ 2 - 4 * Real.log (u x) - E) / 4 := by
    rw [div_eq_iff hp]
    linear_combination (-1 / 4 : ℝ) * hx
  have hv : centeredLog2_EX01221 u x
      = 2 * Real.log (u x) - ∫ t in (0:ℝ)..1, 2 * Real.log (u t) := rfl
  rw [angD_angD_centeredLog2_EX01221 hu hpos x, angD_centeredLog2_EX01221 hu hpos x, hv]
  linear_combination 2 * hbp + (h ^ 2 / 2) * sin_sq_eq_EX01221 x

/-- Main statement: for an admissible `u` that minimizes `E_h(u²)` among admissible densities
(the hypothesis of EX012.20 part (ii)), the two logarithmic derivative identities hold pointwise,
and `D² v + v + (D v)²/2 + (h²/4) c₂` is a spatial constant. -/
theorem ex012_21_logarithmic_derivative_identities (h : ℝ) {u : ℝ → ℝ}
    (hu : IsAdmSmooth_EX01236 u)
    (hmin : ∀ v : ℝ → ℝ, IsAdmSmooth_EX01236 v → groundE_EX01236 h u ≤ groundE_EX01236 h v) :
    (∀ x, angD_EX01217 u x / u x = angD_EX01217 (centeredLog2_EX01221 u) x / 2) ∧
    (∀ x, angD_EX01217 (angD_EX01217 u) x / u x
        = angD_EX01217 (angD_EX01217 (centeredLog2_EX01221 u)) x / 2
          + (angD_EX01217 (centeredLog2_EX01221 u) x) ^ 2 / 4) ∧
    ∃ K : ℝ, ∀ x, angD_EX01217 (angD_EX01217 (centeredLog2_EX01221 u)) x
        + centeredLog2_EX01221 u x + (angD_EX01217 (centeredLog2_EX01221 u) x) ^ 2 / 2
        + (h ^ 2 / 4) * Real.cos (2 * Real.pi * 2 * x) = K := by
  have hT := (ex012_20_stationarity_implies_pointwise_euler_identity h hu).2 hmin
  refine ⟨fun x => ex012_21_logarithmic_derivative_identities_first hu.smooth hu.pos x,
    fun x => ex012_21_logarithmic_derivative_identities_second hu.smooth hu.pos x, ?_⟩
  exact ⟨_, fun x => ex012_21_logarithmic_derivative_identities_of_euler h
    (groundE_EX01236 h u) hu.smooth hu.pos hT x⟩

end DGPS.Frontier.EX012
