import DGPS.Frontier.EX049.T41
import DGPS.Frontier.EX049.T42

/-!
# EX049.08: Fixed-h positive density and full weighted domain

Task id and title: EX049.08, "Fixed-h positive density and full weighted domain" (node EX049,
frontier unit, leaf formalization, prerequisites EX049.41 and EX049.42).  For a real `h ≥ 2`
put `q_h = qAng h` on the angular circle.  Then `q_h` is smooth, periodic and bounded above and
below by positive constants; multiplication by `√q_h` and by `1 / √q_h` preserves the angular
`H¹` class, and the two multiplications are mutually inverse; and the weighted domain for
`μ_h = q_h m` agrees with the Haar angular `H¹` domain for the same weak derivative.

## Provides
* `DGPS.Frontier.EX049.ex049_08_fixed_h_positive_density_full_weighted` : the main statement, for
  `2 ≤ h`, a conjunction of four blocks: the density block (smoothness, periodicity and positive
  bounds of `q_h`), the two multipliers preserve `AngularH1`, the two multiplications are inverse
  identities, and the weighted and Haar domains agree (for pairs and for domains).
* `DGPS.Frontier.EX049.weighted_iff_EX04908` : for every `h`, the weighted weak-pair relation of
  EX049.25 for `μ_h` is the weighted relation of EX049.42 for the density `qAng h`.

## R5 notes
* The only hypothesis is `2 ≤ h`, the specification's "for each `h ≥ 2`".  No hypothesis is added
  and none of the specification's hypotheses is dropped.  Positivity of `q_h` is not assumed; it
  is derived from the quantified bounds of EX049.41.
* "Smooth" is read as `C^∞` of the real lift `t ↦ qAng h t` on `ℝ`, as in EX049.41.  "Periodic" is
  read as `Function.Periodic` of the same lift with period `2π`.  For a function on the circle the
  periodicity is automatic; it is stated for the lift because the lift is the smooth object.
* "Bounded above and below by positive constants" is read as
  `∃ c C, 0 < c ∧ ∀ θ, c ≤ q_h θ ∧ q_h θ ≤ C`.  The proof uses the explicit witnesses
  `exp (-(2h + 6√h))` and `exp (2h + 6√h)` of EX049.41, which are not part of the statement.
* The weighted domain is the EX049.25 structure `IsAngularWeakDerivW_EX04925 h`: `u` and `g` lie
  in `L²(μ_h)` with `μ_h = circleReference h = q_h · angHaar`, and the pairing is the unweighted
  pairing against `angHaar` with smooth circle test functions.  This is the convention of the Haar
  domain `IsAngularWeakDeriv`.  A drift-corrected weak derivative is neither used nor claimed.
* The Haar domain is `AngularH1`: `u` belongs to it when some `g` is an angular weak derivative in
  `L²(angHaar)`.  The domain agreement is stated twice.  The first clause compares the weak-pair
  relations `(u, g)` for every `u` and `g`, so zeros and sign-changing functions are included and
  no positivity is assumed.  The second clause compares the domains `∃ g, …`.
* The multipliers are `θ ↦ √(q_h θ)` and `θ ↦ 1 / √(q_h θ)`.  "Preserve angular `H¹`" is read as
  `AngularH1 v → AngularH1 (multiplier · v)`.  The weak derivative of a product is not part of the
  specification and is not stated here.
* "Inverse maps" is stated as the two identities of functions
  `(1 / √q_h)(√q_h · v) = v` and `√q_h · ((1 / √q_h) · v) = v` for every `v : AngCircle → ℝ`.
  This is stronger than the restriction to `AngularH1`, which is the literal reading, and it
  implies that restriction.
* All functions are real valued, as in the campaign.  The constants may depend on the fixed `h`.
  No constant uniform in `h` is stated or used, as the specification requires.
* The proof uses EX049.41 for the density block and EX049.42 for the multipliers and for the domain
  agreement.  The conversion from the EX049.25 weighted structure to the EX049.42 structure is
  `weighted_iff_EX04908`, which holds by unfolding `circleReference`.
-/

open scoped ContDiff
open DGPS.Circle.AngularNormalization DGPS.Examples.EngineeredRankOne

namespace DGPS.Frontier.EX049

/-- For every `h`, the weighted weak-pair relation of EX049.25 for `μ_h = q_h m` (`circleReference h`)
is the weighted relation of EX049.42 for the density `qAng h`.  The two structures have the same
three fields, and `circleReference h` unfolds to the `withDensity` measure used by EX049.42. -/
theorem weighted_iff_EX04908 (h : ℝ) (u g : AngCircle → ℝ) :
    IsAngularWeakDerivW_EX04925 h u g ↔ IsAngularWeakDerivW_EX04942 (qAng h) u g :=
  ⟨fun H => ⟨H.memLp, H.memLp_deriv, H.ibp⟩, fun H => ⟨H.memLp, H.memLp_deriv, H.ibp⟩⟩

/-- EX049.08: for a real `h ≥ 2`, the density `q_h` is smooth, periodic and bounded above and
below by positive constants; multiplication by `√q_h` and by `1 / √q_h` preserves the angular `H¹`
class; the two multiplications are inverse to each other; and the weighted domain for `μ_h = q_h m`
agrees with the Haar angular `H¹` domain, both for weak-pair relations and for domains. -/
theorem ex049_08_fixed_h_positive_density_full_weighted (h : ℝ) (hh : 2 ≤ h) :
    (ContDiff ℝ ∞ (fun t : ℝ => qAng h (t : AngCircle)) ∧
      Function.Periodic (fun t : ℝ => qAng h (t : AngCircle)) (2 * Real.pi) ∧
      ∃ c C : ℝ, 0 < c ∧ ∀ θ : AngCircle, c ≤ qAng h θ ∧ qAng h θ ≤ C) ∧
    (∀ v : AngCircle → ℝ, AngularH1 v → AngularH1 (fun θ => Real.sqrt (qAng h θ) * v θ)) ∧
    (∀ v : AngCircle → ℝ, AngularH1 v → AngularH1 (fun θ => 1 / Real.sqrt (qAng h θ) * v θ)) ∧
    (∀ v : AngCircle → ℝ,
      (fun θ => 1 / Real.sqrt (qAng h θ) * (Real.sqrt (qAng h θ) * v θ)) = v) ∧
    (∀ v : AngCircle → ℝ,
      (fun θ => Real.sqrt (qAng h θ) * (1 / Real.sqrt (qAng h θ) * v θ)) = v) ∧
    (∀ u g : AngCircle → ℝ, IsAngularWeakDerivW_EX04925 h u g ↔ IsAngularWeakDeriv u g) ∧
    (∀ u : AngCircle → ℝ, (∃ g, IsAngularWeakDerivW_EX04925 h u g) ↔ AngularH1 u) := by
  obtain ⟨-, -, hq, hD, -, -⟩ := ex049_41_quantified_density_multiplier_bounds h hh
  obtain ⟨hsmooth, hper, -⟩ := hD
  have hc : 0 < Real.exp (-(2 * h + 6 * Real.sqrt h)) := Real.exp_pos _
  have hQ1 : ContDiff ℝ 1 (fun s : ℝ => qAng h (s : AngCircle)) :=
    hsmooth.of_le (by exact_mod_cast le_top)
  obtain ⟨-, -, hW, hDom, -, -, hSq, hInv, hI1, hI2⟩ :=
    ex049_42_weighted_h1_equivalence_inverse_multipliers (qAng h) hQ1
      (Real.exp (-(2 * h + 6 * Real.sqrt h))) (Real.exp (2 * h + 6 * Real.sqrt h)) hc
      (fun θ => (hq θ).1) (fun θ => (hq θ).2)
  exact ⟨⟨hsmooth, hper, Real.exp (-(2 * h + 6 * Real.sqrt h)),
      Real.exp (2 * h + 6 * Real.sqrt h), hc, fun θ => hq θ⟩,
    hSq, hInv, hI1, hI2,
    fun u g => (weighted_iff_EX04908 h u g).trans (hW u g),
    fun u => (exists_congr fun g => weighted_iff_EX04908 h u g).trans (hDom u)⟩

end DGPS.Frontier.EX049
