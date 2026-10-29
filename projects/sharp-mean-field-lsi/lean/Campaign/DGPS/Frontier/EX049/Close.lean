import DGPS.Frontier.EX049.T02
import DGPS.Frontier.EX049.T24
import DGPS.Frontier.EX049.T25

/-!
# EX049.CLOSE: Closing unit, declare and prove the frozen sharp defective LSI statement

Task id: EX049.CLOSE. Title: Closing unit: declare and prove
`DGPS.Examples.engineered_three_zone_sharp_defective_lsi_source_blocker`. Node EX049, closing
unit of the reconstructed replacement source (RD-002), verification level V5.

Frozen specification (the Required missing-source interface): there are absolute `C, h0 > 0`
such that every `h ≥ h0` and every angular `H¹` function `v` satisfy
`Ent_{μ_h}(v²) ≤ (2 + C h^(-1/2)) ∫ (v')² dμ_h + C √h ∫ v² dμ_h`, uniformly over all `v`,
including very small entropy.

The Lean statement is authored from that informal text in the campaign's own objects:
`μ_h = circleReference h`, the entropy `entEX04910`, the angular `H¹` predicate `AngularH1` with
its weak derivative predicate `IsAngularWeakDeriv`. It is the existential frozen form of the
produced prerequisite EX049.24 (`ex049_24_frozen_conclusion_explicit_witnesses_exists`), restated
under the frozen name, and the proof is that prerequisite. The binding of the campaign objects to
the source objects is the integrated task EX049.25 (`DGPS.Frontier.EX049` module `T25`).

## Provides

* `DGPS.Examples.engineered_three_zone_sharp_defective_lsi_source_blocker`: the frozen
  statement. There are `C > 0` and `h0 > 0` such that for every real `h ≥ h0`, every `v` with
  `AngularH1 v` and every weak angular derivative `v'` of `v`,
  `Ent_{μ_h}(v²) ≤ (2 + C h^(-1/2)) ∫ (v')² dμ_h + C √h ∫ v² dμ_h`.
* `DGPS.Examples.engineered_three_zone_sharp_defective_lsi_source_blocker_sqrt_inv_EX049CLOSE`:
  the same statement with the coefficient `h^(-1/2)` written `(√h)⁻¹`.
* `DGPS.Examples.engineered_three_zone_sharp_defective_lsi_source_blocker_exists_deriv_EX049CLOSE`:
  the same statement in the form where the weak derivative is existentially chosen, for
  `v` with `AngularH1 v`.
* `DGPS.Examples.energy_eq_of_weakDeriv_EX049CLOSE`: for `h > 0`, two weak derivatives of the same
  function have the same energy `∫ (v')² dμ_h`, so the energy term does not depend on the chosen
  `v'`.
* `DGPS.Examples.integrable_entropy_terms_EX049CLOSE`: for `h > 0` and `AngularH1 v`, the two
  integrands `v²` and `v² log v²` of the entropy of `v²` are integrable against `μ_h`, so the
  entropy in the frozen statement is a genuine difference of finite integrals.

## R5 notes

* Authorship. The specification has no Lean text. The Lean statement is worker-authored. The
  source is a reconstructed replacement record (RD-002), not independently certified, and this
  file carries no stronger status. The frozen name is kept although the proof does not use any
  three-zone localization: the proof is the global square-completion route of EX049.55 combined
  with the entropy reduction of EX049.13, assembled in EX049.24.
* Proof. The closing declaration is the exact statement of
  `DGPS.Frontier.EX049.ex049_24_frozen_conclusion_explicit_witnesses_exists`, so the proof is that
  term. Nothing is weakened: `C` and `h0` are existential and positive and are chosen before `h`
  and `v`; the range is every real `h ≥ h0`; the function is every `v` with `AngularH1 v`. No
  positivity, mass, entropy, boundedness or measurability condition on `v` is added.
* Hypotheses. The only hypotheses under the quantifiers are `h0 ≤ h` (the specification's
  `h ≥ h0`), `AngularH1 v`, and `IsAngularWeakDeriv v v'` (see the weak derivative note). The
  conclusion states `0 < C` and `0 < h0`. Because `h0 > 0`, every `h` in range is positive, which
  is the only positivity that the campaign bindings of EX049.25 need.
* Constants. The statement is existential in `C` and `h0`, as the specification is. The
  prerequisite supplies the explicit values `h0 = 2` and `C = max 1 C0 + log (2 + 8π²) + 9`, where
  `C0` is the EX037 witness selected once inside EX049.13. The explicit values are not part of
  the frozen statement and are not restated here.
* Reading of `h^(-1/2)`. It is the real power `h ^ (-(1/2 : ℝ))`, which equals `(√h)⁻¹` for
  `h > 0` (`DGPS.Frontier.EX049.rpow_neg_half_EX04924`). The `(√h)⁻¹` form is the declaration
  `..._sqrt_inv_EX049CLOSE`. The factor `√h` is `Real.sqrt h`.
* Reading of the entropy of `v²`. It is `entEX04910 (circleReference h) (fun θ => v θ ^ 2)`, that
  is `∫ v² log v² dμ_h - (∫ v² dμ_h) log (∫ v² dμ_h)` with Bochner integrals and `0 log 0 = 0`
  supplied by `Real.log 0 = 0`. The specification defines the entropy for a bounded nonnegative
  function. Here `v²` is nonnegative, and boundedness is not assumed: a function with
  `AngularH1 v` has a continuous representative (EX049.02), so `v²` is bounded `μ_h`-almost
  everywhere. `integrable_entropy_terms_EX049CLOSE` records that both integrands are integrable,
  so no junk value `0` of a non-integrable Bochner integral enters the entropy, and the entropy
  is the one of the specification.
* Identification of the reference measure. `μ_h` is `circleReference h`, which is
  `angHaar.withDensity (fun θ => ENNReal.ofReal (qAng h θ))` with `qAng h = Z_h⁻¹ e^(-Φ_h)`,
  `Φ_h = h U + corr h U` and `U = 1 - cos`. The identification with `q_h m` (normalized Haar
  measure `m`) is proved in EX049.25 for `h > 0`
  (`DGPS.Frontier.EX049.circleReference_eq_EX04925`, and
  `DGPS.Frontier.EX049.isProbabilityMeasure_circleReference_EX04925`). This file uses that binding
  and does not re-prove it; the statement contains no weighted or reweighted reading of the
  measure.
* The weak derivative and `AngularH1 v`. The predicate `AngularH1 v` is
  `∃ g, IsAngularWeakDeriv v g`, so it does not carry a distinguished derivative. The derivative
  `v'` is a separate universally quantified argument constrained only by
  `IsAngularWeakDeriv v v'`; this is the strongest reading, and it implies the reading with an
  existentially chosen derivative (`..._exists_deriv_EX049CLOSE`). The two readings agree because
  angular weak derivatives are unique almost everywhere, hence `μ_h`-almost everywhere, and
  `energy_eq_of_weakDeriv_EX049CLOSE` shows that the energy does not depend on the choice. The
  weak derivative notion is the campaign one: unweighted `L²(angHaar)` with smooth angular test
  functions. The weighted `L²(μ_h)` notion is equivalent for `h > 0` by EX049.25
  (`DGPS.Frontier.EX049.isAngularWeakDerivW_iff_EX04925`).
* Finiteness of the energy and the mass. For `h > 0` and a weak derivative `v'` of `v`, the
  functions `v` and `v'` are in `L²(angHaar)`, hence in `L²(μ_h)` (EX049.25), so both integrals
  `∫ (v')² dμ_h` and `∫ v² dμ_h` are finite genuine integrals.
* Real valued. The functions `v` and `v'` are real valued, as in the campaign; there is no complex
  domain.
* Not used. The statement does not mention `groundPot`, `driftB` or the EX037 witness. They enter
  only through the proof of the prerequisites.
-/

namespace DGPS.Examples

open MeasureTheory
open DGPS.Circle.AngularNormalization DGPS.Examples.EngineeredGroundState DGPS.Frontier.EX049

/-- For `h > 0`, two weak angular derivatives of the same function have the same energy against
`μ_h = circleReference h`: they agree `angHaar`-almost everywhere, hence `μ_h`-almost
everywhere. -/
theorem energy_eq_of_weakDeriv_EX049CLOSE (h : ℝ) (hh : 0 < h) {v g g' : AngCircle → ℝ}
    (hg : IsAngularWeakDeriv v g) (hg' : IsAngularWeakDeriv v g') :
    ∫ θ, g θ ^ 2 ∂circleReference h = ∫ θ, g' θ ^ 2 ∂circleReference h := by
  have hae : g =ᵐ[circleReference h] g' :=
    (circleReference_ae_iff_EX04925 h hh g g').1 (angularWeakDeriv_ae_eq_EX04925 hg hg')
  refine integral_congr_ae ?_
  filter_upwards [hae] with θ hθ
  rw [hθ]

/-- For `h > 0` and `AngularH1 v`, the integrands `v²` and `v² log v²` of the entropy of `v²` are
integrable against `μ_h = circleReference h`. The proof replaces `v` by its continuous
representative from EX049.02, which agrees with `v` `angHaar`-almost everywhere and hence
`μ_h`-almost everywhere; continuous functions on the compact circle are integrable for the
probability measure `μ_h`. -/
theorem integrable_entropy_terms_EX049CLOSE (h : ℝ) (hh : 0 < h) {v : AngCircle → ℝ}
    (hv : AngularH1 v) :
    Integrable (fun θ => v θ ^ 2) (circleReference h) ∧
      Integrable (fun θ => v θ ^ 2 * Real.log (v θ ^ 2)) (circleReference h) := by
  have : IsProbabilityMeasure (circleReference h) :=
    isProbabilityMeasure_circleReference_EX04925 h hh
  obtain ⟨w, hwc, hwv, -⟩ := ex049_02_angular_h1_has_absolutely_continuous_representative v hv
  have hae : w =ᵐ[circleReference h] v := (circleReference_ae_iff_EX04925 h hh w v).1 hwv
  have hae2 : (fun θ => w θ ^ 2) =ᵐ[circleReference h] fun θ => v θ ^ 2 := by
    filter_upwards [hae] with θ hθ
    rw [hθ]
  have hae3 : (fun θ => w θ ^ 2 * Real.log (w θ ^ 2)) =ᵐ[circleReference h]
      fun θ => v θ ^ 2 * Real.log (v θ ^ 2) := by
    filter_upwards [hae] with θ hθ
    rw [hθ]
  refine ⟨?_, ?_⟩
  · exact ((hwc.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).congr hae2
  · exact ((Real.continuous_mul_log.comp (hwc.pow 2)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).congr hae3

/-- **EX049.CLOSE (frozen statement).** There are `C > 0` and `h0 > 0` such that for every real
`h ≥ h0`, every angular `H¹` function `v` and every weak angular derivative `v'` of `v`,
`Ent_{μ_h}(v²) ≤ (2 + C h^(-1/2)) ∫ (v')² dμ_h + C √h ∫ v² dμ_h`, where `μ_h` is
`circleReference h` and the entropy is `entEX04910`. -/
theorem engineered_three_zone_sharp_defective_lsi_source_blocker :
    ∃ C h0 : ℝ, 0 < C ∧ 0 < h0 ∧
      ∀ h : ℝ, h0 ≤ h → ∀ v : AngCircle → ℝ, AngularH1 v →
        ∀ v' : AngCircle → ℝ, IsAngularWeakDeriv v v' →
          entEX04910 (circleReference h) (fun θ => v θ ^ 2) ≤
            (2 + C * h ^ (-(1 / 2 : ℝ))) * (∫ θ, v' θ ^ 2 ∂circleReference h) +
              C * Real.sqrt h * (∫ θ, v θ ^ 2 ∂circleReference h) :=
  ex049_24_frozen_conclusion_explicit_witnesses_exists

/-- The frozen statement with the coefficient `h^(-1/2)` written as `(√h)⁻¹`. -/
theorem engineered_three_zone_sharp_defective_lsi_source_blocker_sqrt_inv_EX049CLOSE :
    ∃ C h0 : ℝ, 0 < C ∧ 0 < h0 ∧
      ∀ h : ℝ, h0 ≤ h → ∀ v : AngCircle → ℝ, AngularH1 v →
        ∀ v' : AngCircle → ℝ, IsAngularWeakDeriv v v' →
          entEX04910 (circleReference h) (fun θ => v θ ^ 2) ≤
            (2 + C * (Real.sqrt h)⁻¹) * (∫ θ, v' θ ^ 2 ∂circleReference h) +
              C * Real.sqrt h * (∫ θ, v θ ^ 2 ∂circleReference h) := by
  obtain ⟨C, h0, hC, hh0, hmain⟩ := engineered_three_zone_sharp_defective_lsi_source_blocker
  refine ⟨C, h0, hC, hh0, fun h hh v hv v' hv' => ?_⟩
  have hbound := hmain h hh v hv v' hv'
  rwa [rpow_neg_half_EX04924 h (lt_of_lt_of_le hh0 hh)] at hbound

/-- The frozen statement with the weak derivative chosen existentially: for every `v` with
`AngularH1 v` some weak angular derivative `v'` of `v` satisfies the bound. -/
theorem engineered_three_zone_sharp_defective_lsi_source_blocker_exists_deriv_EX049CLOSE :
    ∃ C h0 : ℝ, 0 < C ∧ 0 < h0 ∧
      ∀ h : ℝ, h0 ≤ h → ∀ v : AngCircle → ℝ, AngularH1 v →
        ∃ v' : AngCircle → ℝ, IsAngularWeakDeriv v v' ∧
          entEX04910 (circleReference h) (fun θ => v θ ^ 2) ≤
            (2 + C * h ^ (-(1 / 2 : ℝ))) * (∫ θ, v' θ ^ 2 ∂circleReference h) +
              C * Real.sqrt h * (∫ θ, v θ ^ 2 ∂circleReference h) := by
  obtain ⟨C, h0, hC, hh0, hmain⟩ := engineered_three_zone_sharp_defective_lsi_source_blocker
  refine ⟨C, h0, hC, hh0, fun h hh v hv => ?_⟩
  obtain ⟨g, hg⟩ := hv
  exact ⟨g, hg, hmain h hh v ⟨g, hg⟩ g hg⟩

end DGPS.Examples
