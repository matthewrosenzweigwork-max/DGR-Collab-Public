import DGPS.Frontier.EX049.T02
import DGPS.Frontier.EX049.T09
import DGPS.Frontier.EX049.T10
import DGPS.Frontier.EX049.T25

/-!
# EX049.12: Exact entropy conjugation

For every real `h ≥ 2` and every real angular `H¹` function `v`, put `w = v √q_h`
(`groundStateConj h v`), `m = angHaar` and `μ_h = circleReference h`.  Then

  `Ent_{μ_h}(v²) = Ent_m(w²) + ∫ Φ_h w² dm + (log Z_h) M_h(v)`,

where `Ent_ν(f) = ∫ f log f dν − (∫ f dν) log (∫ f dν)` is `entEX04910` (EX049.10),
`Φ_h = h U + corr h U` with `U = Uang`, and `M_h(v) = ∫ v² dμ_h`.

The proof is an exact change of density.  The two masses agree by the EX049.09 mass identity.
On the set where `v ≠ 0`, `log v² = log w² + log Z_h + Φ_h`; on the zero set both sides vanish.
Integrability is supplied by the continuous representative of `v` from EX049.02, which agrees
with `v` almost everywhere under both `m` and `μ_h`, and the identity is transferred by
almost-everywhere congruence.

## Provides

* `DGPS.Frontier.EX049.ex049_12_exact_entropy_conjugation`: the frozen identity above, for every
  `h ≥ 2` and every `v` with `AngularH1 v`.
* `DGPS.Frontier.EX049.core_EX04912`: the same identity for continuous `v` and `0 < h`.
* Helpers, each suffixed `_EX04912`: `sq_conj_EX04912` (the conjugate squared is `v² q_h`),
  `log_qAng_EX04912` (the log-density relation), `pointwise_EX04912` (the scalar identity),
  `entropy_congr_EX04912` (entropy depends only on the almost-everywhere class),
  `gsc_congr_EX04912` (the conjugate squared depends only on the almost-everywhere class),
  `integrable_cont_EX04912` (continuous functions are `m`-integrable).

## R5 notes

* Hypotheses: `hh : 2 ≤ h` is the frozen domain; the proof uses only `0 < h`.  `hv : AngularH1 v`
  is the angular `H¹` domain.  No hypothesis is added.
* `Φ_h` has no Lean declaration in the campaign.  It is written inline as
  `h * Uang θ + corr h (Uang θ)`, which matches `logq h θ = -(h * Uang θ) - corr h (Uang θ)`,
  that is `log q_h = -log Z_h - Φ_h`.
* `log Z_h` is `Real.log (Zh h)`; `Zh h > 0` is used to make the logarithm of `q_h` well defined.
* `M_h(v)` is `∫ θ, v θ ^ 2 ∂circleReference h`; `∫ Φ_h w² dm` is `∫ θ, Φ θ * w θ ^ 2 ∂angHaar`.
* `Ent` is `entEX04910`, the real-valued definition of EX049.10.  The convention `0 log 0 = 0`
  is `Real.log 0 = 0`.
* `w = v √q_h` is `groundStateConj h v`, the function `θ ↦ v θ * √(qAng h θ)`.
* Integrability is not assumed.  The Lean integrals are Bochner integrals, which are zero on a
  non-integrable integrand; the proof establishes integrability for the continuous representative,
  and the almost-everywhere transfer carries the identity to every `v` with `AngularH1 v`.
* Entropy is read on the probability measures `μ_h` and `m`; the mass identity of EX049.09 gives
  the equality of the two `M` terms, so the `M log M` terms cancel.

-/

open MeasureTheory Filter Real
open DGPS.Circle.AngularNormalization DGPS.Examples.EngineeredRankOne
  DGPS.Examples.EngineeredGroundState

namespace DGPS.Frontier.EX049

/-! ### Pointwise algebra -/

/-- The conjugate squared is `v² q_h`. -/
lemma sq_conj_EX04912 (h : ℝ) (hh : 0 < h) (v : AngCircle → ℝ) (θ : AngCircle) :
    groundStateConj h v θ ^ 2 = v θ ^ 2 * qAng h θ := by
  show (v θ * Real.sqrt (qAng h θ)) ^ 2 = v θ ^ 2 * qAng h θ
  rw [mul_pow, Real.sq_sqrt (qAng_pos h hh θ).le]

/-- The log-density relation `log q_h = -log Z_h - Φ_h` with `Φ_h = h U + corr h U`. -/
lemma log_qAng_EX04912 (h : ℝ) (hh : 0 < h) (θ : AngCircle) :
    Real.log (qAng h θ) = -Real.log (Zh h) - (h * Uang θ + corr h (Uang θ)) := by
  have hZ : (Zh h)⁻¹ ≠ 0 := (inv_pos.2 (Zh_pos h hh)).ne'
  unfold qAng
  rw [Real.log_mul hZ (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
  unfold logq
  ring

/-- The scalar identity behind the entropy conjugation: with `x log x · q = x q log (x q) +
(log Z) x q + Φ x q` whenever `log q = -log Z - Φ`. -/
lemma pointwise_EX04912 (x q Z Φ : ℝ) (hq : 0 < q) (hL : Real.log q = -Real.log Z - Φ) :
    x * Real.log x * q = x * q * Real.log (x * q) + Real.log Z * (x * q) + Φ * (x * q) := by
  rcases eq_or_ne x 0 with hx | hx
  · simp [hx]
  · rw [Real.log_mul hx hq.ne', hL]
    ring

/-! ### Almost-everywhere transfer and integrability -/

/-- Entropy depends only on the almost-everywhere class of the function. -/
lemma entropy_congr_EX04912 {ν : Measure AngCircle} {f g : AngCircle → ℝ} (hfg : f =ᵐ[ν] g) :
    entEX04910 ν f = entEX04910 ν g := by
  have h1 : (fun x => f x * Real.log (f x)) =ᵐ[ν] (fun x => g x * Real.log (g x)) := by
    filter_upwards [hfg] with x hx
    simp only [hx]
  unfold entEX04910
  rw [integral_congr_ae h1, integral_congr_ae hfg]

/-- The squared conjugate depends only on the almost-everywhere class of `v`. -/
lemma gsc_congr_EX04912 (h : ℝ) {v u : AngCircle → ℝ} (hvu : v =ᵐ[angHaar] u) :
    (fun θ => groundStateConj h v θ ^ 2) =ᵐ[angHaar] (fun θ => groundStateConj h u θ ^ 2) := by
  filter_upwards [hvu] with θ hθ
  show (v θ * Real.sqrt (qAng h θ)) ^ 2 = (u θ * Real.sqrt (qAng h θ)) ^ 2
  rw [hθ]

/-- A continuous function on the compact circle is integrable for the Haar probability. -/
lemma integrable_cont_EX04912 {f : AngCircle → ℝ} (hf : Continuous f) :
    Integrable f angHaar :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ### The continuous case -/

/-- The exact entropy conjugation for continuous `v` and `0 < h`. -/
lemma core_EX04912 (h : ℝ) (hh : 0 < h) (v : AngCircle → ℝ) (hc : Continuous v) :
    entEX04910 (circleReference h) (fun θ => v θ ^ 2) =
      entEX04910 angHaar (fun θ => groundStateConj h v θ ^ 2)
        + (∫ θ, (h * Uang θ + corr h (Uang θ)) * groundStateConj h v θ ^ 2 ∂angHaar)
        + Real.log (Zh h) * (∫ θ, v θ ^ 2 ∂circleReference h) := by
  have hwc : Continuous (groundStateConj h v) := hc.mul (continuous_qAng h hh).sqrt
  have hW : Continuous (fun θ => groundStateConj h v θ ^ 2) := hwc.pow 2
  have hΦ : Continuous (fun θ => h * Uang θ + corr h (Uang θ)) :=
    (continuous_const.mul continuous_Uang).add (continuous_corrU h hh)
  have hpt : ∀ θ, v θ ^ 2 * Real.log (v θ ^ 2) * qAng h θ =
      groundStateConj h v θ ^ 2 * Real.log (groundStateConj h v θ ^ 2)
        + Real.log (Zh h) * groundStateConj h v θ ^ 2
        + (h * Uang θ + corr h (Uang θ)) * groundStateConj h v θ ^ 2 := by
    intro θ
    rw [sq_conj_EX04912 h hh v θ]
    exact pointwise_EX04912 (v θ ^ 2) (qAng h θ) (Zh h) (h * Uang θ + corr h (Uang θ))
      (qAng_pos h hh θ) (log_qAng_EX04912 h hh θ)
  have hA : Continuous (fun θ => groundStateConj h v θ ^ 2 * Real.log (groundStateConj h v θ ^ 2)) :=
    Real.continuous_mul_log.comp hW
  have hB : Continuous (fun θ => Real.log (Zh h) * groundStateConj h v θ ^ 2) :=
    continuous_const.mul hW
  have hC : Continuous (fun θ => (h * Uang θ + corr h (Uang θ)) * groundStateConj h v θ ^ 2) :=
    hΦ.mul hW
  have hint : ∫ θ, v θ ^ 2 * Real.log (v θ ^ 2) * qAng h θ ∂angHaar =
      ∫ θ, (groundStateConj h v θ ^ 2 * Real.log (groundStateConj h v θ ^ 2)
        + Real.log (Zh h) * groundStateConj h v θ ^ 2
        + (h * Uang θ + corr h (Uang θ)) * groundStateConj h v θ ^ 2) ∂angHaar :=
    integral_congr_ae (Eventually.of_forall hpt)
  have iA : Integrable (fun θ => groundStateConj h v θ ^ 2 * Real.log (groundStateConj h v θ ^ 2))
      angHaar := integrable_cont_EX04912 hA
  have iB : Integrable (fun θ => Real.log (Zh h) * groundStateConj h v θ ^ 2) angHaar :=
    integrable_cont_EX04912 hB
  have iC : Integrable (fun θ => (h * Uang θ + corr h (Uang θ)) * groundStateConj h v θ ^ 2)
      angHaar := integrable_cont_EX04912 hC
  have iAB : Integrable (fun θ => groundStateConj h v θ ^ 2 * Real.log (groundStateConj h v θ ^ 2)
      + Real.log (Zh h) * groundStateConj h v θ ^ 2) angHaar := iA.add iB
  have hsplit : ∫ θ, v θ ^ 2 * Real.log (v θ ^ 2) * qAng h θ ∂angHaar =
      (∫ θ, groundStateConj h v θ ^ 2 * Real.log (groundStateConj h v θ ^ 2) ∂angHaar)
        + Real.log (Zh h) * (∫ θ, groundStateConj h v θ ^ 2 ∂angHaar)
        + (∫ θ, (h * Uang θ + corr h (Uang θ)) * groundStateConj h v θ ^ 2 ∂angHaar) := by
    rw [hint, integral_add iAB iC, integral_add iA iB, integral_const_mul]
  have hM : ∫ θ, groundStateConj h v θ ^ 2 ∂angHaar = ∫ θ, v θ ^ 2 ∂circleReference h :=
    mass_EX04909 h hh v
  have hL1 : ∫ θ, v θ ^ 2 * Real.log (v θ ^ 2) ∂circleReference h =
      ∫ θ, v θ ^ 2 * Real.log (v θ ^ 2) * qAng h θ ∂angHaar :=
    integral_circleReference h hh (fun θ => v θ ^ 2 * Real.log (v θ ^ 2))
  have eL : entEX04910 (circleReference h) (fun θ => v θ ^ 2) =
      (∫ θ, v θ ^ 2 * Real.log (v θ ^ 2) ∂circleReference h)
        - (∫ θ, v θ ^ 2 ∂circleReference h) * Real.log (∫ θ, v θ ^ 2 ∂circleReference h) := rfl
  have eR : entEX04910 angHaar (fun θ => groundStateConj h v θ ^ 2) =
      (∫ θ, groundStateConj h v θ ^ 2 * Real.log (groundStateConj h v θ ^ 2) ∂angHaar)
        - (∫ θ, groundStateConj h v θ ^ 2 ∂angHaar)
          * Real.log (∫ θ, groundStateConj h v θ ^ 2 ∂angHaar) := rfl
  rw [eL, eR, hL1, hsplit, hM]
  ring

/-! ### The main theorem -/

/-- EX049.12: exact entropy conjugation.  For every `h ≥ 2` and every angular `H¹` function `v`,
with `w = v √q_h`,
`Ent_{μ_h}(v²) = Ent_m(w²) + ∫ Φ_h w² dm + (log Z_h) M_h(v)`. -/
theorem ex049_12_exact_entropy_conjugation (h : ℝ) (hh : 2 ≤ h)
    (v : AngCircle → ℝ) (hv : AngularH1 v) :
    entEX04910 (circleReference h) (fun θ => v θ ^ 2) =
      entEX04910 angHaar (fun θ => groundStateConj h v θ ^ 2)
        + (∫ θ, (h * Uang θ + corr h (Uang θ)) * groundStateConj h v θ ^ 2 ∂angHaar)
        + Real.log (Zh h) * (∫ θ, v θ ^ 2 ∂circleReference h) := by
  have hh0 : 0 < h := by linarith
  obtain ⟨v₀, hc, hae, -⟩ := ex049_02_angular_h1_has_absolutely_continuous_representative v hv
  have hμ : v₀ =ᵐ[circleReference h] v := (circleReference_ae_iff_EX04925 h hh0 v₀ v).1 hae
  have hsq : (fun θ => v θ ^ 2) =ᵐ[circleReference h] (fun θ => v₀ θ ^ 2) := by
    filter_upwards [hμ.symm] with θ hθ
    show v θ ^ 2 = v₀ θ ^ 2
    rw [hθ]
  have hL := entropy_congr_EX04912 hsq
  have hW := entropy_congr_EX04912 (gsc_congr_EX04912 h hae.symm)
  have hΦ : (∫ θ, (h * Uang θ + corr h (Uang θ)) * groundStateConj h v θ ^ 2 ∂angHaar) =
      ∫ θ, (h * Uang θ + corr h (Uang θ)) * groundStateConj h v₀ θ ^ 2 ∂angHaar := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with θ hθ
    show (h * Uang θ + corr h (Uang θ)) * (v θ * Real.sqrt (qAng h θ)) ^ 2 =
      (h * Uang θ + corr h (Uang θ)) * (v₀ θ * Real.sqrt (qAng h θ)) ^ 2
    rw [hθ]
  have hM : (∫ θ, v θ ^ 2 ∂circleReference h) = ∫ θ, v₀ θ ^ 2 ∂circleReference h :=
    integral_congr_ae hsq
  rw [hL, hW, hΦ, hM]
  exact core_EX04912 h hh0 v₀ hc

end DGPS.Frontier.EX049
