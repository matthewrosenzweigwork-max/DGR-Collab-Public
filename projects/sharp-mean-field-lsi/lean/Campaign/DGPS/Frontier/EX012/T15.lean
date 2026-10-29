import DGPS.Frontier.EX012.T14

/-!
# EX012.15: Bundle the captured logarithm

Task id: EX012.15 (node EX012, leaf formalization).
Title: Bundle the captured logarithm.

For every `ε > 0`, let `h1` be the threshold supplied by EX011 (its uniform capture clause for the
fixed Hölder exponent `α`). For every `h ∈ (0, h1)` and every minimizing `ρ` of the ground
functional `ex010_ground h`, EX011 gives a positive smooth representative `r` of `ρ.density`. The
centered logarithm `s ↦ log (r (torusLift fun _ => s)) - ℓ`, where `ℓ = ∫ log r`, is bundled as an
element `w : PH α 2` with `w.val` equal to it and `‖w‖ ≤ ε`. The same `w` has mean zero over one
period, `∫ t in 0..1, w.val t = 0`. The torus mean `∫ (log r - ℓ) = 0` holds as in EX012.14.

## Provides

* `DGPS.Frontier.EX012.ex012_15_bundle_captured_logarithm (α : ℝ) [HolderExponent α]`:
  the uniform assertion `∀ ε > 0, ∃ h1 > 0, ∀ h ∈ (0, h1), ∀ minimizing ρ, ∃ r, ...`. The
  representative `r` is positive, smooth, and `ρ.density =ᵐ[haar 1] r`; it is the only smooth
  representative of `ρ.density`; the torus mean of `log r - ℓ` is zero; and there is
  `w : PH α 2` with `w.val` the centered logarithm of `r`, `‖w‖ ≤ ε`, and interval mean zero.

## R5 notes

* Hölder exponent: `α : ℝ` with `[HolderExponent α]` is a parameter of the main theorem. The
  uniform displayed assertion does not name `α`, but `PH α 2` does, and EX011 is stated for each
  such `α`. `[HolderExponent α]` is the campaign form of the preamble's `Fix 0 < α < 1` (T25, T26
  and T29 use the same instance); it is not an added hypothesis. Its `pos` and `lt_one` fields
  supply EX011's `0 < α` and `α < 1`.
* Threshold: `h1` is EX011's threshold. Its extra bound `h1 ≤ h0` is not repeated, because nothing
  downstream needs it.
* Minimizers: the hypothesis `∀ ρ', ex010_ground h ρ ≤ ex010_ground h ρ'` is the one used by EX011.
* Captured logarithm: read as a function on `ℝ`, `s ↦ log (r (torusLift fun _ => s)) - ℓ`, which
  is the form EX011 uses. The bundled element is `PH.mk v hph`, where `hph` is EX011's `IsPH`
  proof, so `w.val = v` holds by `rfl`.
* Norm: `‖w‖ = phNorm α 2 w.val` is `PH.norm_def` (by `rfl`). This is the definition-level equality
  the brief asks for. No regularity estimate is needed.
* Mean zero is read in two places. The torus Haar mean `∫ (log r - ℓ) ∂haar 1 = 0` is EX012.14's
  identity. The interval mean `∫ t in 0..1, w.val t = 0` is for the PH function and is proved from
  `DGPS.integral_haar_one` and continuity of `log r`.
* Uniqueness conjunct (added, not in the specification's list): `∀ r', IsSmoothPeriodic r' →
  ρ.density =ᵐ[haar 1] r' → r' = r`. It makes "the same representative" literal, and it is
  EX012.13's `ex012_13_transfer_smooth_representative_mass_unique`. It adds a conclusion and weakens
  nothing. It shows that `w` does not depend on which smooth representative EX011 chose.
* The `∃ r` does not hide a choice of representative: any other smooth representative with the
  same density equals `r` everywhere, by the uniqueness conjunct.
* No limiting argument is done here. The quantifier order is that of EX011's uniform clause.
-/

open MeasureTheory
open DGPS.Circle.VonMisesSmallField
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.EX012

theorem interval_mean_zero_EX01215 {r : Torus 1 → ℝ} (hr : ∀ x, 0 < r x)
    (hsm : IsSmoothPeriodic r) :
    ∫ t in (0 : ℝ)..1, (Real.log (r (torusLift fun _ => t)) - ∫ y, Real.log (r y) ∂haar 1) = 0 := by
  have hrt : Continuous fun t : ℝ => r (torusLift fun _ => t) :=
    (hsm.comp (contDiff_pi.2 fun _ => contDiff_id)).continuous
  have hlog : Continuous fun t : ℝ => Real.log (r (torusLift fun _ => t)) :=
    hrt.log fun t => (hr _).ne'
  have hI : ∫ y, Real.log (r y) ∂haar 1 =
      ∫ t in (0 : ℝ)..1, Real.log (r (torusLift fun _ => t)) :=
    DGPS.integral_haar_one (fun y => Real.log (r y)) (continuous_log_EX01214 hr hsm)
  rw [intervalIntegral.integral_sub (hlog.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1), intervalIntegral.integral_const, ← hI]
  simp

theorem ex012_15_bundle_captured_logarithm (α : ℝ) [HolderExponent α] :
    ∀ ε : ℝ, 0 < ε → ∃ h1 : ℝ, 0 < h1 ∧
      ∀ h : ℝ, 0 < h → h < h1 → ∀ ρ : AbsoluteDensity 1,
        (∀ ρ' : AbsoluteDensity 1, ex010_ground h ρ ≤ ex010_ground h ρ') →
        ∃ r : Torus 1 → ℝ, (∀ x, 0 < r x) ∧ IsSmoothPeriodic r ∧ ρ.density =ᵐ[haar 1] r ∧
          (∀ r' : Torus 1 → ℝ, IsSmoothPeriodic r' → ρ.density =ᵐ[haar 1] r' → r' = r) ∧
          (∫ x, (Real.log (r x) - ∫ y, Real.log (r y) ∂haar 1) ∂haar 1 = 0) ∧
          ∃ w : PH α 2,
            w.val = (fun s => Real.log (r (torusLift fun _ => s)) - ∫ y, Real.log (r y) ∂haar 1) ∧
            ‖w‖ ≤ ε ∧ (∫ t in (0 : ℝ)..1, w.val t) = 0 := by
  intro ε hε
  obtain ⟨_, -, -, hcap⟩ := DGPS.Examples.uniform_haar_capture_of_ground_minimizers
  obtain ⟨h1, hh1, -, hu⟩ :=
    hcap α (HolderExponent.pos (α := α)) (HolderExponent.lt_one (α := α)) ε hε
  refine ⟨h1, hh1, fun h hpos hlt ρ hmin => ?_⟩
  obtain ⟨r, hr, hsm, hρ, hph, hnorm⟩ := hu h hpos hlt ρ hmin
  refine ⟨r, hr, hsm, hρ,
    fun r' hsm' hρ' => ex012_13_transfer_smooth_representative_mass_unique hsm' hsm hρ' hρ,
    ex012_14_normalized_centered_logarithm_mean_zero hr hsm, PH.mk _ hph, rfl, ?_,
    interval_mean_zero_EX01215 hr hsm⟩
  rw [PH.norm_def]
  exact hnorm

end DGPS.Frontier.EX012
