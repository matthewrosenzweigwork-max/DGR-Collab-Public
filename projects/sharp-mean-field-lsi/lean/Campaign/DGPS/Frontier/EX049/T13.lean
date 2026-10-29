import DGPS.Frontier.EX049.T09
import DGPS.Frontier.EX049.T11
import DGPS.Frontier.EX049.T12
import DGPS.Frontier.EX049.T41

/-!
# EX049.13: Global entropy reduction for every h at least two

Task id: EX049.13. Title: Global entropy reduction for every h at least two.

For every real `h ≥ 2`, every angular `H^1` function `v` and every weak angular derivative `v'`
of `v`, with `t = (√h)⁻¹` and `B = max 1 C0 + log (2 + 8π²) + 1`,
`Ent_{μ_h}(v²) ≤ t ∫ (v')² dμ_h + ∫ Φ_h v² dμ_h + B √h ∫ v² dμ_h`, where
`Φ_h = h U + corr h U` and `U = Uang`. The absolute witness `C0` is existentially quantified
together with its EX037 lower bound on `groundPot`.

Provides:
* `DGPS.Frontier.EX049.ex049_13_global_entropy_reduction_h_least_two`: the main statement, with an
  existential absolute witness `C0 > 0` and its lower bound on `groundPot` as conjuncts.
* `DGPS.Frontier.EX049.ex049_13_global_entropy_reduction_h_least_two_of_witness`: the same estimate
  for an arbitrary real `C0` satisfying the lower bound, with `K = max 1 C0`.
* `DGPS.Frontier.EX049.final_chain_EX04913`: the pure real chain that combines the three estimates.

R5 notes:
* Angular `H^1` and weak angular derivatives are the campaign predicates `AngularH1` and
  `IsAngularWeakDeriv` from `DGPS.Circle.AngularNormalization`. Their binding to the source objects
  is the open task EX049.25; this file does not claim it.
* The witness `C0` is existentially quantified in the main statement, with `0 < C0` and the EX037
  lower bound `h ^ 2 * sin t ^ 2 / 4 - C0 * h ≤ groundPot h t` (for `h ≥ 2` and every real `t`) as
  conjuncts. The coefficient uses `K = max 1 C0`, as the specification has `K = max(1, C0)`. The
  `_of_witness` variant states the same estimate for an arbitrary `C0` with that bound.
* `t = h^(-1/2)` is written `(Real.sqrt h)⁻¹`.
* `E_h(v) = ∫ (v')² dμ_h` is quantified over every weak angular derivative `v'` of `v`. Weak
  derivatives are unique almost everywhere, so this is the single-derivative reading and not a
  weaker one.
* `M_h(v)`, `E_h(v)` and the potential integral are taken against `circleReference h`, which is
  `μ_h = q_h m`. Entropy is `entEX04910`, with `0 log 0 = 0` through `Real.log 0 = 0`.
* `Φ_h = h U + R_h(U)` is written `h * Uang θ + corr h (Uang θ)`, with `U = Uang` and
  `R_h = corr h`. The potential integral is literally against `μ_h`. The change of density to `m`
  with `w = v √q_h` is proved in this file, not assumed.
* Non-literal reading (dependency): the specification's proof cites EX049.41 for `Z_h ≤ 1`. This
  file depends on `DGPS.Frontier.EX049.T41` through `Zh_bounds_EX04941` only, in addition to the
  three listed prerequisites. The lower bound of that lemma also supplies `0 ≤ Z_h`, which the sign
  `log Z_h ≤ 0` needs.
* Non-literal reading (route): the specification bounds `log (1/t) = log √h ≤ √h - 1 ≤ √h` and
  `log D ≤ (log D) √h`, then sums the mass coefficient to `B √h`. This file proves the same
  inequalities for `B = max 1 C0 + log D + 1`, with `D = 2 + 8π²`.
* No threshold beyond `h ≥ 2` is used. The hypothesis `2 ≤ h` gives `1 ≤ √h`, which is needed for
  `t ≤ 1` and for `log D ≤ (log D) √h`.
-/

namespace DGPS.Frontier.EX049

open MeasureTheory Real Filter
open DGPS.Circle.AngularNormalization DGPS.Circle.StationaryFlux DGPS.Examples.EngineeredRankOne
  DGPS.Examples.EngineeredGroundState

/-- The pure real chain of the three estimates. The entropy identity `Ent = Ent_m(w²) + Φ_w +
log Z · M` (EX049.12) and `log Z ≤ 0` give `Ent ≤ Ent_m(w²) + Φ_w`. The Haar entropy bound with
coefficient `t` (EX049.11) and the derivative bound (EX049.09) give the mass coefficient, with
`t h = s`, `log (1/t) ≤ s` and `log L ≤ L s`. -/
lemma final_chain_EX04913 {Ent EntW Phi LZ M Mw E W K L L1 t s h : ℝ}
    (hEnt : Ent = EntW + Phi + LZ * M) (hLZ : LZ ≤ 0) (hM0 : 0 ≤ M) (hMw : Mw = M)
    (h11 : EntW ≤ t * W + (L + L1) * Mw) (hW : W ≤ E + K * h * M)
    (ht0 : 0 ≤ t) (hth : t * h = s) (hL : L ≤ L * s) (hL1 : L1 ≤ s) :
    Ent ≤ t * E + Phi + (K + L + 1) * s * M := by
  rw [hMw] at h11
  have hA : t * W ≤ t * E + K * s * M := by
    have h1 := mul_le_mul_of_nonneg_left hW ht0
    have h2 : t * (E + K * h * M) = t * E + K * s * M := by
      rw [← hth]
      ring
    linarith
  have hB : (L + L1) * M ≤ (L * s + s) * M :=
    mul_le_mul_of_nonneg_right (by linarith) hM0
  have hLM : LZ * M ≤ 0 := by
    have := mul_le_mul_of_nonneg_right hLZ hM0
    linarith
  linarith

/-- EX049.13 for an arbitrary real `C0` satisfying the EX037 lower bound on `groundPot`, with
`K = max 1 C0`. Every `h ≥ 2`, every angular `H¹` function `v` and every weak angular derivative
`v'` of `v` satisfy the global entropy estimate. -/
theorem ex049_13_global_entropy_reduction_h_least_two_of_witness (C0 : ℝ)
    (hC0 : ∀ h : ℝ, 2 ≤ h → ∀ t : ℝ, h ^ 2 * Real.sin t ^ 2 / 4 - C0 * h ≤ groundPot h t)
    (h : ℝ) (hh : 2 ≤ h) (v : AngCircle → ℝ) (hv : AngularH1 v)
    (v' : AngCircle → ℝ) (hv' : IsAngularWeakDeriv v v') :
    entEX04910 (circleReference h) (fun θ => v θ ^ 2) ≤
      (Real.sqrt h)⁻¹ * (∫ θ, v' θ ^ 2 ∂circleReference h) +
        (∫ θ, (h * Uang θ + corr h (Uang θ)) * v θ ^ 2 ∂circleReference h) +
        (max 1 C0 + Real.log (2 + 8 * π ^ 2) + 1) * Real.sqrt h *
          (∫ θ, v θ ^ 2 ∂circleReference h) := by
  have hh0 : 0 < h := by linarith
  have hs0 : 0 < Real.sqrt h := Real.sqrt_pos.mpr hh0
  have hs1 : 1 ≤ Real.sqrt h := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ h by linarith)
    rwa [Real.sqrt_one] at this
  have hinv0 : 0 < (Real.sqrt h)⁻¹ := inv_pos.mpr hs0
  have hcancel : (Real.sqrt h)⁻¹ * Real.sqrt h = 1 := inv_mul_cancel₀ hs0.ne'
  have hinv1 : (Real.sqrt h)⁻¹ ≤ 1 := by
    nlinarith [mul_nonneg hinv0.le (sub_nonneg.2 hs1)]
  have hthh : (Real.sqrt h)⁻¹ * h = Real.sqrt h := by
    calc (Real.sqrt h)⁻¹ * h = (Real.sqrt h)⁻¹ * (Real.sqrt h * Real.sqrt h) := by
          rw [Real.mul_self_sqrt hh0.le]
      _ = Real.sqrt h := by rw [← mul_assoc, hcancel, one_mul]
  have hlog1 : Real.log (1 / (Real.sqrt h)⁻¹) ≤ Real.sqrt h := by
    rw [one_div, inv_inv]
    linarith [Real.log_le_sub_one_of_pos hs0]
  have hD1 : (1 : ℝ) ≤ 2 + 8 * π ^ 2 := by
    have := sq_nonneg π
    linarith
  have hLD0 : 0 ≤ Real.log (2 + 8 * π ^ 2) := Real.log_nonneg hD1
  have hLD : Real.log (2 + 8 * π ^ 2) ≤ Real.log (2 + 8 * π ^ 2) * Real.sqrt h := by
    have := mul_le_mul_of_nonneg_left hs1 hLD0
    rwa [mul_one] at this
  -- EX049.09: the ground-state identity, the mass identity and the derivative bound.
  obtain ⟨hw1, hId⟩ := ex049_09_full_h1_ground_state_identity_of_witness C0 hC0 h hh v hv
  have hw1' := hw1
  obtain ⟨w', hw'⟩ := hw1'
  obtain ⟨hmass, -, hW⟩ := hId v' w' hv' hw'
  -- EX049.11: Haar entropy with the energy coefficient `(√h)⁻¹`.
  have h11 := ex049_11_haar_entropy_small_energy_coefficient (groundStateConj h v) hw1
    (Real.sqrt h)⁻¹ hinv0 hinv1 w' hw'
  -- EX049.12: exact entropy conjugation.
  have h12 := ex049_12_exact_entropy_conjugation h hh v hv
  -- EX049.41: the normalizing constant satisfies `0 < Z_h ≤ 1`.
  have hZ := Zh_bounds_EX04941 h hh
  have hZ0 : 0 ≤ Zh h := le_trans (Real.exp_pos _).le hZ.1
  have hlogZ : Real.log (Zh h) ≤ 0 := Real.log_nonpos hZ0 hZ.2
  have hM0 : 0 ≤ ∫ θ, v θ ^ 2 ∂circleReference h := integral_nonneg fun θ => sq_nonneg _
  -- Change of density: the potential integral against `μ_h` is the one against `m` with `w`.
  have hPhi : (∫ θ, (h * Uang θ + corr h (Uang θ)) * v θ ^ 2 ∂circleReference h) =
      ∫ θ, (h * Uang θ + corr h (Uang θ)) * groundStateConj h v θ ^ 2 ∂angHaar := by
    rw [integral_circleReference h hh0]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    show (h * Uang θ + corr h (Uang θ)) * v θ ^ 2 * qAng h θ =
      (h * Uang θ + corr h (Uang θ)) * (v θ * Real.sqrt (qAng h θ)) ^ 2
    rw [mul_pow, Real.sq_sqrt (qAng_pos h hh0 θ).le]
    ring
  rw [hPhi]
  exact final_chain_EX04913 h12 hlogZ hM0 hmass h11 hW hinv0.le hthh hLD hlog1

/-- EX049.13: global entropy reduction for every `h ≥ 2`. There is an absolute witness `C0 > 0`
with the EX037 lower bound on `groundPot`, and for it every angular `H¹` function `v`, every weak
angular derivative `v'` of `v`, and every `h ≥ 2` satisfy
`Ent_{μ_h}(v²) ≤ (√h)⁻¹ ∫ (v')² dμ_h + ∫ Φ_h v² dμ_h + (max 1 C0 + log (2 + 8π²) + 1) √h M_h(v)`. -/
theorem ex049_13_global_entropy_reduction_h_least_two :
    ∃ C0 : ℝ, 0 < C0 ∧
      (∀ h : ℝ, 2 ≤ h → ∀ t : ℝ, h ^ 2 * Real.sin t ^ 2 / 4 - C0 * h ≤ groundPot h t) ∧
      ∀ h : ℝ, 2 ≤ h → ∀ v : AngCircle → ℝ, AngularH1 v →
        ∀ v' : AngCircle → ℝ, IsAngularWeakDeriv v v' →
          entEX04910 (circleReference h) (fun θ => v θ ^ 2) ≤
            (Real.sqrt h)⁻¹ * (∫ θ, v' θ ^ 2 ∂circleReference h) +
              (∫ θ, (h * Uang θ + corr h (Uang θ)) * v θ ^ 2 ∂circleReference h) +
              (max 1 C0 + Real.log (2 + 8 * π ^ 2) + 1) * Real.sqrt h *
                (∫ θ, v θ ^ 2 ∂circleReference h) := by
  obtain ⟨C0, hC0pos, hbound, -⟩ := ex049_09_full_h1_ground_state_identity
  exact ⟨C0, hC0pos, hbound, fun h hh v hv v' hv' =>
    ex049_13_global_entropy_reduction_h_least_two_of_witness C0 hbound h hh v hv v' hv'⟩

end DGPS.Frontier.EX049
