import DGPS.Frontier.FIN068.T01
import DGPS.Frontier.FIN068.T37

/-!
Task id and title: FIN068.02, Logarithmic derivative (module `DGPS.Frontier.FIN068.T02`).

Provides:
* `DGPS.Frontier.FIN068.fin068_02_logarithmic_derivative`: for `ℓ(t) = Real.log (besselI 0 t)`,
  (1) `ℓ` is `C^∞` on all of `ℝ`;
  (2) for every real `t`, `ℓ'(t) = I₀'(t) / I₀(t)`, with `I₀' = deriv (besselI 0)`;
  (3) for every real `t`, `ℓ'(t) = besselRatio t`, i.e. `ℓ' = g = I₁ / I₀`;
  (4) `ℓ''(4) = g'(4)`, written `iteratedDeriv 2 ℓ 4 = deriv besselRatio 4` (this value is the `v₀`
      of the node, `v₀ := g'(4)`).

Proof: smoothness and positivity of `besselI 0` come from FIN068.01 (through FIN068.16) after the
identification `besselI 0 = K_FIN06814 0` (`besselI_zero_eq_K_FIN06837` of FIN068.37). The chain
rule for `Real.log` at a nonzero value, together with `deriv (besselI 0) = besselI 1`
(`hasDerivAt_besselI_zero`), gives (2) and (3). Item (4) follows by `iteratedDeriv_succ` from
the function identity `deriv ℓ = besselRatio`. No series interchange is used.

R5 notes:
* `I₀` is read as the campaign object `besselI 0` (the normalized Haar average over `AddCircle (2π)`
  with `angMode 0 = 1`), the object named in the node. The identification of `besselI 0` with the
  interval integral and with `K_0` is FIN068.37's content and is used only through its lemmas.
* `g` is read as the campaign definition `besselRatio = I₁ / I₀`. The node's identity
  `g = I₀' / I₀` is proved here from `hasDerivAt_besselI_zero`, not assumed.
* The smoothness claim "ℓ is smooth" is read as `ContDiff ℝ ∞` on all of `ℝ` (the global reading).
  No domain restriction is needed, because `besselI 0 t > 0` for every real `t`.
* The node's `v₀` is defined as `g'(4)`. The statement writes `v₀` directly as `deriv besselRatio 4`,
  with no separate name, and `ℓ''(4)` as `iteratedDeriv 2 ℓ 4`. The function-level identity
  `iteratedDeriv 2 ℓ = deriv besselRatio` is proved as a helper and specialised to `4`.
* The derivative of `besselRatio` is not computed in this file. The explicit formula for `v₀` in
  terms of `K_2`, `K_1`, `K_0` is FIN068.37's content and is not needed for this statement.
* No hypothesis is added. Every helper declaration carries the suffix `_FIN06802`.
-/

open DGPS.Circle.BesselMoments
open scoped ContDiff

namespace DGPS.Frontier.FIN068

/-- The campaign `I₀` is `C^∞` on `ℝ`: it equals `K_FIN06814 0`, the head of the FIN068.16 family. -/
theorem besselI_zero_contDiff_FIN06802 : ContDiff ℝ ∞ (besselI 0) := by
  have h : besselI 0 = K_FIN06814 0 := by
    funext t
    exact besselI_zero_eq_K_FIN06837 t
  rw [h]
  exact fin068_16_iterated_derivatives_smoothness_contDiff

/-- Chain rule for `Real.log ∘ I₀` at the positive value `I₀(t)`. -/
theorem hasDerivAt_log_besselI_zero_FIN06802 (t : ℝ) :
    HasDerivAt (fun s => Real.log (besselI 0 s)) (besselI 1 t / besselI 0 t) t :=
  (hasDerivAt_besselI_zero t).log (besselI_zero_pos t).ne'

/-- `ℓ'(t) = I₀'(t) / I₀(t)`, with `I₀'(t) = I₁(t)` by `hasDerivAt_besselI_zero`. -/
theorem deriv_log_eq_FIN06802 (t : ℝ) :
    deriv (fun s => Real.log (besselI 0 s)) t = deriv (besselI 0) t / besselI 0 t := by
  rw [(hasDerivAt_besselI_zero t).deriv]
  exact (hasDerivAt_log_besselI_zero_FIN06802 t).deriv

/-- `ℓ'(t) = g(t) = besselRatio t`. -/
theorem deriv_log_eq_besselRatio_FIN06802 (t : ℝ) :
    deriv (fun s => Real.log (besselI 0 s)) t = besselRatio t :=
  (hasDerivAt_log_besselI_zero_FIN06802 t).deriv

/-- As functions, `ℓ' = besselRatio`. -/
theorem deriv_log_fun_FIN06802 :
    deriv (fun s => Real.log (besselI 0 s)) = besselRatio :=
  funext deriv_log_eq_besselRatio_FIN06802

/-- As functions, `ℓ'' = g'`. -/
theorem iteratedDeriv_two_log_FIN06802 :
    iteratedDeriv 2 (fun s => Real.log (besselI 0 s)) = deriv besselRatio := by
  rw [iteratedDeriv_succ, iteratedDeriv_one, deriv_log_fun_FIN06802]

/-- Logarithmic derivative: `ℓ = log I₀` is smooth, `ℓ' = I₀'/I₀ = g`, and `ℓ''(4) = g'(4)`. -/
theorem fin068_02_logarithmic_derivative :
    ContDiff ℝ ∞ (fun s : ℝ => Real.log (besselI 0 s)) ∧
    (∀ t : ℝ, deriv (fun s : ℝ => Real.log (besselI 0 s)) t = deriv (besselI 0) t / besselI 0 t) ∧
    (∀ t : ℝ, deriv (fun s : ℝ => Real.log (besselI 0 s)) t = besselRatio t) ∧
    iteratedDeriv 2 (fun s : ℝ => Real.log (besselI 0 s)) 4 = deriv besselRatio 4 :=
  ⟨besselI_zero_contDiff_FIN06802.log fun t => (besselI_zero_pos t).ne',
    deriv_log_eq_FIN06802, deriv_log_eq_besselRatio_FIN06802,
    congrFun iteratedDeriv_two_log_FIN06802 4⟩

end DGPS.Frontier.FIN068
