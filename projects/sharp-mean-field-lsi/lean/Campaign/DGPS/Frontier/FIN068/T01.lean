import DGPS.Frontier.FIN068.T14
import DGPS.Frontier.FIN068.T15
import DGPS.Frontier.FIN068.T16

/-!
Task id and title: FIN068.01, Smoothness of the Bessel integral (module
`DGPS.Frontier.FIN068.T01`).

Provides:
* `DGPS.Frontier.FIN068.fin068_01_smoothness_bessel_integral`: for every `k : ℕ` and every `M > 0`:
  (1) `K_FIN06814 0` (the literal `I₀`) is `C^k` on `Set.Ioo (-M) M`;
  (2) for every real `t`, its `k`-th iterated derivative is the integral
      `∫ (cos θ)^k e^{t cos θ} dθ/(2π)` (normalized Haar measure `angHaar`);
  (3) for every `t` with `|t| ≤ M`, `|iteratedDeriv k (K_FIN06814 0) t| ≤ exp M`;
  (4) for every real `t`, `exp (-|t|) ≤ I₀(t)` and `0 < I₀(t)`.

Assembly only: the statement is discharged by FIN068.16 (smoothness and the identity
`iteratedDeriv k K₀ = K_k`), which uses FIN068.15 (one derivative step) and FIN068.14
(continuity, the bound `exp M`, the lower bound and positivity). No new analysis is done here.

R5 notes:
* The measure `m` is read as the normalized Haar measure `angHaar` (`dθ/(2π)`, a probability
  measure on `AddCircle (2π)`), and `cos θ` is `angCos`, as in FIN068.14 and FIN068.37.
* `I₀` is read as the literal `K_FIN06814 0` (the integral `∫ e^{t cos θ} dθ/(2π)`), as the node
  instructs until gate FIN068.37 is resolved. The identification of the campaign's `besselI 0`
  with `K_FIN06814 0` is FIN068.37's content (`besselI_zero_eq_K_FIN06837`) and is not imported
  here, so this file makes no claim about `besselI` itself.
* "`I₀` is `C^k` on `(-M, M)`" is read as `ContDiffOn ℝ k` on `Set.Ioo (-M) M` (real-variable
  `C^k`, `k` finite). The stronger global smoothness is available from FIN068.16 but is not claimed
  as a separate conclusion.
* The derivative formula has no domain in the specification; it is stated for every real `t`,
  which is stronger than the implicit reading on `(-M, M)` and needs no restriction.
* The bound `|I₀^{(k)}(t)| ≤ e^M` is stated for `|t| ≤ M` (closed), as the specification says, and
  for the Mathlib `iteratedDeriv k` of `K_FIN06814 0`; by clause (2) this is the bound on the
  integral.
* The lower bound and positivity are stated for every real `t`, as the specification's
  "`I₀(t) ≥ e^{-|t|} > 0`" carries no domain restriction.
* The specification's "`M > 0`" is stated literally as the hypothesis `0 < M`. No other hypothesis
  is added. The spec's "enlarged interval `[-M-1, M+1]`" device is internal to FIN068.15, which uses
  the ball of radius `1` around each base point, and is not restated here.
* No helper declarations are introduced in this file; the generic order-`k` induction is the
  `iteratedDeriv_family_FIN06816` lemma of FIN068.16, instantiated once.
-/

open MeasureTheory Real
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments

namespace DGPS.Frontier.FIN068

/-- Smoothness of the Bessel integral: for every `k` and `M > 0`, `I₀` is `C^k` on `(-M, M)`,
its `k`-th derivative is `∫ (cos θ)^k e^{t cos θ} dθ/(2π)`, it is bounded by `e^M` on `|t| ≤ M`,
and `e^{-|t|} ≤ I₀(t)` with `0 < I₀(t)` for every real `t`. -/
theorem fin068_01_smoothness_bessel_integral (k : ℕ) {M : ℝ} (hM : 0 < M) :
    ContDiffOn ℝ k (K_FIN06814 0) (Set.Ioo (-M) M) ∧
    (∀ t : ℝ, iteratedDeriv k (K_FIN06814 0) t =
      ∫ θ, angCos θ ^ k * Real.exp (t * angCos θ) ∂angHaar) ∧
    (∀ t : ℝ, |t| ≤ M → |iteratedDeriv k (K_FIN06814 0) t| ≤ Real.exp M) ∧
    (∀ t : ℝ, Real.exp (-|t|) ≤ K_FIN06814 0 t ∧ 0 < K_FIN06814 0 t) := by
  have hit := fin068_16_iterated_derivatives_smoothness_iteratedDeriv
  have hb := fin068_16_iterated_derivatives_smoothness_bounds k hM.le
  have hk : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
    WithTop.coe_le_coe.mpr le_top
  exact ⟨(fin068_16_iterated_derivatives_smoothness_contDiff.of_le hk).contDiffOn,
    fun t => congrFun (hit k) t,
    fun t ht => hb.1 t ht,
    hb.2⟩

end DGPS.Frontier.FIN068
