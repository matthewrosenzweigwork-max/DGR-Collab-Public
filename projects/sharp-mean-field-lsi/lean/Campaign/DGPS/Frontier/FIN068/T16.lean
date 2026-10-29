import DGPS.Frontier.FIN068.T15

/-!
Task id and title: FIN068.16, Iterated derivatives and smoothness (module
`DGPS.Frontier.FIN068.T16`).

Provides:
* `DGPS.Frontier.FIN068.iteratedDeriv_family_FIN06816`: generic lemma; for any family
  `f : ℕ → ℝ → ℝ` with `HasDerivAt (f k) (f (k + 1) t) t` for all `k`, `t`, one has
  `iteratedDeriv k (f 0) = f k` for every `k`.
* `DGPS.Frontier.FIN068.contDiff_family_FIN06816`: for the same kind of family, `f 0` is `C^∞`.
* `DGPS.Frontier.FIN068.fin068_16_iterated_derivatives_smoothness`: for every `k : ℕ`,
  `iteratedDeriv k (K_FIN06814 0) = K_FIN06814 k`, and `K_FIN06814 0` is smooth on `ℝ`
  (`ContDiff ℝ ∞`).
* `DGPS.Frontier.FIN068.fin068_16_iterated_derivatives_smoothness_iteratedDeriv`: the
  identity `iteratedDeriv k (K_FIN06814 0) = K_FIN06814 k` alone.
* `DGPS.Frontier.FIN068.fin068_16_iterated_derivatives_smoothness_contDiff`: smoothness of
  `K_FIN06814 0` alone.
* `DGPS.Frontier.FIN068.fin068_16_iterated_derivatives_smoothness_bounds`: the bounded-interval
  claims of Task 01 (as recorded in FIN068.14), now for the iterated derivatives: for `M ≥ 0`
  and `|t| ≤ M`, `|iteratedDeriv k (K_FIN06814 0) t| ≤ exp M`; moreover
  `exp (-|t|) ≤ K_FIN06814 0 t` and `0 < K_FIN06814 0 t` for every real `t`.

R5 notes:
* `K_k` is `K_FIN06814 k` (measure `angHaar`, i.e. `dθ/(2π)`; `cos θ` is `angCos`), and `K_0` is
  `K_FIN06814 0`, as in FIN068.14/15. No hypothesis is added; `k : ℕ` and `t : ℝ` are unrestricted.
* "Smooth" is read as `ContDiff ℝ ∞` (all finite orders, Mathlib's `∞`, not analytic `ω`).
* The specification's "recover the bounded-interval claims of Task 01" is read non-literally
  as the FIN068.14 conclusions (bound `exp M` on `|t| ≤ M`, lower bound `exp (-|t|)`, positivity),
  with the bound transferred to the iterated derivatives via the identity; the FIN068.14 bound
  for `K_k` itself is the literal claim and is obtained by rewriting with the identity.
* The proof does not use a smooth-parameter-integral theorem; it is one generic induction from the
  one-step derivative of FIN068.15 using Mathlib's `contDiff_of_differentiable_iteratedDeriv`.
-/

open scoped ContDiff
open DGPS.Circle.AngularNormalization DGPS.Circle.BesselMoments

namespace DGPS.Frontier.FIN068

/-- Generic derivative-family induction: if `f (k+1)` is the derivative of `f k`, then
`iteratedDeriv k (f 0) = f k`. -/
theorem iteratedDeriv_family_FIN06816 (f : ℕ → ℝ → ℝ)
    (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) (k : ℕ) :
    iteratedDeriv k (f 0) = f k := by
  induction k with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    exact (hf n t).deriv

/-- Generic smoothness: the head of a derivative family is `C^∞`. -/
theorem contDiff_family_FIN06816 (f : ℕ → ℝ → ℝ)
    (hf : ∀ k t, HasDerivAt (f k) (f (k + 1) t) t) : ContDiff ℝ ∞ (f 0) := by
  refine contDiff_of_differentiable_iteratedDeriv fun m _ => ?_
  rw [iteratedDeriv_family_FIN06816 f hf m]
  exact fun t => (hf m t).differentiableAt

theorem fin068_16_iterated_derivatives_smoothness_iteratedDeriv (k : ℕ) :
    iteratedDeriv k (K_FIN06814 0) = K_FIN06814 k :=
  iteratedDeriv_family_FIN06816 K_FIN06814 fin068_15_one_derivative_step k

theorem fin068_16_iterated_derivatives_smoothness_contDiff :
    ContDiff ℝ ∞ (K_FIN06814 0) :=
  contDiff_family_FIN06816 K_FIN06814 fin068_15_one_derivative_step

/-- For every natural `k`, `iteratedDeriv k K_0 = K_k`, and `K_0` is smooth on `ℝ`. -/
theorem fin068_16_iterated_derivatives_smoothness :
    (∀ k : ℕ, iteratedDeriv k (K_FIN06814 0) = K_FIN06814 k) ∧
      ContDiff ℝ ∞ (K_FIN06814 0) :=
  ⟨fin068_16_iterated_derivatives_smoothness_iteratedDeriv,
    fin068_16_iterated_derivatives_smoothness_contDiff⟩

/-- Bounded-interval claims of Task 01, recovered for the iterated derivatives. -/
theorem fin068_16_iterated_derivatives_smoothness_bounds (k : ℕ) {M : ℝ} (_hM : 0 ≤ M) :
    (∀ t : ℝ, |t| ≤ M → |iteratedDeriv k (K_FIN06814 0) t| ≤ Real.exp M) ∧
      (∀ t : ℝ, Real.exp (-|t|) ≤ K_FIN06814 0 t ∧ 0 < K_FIN06814 0 t) := by
  refine ⟨fun t ht => ?_, fun t => ⟨?_, ?_⟩⟩
  · rw [fin068_16_iterated_derivatives_smoothness_iteratedDeriv]
    exact fin068_14_uniform_integrability_bounds_positivity_abs_le k ht
  · exact fin068_14_uniform_integrability_bounds_positivity_lower t
  · exact fin068_14_uniform_integrability_bounds_positivity_pos t

end DGPS.Frontier.FIN068
