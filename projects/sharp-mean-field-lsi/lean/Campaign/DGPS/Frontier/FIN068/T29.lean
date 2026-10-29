import Mathlib
import DGPS.Frontier.FIN068.T28

/-!
# FIN068.29: All-order compact parameter integration

Provides:
* `DGPS.Frontier.FIN068.fin068_29_order_compact_parameter_integration`: for finite-dimensional
  real normed spaces `E`, `F`, an open `U ⊆ E` and `H : ℝ → E → F` such that `H t` is `C^∞` on `U`
  for every `t ∈ [0,1]` and, for every `k : ℕ`, `(t, p) ↦ D^k_p H(t, p)` is jointly continuous on
  `[0,1] × U`, the parameter integral `p ↦ ∫₀¹ H(t,p) dt` is `C^∞` on `U` and, for every `k` and
  every `p ∈ U`, its `k`-th Fréchet derivative is `∫₀¹ D^k_p H(t,p) dt`.
* `DGPS.Frontier.FIN068.fin068_29_order_compact_parameter_integration_hasFDerivAt`: the pointwise
  statement at each order, i.e. the `k`-th derivative integral has Fréchet derivative the integral
  of the `(k+1)`-st parameter derivative (curried on the left).
* Helpers (all with suffix `_FIN06829`): `finiteDimensional_cmm_FIN06829` (finite dimensionality of
  the spaces of continuous `k`-multilinear maps), `intervalIntegral_equiv_comm_FIN06829`, `hasFDerivAt_integral_iteratedFDeriv_FIN06829`, `iteratedFDeriv_integral_FIN06829`.

R5 notes:
* The function `H : [0,1] × U → F` is encoded as `H : ℝ → E → F`; only values on
  `Set.Icc 0 1 ×ˢ U` matter.
* "All iterated parameter derivatives exist" is `ContDiffOn ℝ ∞ (H t) U` for each `t ∈ [0,1]`
  (`U` open, so this is existence of all iterated Fréchet derivatives on `U`). "Jointly continuous"
  is `ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ k (H q.1) q.2) (Icc 0 1 ×ˢ U)` for each
  `k : ℕ`; the case `k = 0` is joint continuity of `H` itself (via the isometric identification of
  `iteratedFDeriv ℝ 0` with the function value).
* The `k`-th parameter derivative is the iterated Fréchet derivative `iteratedFDeriv ℝ k (H t) p`
  (a continuous `k`-multilinear map). The integral is `∫ t in (0:ℝ)..1`.
* "The parameter integral is smooth" is `ContDiffOn ℝ ∞ _ U` (smooth on the open set `U`); the
  derivative formula is stated for `p ∈ U` with the global `iteratedFDeriv`, which agrees with the
  derivative within `U` since `U` is open.
* Finite dimensionality of `E` and `F` is exactly as in FIN068.28; no hypothesis beyond the
  specification is added. The inductive step applies FIN068.28 with codomain the (finite
  dimensional) space of continuous `k`-multilinear maps; no uniform bound in `k` is used.
-/

open MeasureTheory Set Metric
open scoped ContDiff

namespace DGPS.Frontier.FIN068

/-- The space of continuous `k`-multilinear maps `E^k → F` between finite-dimensional real normed
spaces is finite dimensional. -/
theorem finiteDimensional_cmm_FIN06829
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] (k : ℕ) :
    FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) := by
  induction k with
  | zero =>
    exact LinearEquiv.finiteDimensional
      (continuousMultilinearCurryFin0 ℝ E F).symm.toLinearEquiv
  | succ k ih =>
    have : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) := ih
    exact LinearEquiv.finiteDimensional
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm.toLinearEquiv

/-- Linear isometric equivalences commute with the interval integral. -/
theorem intervalIntegral_equiv_comm_FIN06829
    {G G' : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
    [NormedAddCommGroup G'] [NormedSpace ℝ G'] [CompleteSpace G'] (L : G ≃ₗᵢ[ℝ] G') (f : ℝ → G) :
    ∫ t in (0 : ℝ)..1, L (f t) = L (∫ t in (0 : ℝ)..1, f t) :=
  L.toLinearIsometry.intervalIntegral_comp_comm f

/-- The order-`k` step: the integral of the `k`-th parameter derivative is differentiable, with
derivative the integral of the derivative of the `k`-th parameter derivative. -/
theorem hasFDerivAt_integral_iteratedFDeriv_FIN06829
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {H : ℝ → E → F}
    (hsm : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffOn ℝ ∞ (H t) U)
    (hcont : ∀ k : ℕ, ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ k (H q.1) q.2)
      (Icc (0 : ℝ) 1 ×ˢ U))
    (k : ℕ) {p : E} (hp : p ∈ U) :
    HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ k (H t) x)
      (∫ t in (0 : ℝ)..1, fderiv ℝ (iteratedFDeriv ℝ k (H t)) p) p := by
  have := finiteDimensional_cmm_FIN06829 (E := E) (F := F) k
  refine fin068_28_one_parameter_derivative_compact_integral
    (H := fun t x => iteratedFDeriv ℝ k (H t) x) hU (hcont k) ?_ ?_ p hp
  · intro t ht q hq
    have h1 : ContDiffAt ℝ ∞ (H t) q := (hsm t ht).contDiffAt (hU.mem_nhds hq)
    have h2 : ContDiffAt ℝ 1 (iteratedFDeriv ℝ k (H t)) q :=
      h1.iteratedFDeriv_right (m := 1) (i := k) (by exact_mod_cast le_top)
    exact h2.differentiableAt (by simp)
  · have h : (fun q : ℝ × E => fderiv ℝ (iteratedFDeriv ℝ k (H q.1)) q.2)
        = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F) ∘
          (fun q : ℝ × E => iteratedFDeriv ℝ (k + 1) (H q.1) q.2) := by
      funext q
      exact congrFun fderiv_iteratedFDeriv q.2
    rw [h]
    exact (LinearIsometryEquiv.continuous _).comp_continuousOn (hcont (k + 1))

/-- On `U`, the `k`-th derivative of the parameter integral is the integral of the `k`-th
parameter derivatives. -/
theorem iteratedFDeriv_integral_FIN06829
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {H : ℝ → E → F}
    (hsm : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffOn ℝ ∞ (H t) U)
    (hcont : ∀ k : ℕ, ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ k (H q.1) q.2)
      (Icc (0 : ℝ) 1 ×ˢ U))
    (k : ℕ) :
    ∀ p ∈ U, iteratedFDeriv ℝ k (fun x => ∫ t in (0 : ℝ)..1, H t x) p
      = ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ k (H t) p := by
  induction k with
  | zero =>
    intro p hp
    have key := (continuousMultilinearCurryFin0 ℝ E F).toLinearIsometry.intervalIntegral_comp_comm
      (a := 0) (b := 1) (μ := volume) (fun t => iteratedFDeriv ℝ 0 (H t) p)
    have e : ∀ t, (continuousMultilinearCurryFin0 ℝ E F) (iteratedFDeriv ℝ 0 (H t) p) = H t p :=
      fun t => by simp [iteratedFDeriv_zero_eq_comp]
    simp only [LinearIsometryEquiv.coe_toLinearIsometry, e] at key
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, key]
    simp
  | succ k ih =>
    intro p hp
    have hev : iteratedFDeriv ℝ k (fun x => ∫ t in (0 : ℝ)..1, H t x)
        =ᶠ[nhds p] fun x => ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ k (H t) x :=
      Filter.eventually_of_mem (hU.mem_nhds hp) fun x hx => ih x hx
    have hD := hasFDerivAt_integral_iteratedFDeriv_FIN06829 hU hsm hcont k hp
    have hD' : fderiv ℝ (iteratedFDeriv ℝ k (fun x => ∫ t in (0 : ℝ)..1, H t x)) p
        = ∫ t in (0 : ℝ)..1, fderiv ℝ (iteratedFDeriv ℝ k (H t)) p := by
      rw [hev.fderiv_eq]
      exact hD.fderiv
    have hD2 : ∀ t, fderiv ℝ (iteratedFDeriv ℝ k (H t)) p
        = (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F)
          (iteratedFDeriv ℝ (k + 1) (H t) p) := fun t => congrFun fderiv_iteratedFDeriv p
    have key := intervalIntegral_equiv_comm_FIN06829
      (G := E →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
      (G' := ContinuousMultilinearMap ℝ (fun _ : Fin (k + 1) => E) F)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm
      (fun t => fderiv ℝ (iteratedFDeriv ℝ k (H t)) p)
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, hD', ← key]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hD2, LinearIsometryEquiv.symm_apply_apply]

/-- Pointwise statement at order `k`. -/
theorem fin068_29_order_compact_parameter_integration_hasFDerivAt
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {H : ℝ → E → F}
    (hsm : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffOn ℝ ∞ (H t) U)
    (hcont : ∀ k : ℕ, ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ k (H q.1) q.2)
      (Icc (0 : ℝ) 1 ×ˢ U))
    (k : ℕ) {p : E} (hp : p ∈ U) :
    HasFDerivAt (fun x => ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ k (H t) x)
      (∫ t in (0 : ℝ)..1, fderiv ℝ (iteratedFDeriv ℝ k (H t)) p) p :=
  hasFDerivAt_integral_iteratedFDeriv_FIN06829 hU hsm hcont k hp

/-- **FIN068.29.** All-order differentiation of `p ↦ ∫₀¹ H(t,p) dt` under the integral sign: the
integral is smooth on `U` and its `k`-th derivative is the integral of the `k`-th parameter
derivative. -/
theorem fin068_29_order_compact_parameter_integration
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {U : Set E} (hU : IsOpen U) {H : ℝ → E → F}
    (hsm : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffOn ℝ ∞ (H t) U)
    (hcont : ∀ k : ℕ, ContinuousOn (fun q : ℝ × E => iteratedFDeriv ℝ k (H q.1) q.2)
      (Icc (0 : ℝ) 1 ×ˢ U)) :
    ContDiffOn ℝ ∞ (fun x => ∫ t in (0 : ℝ)..1, H t x) U ∧
      ∀ k : ℕ, ∀ p ∈ U, iteratedFDeriv ℝ k (fun x => ∫ t in (0 : ℝ)..1, H t x) p
        = ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ k (H t) p := by
  refine ⟨?_, fun k => iteratedFDeriv_integral_FIN06829 hU hsm hcont k⟩
  rw [contDiffOn_infty]
  intro n
  have hdiff : ∀ m : ℕ, DifferentiableOn ℝ
      (fun x => iteratedFDerivWithin ℝ m (fun x => ∫ t in (0 : ℝ)..1, H t x) U x) U := by
    intro m
    have hG : DifferentiableOn ℝ (fun x => ∫ t in (0 : ℝ)..1, iteratedFDeriv ℝ m (H t) x) U :=
      fun p hp => (hasFDerivAt_integral_iteratedFDeriv_FIN06829 hU hsm hcont m hp
        ).differentiableAt.differentiableWithinAt
    refine hG.congr fun x hx => ?_
    rw [iteratedFDerivWithin_of_isOpen m hU hx]
    exact iteratedFDeriv_integral_FIN06829 hU hsm hcont m x hx
  exact contDiffOn_of_continuousOn_differentiableOn (n := (n : ℕ∞))
    (fun m _ => (hdiff m).continuousOn) (fun m _ => hdiff m)

end DGPS.Frontier.FIN068
