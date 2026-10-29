import DGPS.Analysis.ComplementaryElliptic

/-!
# EX012.37: Angular elliptic-operator definition gate

Task id: EX012.37 (node EX012, one-site complementary range equation).
Title: Angular elliptic-operator definition gate.

Bindings (source object or notion in the specification, the actual declaration, its type or
binder list, and any discrepancy with the specification text):

| Source notion | Actual declaration (file:line) | Type / binders | Discrepancy |
|---|---|---|---|
| Hölder exponent `0 < α < 1` | `DGPS.Analysis.PeriodicHolder.HolderExponent` (`Campaign/DGPS/Analysis/PeriodicHolder.lean:601`) | `class HolderExponent (α : ℝ) : Prop` with fields `pos : 0 < α`, `lt_one : α < 1` | none; the hypothesis `0 < α < 1` is the instance argument `[HolderExponent α]` |
| `PH α k` | `DGPS.Analysis.PeriodicHolder.PH` (`PeriodicHolder.lean:644`) | `PH (α : ℝ) [HolderExponent α] (k : ℕ) : Type`, a subalgebra of `ℝ → ℝ` | none |
| underlying function of `f : PH α k` | `PH.val` (`PeriodicHolder.lean:653`), `PH.isPH` (`:658`), `PH.mk` (`:656`) | `PH.val : PH α k → ℝ → ℝ` | none; `IsPH α 2 u` means `1`-periodic, `u` and `deriv u` differentiable, `deriv (deriv u)` Hölder (`:78`) |
| `W = PH.orthSub α 2` | `DGPS.Analysis.PeriodicHolder.PH.orthSub` (`PeriodicHolder.lean:1167`) | `PH.orthSub (α : ℝ) [HolderExponent α] (k : ℕ) : Submodule ℝ (PH α k)` | none |
| angular `(2π)^(-2)` | `DGPS.Analysis.ComplementaryElliptic.kappa` (`Campaign/DGPS/Analysis/ComplementaryElliptic.lean:18`) | `kappa : ℝ := (2 * Real.pi) ^ 2` | the specification writes `(2π)^(-2)`; the campaign stores the reciprocal `kappa⁻¹` |
| body of the operator | `DGPS.Analysis.ComplementaryElliptic.ellFun` (`ComplementaryElliptic.lean:23`) | `ellFun (u : ℝ → ℝ) : ℝ → ℝ := kappa⁻¹ • deriv (deriv u) + u` | none; the body IS printed in the source (the specification says it is not) |
| `ComplementaryElliptic.ell` | `DGPS.Analysis.ComplementaryElliptic.ell` (`ComplementaryElliptic.lean:91`) | `ell {α : ℝ} [HolderExponent α] : PH α 2 →L[ℝ] PH α 0`, built by `LinearMap.mkContinuous` from `PH.mk (ellFun u.val) _`; `ell_val` (`:100`) is `rfl` | none |
| equivalence of FOU018 | `DGPS.Analysis.ComplementaryElliptic.ellEquiv` (`ComplementaryElliptic.lean:542`), `ellEquiv_apply` (`:547`) | `ellEquiv : PH.orthSub α 2 ≃L[ℝ] PH.orthSub α 0` | none |
| FOU018 | `DGPS.Analysis.complementary_circle_elliptic_inverse` (`ComplementaryElliptic.lean:1041`) | `(α : ℝ) [HolderExponent α]`; its first clause provides `e` with `(e u : PH α 0) = ell (u : PH α 2)` | none |
| derivative `f''` | Mathlib `deriv` applied twice | `deriv (deriv f.val)`, in the campaign unit-period variable `x` | the specification's `f''` is read as the second derivative in `x`, the coefficient `(2π)^(-2)` converting to the angular variable |

Provides:
* `DGPS.Frontier.EX012.gate_ex012_37_angular_elliptic_operator_definition_gate`: for every
  `f : PH α 2` and every `x`, `(ell f).val x = ((2π)^2)⁻¹ * deriv (deriv f.val) x + f.val x`.
* `DGPS.Frontier.EX012.gate_ex012_37_angular_elliptic_operator_definition_gate_fun`: the same
  identity as an equality of functions, `(ell f).val = ((2π)^2)⁻¹ • deriv (deriv f.val) + f.val`.
* `DGPS.Frontier.EX012.gate_ex012_37_angular_elliptic_operator_definition_gate_mk`: the identity
  in `PH α 0`, `ell f = PH.mk (fun x => ((2π)^2)⁻¹ * deriv (deriv f.val) x + f.val x) _`.
* `DGPS.Frontier.EX012.gate_ex012_37_angular_elliptic_operator_definition_gate_angular`: with
  `D = (2π)⁻¹ ∂_x` the angular derivative, `(ell f).val x = D (D f.val) x + f.val x`.
* `DGPS.Frontier.EX012.gate_ex012_37_angular_elliptic_operator_definition_gate_equiv`: for every
  `u : PH.orthSub α 2`, `(ellEquiv u : PH α 0).val x = ((2π)^2)⁻¹ * deriv (deriv u.val) x + u.val x`.
* `DGPS.Frontier.EX012.gate_ex012_37_angular_elliptic_operator_definition_gate_fou018`: the
  equivalence `e` of FOU018 satisfies the same pointwise formula on `W`.

R5 notes:
* No hypothesis is added beyond `[HolderExponent α]`, the campaign form of `0 < α < 1`.
* The specification says the body of `ell` is not printed. It is printed: `ell` is the continuous
  linear extension of `PH.mk (ellFun u.val) _` with `ellFun u = kappa⁻¹ • deriv (deriv u) + u`, so
  the bridge is definitional and no premise of the specification fails in Lean. Only the remark
  that the body is unavailable is out of date.
* `(2π)^(-2)` is read as `((2 * Real.pi) ^ 2)⁻¹ = kappa⁻¹`, and `f''` as `deriv (deriv f.val)`
  in the unit-period variable `x`. The angular reading `D = (2π)⁻¹ ∂_x` is also stated
  (`_angular`), so the leading coefficient `1/12` of the downstream range equation is computed
  against `D`, not against the unit-period derivative.
* "Pointwise value in `PH α 0`" is read as equality of the underlying functions of
  `ell f : PH α 0` (the `PH.val`), plus the `PH.mk` form.
* `PH.val` of the element of `PH.orthSub α 2` is read through the coercion `(u : PH α 2)`.
-/

open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Frontier.EX012

/-- Angular derivative `D = (2π)⁻¹ ∂_x` of a function of the unit-period variable. -/
noncomputable def angDerivFun_EX01237 (g : ℝ → ℝ) : ℝ → ℝ := (2 * Real.pi)⁻¹ • deriv g

theorem kappa_inv_eq_EX01237 : kappa⁻¹ = ((2 * Real.pi) ^ 2)⁻¹ := rfl

theorem ellFun_apply_EX01237 (u : ℝ → ℝ) (x : ℝ) :
    ellFun u x = ((2 * Real.pi) ^ 2)⁻¹ * deriv (deriv u) x + u x := by
  simp [ellFun, kappa]

theorem ellFun_eq_angDerivFun_EX01237 {u : ℝ → ℝ} (hu : Differentiable ℝ (deriv u)) (x : ℝ) :
    ellFun u x = angDerivFun_EX01237 (angDerivFun_EX01237 u) x + u x := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h : deriv (angDerivFun_EX01237 u) = (2 * Real.pi)⁻¹ • deriv (deriv u) := by
    unfold angDerivFun_EX01237
    ext y
    exact deriv_const_smul _ (hu y)
  rw [ellFun_apply_EX01237]
  unfold angDerivFun_EX01237 at h ⊢
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [h]
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp

/-- **EX012.37.**  For every `f : PH α 2`, `ComplementaryElliptic.ell f` has pointwise value
`(2π)^(-2) f'' + f`. -/
theorem gate_ex012_37_angular_elliptic_operator_definition_gate {α : ℝ} [HolderExponent α]
    (f : PH α 2) (x : ℝ) :
    (ell f).val x = ((2 * Real.pi) ^ 2)⁻¹ * deriv (deriv f.val) x + f.val x := by
  rw [ell_val]
  exact ellFun_apply_EX01237 f.val x

theorem gate_ex012_37_angular_elliptic_operator_definition_gate_fun {α : ℝ} [HolderExponent α]
    (f : PH α 2) :
    (ell f).val = ((2 * Real.pi) ^ 2)⁻¹ • deriv (deriv f.val) + f.val := by
  funext x
  simpa using gate_ex012_37_angular_elliptic_operator_definition_gate f x

theorem gate_ex012_37_angular_elliptic_operator_definition_gate_mk {α : ℝ} [HolderExponent α]
    (f : PH α 2) :
    ell f = PH.mk (fun x => ((2 * Real.pi) ^ 2)⁻¹ * deriv (deriv f.val) x + f.val x)
      (by
        have h := isPH_ellFun f.isPH
        have e : ellFun f.val =
            fun x => ((2 * Real.pi) ^ 2)⁻¹ * deriv (deriv f.val) x + f.val x :=
          funext (ellFun_apply_EX01237 f.val)
        rwa [e] at h) := by
  apply PH.ext
  funext x
  simpa using gate_ex012_37_angular_elliptic_operator_definition_gate f x

theorem gate_ex012_37_angular_elliptic_operator_definition_gate_angular {α : ℝ}
    [HolderExponent α] (f : PH α 2) (x : ℝ) :
    (ell f).val x =
      angDerivFun_EX01237 (angDerivFun_EX01237 f.val) x + f.val x := by
  rw [ell_val]
  exact ellFun_eq_angDerivFun_EX01237 f.isPH.2.2.2.1 x

theorem gate_ex012_37_angular_elliptic_operator_definition_gate_equiv {α : ℝ}
    [HolderExponent α] (u : PH.orthSub α 2) (x : ℝ) :
    ((ellEquiv u : PH.orthSub α 0) : PH α 0).val x =
      ((2 * Real.pi) ^ 2)⁻¹ * deriv (deriv (u : PH α 2).val) x + (u : PH α 2).val x := by
  rw [ellEquiv_apply]
  exact gate_ex012_37_angular_elliptic_operator_definition_gate u.1 x

theorem gate_ex012_37_angular_elliptic_operator_definition_gate_fou018 {α : ℝ}
    [HolderExponent α] :
    ∃ e : PH.orthSub α 2 ≃L[ℝ] PH.orthSub α 0,
      ∀ (u : PH.orthSub α 2) (x : ℝ),
        ((e u : PH.orthSub α 0) : PH α 0).val x =
          ((2 * Real.pi) ^ 2)⁻¹ * deriv (deriv (u : PH α 2).val) x + (u : PH α 2).val x := by
  obtain ⟨⟨e, he, _⟩, _⟩ := DGPS.Analysis.complementary_circle_elliptic_inverse α
  refine ⟨e, fun u x => ?_⟩
  rw [he]
  exact gate_ex012_37_angular_elliptic_operator_definition_gate u.1 x

end DGPS.Frontier.EX012
