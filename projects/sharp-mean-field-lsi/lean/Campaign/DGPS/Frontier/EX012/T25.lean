import DGPS.Frontier.EX012.T37

/-!
# EX012.25: Inclusion, second derivative, and elliptic compatibility

Task id: EX012.25 (node EX012, one-site complementary range equation).
Title: Inclusion, second derivative, and elliptic compatibility.

Provides:
* `DGPS.Frontier.EX012.ex012_25_inclusion_second_derivative_elliptic_compatibility_incl`: the
  inclusion `ι : PH α 2 →L[ℝ] PH α 0`, `(ι f).val = f.val`.
* `DGPS.Frontier.EX012.ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv`:
  the angular second derivative `D² : PH α 2 →L[ℝ] PH α 0`,
  `(D² f).val = ((2π)^2)⁻¹ • deriv (deriv f.val)`, i.e. `D = (2π)⁻¹ ∂ₓ` applied twice.
* `DGPS.Frontier.EX012.ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_val`:
  pointwise formula `(ι f).val x = f.val x`.
* `DGPS.Frontier.EX012.ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_val`:
  pointwise formula `(D² f).val x = ((2π)^2)⁻¹ * deriv (deriv f.val) x`.
* `DGPS.Frontier.EX012.ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_angular`:
  `(D² f).val x = D (D f.val) x` for the angular derivative `D = (2π)⁻¹ ∂ₓ` of T37.
* `DGPS.Frontier.EX012.ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_norm_le`:
  `‖ι f‖ ≤ 3 * ‖f‖`.
* `DGPS.Frontier.EX012.ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_norm_le`:
  `‖D² f‖ ≤ ((2π)^2)⁻¹ * ‖f‖`.
* `DGPS.Frontier.EX012.ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_opNorm_le`:
  operator-norm form `‖ι‖ ≤ 3`.
* `DGPS.Frontier.EX012.ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_opNorm_le`:
  operator-norm form `‖D²‖ ≤ ((2π)^2)⁻¹`.
* `DGPS.Frontier.EX012.ex012_25_inclusion_second_derivative_elliptic_compatibility_ell_eq`:
  `ComplementaryElliptic.ell f = D² f + ι f` in `PH α 0`.
* `DGPS.Frontier.EX012.ex012_25_inclusion_second_derivative_elliptic_compatibility_orth`:
  for `u : PH.orthSub α 2`, `D² u + ι u ∈ PH.orthSub α 0` and
  `(ComplementaryElliptic.ellEquiv u : PH α 0) = D² u + ι u`.
* `DGPS.Frontier.EX012.ex012_25_inclusion_second_derivative_elliptic_compatibility`: the main
  statement, a conjunction of the pointwise formulas, the two norm bounds, `ell f = D² f + ι f`,
  the restriction `W → Y` of `D² + ι`, and its agreement with the FOU018 equivalence.

R5 notes:
* No hypothesis is added beyond `[HolderExponent α]`, the campaign form of `0 < α < 1`.
* The angular scale is kept visible: `D² f` is `((2π)^2)⁻¹ • deriv (deriv f.val)`, with `deriv`
  taken in the unit-period variable `x`, so that `(2π)^(-2)` of the specification is
  `((2 * Real.pi) ^ 2)⁻¹ = ComplementaryElliptic.kappa⁻¹` (definitional, T37 `kappa_inv_eq_EX01237`).
  The angular reading `D = (2π)⁻¹ ∂ₓ` is stated separately (`_secondDeriv_angular`).
* "Bounded maps" is read as continuous linear maps `PH α 2 →L[ℝ] PH α 0`, built with
  `LinearMap.mkContinuous` (the packaging identifier was marked unverified in the specification;
  it was checked by compilation). The norm bounds are stated both pointwise (`‖ι f‖ ≤ 3 ‖f‖`)
  and as operator norms.
* The constant `3` for `ι` is proved directly (`[f]_α ≤ ‖f'‖∞ + 2 ‖f‖∞` from a Lipschitz bound
  and a sup bound, then `‖ι f‖ ≤ 3 ‖f‖∞ + ‖f'‖∞ ≤ 3 ‖f‖_{2,α}`), not by composing the two
  steps `C²,α → C¹,α → C⁰,α`, which would only give the constant `9`.
* "Its codomain is `Y`" is read as: for `u ∈ W = PH.orthSub α 2`, the element `D² u + ι u` of
  `PH α 0` lies in `Y = PH.orthSub α 0`. "The equivalence chosen from FOU018" is read both as the
  campaign's `ComplementaryElliptic.ellEquiv` and as the existential `e` delivered by
  `DGPS.Analysis.complementary_circle_elliptic_inverse`; both agree with `D² + ι` on `W`.
* `PH.val` of an element of `PH.orthSub α k` is read through the coercion to `PH α k`.
* The task text says the elliptic equality is a definition check; it is proved from the T37 gate
  `gate_ex012_37_angular_elliptic_operator_definition_gate_fun` (no normalization assumed).
-/

open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Frontier.EX012

section Maps

variable {α : ℝ} [HolderExponent α]

theorem phNorm_incl_le_EX01225 {u : ℝ → ℝ} (h : IsPH α 2 u) :
    phNorm α 0 u ≤ 3 * phNorm α 2 u := by
  have hα0 := (HolderExponent.pos (α := α)).le
  have hα1 := (HolderExponent.lt_one (α := α)).le
  have h1 : IsPH α 1 u := IsPH.of_succ hα0 hα1 h
  have hb : Bdd u := h.bdd
  have hb' : Bdd (deriv u) := h1.2.2.bdd
  have e1 := holderSeminorm_le_succ hα0 hα1 h.2.1 hb hb'
  have e2 := supNorm_nonneg u
  have e3 := supNorm_nonneg (deriv u)
  have e4 := phNorm_nonneg (α := α) 0 (deriv (deriv u))
  simp only [phNorm] at e4 ⊢
  linarith

omit [HolderExponent α] in
theorem phNorm_secondDeriv_le_EX01225 {u : ℝ → ℝ} (h : IsPH α 2 u) :
    phNorm α 0 (kappa⁻¹ • deriv (deriv u)) ≤ kappa⁻¹ * phNorm α 2 u := by
  have e4 := phNorm_smul_le kappa⁻¹ (isPH_deriv_deriv h)
  have hk : |kappa⁻¹| = kappa⁻¹ := abs_of_pos (inv_pos.mpr kappa_pos)
  have e5 : phNorm α 0 (deriv (deriv u)) ≤ phNorm α 2 u := by
    have := supNorm_nonneg u
    have := supNorm_nonneg (deriv u)
    simp only [phNorm]; linarith
  rw [hk] at e4
  have e7 : 0 ≤ kappa⁻¹ := (inv_pos.mpr kappa_pos).le
  nlinarith

/-- The inclusion `ι : C^{2,α} → C^{0,α}` as a bounded linear map; `(ι f).val = f.val`. -/
noncomputable def ex012_25_inclusion_second_derivative_elliptic_compatibility_incl :
    PH α 2 →L[ℝ] PH α 0 :=
  LinearMap.mkContinuous
    { toFun := fun f => PH.mk f.val (isPH_of_two f.isPH)
      map_add' := fun _ _ => PH.ext rfl
      map_smul' := fun _ _ => PH.ext rfl }
    3 (fun f => by
      show phNorm α 0 f.val ≤ 3 * phNorm α 2 f.val
      exact phNorm_incl_le_EX01225 f.isPH)

/-- The angular second derivative `D² = ((2π)^2)⁻¹ ∂ₓ²` as a bounded linear map
`C^{2,α} → C^{0,α}`. -/
noncomputable def ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv :
    PH α 2 →L[ℝ] PH α 0 :=
  LinearMap.mkContinuous
    { toFun := fun f => PH.mk (kappa⁻¹ • deriv (deriv f.val))
        (IsPH.smul _ (isPH_deriv_deriv f.isPH))
      map_add' := fun f g => PH.ext (by
        show kappa⁻¹ • deriv (deriv (f.val + g.val)) =
          kappa⁻¹ • deriv (deriv f.val) + kappa⁻¹ • deriv (deriv g.val)
        rw [deriv_add_fun f.isPH.2.1 g.isPH.2.1,
          deriv_add_fun f.isPH.2.2.2.1 g.isPH.2.2.2.1, smul_add])
      map_smul' := fun c f => PH.ext (by
        show kappa⁻¹ • deriv (deriv (c • f.val)) = c • (kappa⁻¹ • deriv (deriv f.val))
        rw [deriv_smul_fun c f.isPH.2.1, deriv_smul_fun c f.isPH.2.2.2.1, smul_comm]) }
    kappa⁻¹ (fun f => by
      show phNorm α 0 (kappa⁻¹ • deriv (deriv f.val)) ≤ kappa⁻¹ * phNorm α 2 f.val
      exact phNorm_secondDeriv_le_EX01225 f.isPH)

theorem ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_val (f : PH α 2)
    (x : ℝ) :
    (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f).val x = f.val x := rfl

theorem ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_val
    (f : PH α 2) (x : ℝ) :
    (ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv f).val x =
      ((2 * Real.pi) ^ 2)⁻¹ * deriv (deriv f.val) x := rfl

theorem ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_norm_le
    (f : PH α 2) :
    ‖ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f‖ ≤ 3 * ‖f‖ :=
  ContinuousLinearMap.le_of_opNorm_le _ (by
    refine LinearMap.mkContinuous_norm_le _ (by norm_num) _) f

theorem ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_norm_le
    (f : PH α 2) :
    ‖ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv f‖ ≤
      ((2 * Real.pi) ^ 2)⁻¹ * ‖f‖ :=
  ContinuousLinearMap.le_of_opNorm_le _ (by
    refine LinearMap.mkContinuous_norm_le _ (inv_pos.mpr kappa_pos).le _) f

theorem ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_opNorm_le :
    ‖(ex012_25_inclusion_second_derivative_elliptic_compatibility_incl : PH α 2 →L[ℝ] PH α 0)‖
      ≤ 3 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_opNorm_le :
    ‖(ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv :
        PH α 2 →L[ℝ] PH α 0)‖ ≤ ((2 * Real.pi) ^ 2)⁻¹ :=
  LinearMap.mkContinuous_norm_le _ (inv_pos.mpr kappa_pos).le _

theorem ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_angular
    (f : PH α 2) (x : ℝ) :
    (ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv f).val x =
      angDerivFun_EX01237 (angDerivFun_EX01237 f.val) x := by
  have h := ellFun_eq_angDerivFun_EX01237 f.isPH.2.2.2.1 x
  rw [ellFun_apply_EX01237] at h
  rw [ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_val]
  linarith

theorem ex012_25_inclusion_second_derivative_elliptic_compatibility_ell_eq (f : PH α 2) :
    ell f = ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv f +
      ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f := by
  refine PH.ext (funext fun x => ?_)
  rw [gate_ex012_37_angular_elliptic_operator_definition_gate f x, PH.val_add]
  rfl

theorem ex012_25_inclusion_second_derivative_elliptic_compatibility_orth
    (u : PH.orthSub α 2) :
    ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv (u : PH α 2) +
        ex012_25_inclusion_second_derivative_elliptic_compatibility_incl (u : PH α 2) ∈
      PH.orthSub α 0 ∧
    ((ellEquiv u : PH.orthSub α 0) : PH α 0) =
      ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv (u : PH α 2) +
        ex012_25_inclusion_second_derivative_elliptic_compatibility_incl (u : PH α 2) := by
  have h : ((ellEquiv u : PH.orthSub α 0) : PH α 0) =
      ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv (u : PH α 2) +
        ex012_25_inclusion_second_derivative_elliptic_compatibility_incl (u : PH α 2) := by
    rw [ellEquiv_apply]
    exact ex012_25_inclusion_second_derivative_elliptic_compatibility_ell_eq u.1
  exact ⟨h ▸ (ellEquiv u).2, h⟩

/-- **EX012.25.**  The inclusion `ι` and the angular second derivative `D²` are bounded maps
`PH α 2 → PH α 0` with the stated pointwise formulas and norm bounds, `ell f = D² f + ι f`, and
on `W = PH.orthSub α 2` the map `D² + ι` takes values in `Y = PH.orthSub α 0` and agrees with
the equivalence of FOU018. -/
theorem ex012_25_inclusion_second_derivative_elliptic_compatibility :
    (∀ (f : PH α 2) (x : ℝ),
      (ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f).val x = f.val x) ∧
    (∀ (f : PH α 2) (x : ℝ),
      (ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv f).val x =
        ((2 * Real.pi) ^ 2)⁻¹ * deriv (deriv f.val) x) ∧
    (∀ f : PH α 2,
      ‖ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f‖ ≤ 3 * ‖f‖) ∧
    (∀ f : PH α 2,
      ‖ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv f‖ ≤
        ((2 * Real.pi) ^ 2)⁻¹ * ‖f‖) ∧
    (∀ f : PH α 2,
      ell f = ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv f +
        ex012_25_inclusion_second_derivative_elliptic_compatibility_incl f) ∧
    (∀ u : PH.orthSub α 2,
      ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv (u : PH α 2) +
          ex012_25_inclusion_second_derivative_elliptic_compatibility_incl (u : PH α 2) ∈
        PH.orthSub α 0) ∧
    (∀ u : PH.orthSub α 2,
      ((ellEquiv u : PH.orthSub α 0) : PH α 0) =
        ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv (u : PH α 2) +
          ex012_25_inclusion_second_derivative_elliptic_compatibility_incl (u : PH α 2)) ∧
    (∃ e : PH.orthSub α 2 ≃L[ℝ] PH.orthSub α 0,
      ∀ u : PH.orthSub α 2,
        ((e u : PH.orthSub α 0) : PH α 0) = ell (u : PH α 2) ∧
        ((e u : PH.orthSub α 0) : PH α 0) =
          ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv
              (u : PH α 2) +
            ex012_25_inclusion_second_derivative_elliptic_compatibility_incl (u : PH α 2)) := by
  refine ⟨fun f x => rfl, fun f x => rfl,
    ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_norm_le,
    ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_norm_le,
    ex012_25_inclusion_second_derivative_elliptic_compatibility_ell_eq,
    fun u => (ex012_25_inclusion_second_derivative_elliptic_compatibility_orth u).1,
    fun u => (ex012_25_inclusion_second_derivative_elliptic_compatibility_orth u).2, ?_⟩
  obtain ⟨⟨e, he, _⟩, _⟩ := DGPS.Analysis.complementary_circle_elliptic_inverse α
  exact ⟨e, fun u => ⟨he u, (he u).trans
    (ex012_25_inclusion_second_derivative_elliptic_compatibility_ell_eq u.1)⟩⟩

end Maps

end DGPS.Frontier.EX012
