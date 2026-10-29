import DGPS.Analysis.PeriodicHolder

/-!
# EX012.24: Bounded angular first derivative

Task id: EX012.24 (node EX012, one-site complementary range equation).
Title: Bounded angular first derivative.

Provides:
* `DGPS.Frontier.EX012.ex012_24_bounded_angular_first_derivative`: there is a continuous linear
  map `D : PH α 2 →L[ℝ] PH α 0` whose value is `(D f).val x = (2π)⁻¹ * deriv f.val x`, with
  `‖D f‖ ≤ 3 / (2π) * ‖f‖`, and whose value `(D f).val` is `1`-periodic and additive/homogeneous
  in `f`.
* `DGPS.Frontier.EX012.ex012_24_bounded_angular_first_derivative_val`: for the constructed map
  `angDeriv_EX01224`, the pointwise formula `(angDeriv_EX01224 f).val x = (2π)⁻¹ * deriv f.val x`.
* `DGPS.Frontier.EX012.ex012_24_bounded_angular_first_derivative_norm`: the norm bound
  `‖angDeriv_EX01224 f‖ ≤ 3 / (2π) * ‖f‖`.
* `DGPS.Frontier.EX012.ex012_24_bounded_angular_first_derivative_periodic`: the value of
  `angDeriv_EX01224 f` is `1`-periodic.
* `DGPS.Frontier.EX012.ex012_24_bounded_angular_first_derivative_add` and
  `DGPS.Frontier.EX012.ex012_24_bounded_angular_first_derivative_smul`: the value is additive and
  homogeneous in `f`, as functions.

R5 notes:
* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`.
* The specification's `f'` with `D = (2π)⁻¹ ∂_x` is read as `deriv f.val` in the unit-period
  variable `x`; the factor `(2π)⁻¹` converts to the angular variable.
* The Hölder seminorm of FOU017 (`holderSeminorm`) is the global one on `ℝ × ℝ`, with the
  Euclidean distance `|x - y|`, not a periodic quotient distance. So the two-distance estimate
  (`|x - y| ≤ 1` by the mean value bound, `|x - y| ≥ 1` by `2 ‖f'‖∞`) is used as stated; it is
  already provided by `holderSeminorm_le_succ` and `phNorm_le_succ` of FOU017, which are reused
  here (no periodic-distance variant is needed).
* The bound in the specification is `‖D f‖ ≤ 3/(2π) ‖f‖`; it is proved with the norm of `f` in
  `PH α 2`, as `phNorm 0 f' ≤ phNorm 1 f ≤ 3 phNorm 2 f`.
* "Construct `D`" is stated as an existence statement together with the named construction
  `angDeriv_EX01224`; the "value" clause is the pointwise formula on `PH.val`.
* "Linearity of its value" is stated at the level of the underlying functions (`val`), and
  periodicity is the `Function.Periodic _ 1` statement.
-/

open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.EX012

section

variable {α : ℝ} [HolderExponent α]

/-- The underlying function of the angular derivative: `(2π)⁻¹ • deriv f`. -/
noncomputable def angDerivFun_EX01224 (f : ℝ → ℝ) : ℝ → ℝ := (2 * Real.pi)⁻¹ • deriv f

omit [HolderExponent α] in
theorem angDerivFun_EX01224_apply (f : ℝ → ℝ) (x : ℝ) :
    angDerivFun_EX01224 f x = (2 * Real.pi)⁻¹ * deriv f x := rfl

theorem isPH_angDerivFun_EX01224 {f : ℝ → ℝ} (h : IsPH α 2 f) :
    IsPH α 0 (angDerivFun_EX01224 f) :=
  IsPH.smul _ (IsPH.of_succ (HolderExponent.pos (α := α)).le
    (HolderExponent.lt_one (α := α)).le h.2.2)

omit [HolderExponent α] in
theorem angDerivFun_EX01224_add {f g : ℝ → ℝ} (hf : IsPH α 2 f) (hg : IsPH α 2 g) :
    angDerivFun_EX01224 (f + g) = angDerivFun_EX01224 f + angDerivFun_EX01224 g := by
  ext x
  simp only [angDerivFun_EX01224_apply, Pi.add_apply]
  rw [deriv_add (hf.2.1 x) (hg.2.1 x)]
  ring

omit [HolderExponent α] in
theorem angDerivFun_EX01224_smul (c : ℝ) {f : ℝ → ℝ} (hf : IsPH α 2 f) :
    angDerivFun_EX01224 (c • f) = c • angDerivFun_EX01224 f := by
  ext x
  simp only [angDerivFun_EX01224_apply, Pi.smul_apply, smul_eq_mul]
  rw [deriv_const_smul c (hf.2.1 x)]
  simp only [smul_eq_mul]
  ring

omit [HolderExponent α] in
theorem angDerivFun_EX01224_periodic {f : ℝ → ℝ} (hf : IsPH α 2 f) :
    Function.Periodic (angDerivFun_EX01224 f) 1 := by
  intro x
  rw [angDerivFun_EX01224_apply, angDerivFun_EX01224_apply]
  rw [(periodic_deriv hf.1) x]

theorem phNorm_angDerivFun_EX01224_le {f : ℝ → ℝ} (h : IsPH α 2 f) :
    phNorm α 0 (angDerivFun_EX01224 f) ≤ (2 * Real.pi)⁻¹ * (3 * phNorm α 2 f) := by
  have hα0 := (HolderExponent.pos (α := α)).le
  have hα1 := (HolderExponent.lt_one (α := α)).le
  have h1 : phNorm α 1 f ≤ 3 * phNorm α 2 f := phNorm_le_succ hα0 hα1 h
  have h2 : phNorm α 0 (deriv f) ≤ phNorm α 1 f := by
    have := supNorm_nonneg f
    simp only [phNorm]; linarith
  have h3 := phNorm_smul_le (α := α) (2 * Real.pi)⁻¹
    (IsPH.of_succ hα0 hα1 h.2.2)
  have hk : |(2 * Real.pi)⁻¹| = (2 * Real.pi)⁻¹ := abs_of_pos (by positivity)
  rw [hk] at h3
  have h4 : (0 : ℝ) ≤ (2 * Real.pi)⁻¹ := by positivity
  unfold angDerivFun_EX01224
  nlinarith

/-- The angular first derivative `D = (2π)⁻¹ ∂_x : PH α 2 →L[ℝ] PH α 0`. -/
noncomputable def angDeriv_EX01224 : PH α 2 →L[ℝ] PH α 0 :=
  LinearMap.mkContinuous
    { toFun := fun f => PH.mk (angDerivFun_EX01224 f.val) (isPH_angDerivFun_EX01224 f.isPH)
      map_add' := fun f g => PH.ext (angDerivFun_EX01224_add f.isPH g.isPH)
      map_smul' := fun c f => PH.ext (angDerivFun_EX01224_smul c f.isPH) }
    (3 / (2 * Real.pi)) (fun f => by
      show phNorm α 0 (angDerivFun_EX01224 f.val) ≤ 3 / (2 * Real.pi) * phNorm α 2 f.val
      have := phNorm_angDerivFun_EX01224_le f.isPH
      calc _ ≤ _ := this
        _ = _ := by ring)

theorem angDeriv_EX01224_val (f : PH α 2) :
    (angDeriv_EX01224 f).val = angDerivFun_EX01224 f.val := rfl

/-- Pointwise value of the angular derivative: `(D f)(x) = (2π)⁻¹ f'(x)`. -/
theorem ex012_24_bounded_angular_first_derivative_val (f : PH α 2) (x : ℝ) :
    (angDeriv_EX01224 f).val x = (2 * Real.pi)⁻¹ * deriv f.val x := rfl

/-- The norm bound `‖D f‖ ≤ 3/(2π) ‖f‖`. -/
theorem ex012_24_bounded_angular_first_derivative_norm (f : PH α 2) :
    ‖angDeriv_EX01224 f‖ ≤ 3 / (2 * Real.pi) * ‖f‖ := by
  have := phNorm_angDerivFun_EX01224_le f.isPH
  rw [PH.norm_def, PH.norm_def, angDeriv_EX01224_val]
  calc _ ≤ _ := this
    _ = _ := by ring

/-- The value of `D f` is `1`-periodic. -/
theorem ex012_24_bounded_angular_first_derivative_periodic (f : PH α 2) :
    Function.Periodic (angDeriv_EX01224 f).val 1 :=
  (angDeriv_EX01224 f).isPH.periodic

/-- The value of `D` is additive in `f`. -/
theorem ex012_24_bounded_angular_first_derivative_add (f g : PH α 2) :
    (angDeriv_EX01224 (f + g)).val = (angDeriv_EX01224 f).val + (angDeriv_EX01224 g).val :=
  angDerivFun_EX01224_add f.isPH g.isPH

/-- The value of `D` is homogeneous in `f`. -/
theorem ex012_24_bounded_angular_first_derivative_smul (c : ℝ) (f : PH α 2) :
    (angDeriv_EX01224 (c • f)).val = c • (angDeriv_EX01224 f).val :=
  angDerivFun_EX01224_smul c f.isPH

/-- **EX012.24.**  There is a bounded linear map `D : PH α 2 →L[ℝ] PH α 0` with value
`(2π)⁻¹ f'`, norm bound `‖D f‖ ≤ 3/(2π) ‖f‖`, and `1`-periodic, additive and homogeneous
values. -/
theorem ex012_24_bounded_angular_first_derivative :
    ∃ D : PH α 2 →L[ℝ] PH α 0,
      (∀ (f : PH α 2) (x : ℝ), (D f).val x = (2 * Real.pi)⁻¹ * deriv f.val x) ∧
      (∀ f : PH α 2, ‖D f‖ ≤ 3 / (2 * Real.pi) * ‖f‖) ∧
      (∀ f : PH α 2, Function.Periodic (D f).val 1) ∧
      (∀ f g : PH α 2, (D (f + g)).val = (D f).val + (D g).val) ∧
      (∀ (c : ℝ) (f : PH α 2), (D (c • f)).val = c • (D f).val) :=
  ⟨angDeriv_EX01224, ex012_24_bounded_angular_first_derivative_val,
    ex012_24_bounded_angular_first_derivative_norm,
    ex012_24_bounded_angular_first_derivative_periodic,
    ex012_24_bounded_angular_first_derivative_add,
    ex012_24_bounded_angular_first_derivative_smul⟩

end

end DGPS.Frontier.EX012
