import DGPS.Analysis.PeriodicHolder

/-!
# EX012.27: Bounded multiplication

Task id: EX012.27 (node EX012, one-site complementary range equation).
Title: Bounded multiplication.

Provides:
* `DGPS.Frontier.EX012.ex012_27_bounded_multiplication`: the continuous bilinear map
  `PH α 0 →L[ℝ] PH α 0 →L[ℝ] PH α 0` (the curried form of a continuous bilinear map on
  `PH α 0 × PH α 0`), with explicit exponent argument `α`.
* `DGPS.Frontier.EX012.ex012_27_bounded_multiplication_apply`: its value on `f g` is the ring
  product `f * g` in `PH α 0`.
* `DGPS.Frontier.EX012.ex012_27_bounded_multiplication_val`: its value is pointwise
  multiplication, `(m f g).val x = f.val x * g.val x`.
* `DGPS.Frontier.EX012.ex012_27_bounded_multiplication_bilinear`: additivity and homogeneity
  of the map in each argument, written out.
* `DGPS.Frontier.EX012.ex012_27_bounded_multiplication_comm`: symmetry `m f g = m g f`.
* `DGPS.Frontier.EX012.ex012_27_bounded_multiplication_bound`: the norm bound
  `‖m f g‖ ≤ C * (‖f‖ * ‖g‖)` with `C = mulConst_EX01227 α`, the nonnegative constant supplied by
  FOU017 (`PH.mul_bound`), together with `0 ≤ C`.
* `DGPS.Frontier.EX012.ex012_27_bounded_multiplication_bound_exists`: the existential form of the
  bound, `∃ C, 0 ≤ C ∧ ∀ f g, ‖m f g‖ ≤ C * (‖f‖ * ‖g‖)`.
* Helpers (all suffixed `_EX01227`): `mulConst_EX01227` (the FOU017 constant, a choice from
  `PH.mul_bound`), `mulConst_nonneg_EX01227`, `mulLin_EX01227` (the bilinear map before
  bundling, built with `LinearMap.mk₂`), `mulLin_apply_EX01227`, `mulBound_EX01227` (the bound for
  the unbundled map).

R5 notes:
* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`, inherited from
  FOU017. No further hypothesis is added. The multiplication is the ring multiplication of
  `PH α 0` (the subalgebra of pointwise products, FOU017), so "value is pointwise multiplication"
  is proved by `rfl` on the underlying functions.
* "Continuous bilinear map from `PH α 0 × PH α 0` into `PH α 0`" is realised as the curried
  continuous bilinear map `PH α 0 →L[ℝ] PH α 0 →L[ℝ] PH α 0`, the standard Mathlib encoding of
  continuous bilinear maps. The uncurried product-domain form is not separately stated.
* "State its bound with the nonnegative constant supplied by FOU017" is read as: the constant is
  the one produced by `PH.mul_bound α 0` (a choice `C ≥ 0` with `‖f * g‖ ≤ C * (‖f‖ * ‖g‖)`), not
  the rescaled constant `PH.scale`, and not a constant one. No normed-algebra instance with
  multiplication constant one is required or used.
* The constant `mulConst_EX01227 α` is defined by `Exists.choose`, so its value is not specified
  beyond the bound and nonnegativity that FOU017 supplies; the bound lemma is stated for that
  constant and the existential form does not depend on the choice.
* "Prove symmetry" is read as commutativity of the bilinear map, `m f g = m g f` as elements of
  `PH α 0`, from commutativity of the commutative ring `PH α 0`.
* The bilinear map is built with `LinearMap.mk₂` and then `LinearMap.mkContinuous₂` using the
  bound from `PH.mul_bound`; the continuity is therefore the bound, not an assumption.
-/

open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.EX012

section Construction

variable (α : ℝ) [HolderExponent α]

/-- The constant supplied by FOU017's product bound `PH.mul_bound α 0` (a chosen witness). -/
noncomputable def mulConst_EX01227 : ℝ :=
  (PH.mul_bound α 0).choose

theorem mulConst_nonneg_EX01227 : 0 ≤ mulConst_EX01227 α :=
  (PH.mul_bound α 0).choose_spec.1

/-- The product bound with the constant `mulConst_EX01227 α`. -/
theorem mulBound_EX01227 (f g : PH α 0) :
    ‖f * g‖ ≤ mulConst_EX01227 α * ‖f‖ * ‖g‖ := by
  rw [mul_assoc]
  exact (PH.mul_bound α 0).choose_spec.2 f g

/-- The multiplication of `PH α 0` as a bilinear map over `ℝ`, before bundling continuity. -/
noncomputable def mulLin_EX01227 : PH α 0 →ₗ[ℝ] PH α 0 →ₗ[ℝ] PH α 0 :=
  LinearMap.mk₂ ℝ (fun f g : PH α 0 => f * g)
    (fun f₁ f₂ g => add_mul f₁ f₂ g)
    (fun c f g => smul_mul_assoc c f g)
    (fun f g₁ g₂ => mul_add f g₁ g₂)
    (fun c f g => mul_smul_comm c f g)

theorem mulLin_apply_EX01227 (f g : PH α 0) : mulLin_EX01227 α f g = f * g := rfl

/-- The continuous bilinear multiplication `PH α 0 × PH α 0 → PH α 0` (pointwise product). -/
noncomputable def ex012_27_bounded_multiplication : PH α 0 →L[ℝ] PH α 0 →L[ℝ] PH α 0 :=
  (mulLin_EX01227 α).mkContinuous₂ (mulConst_EX01227 α) (fun f g => mulBound_EX01227 α f g)

theorem ex012_27_bounded_multiplication_apply (f g : PH α 0) :
    ex012_27_bounded_multiplication α f g = f * g := rfl

/-- The value of the multiplication is the pointwise product of the underlying functions. -/
theorem ex012_27_bounded_multiplication_val (f g : PH α 0) (x : ℝ) :
    (ex012_27_bounded_multiplication α f g).val x = f.val x * g.val x := rfl

/-- Additivity and homogeneity of the multiplication in each argument. -/
theorem ex012_27_bounded_multiplication_bilinear :
    (∀ f₁ f₂ g : PH α 0,
        ex012_27_bounded_multiplication α (f₁ + f₂) g =
          ex012_27_bounded_multiplication α f₁ g + ex012_27_bounded_multiplication α f₂ g) ∧
    (∀ (c : ℝ) (f g : PH α 0),
        ex012_27_bounded_multiplication α (c • f) g = c • ex012_27_bounded_multiplication α f g) ∧
    (∀ f g₁ g₂ : PH α 0,
        ex012_27_bounded_multiplication α f (g₁ + g₂) =
          ex012_27_bounded_multiplication α f g₁ + ex012_27_bounded_multiplication α f g₂) ∧
    (∀ (c : ℝ) (f g : PH α 0),
        ex012_27_bounded_multiplication α f (c • g) = c • ex012_27_bounded_multiplication α f g) := by
  refine ⟨fun f₁ f₂ g => ?_, fun c f g => ?_, fun f g₁ g₂ => ?_, fun c f g => ?_⟩
  · simp only [map_add, add_apply]
  · simp only [map_smul, smul_apply]
  · simp only [map_add]
  · simp only [map_smul]

/-- Symmetry: the multiplication is commutative. -/
theorem ex012_27_bounded_multiplication_comm (f g : PH α 0) :
    ex012_27_bounded_multiplication α f g = ex012_27_bounded_multiplication α g f := by
  rw [ex012_27_bounded_multiplication_apply, ex012_27_bounded_multiplication_apply]
  exact mul_comm f g

/-- The norm bound for the multiplication, with the nonnegative constant from FOU017. -/
theorem ex012_27_bounded_multiplication_bound :
    0 ≤ mulConst_EX01227 α ∧
      ∀ f g : PH α 0,
        ‖ex012_27_bounded_multiplication α f g‖ ≤ mulConst_EX01227 α * (‖f‖ * ‖g‖) := by
  refine ⟨mulConst_nonneg_EX01227 α, fun f g => ?_⟩
  rw [ex012_27_bounded_multiplication_apply, ← mul_assoc]
  exact mulBound_EX01227 α f g

/-- The existential form of the norm bound. -/
theorem ex012_27_bounded_multiplication_bound_exists :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ f g : PH α 0, ‖ex012_27_bounded_multiplication α f g‖ ≤ C * (‖f‖ * ‖g‖) :=
  ⟨mulConst_EX01227 α, ex012_27_bounded_multiplication_bound α⟩

end Construction

end DGPS.Frontier.EX012
