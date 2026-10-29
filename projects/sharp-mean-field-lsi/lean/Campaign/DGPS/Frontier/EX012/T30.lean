import DGPS.Frontier.EX012.T29

/-!
# EX012.30: Equality with the projected residual

Task id: EX012.30 (node EX012, one-site complementary range equation).
Title: Equality with the projected residual.

Provides:
* `DGPS.Frontier.EX012.ex012_30_equality_projected_residual`: the main statement. For all real
  `a b τ` and `w : PH.orthSub α 2`,
  `rangeMap_EX01229 α ((a, b, τ), w) = proj_EX01226 α 0 (residual_EX01230 α (f + w) τ)`
  where `f = harmInj_EX01228 α 2 (a, b) = a c₁ + b s₁`; that is `F((a,b,τ),w) = Q₀ R(a c₁ + b s₁ + w, τ)`.
* `DGPS.Frontier.EX012.ex012_30_equality_projected_residual_residual_val`: the pointwise formula
  of the residual,
  `(R(v,τ)).val x = ((2π)^2)⁻¹ v''(x) + v(x) + (1/2) ((D v)(x)^2 - ∫₀¹ (D v)^2) + (τ/4) cos(2π·2·x)`.
* `DGPS.Frontier.EX012.ex012_30_equality_projected_residual_harmonic`: `D² f + ι f = 0` for the
  first harmonics `f = a c₁ + b s₁`, in `PH α 0`.
* `DGPS.Frontier.EX012.ex012_30_equality_projected_residual_linear`: for `w : PH.orthSub α 2`,
  `Q₀ (D² w + ι w) = L w` (with `L = ComplementaryElliptic.ellEquiv`).
* Helpers (all suffixed `_EX01230`): `residual_EX01230` (the frozen residual
  `R(v, τ) = D² v + v + (1/2)((D v)^2 - ∫ (D v)^2) + (τ/4) c₂ : PH α 2 → ℝ → PH α 0`),
  `incl_cosMode_EX01230`, `incl_sinMode_EX01230` (the inclusion fixes the first harmonics),
  `harmonic_ell_EX01230` (`D² f + ι f = 0`), `ell_proj_EX01230` (`Q₀ (D² w + ι w) = L w`),
  `proj_const_EX01230` (`Q₀` kills every constant), `residual_proj_EX01230` (expansion of
  `Q₀ R`).

R5 notes:
* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`. No further
  hypothesis is added; the statement is for all real `a b τ` and all `w`.
* The residual `R` is not defined in an earlier unit; it is defined here (`residual_EX01230`) from
  the frozen displayed formula
  `R(v,τ) = D²v + v + (1/2)((Dv)^2 - ∫(Dv)^2) + (τ/4) c₂` as an element of `PH α 0` for
  `v : PH α 2`: `D²` is the map of EX012.25, `v` is read through the inclusion `ι` of EX012.25,
  `D` is the map of EX012.24, the square is the diagonal of the bounded multiplication of
  EX012.27, `∫` is the Haar integral `∫₀¹` of the underlying function of `(Dv)^2`, taken as a
  constant element `(∫ ...) • 1` of `PH α 0`, and `c₂ = cosMode_EX01228 α 0 2`. The Haar
  integral of the frozen statement is read as `∫ x in 0..1`.
* "`Q₀`" is `proj_EX01226 α 0`, "`W`" is `PH.orthSub α 2`, "`Y`" is `PH.orthSub α 0`, "`F`" is
  `rangeMap_EX01229 α`, and "`a c₁ + b s₁`" is `harmInj_EX01228 α 2 (a, b)`; the argument of `R`
  is `f + (w : PH α 2)` with the subtype coercion, which is the coercion between `PH α 2` and
  its orthogonal subtype that the specification says this unit owns.
* The identities used are `D² c₁ + ι c₁ = 0`, `D² s₁ + ι s₁ = 0` (EX012.28), `D² w + ι w =
  L w` (EX012.25), `Q₀ 1 = 0` and `Q₀` fixes `Y` (EX012.26), and linearity of `D`.
-/

open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Frontier.EX012

section Construction

variable (α : ℝ) [HolderExponent α]

/-- The frozen residual `R(v, τ) = D² v + v + (1/2)((D v)^2 - ∫ (D v)^2) + (τ/4) c₂ ∈ PH α 0`
for `v ∈ PH α 2`. -/
noncomputable def residual_EX01230 (v : PH α 2) (τ : ℝ) : PH α 0 :=
  ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv v +
    ex012_25_inclusion_second_derivative_elliptic_compatibility_incl v +
    (1 / 2 : ℝ) •
      (ex012_27_bounded_multiplication α (angDeriv_EX01224 v) (angDeriv_EX01224 v) -
        (∫ x in (0 : ℝ)..1, ((angDeriv_EX01224 v).val x) ^ 2) • (1 : PH α 0)) +
    (τ / 4) • cosMode_EX01228 α 0 2

end Construction

section Helpers

variable {α : ℝ} [HolderExponent α]

theorem incl_cosMode_EX01230 (n : ℕ) :
    ex012_25_inclusion_second_derivative_elliptic_compatibility_incl (cosMode_EX01228 α 2 n) =
      cosMode_EX01228 α 0 n :=
  PH.ext (funext fun x => by
    rw [ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_val,
      cosMode_val_EX01228, cosMode_val_EX01228])

theorem incl_sinMode_EX01230 (n : ℕ) :
    ex012_25_inclusion_second_derivative_elliptic_compatibility_incl (sinMode_EX01228 α 2 n) =
      sinMode_EX01228 α 0 n :=
  PH.ext (funext fun x => by
    rw [ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_val,
      sinMode_val_EX01228, sinMode_val_EX01228])

theorem harmonic_ell_EX01230 (a b : ℝ) :
    ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv
        (harmInj_EX01228 α 2 (a, b)) +
      ex012_25_inclusion_second_derivative_elliptic_compatibility_incl
        (harmInj_EX01228 α 2 (a, b)) = 0 := by
  rw [harmInj_apply_EX01228]
  simp only [map_add, map_smul, secondDeriv_cosMode_EX01228, secondDeriv_sinMode_EX01228,
    incl_cosMode_EX01230, incl_sinMode_EX01230]
  simp only [smul_smul, Nat.cast_one, one_pow, neg_smul, mul_one, smul_neg]
  abel

theorem ell_proj_EX01230 (w : PH.orthSub α 2) :
    proj_EX01226 α 0
        (ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv (w : PH α 2) +
          ex012_25_inclusion_second_derivative_elliptic_compatibility_incl (w : PH α 2)) =
      ellEquiv w := by
  obtain ⟨hmem, heq⟩ := ex012_25_inclusion_second_derivative_elliptic_compatibility_orth w
  have h := ex012_26_projections_both_regularities_fixes 0 (⟨_, hmem⟩ : PH.orthSub α 0)
  rw [h]
  exact Subtype.ext heq.symm

theorem proj_const_EX01230 (c : ℝ) : proj_EX01226 α 0 (c • (1 : PH α 0)) = 0 := by
  rw [map_smul, (ex012_26_projections_both_regularities_kills 0).1, smul_zero]

theorem residual_proj_EX01230 (v : PH α 2) (τ : ℝ) :
    proj_EX01226 α 0 (residual_EX01230 α v τ) =
      proj_EX01226 α 0
          (ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv v +
            ex012_25_inclusion_second_derivative_elliptic_compatibility_incl v) +
        proj_EX01226 α 0
          ((1 / 2 : ℝ) •
              ex012_27_bounded_multiplication α (angDeriv_EX01224 v) (angDeriv_EX01224 v) +
            (τ / 4) • cosMode_EX01228 α 0 2) := by
  have hc := proj_const_EX01230 (α := α) (∫ x in (0 : ℝ)..1, ((angDeriv_EX01224 v).val x) ^ 2)
  simp only [residual_EX01230, smul_sub, map_add, map_sub, map_smul, hc, smul_zero, sub_zero]
  abel

end Helpers

section Main

variable (α : ℝ) [HolderExponent α]

/-- Pointwise formula of the residual. -/
theorem ex012_30_equality_projected_residual_residual_val (v : PH α 2) (τ x : ℝ) :
    (residual_EX01230 α v τ).val x =
      ((2 * Real.pi) ^ 2)⁻¹ * deriv (deriv v.val) x + v.val x +
        (1 / 2) * (((angDeriv_EX01224 v).val x) ^ 2 -
          ∫ y in (0 : ℝ)..1, ((angDeriv_EX01224 v).val y) ^ 2) +
        τ / 4 * Real.cos (2 * Real.pi * (2 : ℕ) * x) := by
  simp only [residual_EX01230, PH.val_add, PH.val_sub, PH.val_smul, PH.val_one,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul,
    ex012_27_bounded_multiplication_val,
    ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv_val,
    ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_val,
    cosMode_val_EX01228, mul_one, sq]

/-- `D² f + ι f = 0` on the first harmonics. -/
theorem ex012_30_equality_projected_residual_harmonic (a b : ℝ) :
    ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv
        (harmInj_EX01228 α 2 (a, b)) +
      ex012_25_inclusion_second_derivative_elliptic_compatibility_incl
        (harmInj_EX01228 α 2 (a, b)) = 0 :=
  harmonic_ell_EX01230 a b

/-- `Q₀ (D² w + ι w) = L w` for `w ∈ W`. -/
theorem ex012_30_equality_projected_residual_linear (w : PH.orthSub α 2) :
    proj_EX01226 α 0
        (ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv (w : PH α 2) +
          ex012_25_inclusion_second_derivative_elliptic_compatibility_incl (w : PH α 2)) =
      ellEquiv w :=
  ell_proj_EX01230 w

/-- **EX012.30.**  `F((a,b,τ), w) = Q₀ R(a c₁ + b s₁ + w, τ)` for all real `(a,b,τ)` and
`w ∈ W`. -/
theorem ex012_30_equality_projected_residual (a b τ : ℝ) (w : PH.orthSub α 2) :
    rangeMap_EX01229 α ((a, b, τ), w) =
      proj_EX01226 α 0
        (residual_EX01230 α (harmInj_EX01228 α 2 (a, b) + (w : PH α 2)) τ) := by
  have e : ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv
        (harmInj_EX01228 α 2 (a, b) + (w : PH α 2)) +
      ex012_25_inclusion_second_derivative_elliptic_compatibility_incl
        (harmInj_EX01228 α 2 (a, b) + (w : PH α 2)) =
      0 + (ex012_25_inclusion_second_derivative_elliptic_compatibility_secondDeriv (w : PH α 2) +
        ex012_25_inclusion_second_derivative_elliptic_compatibility_incl (w : PH α 2)) := by
    rw [← ex012_30_equality_projected_residual_harmonic α a b]
    simp only [map_add]
    abel
  rw [residual_proj_EX01230, e, zero_add, ex012_30_equality_projected_residual_linear]
  simp only [rangeMap_EX01229, map_add]

end Main

end DGPS.Frontier.EX012
