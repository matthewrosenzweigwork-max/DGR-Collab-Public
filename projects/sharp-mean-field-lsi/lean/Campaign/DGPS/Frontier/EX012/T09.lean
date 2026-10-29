import DGPS.Frontier.EX012.T31

/-!
# EX012.09: Exact leading term

Task id: EX012.09 (node EX012, one-site complementary range equation).
Title: Exact leading term.

Provides:
* `DGPS.Frontier.EX012.ex012_09_exact_leading_term`: for every continuous linear equivalence
  `e : PH.orthSub α 2 ≃L[ℝ] PH.orthSub α 0` with `e u = ell u` (the operator `L` of FOU018,
  `L w = D² w + w`) and all `a b τ : ℝ`, with `f = a c₁ + b s₁`,
  `-(e⁻¹ (Q₀ ((1/2) (D f)² + (τ/4) c₂))) = ((τ - a²+b²)/12) c₂ - (ab/6) s₂`, the equality being
  taken in `PH α 2` after the coercion from `W = PH.orthSub α 2`.
* `DGPS.Frontier.EX012.ex012_09_exact_leading_term_fou018`: the same identity for an equivalence
  supplied by FOU018, namely `∃ e` with `e u = ell u` on `W` and the identity for all `a b τ`.
* Helper declarations (all suffixed `_EX01209`): `angDeriv_harmF_EX01209` (`D (a c₁ + b s₁) =
  -a s₁ + b c₁`, in `PH α 0`); `forcing_eq_EX01209` (the forcing `(1/2)(Df)² + (τ/4) c₂` equals
  `((a²+b²)/4) 1 + ((τ+b²-a²)/4) c₂ - (ab/2) s₂` in `PH α 0`, from the double-angle identities);
  `wRhs_mem_EX01209` (membership of `((τ-a²+b²)/12) c₂ - (ab/6) s₂` in `W`); `proj_forcing_EX01209`
  (the projection `Q₀` of the forcing is `((τ+b²-a²)/4) c₂ - (ab/2) s₂` in `Y`).

R5 notes:
* The only hypothesis of the main statements is `[HolderExponent α]` (the campaign form of
  `0 < α < 1`), plus the equivalence `e` with its defining property `he`, which is exactly the
  input of EX012.31 (the inverse `L⁻¹` is `e.symm`). The `_fou018` variant proves that such an `e`
  exists, from `DGPS.Analysis.complementary_circle_elliptic_inverse`, so the statement is not
  vacuous. The result does not depend on which `e` is chosen, since `e` is determined on `W` by `he`.
* `D` is `angDeriv_EX01224 : PH α 2 →L[ℝ] PH α 0` (EX012.24), the angular derivative with
  `D = (2π)⁻¹ ∂ₓ`. The forcing is an element of `PH α 0` (the codomain of `Q₀`), so the square
  `(Df)²` is the ring product `Df * Df` in the commutative algebra `PH α 0`. Its pointwise value
  is `(Df x)²`, by `PH.val_mul`.
* `Q` is `Q₀ = proj_EX01226 α 0` (EX012.26), the projection removing the mean and the first
  cosine and sine modes, with codomain `Y = PH.orthSub α 0`. The specification's `Q` is taken at
  regularity `0` because `L⁻¹` is only defined on `Y`; EX012.26 proves that `Q₀` and `Q₂` agree
  on `PH α 2`.
* `f = a c₁ + b s₁` is written as `a • cosMode α 2 1 + b • sinMode α 2 1` in `PH α 2`, the
  bundled modes of EX012.28, rather than through the injection `harmInj`. The product `Df * Df`
  and `c₂ = cosMode α 0 2` are written with the same bundled modes.
* The right side `w₂` is stated as `((τ - a²+b²)/12) • c₂ - (ab/6) • s₂` in `PH α 2`, using the
  bundled modes `cosMode α 2 2`, `sinMode α 2 2`. The minus sign is kept as in the specification.
  The value of `L c₂` and `L s₂` (`-3 c₂`, `-3 s₂`) is taken from EX012.31, not recomputed.
* The double-angle identities are proved pointwise (`PH.ext`, `Real.cos_two_mul`, `Real.sin_two_mul`
  and `sin² + cos² = 1`). The projection identities use EX012.26's `kills` (`Q₀ 1 = 0`) and
  `fixes` (`Q₀ w = w` for `w ∈ PH.orthSub α 0`) lemmas, which are not re-proved here.
* The operator `L` is the `ell` of `DGPS.Analysis.ComplementaryElliptic`, with `ell = D² + 1` as
  recorded by EX012.25 (`ell_eq`). The specification's displayed angular operator is used as given;
  the Task 37 identification of `L` with the packet's operator is not needed for this statement,
  as in EX012.31.
* The specification's Proof removes the constant by `Q`, then applies `L⁻¹`, using `L c₂ = -3 c₂`
  and `L s₂ = -3 s₂` (EX012.31). Here this is carried out by `e.symm` and `he`, through
  `e (-w) = -ell w` and linearity of `ell`; no Fourier completeness is used.
-/

open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Frontier.EX012

section Forcing

variable {α : ℝ} [HolderExponent α]

theorem angDeriv_harmF_EX01209 (a b : ℝ) :
    angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1) =
      (-a) • sinMode_EX01228 α 0 1 + b • cosMode_EX01228 α 0 1 := by
  rw [map_add, map_smul, map_smul, angDeriv_cosMode_EX01228, angDeriv_sinMode_EX01228]
  simp only [Nat.cast_one]
  module

theorem forcing_eq_EX01209 (a b τ : ℝ) :
    (1 / 2 : ℝ) • (angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1) *
        angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1)) +
      (τ / 4) • cosMode_EX01228 α 0 2 =
    ((a ^ 2 + b ^ 2) / 4) • (1 : PH α 0) + ((τ + b ^ 2 - a ^ 2) / 4) • cosMode_EX01228 α 0 2 +
      (-(a * b / 2)) • sinMode_EX01228 α 0 2 := by
  rw [angDeriv_harmF_EX01209]
  refine PH.ext (funext fun x => ?_)
  have h2c : Real.cos (2 * Real.pi * 2 * x) =
      Real.cos (2 * Real.pi * x) ^ 2 - Real.sin (2 * Real.pi * x) ^ 2 := by
    rw [show 2 * Real.pi * 2 * x = 2 * (2 * Real.pi * x) by ring, Real.cos_two_mul]
    linear_combination Real.sin_sq_add_cos_sq (2 * Real.pi * x)
  have h2s : Real.sin (2 * Real.pi * 2 * x) =
      2 * Real.sin (2 * Real.pi * x) * Real.cos (2 * Real.pi * x) := by
    rw [show 2 * Real.pi * 2 * x = 2 * (2 * Real.pi * x) by ring, Real.sin_two_mul]
  simp only [PH.val_add, PH.val_smul, PH.val_mul, PH.val_one, Pi.add_apply, Pi.smul_apply,
    Pi.mul_apply, Pi.one_apply, smul_eq_mul, cosMode_val_EX01228, sinMode_val_EX01228,
    Nat.cast_one, Nat.cast_ofNat, mul_one]
  rw [h2c, h2s]
  linear_combination ((a ^ 2 + b ^ 2) / 4) * Real.sin_sq_add_cos_sq (2 * Real.pi * x)

end Forcing

section Projection

variable {α : ℝ} [HolderExponent α]

theorem wRhs_mem_EX01209 (a b τ : ℝ) :
    ((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α 2 2 - (a * b / 6) • sinMode_EX01228 α 2 2 ∈
      PH.orthSub α 2 :=
  Submodule.sub_mem _ (Submodule.smul_mem _ _ (cosMode_mem_EX01231 2))
    (Submodule.smul_mem _ _ (sinMode_mem_EX01231 2))

theorem proj_forcing_EX01209 (a b τ : ℝ) :
    proj_EX01226 α 0
        ((1 / 2 : ℝ) • (angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1) *
            angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1)) +
          (τ / 4) • cosMode_EX01228 α 0 2) =
      ((τ + b ^ 2 - a ^ 2) / 4) • (⟨cosMode_EX01228 α 0 2, cosMode_mem_EX01231 0⟩ : PH.orthSub α 0) +
        (-(a * b / 2)) • (⟨sinMode_EX01228 α 0 2, sinMode_mem_EX01231 0⟩ : PH.orthSub α 0) := by
  have hc : proj_EX01226 α 0 (cosMode_EX01228 α 0 2) =
      (⟨cosMode_EX01228 α 0 2, cosMode_mem_EX01231 0⟩ : PH.orthSub α 0) :=
    ex012_26_projections_both_regularities_fixes 0 ⟨_, cosMode_mem_EX01231 0⟩
  have hs : proj_EX01226 α 0 (sinMode_EX01228 α 0 2) =
      (⟨sinMode_EX01228 α 0 2, sinMode_mem_EX01231 0⟩ : PH.orthSub α 0) :=
    ex012_26_projections_both_regularities_fixes 0 ⟨_, sinMode_mem_EX01231 0⟩
  rw [forcing_eq_EX01209, map_add, map_add, map_smul, map_smul, map_smul,
    (ex012_26_projections_both_regularities_kills 0).1, hc, hs, smul_zero, zero_add]

end Projection

section Main

variable {α : ℝ} [HolderExponent α]

/-- **EX012.09.**  For the equivalence `L = e` of FOU018 (`e u = ell u` on `W`), all `a, b, τ`
and `f = a c₁ + b s₁`:
`-(L⁻¹ (Q₀ ((1/2)(Df)² + (τ/4) c₂))) = ((τ - a²+b²)/12) c₂ - (ab/6) s₂` as functions. -/
theorem ex012_09_exact_leading_term
    (e : PH.orthSub α 2 ≃L[ℝ] PH.orthSub α 0)
    (he : ∀ u : PH.orthSub α 2, (e u : PH α 0) = ell (u : PH α 2)) (a b τ : ℝ) :
    ((-(e.symm (proj_EX01226 α 0
        ((1 / 2 : ℝ) • (angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1) *
            angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1)) +
          (τ / 4) • cosMode_EX01228 α 0 2))) : PH.orthSub α 2) : PH α 2) =
      ((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α 2 2 - (a * b / 6) • sinMode_EX01228 α 2 2 := by
  have h1 : e.symm (proj_EX01226 α 0
        ((1 / 2 : ℝ) • (angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1) *
            angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1)) +
          (τ / 4) • cosMode_EX01228 α 0 2)) =
      -(⟨((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α 2 2 - (a * b / 6) • sinMode_EX01228 α 2 2,
        wRhs_mem_EX01209 a b τ⟩ : PH.orthSub α 2) := by
    rw [ContinuousLinearEquiv.symm_apply_eq, proj_forcing_EX01209]
    apply Subtype.ext
    rw [he]
    simp only [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_neg,
      map_neg, map_sub, map_smul, ell_cosMode_EX01231, ell_sinMode_EX01231]
    module
  rw [h1, neg_neg]

/-- The same identity for an equivalence supplied by FOU018: such an `e` exists and satisfies
`e u = ell u` on `W`, and the identity of `ex012_09_exact_leading_term` holds for all `a, b, τ`. -/
theorem ex012_09_exact_leading_term_fou018 :
    ∃ e : PH.orthSub α 2 ≃L[ℝ] PH.orthSub α 0,
      (∀ u : PH.orthSub α 2, (e u : PH α 0) = ell (u : PH α 2)) ∧
      ∀ a b τ : ℝ,
        ((-(e.symm (proj_EX01226 α 0
            ((1 / 2 : ℝ) • (angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1) *
                angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1)) +
              (τ / 4) • cosMode_EX01228 α 0 2))) : PH.orthSub α 2) : PH α 2) =
          ((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α 2 2 -
            (a * b / 6) • sinMode_EX01228 α 2 2 := by
  obtain ⟨⟨e, he, _⟩, _⟩ := DGPS.Analysis.complementary_circle_elliptic_inverse α
  exact ⟨e, he, fun a b τ => ex012_09_exact_leading_term e he a b τ⟩

end Main

end DGPS.Frontier.EX012
