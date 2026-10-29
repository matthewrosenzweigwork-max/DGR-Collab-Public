import DGPS.Frontier.EX012.T25
import DGPS.Frontier.EX012.T26
import DGPS.Frontier.EX012.T28

/-!
# EX012.31: Inverse on second harmonics

Task id: EX012.31 (node EX012, one-site complementary range equation).
Title: Inverse on second harmonics.

Provides:
* `DGPS.Frontier.EX012.ex012_31_inverse_second_harmonics`: for every continuous linear equivalence
  `e : PH.orthSub α 2 ≃L[ℝ] PH.orthSub α 0` with `e u = ell u` for all `u` (the equivalence `L` of
  FOU018, `L w = D² w + w`) and all `A₂ B₂ : ℝ`, `e.symm (A₂ c₂ + B₂ s₂) = -(A₂/3) c₂ - (B₂/3) s₂`
  as an equality of elements of `W = PH.orthSub α 2`.
* `DGPS.Frontier.EX012.ex012_31_inverse_second_harmonics_fou018`: the same identity for an
  equivalence supplied by FOU018, namely `∃ e`, with `e u = ell u` on `W` and the identity for all
  `A₂ B₂`.
* `DGPS.Frontier.EX012.wRhs_EX01231`: the element `-(A₂/3) c₂ - (B₂/3) s₂` of `W`, with its
  membership in `W` proved.
* `DGPS.Frontier.EX012.yLhs_EX01231`: the element `A₂ c₂ + B₂ s₂` of `Y = PH.orthSub α 0`, with its
  membership in `Y` proved.
* Helpers (all suffixed `_EX01231`): `cosMode_mem_EX01231`, `sinMode_mem_EX01231` (`c₂`, `s₂` lie in
  `PH.orthSub α k` for `k = 0, 2`); `incl_cosMode_EX01231`, `incl_sinMode_EX01231` (the inclusion
  of EX012.25 fixes `c₂`, `s₂`); `ell_cosMode_EX01231`, `ell_sinMode_EX01231` (`ell c₂ = -3 c₂`,
  `ell s₂ = -3 s₂`, from `D² c₂ = -4 c₂` of EX012.28 and `ell = D² + ι` of EX012.25);
  `wRhs_coe_EX01231`, `yLhs_coe_EX01231` (underlying elements).

R5 notes:
* The only hypothesis is `[HolderExponent α]` (the campaign form of `0 < α < 1`). The equivalence
  `L` is not assumed to exist: the main statement takes an arbitrary equivalence `e` with the
  property `e u = ell u` that the specification gives `L` (`L w = D² w + w`, with the angular
  operator of EX012.25 and EX012.37). The `_fou018` variant proves that such an `e` exists
  (from `DGPS.Analysis.complementary_circle_elliptic_inverse`), so the statement is not vacuous.
  Because `e` is any such equivalence, the result does not depend on which one is chosen.
* `L⁻¹` is `e.symm`. The conclusion is an equality in `W` (the subtype `PH.orthSub α 2`),
  i.e. an equality of underlying functions, not of Fourier coefficients.
* The two elements named in the statement are built as subtype elements with their membership
  proofs; these proofs are derived (from the coefficient integrals of EX012.28), not assumed.
  `c₂` and `s₂` are the modes `cosMode_EX01228 α k 2` and `sinMode_EX01228 α k 2`, with `k = 0`
  for the right side of `L` and `k = 2` for the element of `W`.
* The harmonic identities `D² c₂ = -4 c₂` and `D² s₂ = -4 s₂` are EX012.28's
  `secondDeriv_cosMode`/`secondDeriv_sinMode` at `n = 2`, with the angular normalization
  `D = (2π)⁻¹ ∂ₓ` (through `((2π)²)⁻¹` in the unit-period variable). With `ell = D² + ι` this gives
  `L c₂ = -3 c₂` and `L s₂ = -3 s₂`, which is the consistency check `(-(A/3))(-3) = A`.
* The conclusion is obtained from injectivity of the equivalence (`ContinuousLinearEquiv.symm_apply_eq`),
  applied to `L (-(A/3) c₂ - (B/3) s₂) = A c₂ + B s₂`, using linearity of `ell`. No Fourier
  completeness theorem is used, as the specification requires.
* The inclusion `ι` of EX012.25 is used only to identify `c₂`, `s₂` in `PH α 2` with their
  copies in `PH α 0`; the value of `ell` is taken from `ell_eq` of EX012.25 and not recomputed.
-/

open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Frontier.EX012

section Membership

variable {α : ℝ} [HolderExponent α]

theorem cosMode_mem_EX01231 (k : ℕ) : cosMode_EX01228 α k 2 ∈ PH.orthSub α k := by
  refine (PH.mem_orthSub _).2 ⟨?_, ?_, ?_⟩
  · rw [PH.integral_apply]
    exact int_cosMode_EX01228 k (by norm_num)
  · rw [PH.cosCoeff_apply]
    simp only [cosMode_val_EX01228]
    rw [int_cos_cos_EX01228 2 one_ne_zero]
    norm_num
  · rw [PH.sinCoeff_apply]
    simp only [cosMode_val_EX01228]
    refine (intervalIntegral.integral_congr fun x _ => mul_comm _ _).trans ?_
    exact int_sin_cos_EX01228 1 two_ne_zero

theorem sinMode_mem_EX01231 (k : ℕ) : sinMode_EX01228 α k 2 ∈ PH.orthSub α k := by
  refine (PH.mem_orthSub _).2 ⟨?_, ?_, ?_⟩
  · rw [PH.integral_apply]
    exact int_sinMode_EX01228 k (by norm_num)
  · rw [PH.cosCoeff_apply]
    simp only [sinMode_val_EX01228]
    exact int_sin_cos_EX01228 2 one_ne_zero
  · rw [PH.sinCoeff_apply]
    simp only [sinMode_val_EX01228]
    rw [int_sin_sin_EX01228 2 one_ne_zero]
    norm_num

end Membership

section Operator

variable {α : ℝ} [HolderExponent α]

theorem incl_cosMode_EX01231 (n : ℕ) :
    ex012_25_inclusion_second_derivative_elliptic_compatibility_incl
        (cosMode_EX01228 α 2 n) = cosMode_EX01228 α 0 n :=
  PH.ext (funext fun x => by
    rw [ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_val,
      cosMode_val_EX01228, cosMode_val_EX01228])

theorem incl_sinMode_EX01231 (n : ℕ) :
    ex012_25_inclusion_second_derivative_elliptic_compatibility_incl
        (sinMode_EX01228 α 2 n) = sinMode_EX01228 α 0 n :=
  PH.ext (funext fun x => by
    rw [ex012_25_inclusion_second_derivative_elliptic_compatibility_incl_val,
      sinMode_val_EX01228, sinMode_val_EX01228])

theorem ell_cosMode_EX01231 :
    ell (cosMode_EX01228 α 2 2) = (-3 : ℝ) • cosMode_EX01228 α 0 2 := by
  rw [ex012_25_inclusion_second_derivative_elliptic_compatibility_ell_eq,
    secondDeriv_cosMode_EX01228, incl_cosMode_EX01231]
  module

theorem ell_sinMode_EX01231 :
    ell (sinMode_EX01228 α 2 2) = (-3 : ℝ) • sinMode_EX01228 α 0 2 := by
  rw [ex012_25_inclusion_second_derivative_elliptic_compatibility_ell_eq,
    secondDeriv_sinMode_EX01228, incl_sinMode_EX01231]
  module

end Operator

section Elements

variable {α : ℝ} [HolderExponent α]

/-- The element `-(A₂/3) c₂ - (B₂/3) s₂` of `W = PH.orthSub α 2`. -/
noncomputable def wRhs_EX01231 (α : ℝ) [HolderExponent α] (A B : ℝ) : PH.orthSub α 2 :=
  ⟨(-(A / 3)) • cosMode_EX01228 α 2 2 + (-(B / 3)) • sinMode_EX01228 α 2 2,
    Submodule.add_mem _ (Submodule.smul_mem _ _ (cosMode_mem_EX01231 2))
      (Submodule.smul_mem _ _ (sinMode_mem_EX01231 2))⟩

/-- The element `A₂ c₂ + B₂ s₂` of `Y = PH.orthSub α 0`. -/
noncomputable def yLhs_EX01231 (α : ℝ) [HolderExponent α] (A B : ℝ) : PH.orthSub α 0 :=
  ⟨A • cosMode_EX01228 α 0 2 + B • sinMode_EX01228 α 0 2,
    Submodule.add_mem _ (Submodule.smul_mem _ _ (cosMode_mem_EX01231 0))
      (Submodule.smul_mem _ _ (sinMode_mem_EX01231 0))⟩

theorem wRhs_coe_EX01231 (A B : ℝ) :
    ((wRhs_EX01231 α A B : PH.orthSub α 2) : PH α 2) =
      (-(A / 3)) • cosMode_EX01228 α 2 2 + (-(B / 3)) • sinMode_EX01228 α 2 2 := rfl

theorem yLhs_coe_EX01231 (A B : ℝ) :
    ((yLhs_EX01231 α A B : PH.orthSub α 0) : PH α 0) = A • cosMode_EX01228 α 0 2 + B • sinMode_EX01228 α 0 2 := rfl

end Elements

section Main

variable {α : ℝ} [HolderExponent α]

/-- **EX012.31.**  For the equivalence `L = e` of FOU018 (`e u = ell u` on `W`) and all `A₂, B₂`,
`e⁻¹ (A₂ c₂ + B₂ s₂) = -(A₂/3) c₂ - (B₂/3) s₂` as an equality in `W`. -/
theorem ex012_31_inverse_second_harmonics
    (e : PH.orthSub α 2 ≃L[ℝ] PH.orthSub α 0)
    (he : ∀ u : PH.orthSub α 2, (e u : PH α 0) = ell (u : PH α 2)) (A B : ℝ) :
    e.symm (yLhs_EX01231 α A B) = wRhs_EX01231 α A B := by
  rw [ContinuousLinearEquiv.symm_apply_eq]
  apply Subtype.ext
  rw [he, yLhs_coe_EX01231, wRhs_coe_EX01231, map_add, map_smul, map_smul,
    ell_cosMode_EX01231, ell_sinMode_EX01231]
  module

/-- The same identity for an equivalence supplied by FOU018: such an `e` exists and satisfies
`e u = ell u` on `W`, and `e⁻¹ (A₂ c₂ + B₂ s₂) = -(A₂/3) c₂ - (B₂/3) s₂` for all `A₂, B₂`. -/
theorem ex012_31_inverse_second_harmonics_fou018 :
    ∃ e : PH.orthSub α 2 ≃L[ℝ] PH.orthSub α 0,
      (∀ u : PH.orthSub α 2, (e u : PH α 0) = ell (u : PH α 2)) ∧
      ∀ A B : ℝ, e.symm (yLhs_EX01231 α A B) = wRhs_EX01231 α A B := by
  obtain ⟨⟨e, he, _⟩, _⟩ := DGPS.Analysis.complementary_circle_elliptic_inverse α
  exact ⟨e, he, fun A B => ex012_31_inverse_second_harmonics e he A B⟩

end Main

end DGPS.Frontier.EX012
