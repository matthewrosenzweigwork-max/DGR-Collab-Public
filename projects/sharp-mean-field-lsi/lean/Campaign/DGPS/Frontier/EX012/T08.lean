import DGPS.Frontier.EX012.T32
import DGPS.Frontier.EX012.T33
import DGPS.Frontier.EX012.T34

/-!
# EX012.08: Uniform bilinear estimate

Task id: EX012.08 (node EX012, one-site complementary range equation).
Title: Uniform bilinear estimate.

Provides:
* `DGPS.Frontier.EX012.ex012_08_uniform_bilinear_estimate`: for `α` with `[HolderExponent α]`
  there are fixed numbers `b₂, M₁, C₂ ≥ 1` such that (i) `‖B₂(f, g)‖ ≤ b₂ ‖f‖ ‖g‖` for the
  bilinear map `B₂ = bilin_EX01232 α` of EX012.32 (values in `W = PH.orthSub α 2`);
  (ii) `‖a c₁ + b s₁‖ ≤ M₁ (|a| + |b|)` for the first-harmonic modes `c₁, s₁` of `PH α 2`;
  (iii) `‖w₂(a, b, τ)‖ ≤ C₂ (|a| + |b| + √|τ|)²` for the explicit polynomial
  `w₂(a, b, τ) = ((τ - a² + b²)/12) c₂ - (ab/6) s₂`; and (iv) for these same `b₂` and `M₁`,
  there is an open neighborhood `U` of `0` in `ℝ × ℝ × ℝ` (with `V`, `w` the analytic
  implicit-function package of EX012.07, as produced by EX012.34) on which `‖w p‖ ≤ 1/(4 b₂)`
  and `|a| + |b| + √|τ| ≤ min(1, 1/(8 b₂ M₁))`.

R5 notes:
* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`. No hypothesis
  is added, and the specification's hypotheses are not weakened.
* "There are fixed numbers `b₂, M₁, C₂ ≥ 1`" is read as an existential statement. The statement
  does not fix explicit values for them. The proof takes the constants of EX012.32 and EX012.33,
  `bConst_EX01232 α`, `mConst_EX01232 α` and `C2_EX01233 α 2`, but those formulas are not part
  of this statement.
* "Shrink `U`" is read as the existential clause in (iv). It is quantified after `b₂` and `M₁`,
  so the bounds `1/(4 b₂)` and `min(1, 1/(8 b₂ M₁))` refer to the chosen constants. The
  neighborhood package `(U, V, w)` is the EX012.07 package in the form that EX012.34 produces
  (`IsOpen`, `0 ∈ U`, `0 ∈ V`, analyticity on `U`, `w(U) ⊆ V`, `w 0 = 0`, and uniqueness
  `F(p, z) = 0 ↔ z = w p` on `U × V`). The `∃ w` form lets the statement avoid naming the
  EX012.07 data. Uniqueness on `V` forces the choice of `w` on `U` in any case.
* The bilinear map `B₂` is `bilin_EX01232 α : PH α 2 →L[ℝ] PH α 2 →L[ℝ] PH.orthSub α 2`, the
  curried form of `(f, g) ↦ ½ L⁻¹ Q₀((Df)(Dg))` from EX012.32. Its norm inequality is stated in
  the `W` norm, which is the `PH α 2` norm restricted to the subspace `W`.
* The first-harmonic modes are read as `c₁ = cosMode_EX01228 α 2 1` and
  `s₁ = sinMode_EX01228 α 2 1` in `PH α 2`, as in EX012.32.
* `w₂` is written out literally in (iii), with `p = (a, b, τ)` and `c₂ = cosMode_EX01228 α 2 2`,
  `s₂ = sinMode_EX01228 α 2 2` in `PH α 2`, as in EX012.33. The bound is over all real
  `(a, b, τ)` and is not restricted to small parameters.
* `r = |a| + |b| + √|τ|` is written literally as `|a| + |b| + Real.sqrt |τ|`, and
  `Real.sqrt |τ|` is nonnegative for every real `τ`. In (iv) the coordinates of `p` are read as
  `p.1 = a`, `p.2.1 = b`, `p.2.2 = τ`.
* The inequalities of (i) and (iii) are stated with `b₂ * ‖f‖ * ‖g‖` and
  `C₂ * (...)^2`, matching the specification's order of factors. The proof converts from the
  EX012.32 form `b₂ * (‖f‖ * ‖g‖)` by `mul_assoc`.
* The statement inherits the interface of `ellInv` (the FOU018 inverse) from EX012.29 and
  EX012.32. The node note says its identification with the displayed range operator `R` depends
  on the open task EX012.37. That dependence is not restated here, and this file does not
  reprove it.
* Task EX012.04 (the bounded-derivative bound) enters only through EX012.32, which uses it for
  `‖D‖ ≤ 3/(2π)` in the explicit-constant form.
-/

open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Frontier.EX012

section Main

variable (α : ℝ) [HolderExponent α]

/-- **EX012.08.** Uniform bilinear estimate: fixed constants `b₂, M₁, C₂ ≥ 1` with the bilinear
bound, the harmonic bound and the `w₂` bound, together with a neighborhood `U` of `0` on which
the EX012.07 package satisfies `‖w p‖ ≤ 1/(4 b₂)` and `r ≤ min(1, 1/(8 b₂ M₁))`. -/
theorem ex012_08_uniform_bilinear_estimate :
    ∃ (b₂ M₁ C₂ : ℝ), 1 ≤ b₂ ∧ 1 ≤ M₁ ∧ 1 ≤ C₂ ∧
      (∀ f g : PH α 2, ‖bilin_EX01232 α f g‖ ≤ b₂ * ‖f‖ * ‖g‖) ∧
      (∀ a b : ℝ, ‖a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1‖ ≤
        M₁ * (|a| + |b|)) ∧
      (∀ a b τ : ℝ,
        ‖((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α 2 2 -
            ((a * b) / 6) • sinMode_EX01228 α 2 2‖ ≤
          C₂ * (|a| + |b| + Real.sqrt |τ|) ^ 2) ∧
      ∃ (U : Set (ℝ × ℝ × ℝ)) (V : Set (PH.orthSub α 2)) (w : ℝ × ℝ × ℝ → PH.orthSub α 2),
        IsOpen U ∧ IsOpen V ∧ (0 : ℝ × ℝ × ℝ) ∈ U ∧ (0 : PH.orthSub α 2) ∈ V ∧
        AnalyticOnNhd ℝ w U ∧ Set.MapsTo w U V ∧ w 0 = 0 ∧
        (∀ p ∈ U, ∀ z ∈ V, rangeMap_EX01229 α (p, z) = 0 ↔ z = w p) ∧
        (∀ p ∈ U, ‖w p‖ ≤ 1 / (4 * b₂)) ∧
        (∀ p ∈ U, |p.1| + |p.2.1| + Real.sqrt |p.2.2| ≤ min 1 (1 / (8 * b₂ * M₁))) := by
  refine ⟨bConst_EX01232 α, mConst_EX01232 α, C2_EX01233 α 2,
    one_le_bConst_EX01232 α, one_le_mConst_EX01232 α, one_le_C2_EX01233 α 2,
    fun f g => ((ex012_32_bilinear_norm_constant_bound (α := α)).2 f g).trans_eq
      (mul_assoc _ _ _).symm,
    fun a b => (ex012_32_bilinear_norm_constant_harmonic (α := α)).2 a b,
    fun a b τ => (ex012_33_explicit_weighted_polynomial_bound α 2).2 a b τ, ?_⟩
  exact ex012_34_one_common_small_neighborhood α

end Main

end DGPS.Frontier.EX012
