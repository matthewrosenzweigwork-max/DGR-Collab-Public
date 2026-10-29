import DGPS.Frontier.EX012.T08
import DGPS.Frontier.EX012.T09

/-!
# EX012.10: Quadratic estimate

Task id: EX012.10 (node EX012, one-site complementary range equation).
Title: Quadratic estimate.

Provides:
* `DGPS.Frontier.EX012.ex012_10_quadratic_estimate`: for `α` with `[HolderExponent α]` there are
  fixed numbers `b₂, M₁, C₂ ≥ 1` and a neighborhood package `(U, V, w)` of the analytic
  implicit-function data, such that all clauses of `ex012_08_uniform_bilinear_estimate` hold for
  these data, and in addition `‖w p‖ ≤ 2 C₂ r(p)²` for every `p ∈ U`, where
  `r(p) = |p.1| + |p.2.1| + √|p.2.2|`.
* Helpers (all suffixed `_EX01210`): `sq_expand_EX01210` (the square of a sum under the bounded
  product of `PH α 0`); `solve_abstract_EX01210` (the range equation solved for the linear term);
  `ident_EX01210` (the exact identity `u = w₂ - 2 B₂(f, u) - B₂(u, u)` in `W`, from the range
  equation and the leading term of EX012.09); `norm_core_EX01210` (the norm estimate from that
  identity, with the coefficient `≤ 1/2`).

R5 notes:
* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`. No hypothesis is
  added to the specification.
* "On the neighborhood chosen in Task 08" is read as a statement about the existential witnesses
  of EX012.08: the new conjunct `‖w p‖ ≤ 2 C₂ r(p)²` is quantified over the same `b₂, M₁, C₂`,
  `U, V, w` that EX012.08 provides. The statement therefore restates the whole EX012.08 conjunction
  and adds the quadratic bound to it, so the neighborhood is the one in which the clauses hold.
* The constants are existential, as in EX012.08. No explicit values are fixed. The bound is over
  all `p ∈ U`, with no further shrinking.
* `r(p) = |p.1| + |p.2.1| + √|p.2.2|` is written literally, with `p = (a, b, τ)`. The
  inequality is used in the form `|a| + |b| ≤ r`, with `√|τ| ≥ 0`.
* The range equation is the `rangeMap_EX01229 α` of EX012.29, and the relation `F(p, w p) = 0`
  comes from the uniqueness clause of EX012.08 (`F(p, z) = 0 ↔ z = w p` on `U × V`).
* The operator `L⁻¹` is `ellEquiv.symm`, the FOU018 inverse `ellInv` of
  `DGPS.Analysis.ComplementaryElliptic`, used exactly as in EX012.09 and EX012.32. Its
  identification with the displayed range operator depends on the open task EX012.37. That
  dependence is inherited from EX012.08 and is not reproved here.
* `Q` is `Q₀ = proj_EX01226 α 0`, as in EX012.09. `B₂` is `bilin_EX01232 α`, the curried form of
  `(f, g) ↦ ½ L⁻¹ Q₀((Df)(Dg))`; the identities `B₂(f, g) = ½ L⁻¹ Q₀((Df)(Dg))` are closed by `rfl`.
* The leading term `w₂(a, b, τ) = ((τ - a² + b²)/12) c₂ - (ab/6) s₂` enters only through
  `ex012_09_exact_leading_term`, with `e = ellEquiv` and `he` by `rfl`. The bound on `‖w₂‖`
  enters only through clause (iii) of EX012.08.
* The bilinear norm bound uses clause (i) of EX012.08 with `‖(u : PH α 2)‖ = ‖u‖` for `u ∈ W`
  (`Submodule.norm_coe`, which is definitional). The harmonic bound uses clause (ii) with
  `‖f‖ ≤ M₁ (|a| + |b|)`, and `2 b₂ M₁ r ≤ 1/4` and `b₂ ‖w p‖ ≤ 1/4` come from clause (iv) and
  `‖w p‖ ≤ 1/(4 b₂)`.
-/

open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Frontier.EX012

section Algebra

variable {α : ℝ} [HolderExponent α]

/-- Expansion of the square of a sum under the bounded product in `PH α 0`. -/
theorem sq_expand_EX01210 (X Y : PH α 0) :
    ex012_27_bounded_multiplication α (X + Y) (X + Y) =
      ex012_27_bounded_multiplication α X X + (2 : ℝ) • ex012_27_bounded_multiplication α X Y +
        ex012_27_bounded_multiplication α Y Y := by
  simp only [map_add, add_apply]
  rw [ex012_27_bounded_multiplication_comm α Y X]
  module

/-- The range equation with the linear term isolated, for abstract `G, D, c` in `PH α 0`. -/
theorem solve_abstract_EX01210 (G D c : PH α 0) (L : PH.orthSub α 0)
    (h : L + proj_EX01226 α 0 ((1 / 2 : ℝ) • ex012_27_bounded_multiplication α (G + D) (G + D) + c)
      = 0) :
    L = -proj_EX01226 α 0 ((1 / 2 : ℝ) • (G * G) + c)
      - proj_EX01226 α 0 (ex012_27_bounded_multiplication α G D)
      - (1 / 2 : ℝ) • proj_EX01226 α 0 (ex012_27_bounded_multiplication α D D) := by
  have key : proj_EX01226 α 0 ((1 / 2 : ℝ) • ex012_27_bounded_multiplication α (G + D) (G + D) + c) =
      proj_EX01226 α 0 ((1 / 2 : ℝ) • (G * G) + c)
        + proj_EX01226 α 0 (ex012_27_bounded_multiplication α G D)
        + (1 / 2 : ℝ) • proj_EX01226 α 0 (ex012_27_bounded_multiplication α D D) := by
    rw [sq_expand_EX01210]
    simp only [map_add, map_smul, ex012_27_bounded_multiplication_apply]
    module
  rw [key] at h
  linear_combination (norm := module) h

/-- The exact identity `u = w₂ - 2 B₂(f, u) - B₂(u, u)` in `W`, for `f = a c₁ + b s₁`, obtained
from the range equation at `((a, b, τ), u)` and the leading term of EX012.09. -/
theorem ident_EX01210 (a b τ : ℝ) (u : PH.orthSub α 2)
    (hF : rangeMap_EX01229 α ((a, b, τ), u) = 0) :
    u = (⟨((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α 2 2 - (a * b / 6) • sinMode_EX01228 α 2 2,
        wRhs_mem_EX01209 a b τ⟩ : PH.orthSub α 2)
      - (2 : ℝ) • bilin_EX01232 α (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1)
          (u : PH α 2)
      - bilin_EX01232 α (u : PH α 2) (u : PH α 2) := by
  have hsolve := solve_abstract_EX01210
    (angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1))
    (angDeriv_EX01224 (u : PH α 2)) ((τ / 4) • cosMode_EX01228 α 0 2) (ellEquiv u) hF
  have hT09 := ex012_09_exact_leading_term (α := α) ellEquiv (fun _ => rfl) a b τ
  have hP1 : -(ellEquiv.symm (proj_EX01226 α 0
        ((1 / 2 : ℝ) • (angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1) *
            angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1)) +
          (τ / 4) • cosMode_EX01228 α 0 2))) =
      (⟨((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α 2 2 - (a * b / 6) • sinMode_EX01228 α 2 2,
        wRhs_mem_EX01209 a b τ⟩ : PH.orthSub α 2) :=
    Subtype.ext hT09
  have hu : u = ellEquiv.symm (ellEquiv u) := (ellEquiv.symm_apply_apply u).symm
  rw [hsolve] at hu
  simp only [map_sub, map_neg, map_smul] at hu
  have hB1 : bilin_EX01232 α (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1) (u : PH α 2) =
      (1 / 2 : ℝ) • ellEquiv.symm (proj_EX01226 α 0
        (ex012_27_bounded_multiplication α
          (angDeriv_EX01224 (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1))
          (angDeriv_EX01224 (u : PH α 2)))) := rfl
  have hB2 : bilin_EX01232 α (u : PH α 2) (u : PH α 2) =
      (1 / 2 : ℝ) • ellEquiv.symm (proj_EX01226 α 0
        (ex012_27_bounded_multiplication α (angDeriv_EX01224 (u : PH α 2))
          (angDeriv_EX01224 (u : PH α 2)))) := rfl
  rw [hB1, hB2]
  linear_combination (norm := module) hu + hP1

end Algebra

section Norms

variable {α : ℝ} [HolderExponent α]

/-- The norm estimate: from the exact identity `u = W - 2 B₁ - B₂` with `‖W‖ ≤ C₂ r²`,
`‖B₁‖ ≤ b₂ ‖f‖ ‖u‖`, `‖f‖ ≤ M₁ r`, `‖B₂‖ ≤ b₂ ‖u‖²`, `r ≤ 1/(8 b₂ M₁)` and `‖u‖ ≤ 1/(4 b₂)`,
one gets `‖u‖ ≤ 2 C₂ r²`. -/
theorem norm_core_EX01210 {b₂ M₁ C₂ r s : ℝ} (hb : 1 ≤ b₂) (hM : 1 ≤ M₁)
    (u W2 B1 B2 : PH.orthSub α 2) (f : PH α 2)
    (hs : s ≤ r) (hfn : ‖f‖ ≤ M₁ * s) (hr : r ≤ 1 / (8 * b₂ * M₁))
    (hW2 : ‖W2‖ ≤ C₂ * r ^ 2) (hu : ‖u‖ ≤ 1 / (4 * b₂))
    (hB1 : ‖B1‖ ≤ b₂ * ‖f‖ * ‖u‖) (hB2 : ‖B2‖ ≤ b₂ * ‖u‖ * ‖u‖)
    (hid : u = W2 - (2 : ℝ) • B1 - B2) :
    ‖u‖ ≤ 2 * C₂ * r ^ 2 := by
  have hb0 : (0 : ℝ) < b₂ := by linarith
  have hM0 : (0 : ℝ) < M₁ := by linarith
  have hbne : b₂ ≠ 0 := hb0.ne'
  have hn : 0 ≤ ‖u‖ := norm_nonneg u
  have hr1 : r * (8 * b₂ * M₁) ≤ 1 :=
    (le_div_iff₀ (mul_pos (mul_pos (by norm_num) hb0) hM0)).1 hr
  have hA : 2 * b₂ * (M₁ * r) ≤ 1 / 4 := by linarith
  have hB : b₂ * ‖u‖ ≤ 1 / 4 := by
    have h := mul_le_mul_of_nonneg_left hu hb0.le
    have e : b₂ * (1 / (4 * b₂)) = 1 / 4 := by field_simp
    linarith
  have hf : ‖f‖ ≤ M₁ * r := hfn.trans (mul_le_mul_of_nonneg_left hs hM0.le)
  have hB1' : 2 * ‖B1‖ ≤ 1 / 4 * ‖u‖ := by
    have h1 := le_trans hB1 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hf hb0.le) hn)
    have h2 := mul_le_mul_of_nonneg_right hA hn
    linarith
  have hB2' : ‖B2‖ ≤ 1 / 4 * ‖u‖ := le_trans hB2 (mul_le_mul_of_nonneg_right hB hn)
  have hsmul : ‖(2 : ℝ) • B1‖ = 2 * ‖B1‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_two]
  have htri : ‖u‖ ≤ ‖W2‖ + ‖(2 : ℝ) • B1‖ + ‖B2‖ := by
    have h1 : ‖u‖ = ‖W2 - (2 : ℝ) • B1 - B2‖ := congrArg (fun x => ‖x‖) hid
    have h2 := norm_sub_le (W2 - (2 : ℝ) • B1) B2
    have h3 := norm_sub_le W2 ((2 : ℝ) • B1)
    linarith
  rw [hsmul] at htri
  linarith

end Norms

section Main

/-- **EX012.10.** Quadratic estimate on the neighborhood of EX012.08: with the constants
`b₂, M₁, C₂` and the package `(U, V, w)` of EX012.08 (clauses (i)-(iv) unchanged), one has
`‖w p‖ ≤ 2 C₂ (|p.1| + |p.2.1| + √|p.2.2|)²` for every `p ∈ U`. -/
theorem ex012_10_quadratic_estimate (α : ℝ) [HolderExponent α] :
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
        (∀ p ∈ U, |p.1| + |p.2.1| + Real.sqrt |p.2.2| ≤ min 1 (1 / (8 * b₂ * M₁))) ∧
        (∀ p ∈ U, ‖w p‖ ≤ 2 * C₂ * (|p.1| + |p.2.1| + Real.sqrt |p.2.2|) ^ 2) := by
  obtain ⟨b₂, M₁, C₂, hb, hM, hC, hbil, hharm, hW2, U, V, w, hU, hV, h0U, h0V, hanal, hmaps,
    hw0, hiff, hwsmall, hrU⟩ := ex012_08_uniform_bilinear_estimate α
  refine ⟨b₂, M₁, C₂, hb, hM, hC, hbil, hharm, hW2, U, V, w, hU, hV, h0U, h0V, hanal, hmaps,
    hw0, hiff, hwsmall, hrU, fun p hp => ?_⟩
  have hF : rangeMap_EX01229 α ((p.1, p.2.1, p.2.2), w p) = 0 :=
    (hiff p hp (w p) (hmaps hp)).2 rfl
  have hid := ident_EX01210 p.1 p.2.1 p.2.2 (w p) hF
  exact norm_core_EX01210 (r := |p.1| + |p.2.1| + Real.sqrt |p.2.2|)
    (s := |p.1| + |p.2.1|) hb hM (w p) _ _ _ _
    (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (hharm p.1 p.2.1)
    ((hrU p hp).trans (min_le_right _ _)) (by exact hW2 p.1 p.2.1 p.2.2)
    (hwsmall p hp)
    (by exact hbil (p.1 • cosMode_EX01228 α 2 1 + p.2.1 • sinMode_EX01228 α 2 1) (w p : PH α 2))
    (by exact hbil (w p : PH α 2) (w p : PH α 2)) hid

end Main

end DGPS.Frontier.EX012
