import DGPS.Frontier.EX012.T10

/-!
# EX012.11: Weighted remainder

Task id: EX012.11 (node EX012, one-site complementary range equation).
Title: Weighted remainder.

Provides:
* `DGPS.Frontier.EX012.ex012_11_weighted_remainder`: for `α` with `[HolderExponent α]` there are
  fixed numbers `b₂, M₁, C₂ ≥ 1` and a neighborhood package `(U, V, w)` such that all clauses of
  `ex012_10_quadratic_estimate` hold for these data (the EX012.08 clauses, the quadratic bound
  `‖w p‖ ≤ 2 C₂ r(p)²`), and in addition, for every `(a, b, τ) ∈ U`,
  `‖w(a, b, τ) - (((τ - a² + b²)/12) c₂ - (ab/6) s₂)‖ ≤ (4 b₂ M₁ C₂ + 4 b₂ C₂²) (|a| + |b| + √|τ|)³`
  in the norm of `PH α 2`. This is the weighted remainder of order three under the weights `(1,1,2)`.
* Helper (suffixed `_EX01211`): `remainder_core_EX01211` (the norm estimate from the exact
  identity `u = W₂ - 2 B₂(f, u) - B₂(u, u)` of EX012.10, with `‖f‖ ≤ M₁ r`, `‖u‖ ≤ 2 C₂ r²` and
  `r ≤ 1`, giving `‖u - W₂‖ ≤ (4 b₂ M₁ C₂ + 4 b₂ C₂²) r³`).

R5 notes:
* The only hypothesis is `[HolderExponent α]`, the campaign form of `0 < α < 1`. No hypothesis is
  added to the specification.
* "On the same neighborhood" is read as: the neighborhood package of EX012.08 and EX012.10, with
  the same existential witnesses `b₂, M₁, C₂, U, V, w`. The statement therefore restates the
  whole EX012.10 conjunction (including its quadratic bound on `‖w p‖`) and adds the remainder
  estimate as one further conjunct, quantified over the same `U`.
* The constants are existential, as in EX012.08 and EX012.10. No explicit values are fixed, and
  the bound holds for all `(a, b, τ) ∈ U` with no further shrinking.
* The remainder is written literally: `w₂(a, b, τ) = ((τ - a² + b²)/12) c₂ - (ab/6) s₂`, with
  `c₂ = cosMode_EX01228 α 2 2` and `s₂ = sinMode_EX01228 α 2 2` in `PH α 2`, and
  `r = |a| + |b| + √|τ|`. The norm `‖·‖_{2,α}` is read as the norm of `PH α 2` applied to the
  difference `w(a, b, τ) - w₂(a, b, τ)`. This difference lies in `PH.orthSub α 2` (both terms
  do), and the subspace norm is the restriction of the `PH α 2` norm.
* The bound is over both signs of `τ`, since `√|τ| ≥ 0` for every real `τ`, and it is not
  restricted to `τ ≥ 0`.
* The proof uses the range equation at `((a, b, τ), w(a, b, τ))` through the identity
  `ident_EX01210` of EX012.10, the bilinear bound of EX012.08 clause (i), the harmonic bound of
  clause (ii), and the quadratic bound `‖w p‖ ≤ 2 C₂ r²` of EX012.10. The inequality `r ≤ 1` comes
  from the neighborhood clause `r ≤ min 1 (1/(8 b₂ M₁))`. The step `r⁴ ≤ r³` uses `r ≤ 1` and
  `r ≥ 0`.
* The sentence in the node note about analyticity from Task 07 ruling out lower weighted Taylor
  monomials in the difference is not part of the stated estimate. It is not formalized here.
* The dependence of the identity on the FOU018 inverse `ellEquiv` and on the open task EX012.37
  (the identification of the displayed range operator) is inherited from EX012.08, EX012.09 and
  EX012.10. It is not reproved here.
* The weighted-order statement is recorded as the single inequality above. The node note's
  "preferred interface" is that inequality, and it is not replaced by ordinary-degree form.
-/

open DGPS.Analysis.PeriodicHolder DGPS.Analysis.ComplementaryElliptic

namespace DGPS.Frontier.EX012

section Core

variable {α : ℝ} [HolderExponent α]

/-- The norm estimate of the weighted remainder: from `u = W₂ - 2 B₁ - B₂` with
`‖B₁‖ ≤ b₂ ‖f‖ ‖u‖`, `‖B₂‖ ≤ b₂ ‖u‖ ‖u‖`, `‖f‖ ≤ M₁ r`, `‖u‖ ≤ 2 C₂ r²` and `0 ≤ r ≤ 1`,
one gets `‖u - W₂‖ ≤ (4 b₂ M₁ C₂ + 4 b₂ C₂²) r³`. -/
theorem remainder_core_EX01211 {b₂ M₁ C₂ r : ℝ} (hb : 0 ≤ b₂) (hM : 0 ≤ M₁) (hC : 0 ≤ C₂)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (u W2 B1 B2 : PH.orthSub α 2) (f : PH α 2)
    (hfn : ‖f‖ ≤ M₁ * r) (hu : ‖u‖ ≤ 2 * C₂ * r ^ 2)
    (hB1 : ‖B1‖ ≤ b₂ * ‖f‖ * ‖u‖) (hB2 : ‖B2‖ ≤ b₂ * ‖u‖ * ‖u‖)
    (hid : u = W2 - (2 : ℝ) • B1 - B2) :
    ‖u - W2‖ ≤ (4 * b₂ * M₁ * C₂ + 4 * b₂ * C₂ ^ 2) * r ^ 3 := by
  have hn : 0 ≤ ‖u‖ := norm_nonneg u
  have hMr : 0 ≤ M₁ * r := mul_nonneg hM hr0
  have hU0 : 0 ≤ 2 * C₂ * r ^ 2 := mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg r)
  have hA : ‖f‖ * ‖u‖ ≤ (M₁ * r) * (2 * C₂ * r ^ 2) := mul_le_mul hfn hu hn hMr
  have hB1' : ‖B1‖ ≤ b₂ * ((M₁ * r) * (2 * C₂ * r ^ 2)) := by
    calc ‖B1‖ ≤ b₂ * ‖f‖ * ‖u‖ := hB1
      _ = b₂ * (‖f‖ * ‖u‖) := by ring
      _ ≤ b₂ * ((M₁ * r) * (2 * C₂ * r ^ 2)) := mul_le_mul_of_nonneg_left hA hb
  have hU2 : ‖u‖ * ‖u‖ ≤ (2 * C₂ * r ^ 2) * (2 * C₂ * r ^ 2) := mul_le_mul hu hu hn hU0
  have hB2' : ‖B2‖ ≤ b₂ * ((2 * C₂ * r ^ 2) * (2 * C₂ * r ^ 2)) := by
    calc ‖B2‖ ≤ b₂ * ‖u‖ * ‖u‖ := hB2
      _ = b₂ * (‖u‖ * ‖u‖) := by ring
      _ ≤ b₂ * ((2 * C₂ * r ^ 2) * (2 * C₂ * r ^ 2)) := mul_le_mul_of_nonneg_left hU2 hb
  have hsmul : ‖(2 : ℝ) • B1‖ = 2 * ‖B1‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_two]
  have hd : u - W2 = -((2 : ℝ) • B1 + B2) := by
    rw [hid]; abel
  have htri : ‖u - W2‖ ≤ ‖(2 : ℝ) • B1‖ + ‖B2‖ := by
    rw [hd, norm_neg]; exact norm_add_le _ _
  have hr4 : r ^ 4 ≤ r ^ 3 := by
    calc r ^ 4 = r ^ 3 * r := by ring
      _ ≤ r ^ 3 * 1 := mul_le_mul_of_nonneg_left hr1 (pow_nonneg hr0 3)
      _ = r ^ 3 := mul_one _
  have hexp : 2 * (b₂ * ((M₁ * r) * (2 * C₂ * r ^ 2))) +
      b₂ * ((2 * C₂ * r ^ 2) * (2 * C₂ * r ^ 2)) =
      (4 * b₂ * M₁ * C₂ + 4 * b₂ * C₂ ^ 2) * r ^ 3 - 4 * b₂ * C₂ ^ 2 * (r ^ 3 - r ^ 4) := by
    ring
  have hnn : 0 ≤ 4 * b₂ * C₂ ^ 2 * (r ^ 3 - r ^ 4) :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hb) (sq_nonneg C₂)) (sub_nonneg.2 hr4)
  rw [hsmul] at htri
  linarith

end Core

section Main

/-- **EX012.11.** Weighted remainder on the neighborhood of EX012.10: the EX012.10 package
(constants `b₂, M₁, C₂ ≥ 1`, the bilinear, harmonic and `w₂` bounds, the open neighborhoods
`U`, `V` and the analytic map `w`, with the quadratic bound `‖w p‖ ≤ 2 C₂ r²`), together with
the weighted remainder bound `‖w(a,b,τ) - w₂(a,b,τ)‖ ≤ (4 b₂ M₁ C₂ + 4 b₂ C₂²)(|a|+|b|+√|τ|)³`
for every `(a, b, τ) ∈ U`. -/
theorem ex012_11_weighted_remainder (α : ℝ) [HolderExponent α] :
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
        (∀ p ∈ U, ‖w p‖ ≤ 2 * C₂ * (|p.1| + |p.2.1| + Real.sqrt |p.2.2|) ^ 2) ∧
        (∀ a b τ : ℝ, (a, b, τ) ∈ U →
          ‖(w (a, b, τ) : PH α 2) - (((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α 2 2 -
              ((a * b) / 6) • sinMode_EX01228 α 2 2)‖ ≤
            (4 * b₂ * M₁ * C₂ + 4 * b₂ * C₂ ^ 2) * (|a| + |b| + Real.sqrt |τ|) ^ 3) := by
  obtain ⟨b₂, M₁, C₂, hb, hM, hC, hbil, hharm, hW2, U, V, w, hU, hV, h0U, h0V, hanal, hmaps,
    hw0, hiff, hwsmall, hrU, hquad⟩ := ex012_10_quadratic_estimate α
  refine ⟨b₂, M₁, C₂, hb, hM, hC, hbil, hharm, hW2, U, V, w, hU, hV, h0U, h0V, hanal, hmaps,
    hw0, hiff, hwsmall, hrU, hquad, fun a b τ hp => ?_⟩
  have hb0 : (0 : ℝ) ≤ b₂ := by linarith
  have hM0 : (0 : ℝ) ≤ M₁ := by linarith
  have hC0 : (0 : ℝ) ≤ C₂ := by linarith
  have hF : rangeMap_EX01229 α ((a, b, τ), w (a, b, τ)) = 0 :=
    (hiff (a, b, τ) hp (w (a, b, τ)) (hmaps hp)).2 rfl
  have hid := ident_EX01210 (α := α) a b τ (w (a, b, τ)) hF
  have hr0 : 0 ≤ |a| + |b| + Real.sqrt |τ| := by positivity
  have hr1 : |a| + |b| + Real.sqrt |τ| ≤ 1 := (hrU (a, b, τ) hp).trans (min_le_left _ _)
  have hf : ‖a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1‖ ≤
      M₁ * (|a| + |b| + Real.sqrt |τ|) :=
    (hharm a b).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hM0)
  have hu : ‖w (a, b, τ)‖ ≤ 2 * C₂ * (|a| + |b| + Real.sqrt |τ|) ^ 2 := hquad (a, b, τ) hp
  have hB1 := hbil (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1) (w (a, b, τ) : PH α 2)
  have hB2 := hbil (w (a, b, τ) : PH α 2) (w (a, b, τ) : PH α 2)
  have key := remainder_core_EX01211 (b₂ := b₂) (M₁ := M₁) (C₂ := C₂)
    (r := |a| + |b| + Real.sqrt |τ|) hb0 hM0 hC0 hr0 hr1 (w (a, b, τ))
    (⟨((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α 2 2 - (a * b / 6) • sinMode_EX01228 α 2 2,
      wRhs_mem_EX01209 a b τ⟩ : PH.orthSub α 2)
    (bilin_EX01232 α (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1) (w (a, b, τ) : PH α 2))
    (bilin_EX01232 α (w (a, b, τ) : PH α 2) (w (a, b, τ) : PH α 2))
    (a • cosMode_EX01228 α 2 1 + b • sinMode_EX01228 α 2 1) hf hu hB1 hB2 hid
  have hconv : ‖(w (a, b, τ) : PH α 2) - (((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α 2 2 -
      ((a * b) / 6) • sinMode_EX01228 α 2 2)‖ =
      ‖w (a, b, τ) - (⟨((τ - a ^ 2 + b ^ 2) / 12) • cosMode_EX01228 α 2 2 -
        (a * b / 6) • sinMode_EX01228 α 2 2, wRhs_mem_EX01209 a b τ⟩ : PH.orthSub α 2)‖ := by
    rw [← Submodule.norm_coe, Submodule.coe_sub]
  rw [hconv]
  exact key

end Main

end DGPS.Frontier.EX012
