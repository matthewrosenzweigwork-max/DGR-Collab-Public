import DGPS.Lipschitz.MeanFieldLocalFlow

/-!
# LIP032.24: Real L1 and extended-norm bridge

Task id and title: LIP032.24, "Real L1 and ENNReal norm bridge" (node LIP032, contractibility of
the minimizer set; pure integration task, no positive-rate or flow hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.lip032_24_real_l1_ennreal_norm_bridge` : for two real `L²(m)` classes
  `f, f'` the difference `f - f'` is integrable, the real integral `∫ |f - f'| dm` is nonnegative,
  `eLpNorm (f - f') 1 m = ENNReal.ofReal (∫ |f - f'| dm)` (in particular the norm is finite), and
  for every measurable `φ` with `|φ| ≤ M`, `0 ≤ M`, the product `(f - f') φ` is integrable with
  `|∫ (f - f') φ dm| ≤ M ∫ |f - f'| dm`.

## R5 notes
* Hypotheses of the main statement are exactly those of the specification: two classes
  `f f' : L2s d` (the campaign alias `DGPS.Lipschitz.L2s`, an `abbrev` for `Lp ℝ 2 (haar d)`, the
  real `L²(m)`), a function `φ : Torus d → ℝ` that is measurable, and a real `M` with `0 ≤ M`
  and `|φ x| ≤ M` for every `x`. No hypothesis was added; `d` is an arbitrary natural number and
  `m = haar d`.
* The difference is written pointwise as `fun x => f x - f' x` on the coercions of the classes
  (not as the coercion of the difference class); the two agree a.e. but the pointwise form is the
  one in which the integrals and the extended norm are stated.
* "Bounded measurable `φ`" is read as: `Measurable φ` together with the everywhere bound
  `|φ x| ≤ M`. Real finiteness of the integral is expressed by `Integrable` of the difference
  (which gives integrability of its absolute value) and by finiteness of the extended norm.
* Finiteness is established first (membership of the difference in `L²`, then `L¹` on a
  probability space); only afterwards is the extended norm converted into a real integral.
  The Cauchy-Schwarz estimate against the constant one is not stated separately: the inclusion
  `L² ⊆ L¹` on a finite measure space supplies the same finiteness.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- The difference of two real `L²(m)` classes is integrable. -/
theorem integrable_sub_l2s_LIP03224 (f f' : DGPS.Lipschitz.L2s d) :
    Integrable (fun x => f x - f' x) (haar d) :=
  ((Lp.memLp f).sub (Lp.memLp f')).integrable (by norm_num)

/-- The extended `L¹` norm of an integrable function is the extended image of the real integral of
its absolute value. -/
theorem eLpNorm_one_eq_ofReal_integral_abs_LIP03224 {g : Torus d → ℝ}
    (hg : Integrable g (haar d)) :
    eLpNorm g 1 (haar d) = ENNReal.ofReal (∫ x, |g x| ∂haar d) := by
  rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hg]
  · simp only [Real.norm_eq_abs]
  · exact hg.aestronglyMeasurable

/-- **LIP032.24.** For real `L²(m)` classes `f, f'` the difference is integrable, its extended
`L¹` norm is `ofReal` of the (nonnegative) real integral of its absolute value, and for a bounded
measurable test function `φ` the product `(f - f') φ` is integrable with
`|∫ (f - f') φ dm| ≤ M ∫ |f - f'| dm`. -/
theorem lip032_24_real_l1_ennreal_norm_bridge
    (f f' : DGPS.Lipschitz.L2s d) (φ : Torus d → ℝ) (hφ : Measurable φ)
    (M : ℝ) (_hM : 0 ≤ M) (hφM : ∀ x, |φ x| ≤ M) :
    Integrable (fun x => f x - f' x) (haar d) ∧
    0 ≤ ∫ x, |f x - f' x| ∂haar d ∧
    eLpNorm (fun x => f x - f' x) 1 (haar d) = ENNReal.ofReal (∫ x, |f x - f' x| ∂haar d) ∧
    eLpNorm (fun x => f x - f' x) 1 (haar d) < ⊤ ∧
    Integrable (fun x => (f x - f' x) * φ x) (haar d) ∧
    |∫ x, (f x - f' x) * φ x ∂haar d| ≤ M * ∫ x, |f x - f' x| ∂haar d := by
  have hint := integrable_sub_l2s_LIP03224 f f'
  have habs : Integrable (fun x => |f x - f' x|) (haar d) := hint.abs
  have hmajor : Integrable (fun x => M * |f x - f' x|) (haar d) := habs.const_mul M
  have hprod : Integrable (fun x => (f x - f' x) * φ x) (haar d) := by
    refine hmajor.mono' (hint.aestronglyMeasurable.mul hφ.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hφM x) (abs_nonneg _)
  have hnorm := eLpNorm_one_eq_ofReal_integral_abs_LIP03224 hint
  refine ⟨hint, integral_nonneg fun x => abs_nonneg _, hnorm, ?_, hprod, ?_⟩
  · rw [hnorm]
    exact ENNReal.ofReal_lt_top
  · have h1 := norm_integral_le_of_norm_le hmajor
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hφM x) (abs_nonneg _))
    rw [Real.norm_eq_abs, integral_const_mul] at h1
    exact h1

end DGPS.Frontier.LIP032
