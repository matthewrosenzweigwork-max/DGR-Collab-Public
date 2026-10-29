import DGPS.Frontier.EX049.T06

/-!
# EX049.07: Uniform correction bound

Task id and title: EX049.07, "Uniform correction bound" (node EX049, frontier unit, leaf
formalization, prerequisite EX049.06).  For a real `h ≥ 2` let `A = 2 / (1 - e^{-2h})`,
`N u = A (1 - e^{-hu}) - u` and `Q u = N u / (u (2 - u))`, as in EX049.06.  Let `g` be a smooth
extension of `Q` to an open neighborhood of `[0,2]`, and let `R u = ∫_0^u g`.  Then for every
`u ∈ [0,2]` we have `0 ≤ R u ≤ 4 + 3 log h`, and `4 + 3 log h ≤ 6 √h`.

The proof splits `[0,2]` at `1/h` and `1`.  On `[0,1/h]` the bound `g ≤ 3h` gives at most `3`.
On `[1/h,1]` the bound `g ≤ 3/u` gives at most `3 log h`.  On `[1,2]` the bound `g ≤ 1` gives at
most `1`.  Nonnegativity of `g` makes the primitive monotone, so `R u ≤ R 2`.

## Provides
* `DGPS.Frontier.EX049.ex049_07_uniform_correction_bound` : the main statement, for `2 ≤ h`, with
  three conjuncts.  (i) A smooth extension `g` of `Q` on an open `U ⊇ [0,2]` exists, inherited from
  the existence conjunct of EX049.06.  (ii) For every smooth extension `g` of `Q` on an open
  `U ⊇ [0,2]` and every `u ∈ [0,2]`, `0 ≤ ∫_0^u g` and `∫_0^u g ≤ 4 + 3 log h`.  (iii)
  `4 + 3 log h ≤ 6 √h`.
* `DGPS.Frontier.EX049.intervalIntegrable_EX04907` : a function continuous on `[0,2]` is interval
  integrable between any two points of `[0,2]`.
* `DGPS.Frontier.EX049.integrable_inv_EX04907` : the function `x ↦ 3 / x` is interval integrable on
  `[a,b]` when `0 < a ≤ b`.
* `DGPS.Frontier.EX049.integral_bounds_EX04907` : conjunct (ii) for one fixed smooth extension.
* `DGPS.Frontier.EX049.sqrt_chain_EX04907` : conjunct (iii), `4 + 3 log h ≤ 6 √h` for `2 ≤ h`.

## R5 notes
* The only hypothesis of the main statement is `2 ≤ h`, the specification's "for every `h ≥ 2`".
  No hypothesis is added, and nothing is weakened.
* The specification writes `R_h(u) = ∫_0^u r_h(s) ds` with `r_h` the smooth extension of `Q`.  Here
  `r_h` is read as an arbitrary smooth extension `g` of `Q` on an open `U ⊇ [0,2]`, as in EX049.06,
  and `R_h` is `u ↦ ∫ s in 0..u, g s`.  The integral over `[0,u] ⊆ [0,2]` depends only on `g` there,
  and `g` is determined on `[0,2]` by continuity from `(0,2)`, so every admissible extension gives
  the same `R_h`.
* Conjunct (i) is the existence statement of EX049.06, included so that the universal bound in
  conjunct (ii) is not vacuous.  It is a conjunct, not a hypothesis.
* The bound `R_h(u) ≤ 4 + 3 log h` is stated for each `u ∈ [0,2]` as the specification states it.
  It is proved by monotonicity: `R_h(u) ≤ R_h(2)` because `g ≥ 0` on `[u,2]`, and `R_h(2)` is bounded
  by the three piece bounds.  The pieces need `1/h ∈ (0,1]`, which holds since `h ≥ 2`.
* The integral of the reciprocal is Mathlib's `integral_one_div_of_pos`, applied on `[1/h,1]`.
* The inequality `4 + 3 log h ≤ 6 √h` is proved from `log x ≤ x - 1` at `x = √h`, with
  `log h = 2 log √h`.  It is a statement about `h` alone and does not depend on `g`.
* The binding of `R_h` to the campaign object `corr` is not proved here.  It is the open task
  EX049.25, as stated in the specification.
-/

open scoped ContDiff
open Set

namespace DGPS.Frontier.EX049

/-- A function continuous on `[0,2]` is interval integrable between two points of `[0,2]`. -/
theorem intervalIntegrable_EX04907 {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (0:ℝ) 2)) {a b : ℝ}
    (ha : a ∈ Icc (0:ℝ) 2) (hb : b ∈ Icc (0:ℝ) 2) :
    IntervalIntegrable g MeasureTheory.volume a b :=
  ContinuousOn.intervalIntegrable (hg.mono (uIcc_subset_Icc ha hb))

/-- The function `x ↦ 3 / x` is interval integrable on `[a,b]` when `0 < a ≤ b`. -/
theorem integrable_inv_EX04907 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ => 3 / x) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact continuousOn_const.div continuousOn_id (fun x hx => (lt_of_lt_of_le ha hx.1).ne')

/-- Conjunct (ii) for one smooth extension `g` of `quot_EX04906 h` on an open `U ⊇ [0,2]`. -/
theorem integral_bounds_EX04907 (h : ℝ) (hh : 2 ≤ h) (g : ℝ → ℝ) (U : Set ℝ)
    (hI : Icc (0:ℝ) 2 ⊆ U) (hc : ContDiffOn ℝ ∞ g U)
    (hQg : ∀ u ∈ Ioo (0:ℝ) 2, g u = quot_EX04906 h u) :
    ∀ u ∈ Icc (0:ℝ) 2,
      0 ≤ (∫ s in (0:ℝ)..u, g s) ∧ (∫ s in (0:ℝ)..u, g s) ≤ 4 + 3 * Real.log h := by
  obtain ⟨hnn, hb1, hb2, hb3⟩ := bounds_EX04906 h hh g U hI hc hQg
  have hgc : ContinuousOn g (Icc (0:ℝ) 2) := hc.continuousOn.mono hI
  have hpos : 0 < h := by linarith
  have hh0 : h ≠ 0 := hpos.ne'
  have hp0 : 0 < 1 / h := one_div_pos.2 hpos
  have hp1 : 1 / h ≤ 1 := by
    rw [div_le_iff₀ hpos]
    linarith
  have hm02 : (0:ℝ) ∈ Icc (0:ℝ) 2 := ⟨le_rfl, by norm_num⟩
  have hm2 : (2:ℝ) ∈ Icc (0:ℝ) 2 := ⟨by norm_num, le_rfl⟩
  have hmp : 1 / h ∈ Icc (0:ℝ) 2 := ⟨hp0.le, by linarith⟩
  have hm1 : (1:ℝ) ∈ Icc (0:ℝ) 2 := ⟨by norm_num, by norm_num⟩
  -- Split the integral over `[0,2]` at `1/h` and at `1`.
  have hA : (∫ s in (0:ℝ)..(1 / h), g s) + (∫ s in (1 / h)..2, g s) =
      ∫ s in (0:ℝ)..2, g s :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_EX04907 hgc hm02 hmp) (intervalIntegrable_EX04907 hgc hmp hm2)
  have hB : (∫ s in (1 / h)..1, g s) + (∫ s in (1:ℝ)..2, g s) =
      ∫ s in (1 / h)..2, g s :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_EX04907 hgc hmp hm1) (intervalIntegrable_EX04907 hgc hm1 hm2)
  -- Piece on `[0,1/h]`: `g ≤ 3h` and `(1/h) · 3h = 3`.
  have hI1 : (∫ s in (0:ℝ)..(1 / h), g s) ≤ ∫ s in (0:ℝ)..(1 / h), (3 * h) :=
    intervalIntegral.integral_mono_on hp0.le (intervalIntegrable_EX04907 hgc hm02 hmp)
      (continuous_const.intervalIntegrable _ _)
      (fun s hs => hb1 s ⟨hs.1, hs.2.trans hp1⟩)
  have e1 : (∫ s in (0:ℝ)..(1 / h), (3 * h)) = 3 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    have hcalc : (1 / h - 0) * (3 * h) = 3 * (h⁻¹ * h) := by ring
    rw [hcalc, inv_mul_cancel₀ hh0, mul_one]
  -- Piece on `[1/h,1]`: `g ≤ 3/u` and the reciprocal integral.
  have hI2 : (∫ s in (1 / h)..1, g s) ≤ ∫ s in (1 / h)..1, 3 / s :=
    intervalIntegral.integral_mono_on hp1 (intervalIntegrable_EX04907 hgc hmp hm1)
      (integrable_inv_EX04907 hp0 hp1) (fun s hs => hb3 s hs)
  have e4 : (∫ s in (1 / h)..1, 3 / s) = 3 * Real.log h := by
    have hfun : (fun s : ℝ => 3 / s) = fun s => 3 * (1 / s) := by
      funext s
      ring
    rw [hfun, intervalIntegral.integral_const_mul, integral_one_div_of_pos hp0 one_pos,
      one_div_one_div]
  -- Piece on `[1,2]`: `g ≤ 1`.
  have hI3 : (∫ s in (1:ℝ)..2, g s) ≤ ∫ s in (1:ℝ)..2, (1:ℝ) :=
    intervalIntegral.integral_mono_on (by norm_num) (intervalIntegrable_EX04907 hgc hm1 hm2)
      (continuous_const.intervalIntegrable _ _) (fun s hs => hb2 s hs)
  have e3 : (∫ s in (1:ℝ)..2, (1:ℝ)) = 1 := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    norm_num
  have hsum : (∫ s in (0:ℝ)..2, g s) ≤ 4 + 3 * Real.log h := by
    linarith
  intro u hu
  have hnu : 0 ≤ ∫ s in (0:ℝ)..u, g s :=
    intervalIntegral.integral_nonneg hu.1 (fun s hs => hnn s ⟨hs.1, hs.2.trans hu.2⟩)
  have hsplit : (∫ s in (0:ℝ)..u, g s) + (∫ s in u..2, g s) = ∫ s in (0:ℝ)..2, g s :=
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_EX04907 hgc hm02 hu) (intervalIntegrable_EX04907 hgc hu hm2)
  have htail : 0 ≤ ∫ s in u..2, g s :=
    intervalIntegral.integral_nonneg hu.2 (fun s hs => hnn s ⟨le_trans hu.1 hs.1, hs.2⟩)
  exact ⟨hnu, by linarith⟩

/-- Conjunct (iii): `4 + 3 log h ≤ 6 √h` for `2 ≤ h`, from `log x ≤ x - 1` at `x = √h`. -/
theorem sqrt_chain_EX04907 (h : ℝ) (hh : 2 ≤ h) : 4 + 3 * Real.log h ≤ 6 * Real.sqrt h := by
  have hpos : 0 < h := by linarith
  have hsq : 0 < Real.sqrt h := Real.sqrt_pos.2 hpos
  have hlog : Real.log (Real.sqrt h) ≤ Real.sqrt h - 1 := Real.log_le_sub_one_of_pos hsq
  have hlh : Real.log h = 2 * Real.log (Real.sqrt h) := by
    rw [Real.log_sqrt hpos.le]
    ring
  linarith

/-- Uniform correction bound.  For every real `h ≥ 2`, with `A`, `N`, `Q` as in EX049.06:
(i) a smooth extension of `Q` to an open neighborhood of `[0,2]` exists; (ii) every smooth
extension `g` of `Q` on an open `U ⊇ [0,2]` satisfies `0 ≤ ∫_0^u g ≤ 4 + 3 log h` for all
`u ∈ [0,2]`; (iii) `4 + 3 log h ≤ 6 √h`. -/
theorem ex049_07_uniform_correction_bound (h : ℝ) (hh : 2 ≤ h) :
    let A : ℝ := 2 / (1 - Real.exp (-(2 * h)))
    let N : ℝ → ℝ := fun u => A * (1 - Real.exp (-(h * u))) - u
    let Q : ℝ → ℝ := fun u => N u / (u * (2 - u))
    (∃ g : ℝ → ℝ, ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (0:ℝ) 2 ⊆ U ∧ ContDiffOn ℝ ∞ g U ∧
        ∀ u ∈ Set.Ioo (0:ℝ) 2, g u = Q u) ∧
    (∀ g : ℝ → ℝ, ∀ U : Set ℝ, IsOpen U → Set.Icc (0:ℝ) 2 ⊆ U → ContDiffOn ℝ ∞ g U →
        (∀ u ∈ Set.Ioo (0:ℝ) 2, g u = Q u) →
        ∀ u ∈ Set.Icc (0:ℝ) 2,
          0 ≤ (∫ s in (0:ℝ)..u, g s) ∧ (∫ s in (0:ℝ)..u, g s) ≤ 4 + 3 * Real.log h) ∧
    4 + 3 * Real.log h ≤ 6 * Real.sqrt h := by
  intro A N Q
  refine ⟨(ex049_06_pointwise_correction_derivative_bounds h hh).1, ?_, sqrt_chain_EX04907 h hh⟩
  intro g U _ hI hc hQg
  exact integral_bounds_EX04907 h hh g U hI hc hQg

end DGPS.Frontier.EX049
