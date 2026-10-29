import Mathlib
import DGPS.Frontier.FIN068.T25

/-!
Task id and title: FIN068.26, Composition and negative curvature (module
`DGPS.Frontier.FIN068.T26`).

Provides:
* `DGPS.Frontier.FIN068.first_deriv_FIN06826`: for `q` that is `C^∞` on an open `U` and `y` with
  `y ^ 2 ∈ U`, the derivative of `t ↦ q (t ^ 2)` equals `t ↦ q'(t ^ 2) * (2 * t)` on a neighborhood
  of `y` (helper, not part of the interface).
* `DGPS.Frontier.FIN068.fin068_26_composition_negative_curvature_second_deriv`: for `φ(t) = q(t²)`,
  `φ''(y) = 2 q'(y²) + 4 y² q''(y²)` whenever `y² ∈ U`.
* `DGPS.Frontier.FIN068.fin068_26_composition_negative_curvature`: under the hypotheses of FIN068.25
  (with `U`, `δ`, `c₄`, `M`, `q`), for every `y` with `y² ∈ [-δ, δ]`: (1) the identity for `φ''(y)`;
  (2) `|φ(y) - q 0 + c₄ y⁴| ≤ M |y|⁶ / 6`; (3) `φ''(y) ≤ -12 c₄ y² + 5 M y⁴`; (4) if
  `y² ≤ 6 c₄ / (5 max(1, M))`, then `φ''(y) ≤ -6 c₄ y²`.
* `DGPS.Frontier.FIN068.fin068_26_composition_negative_curvature_radius`: if `0 < δ` and `0 < c₄`,
  there is `ρ > 0` with `ρ² ∈ [-δ, δ]` and `ρ² ≤ 6 c₄ / (5 max(1, M))`.

R5 notes:
* Imports: `Mathlib` and `DGPS.Frontier.FIN068.T25` only. FIN068.03 (`DGPS.Frontier.FIN068.T03`) is
  not imported: the statement is generic in `c₄` and `M`, and the FIN068.03 constants are not used.
  Its import would require the unbuilt legacy module `DGPS.FiniteN.QuarticSaddle` in this worktree.
* Domain: `q` is `C^∞` on an open set `U ⊆ ℝ` with `Set.Icc (-δ) δ ⊆ U`, the smooth domain of
  FIN068.25. The identity for `φ''(y)` is proved only for `y` with `y² ∈ U`, where `φ` is smooth
  near `y`. The bounds are stated for `y` with `y² ∈ Set.Icc (-δ) δ`, the interval of FIN068.25.
* `φ(y) = q(y²)` is written `fun t => q (t ^ 2)`. `φ''(y)` is written
  `deriv (deriv (fun t => q (t ^ 2))) y`. `q'`, `q''`, `q'''` are `deriv q`, `deriv (deriv q)`,
  `deriv (deriv (deriv q))`, as in FIN068.25.
* Task 10's value inequality is stated relative to `q 0`, not to `ψ(w₋)`. The identification
  `q 0 = ψ(w₋)` belongs to FIN068.09 and is not part of this file.
* Task 26 says "the two inequalities in Task 10". These are read as (2), the value bound, and (3),
  the second-derivative bound. Item (4) is the consequence stated in Task 10 ("Thus on any smaller
  interval ..."), and is included because it is the radius condition of Task 26.
* "Choose a positive radius" is read in two forms. The main theorem is for every `y` with `y²` in
  the interval; the radius condition appears as the hypothesis of item (4). The existence lemma
  `..._radius` needs `0 < δ` and `0 < c₄`. These positivity hypotheses are used only there, since a
  positive radius with `ρ² ≤ 6 c₄ / (5 max(1, M))` cannot exist unless `c₄ > 0`.
* `c₄` has no sign hypothesis in the main theorem. Item (4) is vacuous when `c₄ < 0`, since then
  no `y` satisfies its hypothesis.
* `M_q ≥ 0` is included as `hM0`, as in FIN068.25. It is used only through FIN068.25.
* `max(1, M_q)` is written `max 1 M`. The value bound uses `|y|⁶`, matching Task 10, and
  `|y²|³ = |y|⁶` is proved in the file.
-/

open scoped ContDiff

namespace DGPS.Frontier.FIN068

/-- First derivative of `t ↦ q (t ^ 2)` near a point `y` with `y ^ 2 ∈ U`. -/
lemma first_deriv_FIN06826 (q : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hq : ContDiffOn ℝ ∞ q U) (y : ℝ) (hy : y ^ 2 ∈ U) :
    deriv (fun t => q (t ^ 2)) =ᶠ[nhds y] fun t => deriv q (t ^ 2) * (2 * t) := by
  have hq1 : ContDiffOn ℝ 1 q U := hq.of_le (by norm_num)
  have hopen : IsOpen ((fun t : ℝ => t ^ 2) ⁻¹' U) := hU.preimage (continuous_pow 2)
  filter_upwards [hopen.mem_nhds hy] with t ht
  have hdq : DifferentiableAt ℝ q (t ^ 2) :=
    (hq1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)
  have hq' : HasDerivAt q (deriv q (t ^ 2)) ((fun s : ℝ => s ^ 2) t) := hdq.hasDerivAt
  have h2 : HasDerivAt (fun s => q (s ^ 2)) (deriv q (t ^ 2) * (2 * t)) t :=
    (HasDerivAt.comp t (h := fun s : ℝ => s ^ 2) hq' (hasDerivAt_pow 2 t)).congr_deriv (by norm_num)
  exact h2.deriv

/-- Composition formula for the second derivative: `φ(t) = q (t²)` gives
`φ''(y) = 2 q'(y²) + 4 y² q''(y²)` at every `y` with `y² ∈ U`. -/
theorem fin068_26_composition_negative_curvature_second_deriv (q : ℝ → ℝ) (U : Set ℝ)
    (hU : IsOpen U) (hq : ContDiffOn ℝ ∞ q U) (y : ℝ) (hy : y ^ 2 ∈ U) :
    deriv (deriv (fun t => q (t ^ 2))) y =
      2 * deriv q (y ^ 2) + 4 * y ^ 2 * deriv (deriv q) (y ^ 2) := by
  rw [(first_deriv_FIN06826 q U hU hq y hy).deriv_eq]
  have hq3 : ContDiffOn ℝ 3 q U := hq.of_le (by norm_num)
  have hf1 : ContDiffOn ℝ 2 (deriv q) U := hq3.deriv_of_isOpen hU (by norm_num)
  have hd : DifferentiableAt ℝ (deriv q) (y ^ 2) :=
    (hf1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  have hd' : HasDerivAt (deriv q) (deriv (deriv q) (y ^ 2)) ((fun s : ℝ => s ^ 2) y) :=
    hd.hasDerivAt
  have hA : HasDerivAt (fun t => deriv q (t ^ 2)) (deriv (deriv q) (y ^ 2) * (2 * y)) y :=
    (HasDerivAt.comp y (h := fun s : ℝ => s ^ 2) hd' (hasDerivAt_pow 2 y)).congr_deriv (by norm_num)
  have hB : HasDerivAt (fun t : ℝ => 2 * t) 2 y :=
    ((hasDerivAt_id' y).const_mul (2 : ℝ)).congr_deriv (by norm_num)
  have hP := hA.mul hB
  refine hP.deriv.trans ?_
  ring

/-- Composition, value and negative curvature bounds for `φ(t) = q (t²)`, under the hypotheses of
FIN068.25. For every `y` with `y²` in the closed interval `[-δ, δ]`: the second derivative identity,
the value bound, the bound `φ'' ≤ -12 c₄ y² + 5 M y⁴`, and, when `y² ≤ 6 c₄ / (5 max(1, M))`,
the bound `φ'' ≤ -6 c₄ y²`. -/
theorem fin068_26_composition_negative_curvature (q : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (δ c₄ M : ℝ) (hsub : Set.Icc (-δ) δ ⊆ U) (hq : ContDiffOn ℝ ∞ q U) (hM0 : 0 ≤ M)
    (hM : ∀ t ∈ Set.Icc (-δ) δ, |deriv (deriv (deriv q)) t| ≤ M)
    (hq1 : deriv q 0 = 0) (hq2 : deriv (deriv q) 0 = -2 * c₄) :
    ∀ y : ℝ, y ^ 2 ∈ Set.Icc (-δ) δ →
      deriv (deriv (fun t => q (t ^ 2))) y = 2 * deriv q (y ^ 2) + 4 * y ^ 2 * deriv (deriv q) (y ^ 2) ∧
      |q (y ^ 2) - q 0 + c₄ * (y ^ 2) ^ 2| ≤ M * |y| ^ 6 / 6 ∧
      deriv (deriv (fun t => q (t ^ 2))) y ≤ -12 * c₄ * y ^ 2 + 5 * M * y ^ 4 ∧
      (y ^ 2 ≤ 6 * c₄ / (5 * max 1 M) →
        deriv (deriv (fun t => q (t ^ 2))) y ≤ -6 * c₄ * y ^ 2) := by
  intro y hy
  have hyU : y ^ 2 ∈ U := hsub hy
  have h1 := fin068_26_composition_negative_curvature_second_deriv q U hU hq y hyU
  obtain ⟨hv, hg, hl⟩ := fin068_25_three_scalar_taylor_bounds_q q U hU δ c₄ M hsub hq hM0 hM
    hq1 hq2 (y ^ 2) hy
  have hz0 : 0 ≤ y ^ 2 := sq_nonneg y
  have habs : |y ^ 2| = y ^ 2 := abs_of_nonneg hz0
  have hy6 : |y ^ 2| ^ 3 = |y| ^ 6 := by
    rw [habs, ← sq_abs y]
    ring
  have hA : deriv q (y ^ 2) ≤ -2 * c₄ * y ^ 2 + M * (y ^ 2) ^ 2 / 2 := by
    have := (abs_le.mp hg).2
    linarith
  have hB : deriv (deriv q) (y ^ 2) ≤ -2 * c₄ + M * y ^ 2 := by
    have := (abs_le.mp hl).2
    rw [habs] at this
    linarith
  have hC : 4 * y ^ 2 * deriv (deriv q) (y ^ 2) ≤ 4 * y ^ 2 * (-2 * c₄ + M * y ^ 2) :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h3 : deriv (deriv (fun t => q (t ^ 2))) y ≤ -12 * c₄ * y ^ 2 + 5 * M * y ^ 4 := by
    rw [h1]
    nlinarith [hA, hC]
  refine ⟨h1, ?_, h3, ?_⟩
  · rw [hy6] at hv
    exact hv
  · intro hr
    have hm : 0 < 5 * max 1 M := by
      have := le_max_left (1 : ℝ) M
      linarith
    have hmul : y ^ 2 * (5 * max 1 M) ≤ 6 * c₄ := (le_div_iff₀ hm).mp hr
    have hM1 : M ≤ max 1 M := le_max_right 1 M
    have hk : 5 * M * y ^ 2 ≤ 6 * c₄ := by
      nlinarith [mul_le_mul_of_nonneg_right hM1 hz0]
    have hk2 : 5 * M * y ^ 2 * y ^ 2 ≤ 6 * c₄ * y ^ 2 :=
      mul_le_mul_of_nonneg_right hk hz0
    nlinarith [h3, hk2]

/-- Existence of a positive radius: if `0 < δ` and `0 < c₄`, some `ρ > 0` has `ρ²` in `[-δ, δ]`
and `ρ² ≤ 6 c₄ / (5 max(1, M))`. -/
theorem fin068_26_composition_negative_curvature_radius (δ c₄ M : ℝ) (hδ : 0 < δ)
    (hc : 0 < c₄) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ^ 2 ∈ Set.Icc (-δ) δ ∧ ρ ^ 2 ≤ 6 * c₄ / (5 * max 1 M) := by
  have hm : 0 < 5 * max 1 M := by
    have := le_max_left (1 : ℝ) M
    linarith
  have hpos : 0 < min δ (6 * c₄ / (5 * max 1 M)) :=
    lt_min hδ (div_pos (by linarith) hm)
  refine ⟨Real.sqrt (min δ (6 * c₄ / (5 * max 1 M))), Real.sqrt_pos.2 hpos, ?_, ?_⟩
  · rw [Real.sq_sqrt hpos.le]
    exact ⟨by linarith, min_le_left _ _⟩
  · rw [Real.sq_sqrt hpos.le]
    exact min_le_right _ _

end DGPS.Frontier.FIN068
