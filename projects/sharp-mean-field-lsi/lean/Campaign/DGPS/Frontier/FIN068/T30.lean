import DGPS.Frontier.FIN068.T07
import DGPS.Frontier.FIN068.T27

/-!
Task id and title: FIN068.30, Exact second-order factorization (module
`DGPS.Frontier.FIN068.T30`).

Provides:
* `DGPS.Frontier.FIN068.fin068_30_exact_second_order_factorization`: there are `δu, δz > 0` and a
  curve `a` with the critical-curve data of FIN068.07/FIN068.24 (`C^∞` on `Set.Ioo (-δz) δz`,
  `a 0 = 0`, the critical equation for `J_u`, uniqueness of its zero in the window), and there are
  `δx, δy > 0` such that, with `x₀ y = -4 + a (y^2)` and the open rectangle
  `P = (-4-δx, -4+δx) × (-δy, δy)`: for `(x, y) ∈ P` and `t ∈ [0,1]` the point
  `(x₀ y + t (x - x₀ y), y)` lies in the fixed rectangle `R = (-5,-3) × (-1,1)` (as in FIN068.27);
  for `(x, y) ∈ P` the first-order condition `ψ_x (x₀ y, y) = 0` holds; and, with `h = x - x₀ y`,
  `ψ(x, y) - ψ(x₀ y, y) = h^2 * ∫₀¹ (1 - t) ψ_xx(x₀ y + t h, y) dt`.
* Helper declarations, all with suffix `_FIN06830` (not part of the interface):
  `taylor_FIN06830` (the scalar second-order integral Taylor identity on a segment, with the
  first-order term kept), `slice_smooth_FIN06830` (the slice `s ↦ ψ(s, y)` is `C^∞` on
  `(-5, -3)` for `|y| < 1`), `hasDerivAt_slice_FIN06830` (the first two slice derivatives of `ψ`
  exist at points of `(-5, -3)`), `factor_FIN06830` (the factorization on a segment inside `(-5, -3)`
  for `|y| < 1`, with the first-order term kept).

Proof: the curve and the patch are obtained exactly as in FIN068.27, by continuity of the
FIN068.24 curve at `0`. On `P` the segment from `x₀ y` to `x` stays in `(-5,-3)`, where the slice
`s ↦ ψ(s, y)` is `C^∞`. The scalar identity `f x - f p = (x - p) f'(p) + (x - p)^2 ∫₀¹ (1 - t)
f''(p + t (x - p)) dt` follows from one integration by parts (no division by `x - p`, so the case
`x = x₀ y` needs no separate treatment). The linear term is `h ψ_x(x₀ y, y) = 0` by the critical
equation of FIN068.24.

R5 notes:
* No hypothesis is added. The statement is closed (existential in the curve and the patch). The
  specification says "for `(x, y) ∈ P`" with `P` the patch of FIN068.27; since FIN068.27's statement
  does not expose the critical equation `ψ_x (x₀ y, y) = 0` on `P` (it does not record
  `y^2 < δz`), the patch is re-obtained here from the same FIN068.24 curve by the same argument
  (`δx = 1/2`, `δy` below `1`, below `δz` in the square, and below the continuity radius of the
  curve). Thus `P` here is a patch of the FIN068.27 kind, not literally the one object chosen
  inside FIN068.27's existential. This is a non-literal reading, forced by the existential form.
* The segment-containment conjunct is repeated from FIN068.27 so that the patch is pinned down.
* `ψ(x, y)` is `quarticPsi_FIN066 !₂[x, y]`, as in FIN068.27. `ψ_xx` is read as the second
  derivative of the slice `s ↦ ψ(s, y)`, `deriv (deriv (fun s => quarticPsi_FIN066 !₂[s, y]))`,
  evaluated at `x₀ y + t (x - x₀ y)`, as in FIN068.27 and FIN068.11. `x₀ y` is `-4 + a (y^2)`,
  the FIN068.24 curve (FIN068.23).
* The integral is the interval integral `∫ t in (0:ℝ)..1`, with the integrand
  `(1 - t) * ψ_xx(x₀ y + t * (x - x₀ y), y)`. The factor `h^2` is `(x - x₀ y)^2`. The `a₂` of
  FIN068.11 (with the factor `2`) is not introduced here.
* The additional conjunct `ψ_x (x₀ y, y) = 0` on `P` is the first-order condition used in the
  proof; it is recorded in the statement because the consuming tasks use it on `P`. It follows
  from the FIN068.24 critical equation, so it adds no hypothesis.
* Smoothness of `ψ` on `R` is inherited from FIN068.27 (`psi_smooth_FIN06827`), hence from
  FIN068.04 and the FIN068.37 and FIN068.38 identifications; this dependency is not repaired here.
-/

open DGPS.FiniteN.QuarticSaddleGlobalFIN066
open scoped ContDiff Topology

namespace DGPS.Frontier.FIN068

/-- The scalar second-order integral Taylor identity on the segment from `p` to `x`, with the
linear term kept. No division by `x - p`. -/
lemma taylor_FIN06830 {f f' f'' : ℝ → ℝ} {p x : ℝ}
    (h1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' (p + t * (x - p))) (p + t * (x - p)))
    (h2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f' (f'' (p + t * (x - p))) (p + t * (x - p)))
    (h3 : ContinuousOn (fun t : ℝ => f'' (p + t * (x - p))) (Set.Icc 0 1)) :
    f x - f p = (x - p) * f' p +
      (x - p) ^ 2 * ∫ t in (0 : ℝ)..1, (1 - t) * f'' (p + t * (x - p)) := by
  have hlin : ∀ t : ℝ, HasDerivAt (fun r : ℝ => p + r * (x - p)) (x - p) t := by
    intro t
    simpa using ((hasDerivAt_id t).mul_const (x - p)).const_add p
  have hu : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun r : ℝ => 1 - r) (-1) t := by
    intro t _
    simpa using (hasDerivAt_id t).const_sub 1
  have hv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => f' (p + r * (x - p)) * (x - p))
        (f'' (p + t * (x - p)) * (x - p) * (x - p)) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact ((h2 t ht).scomp t (hlin t)).mul_const (x - p) |>.congr_deriv (by simp only [smul_eq_mul]; ring)
  have hg : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun r : ℝ => f (p + r * (x - p))) (f' (p + t * (x - p)) * (x - p)) t := by
    intro t ht
    rw [Set.uIcc_of_le zero_le_one] at ht
    exact ((h1 t ht).scomp t (hlin t)).congr_deriv (by simp only [smul_eq_mul]; ring)
  have hf'cont : ContinuousOn (fun t : ℝ => f' (p + t * (x - p))) (Set.Icc 0 1) := by
    intro t ht
    exact (ContinuousAt.comp (f := fun r : ℝ => p + r * (x - p)) (g := f')
      (h2 t ht).continuousAt (hlin t).continuousAt).continuousWithinAt
  have hvint : IntervalIntegrable (fun t : ℝ => f' (p + t * (x - p)) * (x - p)) MeasureTheory.volume
      0 1 :=
    (hf'cont.mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one
  have hv'int : IntervalIntegrable (fun t : ℝ => f'' (p + t * (x - p)) * (x - p) * (x - p))
      MeasureTheory.volume 0 1 :=
    ((h3.mul continuousOn_const).mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
    (intervalIntegrable_const) hv'int
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hg hvint
  simp only [zero_mul, add_zero, one_mul, sub_self, zero_sub, neg_mul,
    intervalIntegral.integral_neg, sub_zero, add_sub_cancel] at hparts hftc
  have hint : ∫ t in (0 : ℝ)..1, (1 - t) * (f'' (p + t * (x - p)) * (x - p) * (x - p)) =
      (x - p) ^ 2 * ∫ t in (0 : ℝ)..1, (1 - t) * f'' (p + t * (x - p)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr (fun t _ => ?_)
    ring
  rw [← hint, hparts]
  linarith

/-- The slice `s ↦ ψ(s, y)` is `C^∞` on `(-5, -3)` when `|y| < 1`. -/
lemma slice_smooth_FIN06830 {y : ℝ} (hy : |y| < 1) :
    ContDiffOn ℝ ∞ (fun s : ℝ => quarticPsi_FIN066 !₂[s, y]) (Set.Ioo (-5 : ℝ) (-3)) := by
  have := psi_smooth_FIN06827.comp
    (by fun_prop : ContDiff ℝ ∞ (fun s : ℝ => (s, y))).contDiffOn
    (fun s hs => Set.mk_mem_prod hs (abs_lt.mp hy))
  exact this

/-- The first two slice derivatives of `ψ` exist at points of `(-5, -3)` for `|y| < 1`, and the
second one is continuous there. -/
lemma hasDerivAt_slice_FIN06830 {y : ℝ} (hy : |y| < 1) :
    (∀ s ∈ Set.Ioo (-5 : ℝ) (-3), HasDerivAt (fun r : ℝ => quarticPsi_FIN066 !₂[r, y])
      (deriv (fun r : ℝ => quarticPsi_FIN066 !₂[r, y]) s) s) ∧
    (∀ s ∈ Set.Ioo (-5 : ℝ) (-3), HasDerivAt (deriv (fun r : ℝ => quarticPsi_FIN066 !₂[r, y]))
      (deriv (deriv (fun r : ℝ => quarticPsi_FIN066 !₂[r, y])) s) s) ∧
    ContinuousOn (deriv (deriv (fun r : ℝ => quarticPsi_FIN066 !₂[r, y]))) (Set.Ioo (-5 : ℝ) (-3)) := by
  have hf := slice_smooth_FIN06830 hy
  have hf1 : ContDiffOn ℝ ∞ (deriv (fun r : ℝ => quarticPsi_FIN066 !₂[r, y]))
      (Set.Ioo (-5 : ℝ) (-3)) := hf.deriv_of_isOpen isOpen_Ioo (by simp)
  have hf2 : ContDiffOn ℝ ∞ (deriv (deriv (fun r : ℝ => quarticPsi_FIN066 !₂[r, y])))
      (Set.Ioo (-5 : ℝ) (-3)) := hf1.deriv_of_isOpen isOpen_Ioo (by simp)
  refine ⟨fun s hs => ?_, fun s hs => ?_, hf2.continuousOn⟩
  · exact ((hf.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hs)).hasDerivAt
  · exact ((hf1.differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hs)).hasDerivAt

/-- On the segment from `p` to `x` inside `(-5, -3)` and for `|y| < 1`, the exact second-order
factorization holds with the first-order term `(x - p) ψ_x(p, y)`. -/
lemma factor_FIN06830 {y p x : ℝ} (hy : |y| < 1)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, p + t * (x - p) ∈ Set.Ioo (-5 : ℝ) (-3)) :
    quarticPsi_FIN066 !₂[x, y] - quarticPsi_FIN066 !₂[p, y] =
      (x - p) * deriv (fun r : ℝ => quarticPsi_FIN066 !₂[r, y]) p +
      (x - p) ^ 2 * ∫ t in (0 : ℝ)..1,
        (1 - t) * deriv (deriv (fun r : ℝ => quarticPsi_FIN066 !₂[r, y])) (p + t * (x - p)) := by
  obtain ⟨d1, d2, c2⟩ := hasDerivAt_slice_FIN06830 hy
  refine taylor_FIN06830 (fun t ht => d1 _ (hseg t ht)) (fun t ht => d2 _ (hseg t ht)) ?_
  exact c2.comp (by fun_prop : Continuous fun t : ℝ => p + t * (x - p)).continuousOn hseg

/-- Exact second-order factorization (FIN068.30). -/
theorem fin068_30_exact_second_order_factorization :
    ∃ δu δz : ℝ, 0 < δu ∧ 0 < δz ∧ ∃ a : ℝ → ℝ,
      ContDiffOn ℝ ∞ a (Set.Ioo (-δz) δz) ∧ a 0 = 0 ∧
      (∀ z : ℝ, |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) (a z) = 0) ∧
      (∀ u z : ℝ, |u| < δu → |z| < δz →
        deriv (fun s : ℝ => liftPotential_FIN06804 s z) u = 0 → u = a z) ∧
      ∃ δx δy : ℝ, 0 < δx ∧ 0 < δy ∧
        (∀ x y t : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
          t ∈ Set.Icc (0 : ℝ) 1 →
          (-4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2))), y) ∈
            Set.Ioo (-5 : ℝ) (-3) ×ˢ Set.Ioo (-1 : ℝ) 1) ∧
        (∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
          deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, y]) (-4 + a (y ^ 2)) = 0) ∧
        ∀ x y : ℝ, (x, y) ∈ Set.Ioo (-4 - δx) (-4 + δx) ×ˢ Set.Ioo (-δy) δy →
          quarticPsi_FIN066 !₂[x, y] - quarticPsi_FIN066 !₂[-4 + a (y ^ 2), y] =
            (x - (-4 + a (y ^ 2))) ^ 2 * ∫ t in (0 : ℝ)..1, (1 - t) *
              deriv (deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, y]))
                (-4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2)))) := by
  obtain ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, -⟩ := fin068_24_curve_taylor_bound_composition
  refine ⟨δu, δz, hu, hz, a, h1, h2, h3, h4, ?_⟩
  have hc0 : ContinuousAt a 0 :=
    h1.continuousOn.continuousAt (isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩)
  obtain ⟨ε, hε, hεa⟩ := Metric.continuousAt_iff.1 hc0 (1 / 2) (by norm_num)
  obtain ⟨δy, hδy, hyprop⟩ : ∃ δy : ℝ, 0 < δy ∧ ∀ y : ℝ, |y| < δy →
      y ^ 2 < ε ∧ y ^ 2 < δz ∧ |y| < 1 := by
    refine ⟨min (min ε δz) 1, lt_min (lt_min hε hz) one_pos, fun y hy => ?_⟩
    have hy1 : |y| < 1 := lt_of_lt_of_le hy (min_le_right _ _)
    have hy2 : |y| < min ε δz := lt_of_lt_of_le hy (min_le_left _ _)
    have hsq : y ^ 2 ≤ |y| := by
      rw [← sq_abs]
      nlinarith [abs_nonneg y, mul_nonneg (abs_nonneg y) (sub_nonneg.2 hy1.le)]
    refine ⟨?_, ?_, hy1⟩
    · exact lt_of_le_of_lt hsq (lt_of_lt_of_le hy2 (min_le_left _ _))
    · exact lt_of_le_of_lt hsq (lt_of_lt_of_le hy2 (min_le_right _ _))
  have hα : ∀ y : ℝ, |y| < δy → -(1 / 2 : ℝ) < a (y ^ 2) ∧ a (y ^ 2) < 1 / 2 := by
    intro y hy
    have hd : dist (y ^ 2) 0 < ε := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (sq_nonneg y)]
      exact (hyprop y hy).1
    have := hεa hd
    rw [Real.dist_eq, h2, sub_zero] at this
    exact abs_lt.mp this
  have hseg : ∀ x y t : ℝ, x ∈ Set.Ioo (-4 - (1 / 2 : ℝ)) (-4 + 1 / 2) → |y| < δy →
      t ∈ Set.Icc (0 : ℝ) 1 →
      -4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2))) ∈ Set.Ioo (-5 : ℝ) (-3) := by
    intro x y t hx hy ht
    obtain ⟨hα1, hα2⟩ := hα y hy
    obtain ⟨hx1, hx2⟩ := hx
    have hconv := (convex_Ioo (-(1 / 2 : ℝ)) (1 / 2))
      (show a (y ^ 2) ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) from ⟨hα1, hα2⟩)
      (show x + 4 ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) from ⟨by linarith, by linarith⟩)
      (sub_nonneg.2 ht.2) ht.1 (by ring)
    simp only [smul_eq_mul] at hconv
    obtain ⟨hc1, hc2⟩ := hconv
    have e : -4 + a (y ^ 2) + t * (x - (-4 + a (y ^ 2)))
        = -4 + ((1 - t) * a (y ^ 2) + t * (x + 4)) := by ring
    rw [e]
    exact ⟨by linarith, by linarith⟩
  have hcrit : ∀ y : ℝ, |y| < δy →
      deriv (fun s : ℝ => quarticPsi_FIN066 !₂[s, y]) (-4 + a (y ^ 2)) = 0 := by
    intro y hy
    obtain ⟨hα1, hα2⟩ := hα y hy
    obtain ⟨-, hyz, hy1⟩ := hyprop y hy
    have hsq : 0 ≤ y ^ 2 := sq_nonneg y
    exact critical_equation_FIN06824 (by nlinarith [abs_lt.mp hy1])
      (abs_lt.mpr ⟨by linarith, by linarith⟩)
      (h3 (y ^ 2) (by rw [abs_of_nonneg hsq]; exact hyz))
  refine ⟨1 / 2, δy, by norm_num, hδy, ?_, ?_, ?_⟩
  · intro x y t hP ht
    obtain ⟨hx, hy⟩ := hP
    exact Set.mk_mem_prod (hseg x y t hx (abs_lt.mpr hy) ht)
      (abs_lt.mp (hyprop y (abs_lt.mpr hy)).2.2)
  · intro x y hP
    exact hcrit y (abs_lt.mpr hP.2)
  · intro x y hP
    obtain ⟨hx, hy⟩ := hP
    have hy' : |y| < δy := abs_lt.mpr hy
    have key := factor_FIN06830 (y := y) (p := -4 + a (y ^ 2)) (x := x)
      (hyprop y hy').2.2 (fun t ht => hseg x y t hx hy' ht)
    rw [hcrit y hy', mul_zero, zero_add] at key
    exact key

end DGPS.Frontier.FIN068
