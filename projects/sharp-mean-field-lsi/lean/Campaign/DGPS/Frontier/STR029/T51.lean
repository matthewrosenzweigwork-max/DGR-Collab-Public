import DGPS.Frontier.STR029.T13

/-!
# STR029.51: Explicit Hölder norm bound for the range inverse

Task id: STR029.51. Title: Explicit Hölder norm bound for the range inverse (node STR029, size L).

Statement (specification): the linear construction `f ↦ w` of `.13` (`w = v - a cos t - b sin t`,
`v(t) = ∫_0^t sin(t - s) f(s) ds`) satisfies `‖w‖_{2,α} ≤ (1 + 30π + 10π²) ‖f‖_{0,α}` for `α = 1/2`.

Provides (every declaration is in the namespace `DGPS.Frontier.STR029`):
* `DGPS.Frontier.STR029.str029_51_explicit_holder_norm_bound_range_inverse`: for `f ∈ Y` at the exponent
  `α = 1/2` (`InY_STR02913 (1/2) f`),
  `c2Norm_STR02901 (1/2) (wRight_STR02913 f) ≤ (1 + 30π + 10π²) * c0Norm_STR02953 (1/2) f`.
* `DGPS.Frontier.STR029.str029_51_explicit_holder_norm_bound_range_inverse_general`: the same bound for every
  `[HolderExponent α]` (`0 < α < 1`), with the same constant.

R5 notes:
* Carriers and norms are the concrete ones of `.01`, `.53` and `.13`: the norm `‖f‖_{0,α}` is
  `c0Norm_STR02953 α f = supNorm f + circHolder_STR02901 α f`, the norm `‖w‖_{2,α}` is
  `c2Norm_STR02901 α w = ‖w‖∞ + ‖w'‖∞ + ‖w''‖∞ + [w'']_α`, with `w'` and `w''` read as `deriv w`
  and `deriv (deriv w)`, and the linear construction is `wRight_STR02913`. The suprema `supNorm` are taken
  over all of `ℝ`; since the functions involved are `2π`-periodic this agrees with the supremum over
  one period, and the bounds are proved on `[0, 2π]` and transported by periodicity.
* The hypothesis is `f ∈ Y` exactly as in `.13` (`InY_STR02913 α f`); nothing is added.
* Exponent: the specification fixes `α = 1/2`, and the main theorem is stated for that literal value. As in
  `.13` the bound is also proved for every `[HolderExponent α]`; only `α ≤ 1` and `0 < α` are used,
  through `π^(1-α) ≤ π`. This generalizes the exponent only.
* The estimate follows the written proof: `|v|, |v'| ≤ 2π ‖f‖∞` (kernel bound `|sin|, |cos| ≤ 1` on a path of
  length at most `2π`), `|a|, |b| ≤ 4π ‖f‖∞` (from `2 ∫ |v|`), hence `‖w‖∞, ‖w'‖∞ ≤ 10π ‖f‖∞` and
  `‖w''‖∞ ≤ (1 + 10π) ‖f‖∞` from `w'' = f - w`. The seminorm of `w''` is bounded by `[f]_α` plus the
  circular Lipschitz bound `|w s - w t| ≤ ‖w'‖∞ d(s,t) ≤ π^(1-α) ‖w'‖∞ d(s,t)^α`, using `d ≤ π`
  (`circDist_le_pow_STR02953`), and finally `π^(1-α) ≤ π`.
* The formula for `v'` used here is the one proved in `.13` (`vDeriv_STR02913` equals
  `t ↦ ∫_0^t cos(t - s) f(s) ds`), so no new differentiation under the integral is needed.
-/

open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-- A kernel bounded by one, integrated against a function bounded by `M` along `[0, t] ⊆ [0, 2π]`. -/
theorem abs_kernel_integral_le_STR02951 {f : ℝ → ℝ} {M : ℝ} (hM : ∀ s, |f s| ≤ M) (k : ℝ → ℝ)
    (hk : ∀ x, |k x| ≤ 1) {t : ℝ} (ht : t ∈ Set.Icc 0 (2 * Real.pi)) :
    |∫ s in (0 : ℝ)..t, k (t - s) * f s| ≤ 2 * Real.pi * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
    (f := fun s => k (t - s) * f s) (C := M) (fun x _ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul (hk _) (hM x) (abs_nonneg _) zero_le_one).trans_eq (one_mul M))
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg ht.1] at h
  calc |∫ s in (0 : ℝ)..t, k (t - s) * f s| ≤ M * t := h
    _ ≤ M * (2 * Real.pi) := mul_le_mul_of_nonneg_left ht.2 hM0
    _ = 2 * Real.pi * M := by ring

/-- A bound on one period of a periodic function holds everywhere. -/
theorem periodic_bound_STR02951 {G : ℝ → ℝ} (hper : Function.Periodic G (2 * Real.pi)) {B : ℝ}
    (h : ∀ t ∈ Set.Icc 0 (2 * Real.pi), |G t| ≤ B) (t : ℝ) : |G t| ≤ B := by
  obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ Real.two_pi_pos t
  rw [hxy]
  exact h y (Set.Ico_subset_Icc_self hy)

/-- Bounds for `w` and `w'` once `v`, `v'` and the coefficients are bounded. -/
theorem wGen_bounds_STR02951 {f : ℝ → ℝ} {M a b : ℝ} (hM0 : 0 ≤ M)
    (hv : ∀ t, |vRight_STR02913 f t| ≤ 2 * Real.pi * M)
    (hd : ∀ t, |vDeriv_STR02913 f t| ≤ 2 * Real.pi * M)
    (ha : |a| ≤ 4 * Real.pi * M) (hb : |b| ≤ 4 * Real.pi * M) (t : ℝ) :
    |wGen_STR02913 f a b t| ≤ 10 * Real.pi * M ∧ |wGen1_STR02913 f a b t| ≤ 10 * Real.pi * M := by
  have h4 : 0 ≤ 4 * Real.pi * M := by positivity
  have hac : |a * Real.cos t| ≤ 4 * Real.pi * M := by
    rw [abs_mul]
    exact (mul_le_mul ha (Real.abs_cos_le_one t) (abs_nonneg _) h4).trans_eq (mul_one _)
  have has : |a * Real.sin t| ≤ 4 * Real.pi * M := by
    rw [abs_mul]
    exact (mul_le_mul ha (Real.abs_sin_le_one t) (abs_nonneg _) h4).trans_eq (mul_one _)
  have hbc : |b * Real.cos t| ≤ 4 * Real.pi * M := by
    rw [abs_mul]
    exact (mul_le_mul hb (Real.abs_cos_le_one t) (abs_nonneg _) h4).trans_eq (mul_one _)
  have hbs : |b * Real.sin t| ≤ 4 * Real.pi * M := by
    rw [abs_mul]
    exact (mul_le_mul hb (Real.abs_sin_le_one t) (abs_nonneg _) h4).trans_eq (mul_one _)
  have h1 := hv t
  have h2 := hd t
  rw [abs_le] at h1 h2 hac has hbc hbs
  unfold wGen_STR02913 wGen1_STR02913
  constructor
  · rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, hac.1, hac.2, hbs.1, hbs.2]
  · rw [abs_le]
    constructor <;> linarith [h2.1, h2.2, has.1, has.2, hbc.1, hbc.2]

/-- The explicit bound for every admissible exponent. -/
theorem str029_51_explicit_holder_norm_bound_range_inverse_general {α : ℝ} [HolderExponent α]
    {f : ℝ → ℝ} (hf : InY_STR02913 α f) :
    c2Norm_STR02901 α (wRight_STR02913 f) ≤
      (1 + 30 * Real.pi + 10 * Real.pi ^ 2) * c0Norm_STR02953 α f := by
  have hα := HolderExponent.pos (α := α)
  have hα1 := HolderExponent.lt_one (α := α)
  have hfc := continuous_of_circHolderBdd_STR02953 hα hf.1.2
  have hfb : Bdd f := bdd_of_circHolderBdd_STR02953 hα hf.1.2
  set M := supNorm f with hMdef
  have hM : ∀ s, |f s| ≤ M := fun s => hfb.abs_le_supNorm s
  have hM0 : 0 ≤ M := supNorm_nonneg f
  obtain ⟨hvp, hdp⟩ := str029_13_periodic_right_inverse_range_operator_periodic hf
  obtain ⟨-, -, hdint⟩ := str029_13_periodic_right_inverse_range_operator_ode hf
  have hv : ∀ t, |vRight_STR02913 f t| ≤ 2 * Real.pi * M := fun t =>
    periodic_bound_STR02951 hvp (fun t ht =>
      abs_kernel_integral_le_STR02951 hM Real.sin Real.abs_sin_le_one ht) t
  have hd : ∀ t, |vDeriv_STR02913 f t| ≤ 2 * Real.pi * M := fun t =>
    periodic_bound_STR02951 hdp (fun t ht => by
      rw [hdint t]
      exact abs_kernel_integral_le_STR02951 hM Real.cos Real.abs_cos_le_one ht) t
  have hcoef : ∀ g : ℝ → ℝ, (∀ t, |g t| ≤ 1) →
      |2 * meanT_STR02901 (fun t => vRight_STR02913 f t * g t)| ≤ 4 * Real.pi * M := by
    intro g hg
    have h1 : |meanT_STR02901 (fun t => vRight_STR02913 f t * g t)| ≤ 2 * Real.pi * M :=
      abs_meanT_le_STR02953 fun t => by
        rw [abs_mul]
        exact (mul_le_mul (hv t) (hg t) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    rw [abs_mul, abs_two]
    linarith
  have ha : |aCoef_STR02913 f| ≤ 4 * Real.pi * M := hcoef Real.cos Real.abs_cos_le_one
  have hb : |bCoef_STR02913 f| ≤ 4 * Real.pi * M := hcoef Real.sin Real.abs_sin_le_one
  have hbd := wGen_bounds_STR02951 (f := f) hM0 hv hd ha hb
  have hw : wRight_STR02913 f = wGen_STR02913 f (aCoef_STR02913 f) (bCoef_STR02913 f) := rfl
  obtain ⟨hd1, hd2⟩ := deriv_wGen_STR02913 hfc (aCoef_STR02913 f) (bCoef_STR02913 f)
  have hwd : Differentiable ℝ (wRight_STR02913 f) := fun t =>
    (wGen_hasDerivAt_STR02913 hfc (aCoef_STR02913 f) (bCoef_STR02913 f) t).1.differentiableAt
  have hwper : Function.Periodic (wRight_STR02913 f) (2 * Real.pi) :=
    wGen_periodic_STR02913 hvp _ _
  have hd1' : deriv (wRight_STR02913 f) = wGen1_STR02913 f (aCoef_STR02913 f) (bCoef_STR02913 f) := by
    rw [hw]; exact hd1
  have hd2' : deriv (deriv (wRight_STR02913 f)) = fun t => f t - wRight_STR02913 f t := by
    rw [hd1', hw]; exact hd2
  have hw0 : ∀ t, |wRight_STR02913 f t| ≤ 10 * Real.pi * M := fun t => (hbd t).1
  have hw1 : ∀ t, |deriv (wRight_STR02913 f) t| ≤ 10 * Real.pi * M := fun t => by
    rw [hd1']; exact (hbd t).2
  have hw2 : ∀ t, |deriv (deriv (wRight_STR02913 f)) t| ≤ (1 + 10 * Real.pi) * M := fun t => by
    rw [hd2']
    have h1 := hM t
    have h2 := hw0 t
    rw [abs_le] at h1 h2 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have s0 : supNorm (wRight_STR02913 f) ≤ 10 * Real.pi * M := supNorm_le hw0
  have s1 : supNorm (deriv (wRight_STR02913 f)) ≤ 10 * Real.pi * M := supNorm_le hw1
  have s2 : supNorm (deriv (deriv (wRight_STR02913 f))) ≤ (1 + 10 * Real.pi) * M := supNorm_le hw2
  -- the Hölder seminorm of `w'' = f - w`
  have hKnn : 0 ≤ circHolder_STR02901 α f + Real.pi ^ (1 - α) * (10 * Real.pi * M) := by
    have := circHolder_nonneg_STR02953 α f
    have : 0 ≤ Real.pi ^ (1 - α) * (10 * Real.pi * M) := by positivity
    linarith
  have hHol : circHolder_STR02901 α (deriv (deriv (wRight_STR02913 f))) ≤
      circHolder_STR02901 α f + Real.pi ^ (1 - α) * (10 * Real.pi * M) := by
    refine circHolder_le_STR02953 hα hKnn fun s t => ?_
    rw [hd2']
    have h1 := abs_sub_le_circHolder_STR02953 hα hf.1.2 s t
    have h2 := circ_lipschitz_STR02953 hwper hwd hw1 s t
    have h3 := circDist_le_pow_STR02953 hα1.le s t
    have h4 : (10 * Real.pi * M) * circDist_STR02901 s t ≤
        (10 * Real.pi * M) * (Real.pi ^ (1 - α) * circDist_STR02901 s t ^ α) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    have e : (circHolder_STR02901 α f + Real.pi ^ (1 - α) * (10 * Real.pi * M)) *
        circDist_STR02901 s t ^ α =
        circHolder_STR02901 α f * circDist_STR02901 s t ^ α +
          (10 * Real.pi * M) * (Real.pi ^ (1 - α) * circDist_STR02901 s t ^ α) := by ring
    rw [e]
    have h5 := abs_le.1 h1
    have h6 := abs_le.1 h2
    rw [abs_le]
    constructor <;> linarith [h5.1, h5.2, h6.1, h6.2]
  have hpi : Real.pi ^ (1 - α) ≤ Real.pi := by
    calc Real.pi ^ (1 - α) ≤ Real.pi ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three]) (by linarith)
      _ = Real.pi := Real.rpow_one _
  have hHol2 : Real.pi ^ (1 - α) * (10 * Real.pi * M) ≤ 10 * Real.pi ^ 2 * M := by
    calc Real.pi ^ (1 - α) * (10 * Real.pi * M) ≤ Real.pi * (10 * Real.pi * M) :=
          mul_le_mul_of_nonneg_right hpi (by positivity)
      _ = 10 * Real.pi ^ 2 * M := by ring
  have hC : 1 ≤ 1 + 30 * Real.pi + 10 * Real.pi ^ 2 := by
    have := Real.pi_pos
    nlinarith [sq_nonneg Real.pi]
  have hsem := circHolder_nonneg_STR02953 α f
  unfold c2Norm_STR02901 c0Norm_STR02953
  nlinarith [mul_nonneg (sub_nonneg.2 hC) hsem]

/-- Main statement: `‖w‖_{2,1/2} ≤ (1 + 30π + 10π²) ‖f‖_{0,1/2}` for the range inverse of `.13`. -/
theorem str029_51_explicit_holder_norm_bound_range_inverse {f : ℝ → ℝ}
    (hf : InY_STR02913 (1 / 2 : ℝ) f) :
    c2Norm_STR02901 (1 / 2 : ℝ) (wRight_STR02913 f) ≤
      (1 + 30 * Real.pi + 10 * Real.pi ^ 2) * c0Norm_STR02953 (1 / 2 : ℝ) f := by
  have : HolderExponent (1 / 2 : ℝ) := holderExponent_half_STR02901
  exact str029_51_explicit_holder_norm_bound_range_inverse_general hf

end DGPS.Frontier.STR029
