import DGPS.Frontier.STR029.T50
import DGPS.Frontier.STR029.T69

/-!
# STR029.47: Insensitivity of the quartic coefficient to a cubic logarithmic remainder

Task id: STR029.47 (node STR029, frontier unit).
Title: Insensitivity of the quartic coefficient to a cubic logarithmic remainder.

Provides `DGPS.Frontier.STR029.str029_47_insensitivity_quartic_coefficient_cubic_logarithmic_remainder`.
For a radius `R` there are `h0 > 0` and `K ≥ 0` such that, for all coefficients `A, …, F` bounded by
`R`, for every `2π`-periodic `C^{2,1/2}` remainder `r h` with Haar mean zero and norm at most `R`,
and for `|h| ≤ h0`, the variation of the logarithmic-chart functional `J(h, 0, ·)` between the
trial functions `h p + h² q + h³ r h` and `h p + h² q` is at most `K |h|⁵`.

Here `p(t) = A cos t + B sin t` and `q(t) = C cos 2t + D sin 2t + E cos 4t + F sin 4t`.

## R5 notes

* The brief defines neither `p` nor `q`. They are taken as trigonometric polynomials: `p` has
  frequency `1` and `q` has frequencies `2` and `4` (the node's line 269 describes the classes of
  `p` and `q` in this way). The auxiliary definitions are `trigN_STR02947`, `pT_STR02947` and
  `qT_STR02947`.
* The brief's prerequisite commit `d4d1d1057ad8e25312ba991a51326842030cf9eb` differs from the local
  branch head. The needed modules STR029.44, 45, 46, 50, 55 and their imports are present locally,
  so no cherry-pick was made.
* The flow argument uses `str029_50_integrate_variation_compute_mean_variation` (STR029.50), which
  gives the first variation of `J(h, 0, ·)` at a `C^{2,1/2}` point in the direction of a
  `C^{2,1/2}` function. It is applied along the segment `u_x = h p + h² q + x h³ r`, with the
  mean-value theorem on `[0, 1]`.
* The `O(h)` term of the gradient is killed exactly: `p'' + p = 0` and `∫ p = 0`.
* The constants are `M = 50 (|R| + 1)`, `h0 = 1 / (64 M)` and `K = 400 M³`. Every bound of the
  flow argument is at most `M`, and the pointwise bound on the gradient is `400 M² h²`.
* The C^{2,1/2} and norm hypotheses of the remainder are stated for every `h` (uniformly in `h`);
  this is the stronger form and is the form used by the proof.
* The node text (node STR029, the sentence beginning "where `r` is a smooth family", about line 281)
  also asks that `r` be smooth in the parameter `h` and bounded with its first five parameter
  derivatives on the chosen interval. Neither condition is stated. The `O(h⁵)` estimate uses only
  the uniform `C^{2,1/2}` bound on `r h`, which the statement assumes for every `h`. Dropping these
  conditions makes the statement stronger; no hypothesis is added.
* The mean-zero hypothesis on `r h` is carried under the name `_hrm`. It is not needed: the bound
  holds for every remainder with `‖r h‖_{C^{2,1/2}} ≤ R`.
* The build line of the brief used a `timeout` wrapper, which conflicts with the orchestrator's
  instruction for targeted builds. The targeted build was run without a timeout wrapper.
-/

open Filter Topology Set DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-! ### Trigonometric polynomials -/

/-- The trigonometric term `a cos(n t) + b sin(n t)`. -/
noncomputable def trigN_STR02947 (a b : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  a * Real.cos ((n : ℝ) * t) + b * Real.sin ((n : ℝ) * t)

/-- The first-harmonic function `p(t) = A cos t + B sin t`. -/
noncomputable def pT_STR02947 (A B : ℝ) (t : ℝ) : ℝ := trigN_STR02947 A B 1 t

/-- The second-and-fourth-harmonic function `q(t) = C cos 2t + D sin 2t + E cos 4t + F sin 4t`. -/
noncomputable def qT_STR02947 (C D E F : ℝ) (t : ℝ) : ℝ :=
  trigN_STR02947 C D 2 t + trigN_STR02947 E F 4 t

/-! ### Derivatives and bounds of `trigN` -/

theorem hasDerivAt_trigN_STR02947 (a b : ℝ) (n : ℕ) (t : ℝ) :
    HasDerivAt (trigN_STR02947 a b n) (trigN_STR02947 (b * n) (-(a * n)) n t) t := by
  have h1 : HasDerivAt (fun s : ℝ => (n : ℝ) * s) ((n : ℝ) * 1) t :=
    (hasDerivAt_id t).const_mul (n : ℝ)
  have h2 := ((h1.cos).const_mul a).add ((h1.sin).const_mul b)
  refine h2.congr_deriv ?_
  simp only [trigN_STR02947]
  ring

theorem deriv_trigN_STR02947 (a b : ℝ) (n : ℕ) :
    deriv (trigN_STR02947 a b n) = trigN_STR02947 (b * n) (-(a * n)) n := by
  funext t
  exact (hasDerivAt_trigN_STR02947 a b n t).deriv

theorem deriv_deriv_trigN_STR02947 (a b : ℝ) (n : ℕ) :
    deriv (deriv (trigN_STR02947 a b n)) = trigN_STR02947 (-(a * n) * n) (-(b * n * n)) n := by
  rw [deriv_trigN_STR02947, deriv_trigN_STR02947]

theorem abs_trigN_le_STR02947 (a b : ℝ) (n : ℕ) (t : ℝ) :
    |trigN_STR02947 a b n t| ≤ |a| + |b| := by
  unfold trigN_STR02947
  have h1 : |a * Real.cos ((n : ℝ) * t)| ≤ |a| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg a) (Real.abs_cos_le_one _)
  have h2 : |b * Real.sin ((n : ℝ) * t)| ≤ |b| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg b) (Real.abs_sin_le_one _)
  exact le_trans (abs_add_le _ _) (add_le_add h1 h2)

theorem abs_deriv_trigN_le_STR02947 (a b : ℝ) (n : ℕ) (t : ℝ) :
    |deriv (trigN_STR02947 a b n) t| ≤ (n : ℝ) * (|a| + |b|) := by
  rw [deriv_trigN_STR02947]
  refine le_trans (abs_trigN_le_STR02947 _ _ n t) (le_of_eq ?_)
  have hn : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (by positivity)
  simp only [abs_neg, abs_mul, hn]
  ring

theorem abs_deriv2_trigN_le_STR02947 (a b : ℝ) (n : ℕ) (t : ℝ) :
    |deriv (deriv (trigN_STR02947 a b n)) t| ≤ (n : ℝ) ^ 2 * (|a| + |b|) := by
  rw [deriv_deriv_trigN_STR02947]
  refine le_trans (abs_trigN_le_STR02947 _ _ n t) (le_of_eq ?_)
  have hn : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (by positivity)
  simp only [abs_neg, abs_mul, hn]
  ring

theorem trigN_periodic_STR02947 (a b : ℝ) (n : ℕ) :
    Function.Periodic (trigN_STR02947 a b n) (2 * Real.pi) := by
  intro t
  have e : (n : ℝ) * (t + 2 * Real.pi) = (n : ℝ) * t + (n : ℝ) * (2 * Real.pi) := by ring
  unfold trigN_STR02947
  rw [e, Real.cos_add_nat_mul_two_pi, Real.sin_add_nat_mul_two_pi]

theorem differentiable_trigN_STR02947 (a b : ℝ) (n : ℕ) :
    Differentiable ℝ (trigN_STR02947 a b n) :=
  fun t => (hasDerivAt_trigN_STR02947 a b n t).differentiableAt

theorem holder_trigN_STR02947 (a b : ℝ) (n : ℕ) :
    CircHolderBdd_STR02901 (1 / 2) (trigN_STR02947 a b n) := by
  obtain ⟨⟨-, h2⟩, -⟩ := c0_of_deriv_STR02953 (α := 1 / 2) half_pos_STR02968 (by norm_num)
    (trigN_periodic_STR02947 a b n) (differentiable_trigN_STR02947 a b n)
    ⟨(n : ℝ) * (|a| + |b|), fun x => abs_deriv_trigN_le_STR02947 a b n x⟩
  exact h2

theorem c2_trigN_STR02947 (a b : ℝ) (n : ℕ) :
    IsC2Alpha_STR02901 (1 / 2) (trigN_STR02947 a b n) := by
  refine ⟨trigN_periodic_STR02947 a b n, differentiable_trigN_STR02947 a b n, ?_, ?_, ?_⟩
  · rw [deriv_trigN_STR02947]
    exact differentiable_trigN_STR02947 _ _ n
  · rw [deriv_deriv_trigN_STR02947]
    exact (differentiable_trigN_STR02947 _ _ n).continuous
  · rw [deriv_deriv_trigN_STR02947]
    exact holder_trigN_STR02947 _ _ n

theorem c2_pT_STR02947 (A B : ℝ) : IsC2Alpha_STR02901 (1 / 2) (pT_STR02947 A B) :=
  c2_trigN_STR02947 A B 1

theorem c2_qT_STR02947 (C D E F : ℝ) : IsC2Alpha_STR02901 (1 / 2) (qT_STR02947 C D E F) :=
  c2_add_STR02969 (c2_trigN_STR02947 C D 2) (c2_trigN_STR02947 E F 4)

/-! ### Haar mean lemmas -/

theorem meanT_sub_const_STR02947 {f : ℝ → ℝ} (hf : Continuous f) (c : ℝ) :
    meanT_STR02901 (fun t => f t - c) = meanT_STR02901 f - c := by
  have hf' : IntervalIntegrable f MeasureTheory.volume 0 (2 * Real.pi) :=
    hf.intervalIntegrable _ _
  have hc' : IntervalIntegrable (fun _ : ℝ => c) MeasureTheory.volume 0 (2 * Real.pi) :=
    continuous_const.intervalIntegrable _ _
  unfold meanT_STR02901
  rw [intervalIntegral.integral_sub hf' hc', intervalIntegral.integral_const]
  have key : (2 * Real.pi)⁻¹ * (2 * Real.pi) = 1 := inv_mul_cancel₀ (by positivity)
  simp only [smul_eq_mul]
  linear_combination (-c) * key

theorem meanT_add2_STR02947 {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    meanT_STR02901 (fun t => f t + g t) = meanT_STR02901 f + meanT_STR02901 g :=
  meanT_add_STR02953 hf hg

theorem meanT_lin3_STR02947 (a b c : ℝ) {p q w : ℝ → ℝ} (hp : Continuous p) (hq : Continuous q)
    (hw : Continuous w) :
    meanT_STR02901 (fun t => a * p t + b * q t + c * w t) =
      a * meanT_STR02901 p + b * meanT_STR02901 q + c * meanT_STR02901 w := by
  have e : (fun t => a * p t + b * q t + c * w t) =
      (fun t => a * p t + b * q t) + c • w := by
    funext t
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have c1 : Continuous (fun t => a * p t + b * q t) := by fun_prop
  have c2 : Continuous (c • w) := hw.const_smul c
  rw [e, meanT_add_STR02953 c1 c2, meanT_smul_STR02953, meanT_comb2_STR02950 hp hq a b]

theorem meanT_pT_STR02947 (A B : ℝ) : meanT_STR02901 (pT_STR02947 A B) = 0 := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt (fun s : ℝ => A * Real.sin s - B * Real.cos s) (pT_STR02947 A B x) x := by
    intro x _
    have h1 := ((Real.hasDerivAt_sin x).const_mul A).sub ((Real.hasDerivAt_cos x).const_mul B)
    refine h1.congr_deriv ?_
    simp only [pT_STR02947, trigN_STR02947, Nat.cast_one, one_mul]
    ring
  have hc : Continuous (pT_STR02947 A B) := (differentiable_trigN_STR02947 A B 1).continuous
  have hint : IntervalIntegrable (pT_STR02947 A B) MeasureTheory.volume 0 (2 * Real.pi) :=
    hc.intervalIntegrable _ _
  have hI := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  unfold meanT_STR02901
  rw [hI]
  simp only [Real.sin_two_pi, Real.cos_two_pi, Real.sin_zero, Real.cos_zero]
  ring

/-! ### Facts about `pT` and `qT` -/

theorem pT_eq_STR02947 (A B : ℝ) : pT_STR02947 A B = trigN_STR02947 A B 1 := rfl

theorem pT_dd_STR02947 (A B t : ℝ) :
    deriv (deriv (pT_STR02947 A B)) t = -pT_STR02947 A B t := by
  rw [pT_eq_STR02947, deriv_deriv_trigN_STR02947]
  simp only [trigN_STR02947, Nat.cast_one, one_mul, mul_one]
  ring

theorem abs_pT_le_STR02947 (A B t : ℝ) : |pT_STR02947 A B t| ≤ |A| + |B| :=
  abs_trigN_le_STR02947 A B 1 t

theorem abs_deriv_pT_le_STR02947 (A B t : ℝ) :
    |deriv (pT_STR02947 A B) t| ≤ |A| + |B| := by
  have h : |deriv (trigN_STR02947 A B 1) t| ≤ ((1 : ℕ) : ℝ) * (|A| + |B|) :=
    abs_deriv_trigN_le_STR02947 A B 1 t
  rw [Nat.cast_one, one_mul] at h
  exact h

theorem abs_qT_le_STR02947 (C D E F t : ℝ) :
    |qT_STR02947 C D E F t| ≤ (|C| + |D|) + (|E| + |F|) := by
  show |trigN_STR02947 C D 2 t + trigN_STR02947 E F 4 t| ≤ _
  exact le_trans (abs_add_le _ _)
    (add_le_add (abs_trigN_le_STR02947 C D 2 t) (abs_trigN_le_STR02947 E F 4 t))

theorem deriv_qT_eq_STR02947 (C D E F t : ℝ) :
    deriv (qT_STR02947 C D E F) t =
      deriv (trigN_STR02947 C D 2) t + deriv (trigN_STR02947 E F 4) t := by
  have h := deriv_add (differentiable_trigN_STR02947 C D 2 t)
    (differentiable_trigN_STR02947 E F 4 t)
  exact h

theorem deriv_qT_fun_STR02947 (C D E F : ℝ) :
    deriv (qT_STR02947 C D E F) =
      deriv (trigN_STR02947 C D 2) + deriv (trigN_STR02947 E F 4) := by
  funext s
  exact deriv_qT_eq_STR02947 C D E F s

theorem abs_deriv_qT_le_STR02947 (C D E F t : ℝ) :
    |deriv (qT_STR02947 C D E F) t| ≤ 2 * (|C| + |D|) + 4 * (|E| + |F|) := by
  rw [deriv_qT_eq_STR02947]
  have h1 : |deriv (trigN_STR02947 C D 2) t| ≤ ((2 : ℕ) : ℝ) * (|C| + |D|) :=
    abs_deriv_trigN_le_STR02947 C D 2 t
  have h2 : |deriv (trigN_STR02947 E F 4) t| ≤ ((4 : ℕ) : ℝ) * (|E| + |F|) :=
    abs_deriv_trigN_le_STR02947 E F 4 t
  have e2 : ((2 : ℕ) : ℝ) = 2 := by norm_num
  have e4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
  rw [e2] at h1
  rw [e4] at h2
  exact le_trans (abs_add_le _ _) (add_le_add h1 h2)

theorem differentiable_deriv_trigN_STR02947 (a b : ℝ) (n : ℕ) :
    Differentiable ℝ (deriv (trigN_STR02947 a b n)) := by
  rw [deriv_trigN_STR02947]
  exact differentiable_trigN_STR02947 _ _ n

theorem abs_deriv2_qT_le_STR02947 (C D E F t : ℝ) :
    |deriv (deriv (qT_STR02947 C D E F)) t| ≤ 4 * (|C| + |D|) + 16 * (|E| + |F|) := by
  rw [deriv_qT_fun_STR02947, deriv_add (differentiable_deriv_trigN_STR02947 C D 2 t)
    (differentiable_deriv_trigN_STR02947 E F 4 t)]
  have h1 := abs_deriv2_trigN_le_STR02947 C D 2 t
  have h2 := abs_deriv2_trigN_le_STR02947 E F 4 t
  have e2 : ((2 : ℕ) : ℝ) ^ 2 = 4 := by norm_num
  have e4 : ((4 : ℕ) : ℝ) ^ 2 = 16 := by norm_num
  rw [e2] at h1
  rw [e4] at h2
  exact le_trans (abs_add_le _ _) (add_le_add h1 h2)

/-! ### Linear combinations, remainder bounds and shifts -/

theorem deriv_lin3_STR02947 (a b c : ℝ) {p q w : ℝ → ℝ} (hp : Differentiable ℝ p)
    (hq : Differentiable ℝ q) (hw : Differentiable ℝ w) :
    deriv (fun t => a * p t + b * q t + c * w t) =
      fun t => a * deriv p t + b * deriv q t + c * deriv w t := by
  funext t
  have h := (((hp t).hasDerivAt.const_mul a).add ((hq t).hasDerivAt.const_mul b)).add
    ((hw t).hasDerivAt.const_mul c)
  exact h.deriv

theorem r_bounds_STR02947 {r : ℝ → ℝ} {R : ℝ} (hr : IsC2Alpha_STR02901 (1 / 2) r)
    (hn : c2Norm_STR02901 (1 / 2) r ≤ R) :
    (∀ t, |r t| ≤ R) ∧ (∀ t, |deriv r t| ≤ R) ∧ (∀ t, |deriv (deriv r) t| ≤ R) := by
  obtain ⟨b0, b1, b2⟩ := bdd_parts_STR02969 hr
  obtain ⟨L0, L1, L2⟩ := le_c2Norm_STR02969 r
  have hH := circHolder_nonneg_STR02953 (1 / 2) (deriv (deriv r))
  refine ⟨fun t => ?_, fun t => ?_, fun t => ?_⟩
  · have := b0.abs_le_supNorm t
    linarith
  · have := b1.abs_le_supNorm t
    linarith
  · have := b2.abs_le_supNorm t
    linarith

theorem bmul_STR02947 {x y A B : ℝ} (hx : |x| ≤ A) (hy : |y| ≤ B) (hA : 0 ≤ A) :
    |x * y| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul hx hy (abs_nonneg y) hA

theorem hasDerivAt_shift_STR02947 {G : ℝ → ℝ} {D x : ℝ} (hG : HasDerivAt G D 0) :
    HasDerivAt (fun y => G (y - x)) D x := by
  have hG' : HasDerivAt G D (x - x) := by
    rw [sub_self]
    exact hG
  exact HasDerivAt.comp_sub_const x x hG'

/-! ### The density `ρ(h, u)` and the gradient bound -/

theorem rho_bounds_STR02947 {h M : ℝ} {u : ℝ → ℝ} (hM : 1 ≤ M) (hMh : M * |h| ≤ 1 / 64)
    (hcu : Continuous u) (hub : ∀ t, |u t| ≤ 3 * M * |h|) :
    (∀ t, |rhoT_STR02901 h u t| ≤ 2) ∧ (∀ t, |rhoT_STR02901 h u t - 1| ≤ 20 * M * |h|) := by
  have hM0 : 0 < M := by linarith
  have hH0 : 0 ≤ |h| := abs_nonneg h
  have hH1 : |h| ≤ M * |h| := le_mul_of_one_le_left hH0 hM
  have hexp_arg : ∀ t, |h * Real.cos (3 * t) + u t| ≤ 4 * M * |h| := by
    intro t
    have e1 : |h * Real.cos (3 * t)| ≤ |h| := by
      rw [abs_mul]
      exact mul_le_of_le_one_right hH0 (Real.abs_cos_le_one _)
    have := abs_add_le (h * Real.cos (3 * t)) (u t)
    linarith [hub t]
  have hexp_small : ∀ t, |Real.exp (h * Real.cos (3 * t) + u t) - 1| ≤ 8 * M * |h| := by
    intro t
    have hx1 : |h * Real.cos (3 * t) + u t| ≤ 1 := by
      linarith [hexp_arg t]
    have h1 := Real.abs_exp_sub_one_le hx1
    linarith [hexp_arg t]
  have hcont_exp : Continuous (fun s => Real.exp (h * Real.cos (3 * s) + u s)) := by
    fun_prop
  have hZ1 : |meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s)) - 1| ≤
      8 * M * |h| := by
    rw [← meanT_sub_const_STR02947 hcont_exp 1]
    exact abs_meanT_le_STR02953 (fun t => hexp_small t)
  set Z := meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s))
  have hMh' : 8 * M * |h| ≤ 1 / 8 := by linarith
  have hZlow : 7 / 8 ≤ Z := by linarith [(abs_le.mp hZ1).1]
  have hZpos : 0 < Z := by linarith
  have he_le : ∀ t, Real.exp (h * Real.cos (3 * t) + u t) ≤ 9 / 8 := by
    intro t
    linarith [(abs_le.mp (hexp_small t)).2]
  have hdiv : ∀ t, rhoT_STR02901 h u t = Real.exp (h * Real.cos (3 * t) + u t) / Z :=
    fun t => rfl
  constructor
  · intro t
    rw [hdiv t, abs_div, abs_of_pos (Real.exp_pos _), abs_of_pos hZpos, div_le_iff₀ hZpos]
    linarith [he_le t]
  · intro t
    have hkey : Real.exp (h * Real.cos (3 * t) + u t) / Z - 1 =
        (Real.exp (h * Real.cos (3 * t) + u t) - Z) / Z := by
      rw [sub_div, div_self hZpos.ne']
    have hA := abs_le.mp (hexp_small t)
    have hB := abs_le.mp hZ1
    have hc16 : |Real.exp (h * Real.cos (3 * t) + u t) - Z| ≤ 16 * M * |h| :=
      abs_le.mpr ⟨by linarith [hA.1, hB.2], by linarith [hA.2, hB.1]⟩
    rw [hdiv t, hkey, abs_div, abs_of_pos hZpos, div_le_iff₀ hZpos]
    nlinarith [mul_nonneg (mul_nonneg hM0.le hH0) (show (0:ℝ) ≤ Z - 7 / 8 by linarith),
      mul_nonneg hM0.le hH0, hc16]

theorem gradG_bound_STR02947 {h M c : ℝ} {p q w u : ℝ → ℝ}
    (hM : 1 ≤ M) (hMh : M * |h| ≤ 1 / 64) (hc : |c| ≤ |h| ^ 3)
    (hp : IsC2Alpha_STR02901 (1 / 2) p) (hq : IsC2Alpha_STR02901 (1 / 2) q)
    (hw : IsC2Alpha_STR02901 (1 / 2) w)
    (hpm : meanT_STR02901 p = 0)
    (hp0 : ∀ t, |p t| ≤ M) (hp1 : ∀ t, |deriv p t| ≤ M)
    (hpp : ∀ t, deriv (deriv p) t = -p t)
    (hq0 : ∀ t, |q t| ≤ M) (hq1 : ∀ t, |deriv q t| ≤ M) (hq2 : ∀ t, |deriv (deriv q) t| ≤ M)
    (hw0 : ∀ t, |w t| ≤ M) (hw1 : ∀ t, |deriv w t| ≤ M) (hw2 : ∀ t, |deriv (deriv w) t| ≤ M)
    (hu : u = fun s => h * p s + h ^ 2 * q s + c * w s) :
    ∀ t, |gradG_STR02950 h 0 u t| ≤ 400 * M ^ 2 * h ^ 2 := by
  have hM0 : 0 < M := by linarith
  have hH0 : 0 ≤ |h| := abs_nonneg h
  have hH1 : |h| ≤ M * |h| := le_mul_of_one_le_left hH0 hM
  have hH2 : |h| ^ 2 ≤ |h| := by
    nlinarith [mul_nonneg hH0 (show (0:ℝ) ≤ 1 - |h| by linarith)]
  have hH3 : |h| ^ 3 ≤ |h| ^ 2 := by
    nlinarith [mul_nonneg (pow_nonneg hH0 2) (show (0:ℝ) ≤ 1 - |h| by linarith)]
  have hsq : h ^ 2 = |h| ^ 2 := (sq_abs h).symm
  have hhsq : |h ^ 2| ≤ |h| ^ 2 := le_of_eq (abs_pow h 2)
  have hMM : M ≤ M ^ 2 := by nlinarith
  have hMsq : M * |h| ^ 2 ≤ M ^ 2 * |h| ^ 2 := mul_le_mul_of_nonneg_right hMM (sq_nonneg _)
  have hpc : Continuous p := hp.2.1.continuous
  have hqc : Continuous q := hq.2.1.continuous
  have hwc : Continuous w := hw.2.1.continuous
  have hcu : Continuous u := by
    rw [hu]
    fun_prop
  have hu_at : ∀ t, u t = h * p t + h ^ 2 * q t + c * w t := fun t => by rw [hu]
  have hu1 : deriv u = fun t => h * deriv p t + h ^ 2 * deriv q t + c * deriv w t := by
    rw [hu]
    exact deriv_lin3_STR02947 h (h ^ 2) c hp.2.1 hq.2.1 hw.2.1
  have hdu : ∀ t, deriv u t = h * deriv p t + h ^ 2 * deriv q t + c * deriv w t :=
    fun t => congrFun hu1 t
  have hdd : ∀ t, deriv (deriv u) t =
      h * deriv (deriv p) t + h ^ 2 * deriv (deriv q) t + c * deriv (deriv w) t := by
    intro t
    rw [hu1, deriv_lin3_STR02947 h (h ^ 2) c hp.2.2.1 hq.2.2.1 hw.2.2.1]
  have huu : ∀ t, deriv (deriv u) t + u t =
      h ^ 2 * (deriv (deriv q) t + q t) + c * (deriv (deriv w) t + w t) := by
    intro t
    rw [hdd t, hu_at t, hpp t]
    ring
  have hub : ∀ t, |u t| ≤ 3 * M * |h| := by
    intro t
    rw [hu_at t]
    have e1 := bmul_STR02947 (le_refl |h|) (hp0 t) hH0
    have e2 := bmul_STR02947 hhsq (hq0 t) (pow_nonneg hH0 2)
    have e3 := bmul_STR02947 hc (hw0 t) (pow_nonneg hH0 3)
    have f1 := abs_add_le (h * p t + h ^ 2 * q t) (c * w t)
    have f2 := abs_add_le (h * p t) (h ^ 2 * q t)
    have f3 : |h| ^ 2 * M ≤ |h| * M := mul_le_mul_of_nonneg_right hH2 hM0.le
    have f4 : |h| ^ 3 * M ≤ |h| * M := mul_le_mul_of_nonneg_right (le_trans hH3 hH2) hM0.le
    linarith
  have hud : ∀ t, |deriv u t| ≤ 3 * M * |h| := by
    intro t
    rw [hdu t]
    have e1 := bmul_STR02947 (le_refl |h|) (hp1 t) hH0
    have e2 := bmul_STR02947 hhsq (hq1 t) (pow_nonneg hH0 2)
    have e3 := bmul_STR02947 hc (hw1 t) (pow_nonneg hH0 3)
    have f1 := abs_add_le (h * deriv p t + h ^ 2 * deriv q t) (c * deriv w t)
    have f2 := abs_add_le (h * deriv p t) (h ^ 2 * deriv q t)
    have f3 : |h| ^ 2 * M ≤ |h| * M := mul_le_mul_of_nonneg_right hH2 hM0.le
    have f4 : |h| ^ 3 * M ≤ |h| * M := mul_le_mul_of_nonneg_right (le_trans hH3 hH2) hM0.le
    linarith
  have hX : ∀ t, |deriv (deriv u) t + u t| ≤ 4 * M * |h| ^ 2 := by
    intro t
    rw [huu t]
    have hq' : |deriv (deriv q) t + q t| ≤ 2 * M := by
      linarith [abs_add_le (deriv (deriv q) t) (q t), hq2 t, hq0 t]
    have hw' : |deriv (deriv w) t + w t| ≤ 2 * M := by
      linarith [abs_add_le (deriv (deriv w) t) (w t), hw2 t, hw0 t]
    have e1 := bmul_STR02947 hhsq hq' (pow_nonneg hH0 2)
    have e2 := bmul_STR02947 hc hw' (pow_nonneg hH0 3)
    have f1 := abs_add_le (h ^ 2 * (deriv (deriv q) t + q t)) (c * (deriv (deriv w) t + w t))
    have f3 : |h| ^ 3 * (2 * M) ≤ |h| ^ 2 * (2 * M) :=
      mul_le_mul_of_nonneg_right hH3 (by linarith)
    linarith
  have hmq : |meanT_STR02901 q| ≤ M := abs_meanT_le_STR02953 hq0
  have hmw : |meanT_STR02901 w| ≤ M := abs_meanT_le_STR02953 hw0
  have hmeanu : meanT_STR02901 u = h ^ 2 * meanT_STR02901 q + c * meanT_STR02901 w := by
    rw [hu, meanT_lin3_STR02947 h (h ^ 2) c hpc hqc hwc, hpm]
    ring
  have hmu : |meanT_STR02901 u| ≤ 2 * M * |h| ^ 2 := by
    rw [hmeanu]
    have e1 := bmul_STR02947 hhsq hmq (pow_nonneg hH0 2)
    have e2 := bmul_STR02947 hc hmw (pow_nonneg hH0 3)
    have f1 := abs_add_le (h ^ 2 * meanT_STR02901 q) (c * meanT_STR02901 w)
    have f3 : |h| ^ 3 * M ≤ |h| ^ 2 * M := mul_le_mul_of_nonneg_right hH3 hM0.le
    linarith
  obtain ⟨hρ2, hρ1⟩ := rho_bounds_STR02947 hM hMh hcu hub
  have hρc : Continuous (rhoT_STR02901 h u) := continuous_rho_STR02950 h hcu
  have hcg : Continuous (fun r => u r * (rhoT_STR02901 h u r - 1)) := by
    fun_prop
  have hsplit : meanT_STR02901 (fun r => u r * rhoT_STR02901 h u r) =
      meanT_STR02901 u + meanT_STR02901 (fun r => u r * (rhoT_STR02901 h u r - 1)) := by
    rw [← meanT_add2_STR02947 hcu hcg]
    congr 1
    funext r
    ring
  have hK : |meanT_STR02901 (fun r => u r * (rhoT_STR02901 h u r - 1))| ≤
      3 * M * |h| * (20 * M * |h|) := by
    apply abs_meanT_le_STR02953
    intro r
    exact bmul_STR02947 (hub r) (hρ1 r) (mul_nonneg (by linarith) hH0)
  have hE : |meanT_STR02901 (fun r => u r * rhoT_STR02901 h u r)| ≤ 62 * M ^ 2 * |h| ^ 2 := by
    rw [hsplit]
    have f1 := abs_add_le (meanT_STR02901 u)
      (meanT_STR02901 (fun r => u r * (rhoT_STR02901 h u r - 1)))
    linarith [hK, hmu]
  have hD1 : ∀ r, |deriv u r ^ 2| ≤ 9 * M ^ 2 * |h| ^ 2 := by
    intro r
    rw [abs_pow]
    have := mul_le_mul (hud r) (hud r) (abs_nonneg _) (mul_nonneg (by linarith) hH0)
    nlinarith [this]
  have hI : ∀ r, |deriv u r ^ 2 * rhoT_STR02901 h u r| ≤ 18 * M ^ 2 * |h| ^ 2 := by
    intro r
    have := bmul_STR02947 (hD1 r) (hρ2 r) (by positivity : (0:ℝ) ≤ 9 * M ^ 2 * |h| ^ 2)
    linarith
  have hImean : |meanT_STR02901 (fun r => deriv u r ^ 2 * rhoT_STR02901 h u r)| ≤
      18 * M ^ 2 * |h| ^ 2 :=
    abs_meanT_le_STR02953 hI
  have key2 : ∀ x y : ℝ, |x| ≤ 2 → |y| ≤ 177 * M ^ 2 * |h| ^ 2 →
      |x * y| ≤ 400 * M ^ 2 * |h| ^ 2 := by
    intro x y hx hy
    rw [abs_mul]
    have hMh2 : 0 ≤ M ^ 2 * |h| ^ 2 := by positivity
    linarith [mul_le_mul hx hy (abs_nonneg y) (by norm_num : (0:ℝ) ≤ 2)]
  have hB : ∀ t, |-2 * deriv (deriv u) t + 6 * h * Real.sin (3 * t) * deriv u t - deriv u t ^ 2 -
      2 * (1 + 0) * u t - meanT_STR02901 (fun r => deriv u r ^ 2 * rhoT_STR02901 h u r) +
      2 * (1 + 0) * meanT_STR02901 (fun r => u r * rhoT_STR02901 h u r)| ≤
        177 * M ^ 2 * |h| ^ 2 := by
    intro t
    have hs6 : |6 * h * Real.sin (3 * t)| ≤ 6 * |h| := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 6)]
      nlinarith [mul_nonneg hH0
        (show (0:ℝ) ≤ 1 - |Real.sin (3 * t)| by linarith [Real.abs_sin_le_one (3 * t)])]
    have hT2 : |6 * h * Real.sin (3 * t) * deriv u t| ≤ 6 * |h| * (3 * M * |h|) :=
      bmul_STR02947 hs6 (hud t) (by positivity)
    obtain ⟨hX1, hX2⟩ := abs_le.mp (hX t)
    obtain ⟨hT31, hT32⟩ := abs_le.mp (hD1 t)
    obtain ⟨hI1, hI2⟩ := abs_le.mp hImean
    obtain ⟨hE1, hE2⟩ := abs_le.mp hE
    obtain ⟨hT21, hT22⟩ := abs_le.mp hT2
    rw [abs_le]
    constructor <;> linarith [hMsq]
  intro t
  unfold gradG_STR02950
  rw [hsq]
  exact key2 _ _ (hρ2 t) (hB t)

/-! ### The flow along the cubic direction and the main statement -/

theorem flow_deriv_STR02947 (h : ℝ) {p q w : ℝ → ℝ} (hp : IsC2Alpha_STR02901 (1 / 2) p)
    (hq : IsC2Alpha_STR02901 (1 / 2) q) (hw : IsC2Alpha_STR02901 (1 / 2) w) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Jchart_STR02950 h 0 (fun t => h * p t + h ^ 2 * q t + (y * h ^ 3) * w t))
      (meanT_STR02901 (fun t => gradG_STR02950 h 0
        (fun s => h * p s + h ^ 2 * q s + (x * h ^ 3) * w s) t * (h ^ 3 * w t))) x := by
  have hU : IsC2Alpha_STR02901 (1 / 2) (fun s => h * p s + h ^ 2 * q s + (x * h ^ 3) * w s) := by
    have e : (fun s => h * p s + h ^ 2 * q s + (x * h ^ 3) * w s)
        = h • p + h ^ 2 • q + (x * h ^ 3) • w := by
      funext s
      simp [smul_eq_mul]
    rw [e]
    exact c2_add_STR02969 (c2_add_STR02969 (c2_smul_STR02969 h hp) (c2_smul_STR02969 (h ^ 2) hq))
      (c2_smul_STR02969 (x * h ^ 3) hw)
  have hV : IsC2Alpha_STR02901 (1 / 2) (fun s => h ^ 3 * w s) := by
    have e : (fun s => h ^ 3 * w s) = (h ^ 3) • w := by
      funext s
      simp [smul_eq_mul]
    rw [e]
    exact c2_smul_STR02969 (h ^ 3) hw
  have hS := hasDerivAt_shift_STR02947 (x := x)
    (str029_50_integrate_variation_compute_mean_variation h 0 hU hV)
  have hfun : (fun y : ℝ => Jchart_STR02950 h 0 (fun t => h * p t + h ^ 2 * q t + (y * h ^ 3) * w t))
      = (fun y : ℝ => Jchart_STR02950 h 0 (fun t =>
          (h * p t + h ^ 2 * q t + (x * h ^ 3) * w t) + (y - x) * (h ^ 3 * w t))) := by
    funext y
    congr 1
    funext t
    ring
  rw [hfun]
  exact hS

theorem flow_bound_STR02947 (h M : ℝ) (hM : 1 ≤ M) (hMh : M * |h| ≤ 1 / 64)
    {p q w : ℝ → ℝ} (hp : IsC2Alpha_STR02901 (1 / 2) p) (hq : IsC2Alpha_STR02901 (1 / 2) q)
    (hw : IsC2Alpha_STR02901 (1 / 2) w)
    (hpm : meanT_STR02901 p = 0)
    (hp0 : ∀ t, |p t| ≤ M) (hp1 : ∀ t, |deriv p t| ≤ M)
    (hpp : ∀ t, deriv (deriv p) t = -p t)
    (hq0 : ∀ t, |q t| ≤ M) (hq1 : ∀ t, |deriv q t| ≤ M) (hq2 : ∀ t, |deriv (deriv q) t| ≤ M)
    (hw0 : ∀ t, |w t| ≤ M) (hw1 : ∀ t, |deriv w t| ≤ M) (hw2 : ∀ t, |deriv (deriv w) t| ≤ M) :
    |Jchart_STR02950 h 0 (fun t => h * p t + h ^ 2 * q t + h ^ 3 * w t)
        - Jchart_STR02950 h 0 (fun t => h * p t + h ^ 2 * q t)| ≤ 400 * M ^ 3 * |h| ^ 5 := by
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope
    (fun y : ℝ => Jchart_STR02950 h 0 (fun t => h * p t + h ^ 2 * q t + (y * h ^ 3) * w t))
    (fun x : ℝ => meanT_STR02901 (fun t => gradG_STR02950 h 0
        (fun s => h * p s + h ^ 2 * q s + (x * h ^ 3) * w s) t * (h ^ 3 * w t)))
    (zero_lt_one : (0 : ℝ) < 1)
    (fun x _ => (flow_deriv_STR02947 h hp hq hw x).continuousAt.continuousWithinAt)
    (fun x _ => flow_deriv_STR02947 h hp hq hw x)
  simp only [one_mul, zero_mul, add_zero, sub_zero, div_one] at hξeq
  have hc : |ξ * h ^ 3| ≤ |h| ^ 3 := by
    rw [abs_mul, abs_pow, abs_of_pos hξ.1]
    exact mul_le_of_le_one_left (by positivity) hξ.2.le
  have hbound : |meanT_STR02901 (fun t => gradG_STR02950 h 0
        (fun s => h * p s + h ^ 2 * q s + (ξ * h ^ 3) * w s) t * (h ^ 3 * w t))|
        ≤ 400 * M ^ 3 * |h| ^ 5 := by
    refine abs_meanT_le_STR02953 (fun t => ?_)
    have hg := gradG_bound_STR02947 (h := h) (M := M) (c := ξ * h ^ 3) (p := p) (q := q)
      (w := w) (u := fun s => h * p s + h ^ 2 * q s + (ξ * h ^ 3) * w s) hM hMh hc hp hq hw
      hpm hp0 hp1 hpp hq0 hq1 hq2 hw0 hw1 hw2 rfl t
    have hy : |h ^ 3 * w t| ≤ |h| ^ 3 * M := by
      rw [abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_left (hw0 t) (by positivity)
    have hA : (0 : ℝ) ≤ 400 * M ^ 2 * h ^ 2 := by positivity
    have key : 400 * M ^ 2 * h ^ 2 * (|h| ^ 3 * M) = 400 * M ^ 3 * |h| ^ 5 := by
      rw [← sq_abs h]
      ring
    calc |gradG_STR02950 h 0 (fun s => h * p s + h ^ 2 * q s + (ξ * h ^ 3) * w s) t
          * (h ^ 3 * w t)|
        ≤ 400 * M ^ 2 * h ^ 2 * (|h| ^ 3 * M) := bmul_STR02947 hg hy hA
      _ = 400 * M ^ 3 * |h| ^ 5 := key
  rw [← hξeq]
  exact hbound

theorem str029_47_insensitivity_quartic_coefficient_cubic_logarithmic_remainder (R : ℝ) :
    ∃ h0 : ℝ, 0 < h0 ∧ ∃ K : ℝ, 0 ≤ K ∧ ∀ A B C D E F : ℝ, |A| ≤ R → |B| ≤ R → |C| ≤ R →
      |D| ≤ R → |E| ≤ R → |F| ≤ R → ∀ r : ℝ → ℝ → ℝ, (∀ h, IsC2Alpha_STR02901 (1 / 2) (r h)) →
      (∀ h, meanT_STR02901 (r h) = 0) → (∀ h, c2Norm_STR02901 (1 / 2) (r h) ≤ R) →
      ∀ h : ℝ, |h| ≤ h0 →
      |Jchart_STR02950 h 0 (fun t => h * pT_STR02947 A B t + h ^ 2 * qT_STR02947 C D E F t + h ^ 3 * r h t)
        - Jchart_STR02950 h 0 (fun t => h * pT_STR02947 A B t + h ^ 2 * qT_STR02947 C D E F t)|
        ≤ K * |h| ^ 5 := by
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = 50 * (|R| + 1) := ⟨_, rfl⟩
  have hR1 : R ≤ |R| := le_abs_self R
  have hR0 : 0 ≤ |R| := abs_nonneg R
  have hM : 1 ≤ M := by linarith
  have hM0 : 0 < M := by linarith
  have hM2 : 2 * R ≤ M := by linarith
  have hM4 : 4 * R ≤ M := by linarith
  have hM12 : 12 * R ≤ M := by linarith
  have hM40 : 40 * R ≤ M := by linarith
  refine ⟨1 / (64 * M), div_pos one_pos (by linarith), 400 * M ^ 3,
    by have := pow_pos hM0 3; linarith, ?_⟩
  intro A B C D E F hA hB hC hD hE hF r hr _hrm hrn h hh
  have hMh : M * |h| ≤ 1 / 64 := by
    have h1 : M * |h| ≤ M * (1 / (64 * M)) := mul_le_mul_of_nonneg_left hh hM0.le
    have h2 : M * (1 / (64 * M)) = 1 / 64 := by
      field_simp
    linarith
  obtain ⟨hw0, hw1, hw2⟩ := r_bounds_STR02947 (hr h) (hrn h)
  have hp0 : ∀ t, |pT_STR02947 A B t| ≤ M := fun t => le_trans (abs_pT_le_STR02947 A B t) (by linarith)
  have hp1 : ∀ t, |deriv (pT_STR02947 A B) t| ≤ M := fun t =>
    le_trans (abs_deriv_pT_le_STR02947 A B t) (by linarith)
  have hq0 : ∀ t, |qT_STR02947 C D E F t| ≤ M := fun t =>
    le_trans (abs_qT_le_STR02947 C D E F t) (by linarith)
  have hq1 : ∀ t, |deriv (qT_STR02947 C D E F) t| ≤ M := fun t =>
    le_trans (abs_deriv_qT_le_STR02947 C D E F t) (by linarith)
  have hq2 : ∀ t, |deriv (deriv (qT_STR02947 C D E F)) t| ≤ M := fun t =>
    le_trans (abs_deriv2_qT_le_STR02947 C D E F t) (by linarith)
  have hRM : R ≤ M := by linarith
  have key := flow_bound_STR02947 h M hM hMh (c2_pT_STR02947 A B) (c2_qT_STR02947 C D E F)
    (hr h) (meanT_pT_STR02947 A B) hp0 hp1 (fun t => pT_dd_STR02947 A B t) hq0 hq1 hq2
    (fun t => le_trans (hw0 t) hRM) (fun t => le_trans (hw1 t) hRM)
    (fun t => le_trans (hw2 t) hRM)
  exact key

end DGPS.Frontier.STR029
