import DGPS.Frontier.STR029.T35

/-!
# STR029.36: Numerical absorption in the cross-form estimate

Task id: STR029.36. Title: Numerical absorption in the cross-form estimate (node STR029).

Provides:
* `DGPS.Frontier.STR029.str029_36_numerical_absorption_cross_form_estimate`: main statement, a conjunction of
  (1) for every `0 ≤ s ≤ 1/1000`: `99/100 ≤ c(s)`, `ℓ(s) ≤ 24/25`, `e^{2s} ≤ 101/100` and `e^{2s} ℓ(s)²/c(s) ≤ 1`,
  where `c = cFun_STR02935` and `ℓ = ellFun_STR02935`; (2) for `|h| ≤ 1/1000` and every periodic `H¹` pair
  `IsPeriodicWeakDerivative_STR02933 f g`: `∫ g² q_h dm ≥ (1 - h²) Var_{q_h m}(f)`, the inequality of STR029.05,
  with `Var_{q_h m}(f) = varQ_STR02935 h (f - ∫ f dm)`.
* `DGPS.Frontier.STR029.str029_36_numerical_absorption_cross_form_estimate_implication`: the literal implication.
  The two inequalities of STR029.35 for `(h, f, g)`, given as hypotheses, imply the STR029.05 inequality for `(h, f, g)`.
* `DGPS.Frontier.STR029.exp_two_le_STR02936`: `e^{2s} ≤ 101/100` for `0 ≤ s ≤ 1/1000`.
* `DGPS.Frontier.STR029.exp_neg_two_ge_STR02936`: `998/1000 ≤ e^{-2s}` for `s ≤ 1/1000`.
* `DGPS.Frontier.STR029.exp_pair_STR02936`: `e^{-2s} · e^{2s} = 1`.
* `DGPS.Frontier.STR029.cFun_lower_STR02936`: `99/100 ≤ c(s)` for `0 ≤ s ≤ 1/1000`.
* `DGPS.Frontier.STR029.sqrt_nine_tenths_le_STR02936`: `√(9/10) ≤ 19/20`.
* `DGPS.Frontier.STR029.sqrt_three_le_STR02936`: `√3 ≤ 2`.
* `DGPS.Frontier.STR029.ell_nonneg_STR02936`: `0 ≤ ℓ(s)` for `0 ≤ s`.
* `DGPS.Frontier.STR029.ell_le_STR02936`: `ℓ(s) ≤ 24/25` for `0 ≤ s ≤ 1/1000`.
* `DGPS.Frontier.STR029.ell_absorb_STR02936`: `e^{2s} ℓ(s)² ≤ c(s)` for `0 ≤ s ≤ 1/1000`.
* `DGPS.Frontier.STR029.exp_ell_ratio_STR02936`: `e^{2s} ℓ(s)² / c(s) ≤ 1` for `0 ≤ s ≤ 1/1000`.
* `DGPS.Frontier.STR029.bForm_nonneg_STR02936`: `0 ≤ b` for a periodic `H¹` pair, from STR029.02 applied to the
  complement `w = f - ∫ f dm - p`.
* `DGPS.Frontier.STR029.absorb_core_STR02936`: abstract completion of the square. From the first STR029.35 inequality
  and the variance comparison `V ≥ e^{-2s}(P + W)`, it gives `N - V ≥ -s² V` (with `N = ∫ g² q_h dm`, `V` the variance,
  `P = ‖p‖₂²`, `W = ‖w‖₂²`).

R5 notes:
* Hypotheses. The only hypotheses are those of the specification: `|h| ≤ 1/1000` (so `s = |h| ∈ [0, 1/1000]`) and
  `IsPeriodicWeakDerivative_STR02933 f g`, the periodic `H¹` class of STR029.35. No hypothesis is added. The two
  STR029.35 inequalities enter `str029_36_numerical_absorption_cross_form_estimate_implication` as explicit
  hypotheses. The main statement's part (2) is unconditional because STR029.35 is proved in the prerequisite unit
  `DGPS.Frontier.STR029.T35`, so the implication is applied to that theorem.
* Non-literal reading of "consequently the estimate in .35 implies .05". The literal implication is a separate
  declaration. The main statement asserts the .05 conclusion unconditionally. This is the same content, since the
  .35 estimate holds for every admissible `(h, f, g)`.
* Domain restriction. The numerical facts are stated for `0 ≤ s ≤ 1/1000` with `s` universally quantified. The
  main statement applies them at `s = |h| ≥ 0`, which matches the specification's `s = |h|`.
* Numerical bounds. The specification's proof uses `e^{2s} ≤ 1003/1000`. The formal proof proves the stated bound
  `e^{2s} ≤ 101/100`, obtained from `exp_two_sub_one_le_STR02904` (`e^{2s} - 1 ≤ 3s`). The lower bound on `e^{-2s}`
  comes from `Real.add_one_le_exp`, giving `e^{-2s} ≥ 1 - 2s ≥ 998/1000`. Then `c(s) ≥ (4·998/1000 - 101/100)/3`,
  which is `≥ 99/100`. The bound `ℓ(s) ≤ 24/25` uses `√(9/10) ≤ 19/20` and `√3 ≤ 2`, proved from `Real.sq_sqrt` and
  `nlinarith`, with `3√3 s ≤ 6s` and `s ≤ 1/1000`. The ratio bound uses `ℓ² ≤ (24/25)²` and `e^{2s} ≤ 101/100`,
  giving `e^{2s} ℓ² ≤ (101/100)(576/625) < 99/100 ≤ c(s)`.
* Square root of `b`. The main estimate writes `Real.sqrt (bForm_STR02935 f g)`. For a negative argument, Lean's
  `Real.sqrt` returns `0`, so `b ≥ 0` is needed for the completion of the square. It is proved here, not assumed, from
  the first inequality of STR029.02 applied to `w = compl_STR02935 f` with weak derivative `g - p'`, together with
  `W ≥ 0`.
* Absorption. Write `K = s ℓ ‖p‖₂` with `‖p‖₂ = Real.sqrt P`. The square `(c √b - K)² ≥ 0` gives
  `c b - 2K√b ≥ -K²/c`. The variance comparison `V ≥ e^{-2s}(P + W)` with `e^{-2s} e^{2s} = 1` gives `P ≤ e^{2s} V`.
  Together with `e^{2s} ℓ² ≤ c` this gives `K² ≤ s² c V`, so `N - V ≥ -s² V`, that is `N ≥ (1 - h²) V`, using
  `|h|² = h²`. The positive weight `c(s)` is divided out at the end.
* Integrals. `normInt_STR02933` is the normalized integral over `Ioc 0 (2π)`, with Lean's Bochner convention (value
  `0` when not integrable). All integrability and orthogonality facts used come from STR029.35 and its prerequisites.
* Variance. `Var_{q_h m}(f)` is `varQ_STR02935 h (f - ∫ f dm)`, the STR029.35 convention. Mean subtraction does not
  change the variance, so this matches the specification.
* Weights and optimizer data. The weight is `qT_STR02904 h`, the density from the STR029.04 unit. The Euler range map,
  the optimizer chart and the entropy and Fisher conventions are not used by this unit.
-/

namespace DGPS.Frontier.STR029

theorem exp_two_le_STR02936 {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 1000) :
    Real.exp (2 * s) ≤ 101 / 100 := by
  linarith [exp_two_sub_one_le_STR02904 hs0 hs]

theorem exp_neg_two_ge_STR02936 {s : ℝ} (hs : s ≤ 1 / 1000) :
    998 / 1000 ≤ Real.exp (-(2 * s)) := by
  linarith [Real.add_one_le_exp (-(2 * s))]

theorem exp_pair_STR02936 (s : ℝ) : Real.exp (-(2 * s)) * Real.exp (2 * s) = 1 := by
  rw [← Real.exp_add]
  simp

theorem cFun_lower_STR02936 {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 1000) :
    99 / 100 ≤ cFun_STR02935 s := by
  have h1 := exp_neg_two_ge_STR02936 hs
  have h2 := exp_two_le_STR02936 hs0 hs
  unfold cFun_STR02935
  linarith

theorem sqrt_nine_tenths_le_STR02936 : Real.sqrt (9 / 10) ≤ 19 / 20 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 9 / 10 by norm_num), Real.sqrt_nonneg (9 / 10 : ℝ)]

theorem sqrt_three_le_STR02936 : Real.sqrt 3 ≤ 2 := by
  nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]

theorem ell_nonneg_STR02936 {s : ℝ} (hs0 : 0 ≤ s) : 0 ≤ ellFun_STR02935 s := by
  unfold ellFun_STR02935
  have h1 := Real.sqrt_nonneg (9 / 10 : ℝ)
  have h2 : 0 ≤ 3 * Real.sqrt 3 * s :=
    mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg 3)) hs0
  linarith

theorem ell_le_STR02936 {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 1000) :
    ellFun_STR02935 s ≤ 24 / 25 := by
  unfold ellFun_STR02935
  have h1 := sqrt_nine_tenths_le_STR02936
  have h3 : Real.sqrt 3 * s ≤ 2 * s := mul_le_mul_of_nonneg_right sqrt_three_le_STR02936 hs0
  nlinarith [h1, h3, hs]

theorem ell_absorb_STR02936 {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 1000) :
    Real.exp (2 * s) * ellFun_STR02935 s ^ 2 ≤ cFun_STR02935 s := by
  have hE := exp_two_le_STR02936 hs0 hs
  have hl0 := ell_nonneg_STR02936 hs0
  have hl := ell_le_STR02936 hs0 hs
  have hl2 : ellFun_STR02935 s ^ 2 ≤ 576 / 625 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hl) (add_nonneg hl0 (by norm_num : (0 : ℝ) ≤ 24 / 25))]
  have hprod : Real.exp (2 * s) * ellFun_STR02935 s ^ 2 ≤ 101 / 100 * (576 / 625) :=
    mul_le_mul hE hl2 (sq_nonneg _) (by norm_num)
  have hc := cFun_lower_STR02936 hs0 hs
  linarith

theorem exp_ell_ratio_STR02936 {s : ℝ} (hs0 : 0 ≤ s) (hs : s ≤ 1 / 1000) :
    Real.exp (2 * s) * ellFun_STR02935 s ^ 2 / cFun_STR02935 s ≤ 1 := by
  have hc := cFun_lower_STR02936 hs0 hs
  have hcpos : 0 < cFun_STR02935 s := by linarith
  exact (div_le_one₀ hcpos).2 (ell_absorb_STR02936 hs0 hs)

theorem bForm_nonneg_STR02936 {f g : ℝ → ℝ} (hfg : IsPeriodicWeakDerivative_STR02933 f g) :
    0 ≤ bForm_STR02935 f g := by
  obtain ⟨o0, oc, os⟩ := compl_orth_STR02935 hfg.1.2
  have key : 3 * normInt_STR02933 (fun t => compl_STR02935 f t ^ 2)
      ≤ normInt_STR02933 (fun t => (g t - dharm_STR02935 (cosCoeff_STR02933 f 1)
          (sinCoeff_STR02933 f 1) t) ^ 2 - compl_STR02935 f t ^ 2) :=
    (str029_02_complementary_fourier_quadratic_inequalities (compl_STR02935 f)
      (fun t => g t - dharm_STR02935 (cosCoeff_STR02933 f 1) (sinCoeff_STR02933 f 1) t)
      (compl_weak_STR02935 hfg) o0 oc os).1
  have hW : 0 ≤ normInt_STR02933 (fun t => compl_STR02935 f t ^ 2) :=
    normInt_nonneg_STR02935 fun t => sq_nonneg _
  have hfh : firstHarm_STR02935 f
      = harm_STR02935 (cosCoeff_STR02933 f 1) (sinCoeff_STR02933 f 1) := rfl
  unfold bForm_STR02935
  rw [hfh, deriv_harm_STR02935]
  linarith

theorem absorb_core_STR02936 {s c el em ep N V Pq W b : ℝ} (hc : 0 < c) (hb : 0 ≤ b)
    (hPq : 0 ≤ Pq) (hW : 0 ≤ W) (he : 0 ≤ em) (hE : 0 ≤ ep) (hee : em * ep = 1)
    (hEc : ep * el ^ 2 ≤ c)
    (H1 : N - V ≥ c * b - 2 * s * el * Real.sqrt Pq * Real.sqrt b)
    (H2 : V ≥ em * (Pq + W)) :
    N - V ≥ -(s ^ 2) * V := by
  have hV : 0 ≤ V := le_trans (mul_nonneg he (add_nonneg hPq hW)) H2
  have hsq : Real.sqrt Pq ^ 2 = Pq := Real.sq_sqrt hPq
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  -- P ≤ e^{2s} V, since e^{-2s} e^{2s} = 1
  have hPqEV : Pq ≤ ep * V := by
    have h1 : ep * (em * (Pq + W)) ≤ ep * V := mul_le_mul_of_nonneg_left H2 hE
    have h2 : ep * (em * (Pq + W)) = Pq + W := by
      rw [← mul_assoc, mul_comm ep em, hee, one_mul]
    linarith
  -- (s ℓ)² P ≤ s² c V
  have hK : (s * el) ^ 2 * Pq ≤ s ^ 2 * c * V := by
    calc (s * el) ^ 2 * Pq ≤ (s * el) ^ 2 * (ep * V) :=
          mul_le_mul_of_nonneg_left hPqEV (sq_nonneg _)
      _ = s ^ 2 * (ep * el ^ 2) * V := by ring
      _ ≤ s ^ 2 * c * V :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEc (sq_nonneg s)) hV
  -- completion of the square: c² b - 2 c s ℓ √P √b + (s ℓ)² P = (c √b - s ℓ √P)² ≥ 0
  have hsq1 : 0 ≤ c ^ 2 * b - c * (2 * s * el * Real.sqrt Pq * Real.sqrt b) + (s * el) ^ 2 * Pq := by
    have e1 : (c * Real.sqrt b - s * el * Real.sqrt Pq) ^ 2
        = c ^ 2 * b - c * (2 * s * el * Real.sqrt Pq * Real.sqrt b) + (s * el) ^ 2 * Pq := by
      linear_combination c ^ 2 * hsb + (s * el) ^ 2 * hsq
    rw [← e1]
    exact sq_nonneg _
  have hX : c * (c * b - 2 * s * el * Real.sqrt Pq * Real.sqrt b) ≤ c * (N - V) :=
    mul_le_mul_of_nonneg_left H1 hc.le
  have hfin : c * (-(s ^ 2) * V) ≤ c * (N - V) := by
    linarith
  exact le_of_mul_le_mul_left hfin hc

theorem str029_36_numerical_absorption_cross_form_estimate_implication {h : ℝ} (hh : |h| ≤ 1 / 1000)
    {f g : ℝ → ℝ} (hfg : IsPeriodicWeakDerivative_STR02933 f g)
    (H1 : normInt_STR02933 (fun t => g t ^ 2 * qT_STR02904 h t)
          - varQ_STR02935 h (fun t => f t - normInt_STR02933 f)
        ≥ cFun_STR02935 |h| * bForm_STR02935 f g
          - 2 * |h| * ellFun_STR02935 |h|
            * Real.sqrt (normInt_STR02933 (fun t => firstHarm_STR02935 f t ^ 2))
            * Real.sqrt (bForm_STR02935 f g))
    (H2 : varQ_STR02935 h (fun t => f t - normInt_STR02933 f)
        ≥ Real.exp (-(2 * |h|)) * (normInt_STR02933 (fun t => firstHarm_STR02935 f t ^ 2)
            + normInt_STR02933 (fun t => compl_STR02935 f t ^ 2))) :
    normInt_STR02933 (fun t => g t ^ 2 * qT_STR02904 h t)
      ≥ (1 - h ^ 2) * varQ_STR02935 h (fun t => f t - normInt_STR02933 f) := by
  have hs0 : 0 ≤ |h| := abs_nonneg h
  have hb := bForm_nonneg_STR02936 hfg
  have hPq : 0 ≤ normInt_STR02933 (fun t => firstHarm_STR02935 f t ^ 2) :=
    normInt_nonneg_STR02935 fun t => sq_nonneg _
  have hW : 0 ≤ normInt_STR02933 (fun t => compl_STR02935 f t ^ 2) :=
    normInt_nonneg_STR02935 fun t => sq_nonneg _
  have hc := cFun_lower_STR02936 hs0 hh
  have key := absorb_core_STR02936 (s := |h|) (c := cFun_STR02935 |h|) (el := ellFun_STR02935 |h|)
    (em := Real.exp (-(2 * |h|))) (ep := Real.exp (2 * |h|))
    (N := normInt_STR02933 (fun t => g t ^ 2 * qT_STR02904 h t))
    (V := varQ_STR02935 h (fun t => f t - normInt_STR02933 f))
    (Pq := normInt_STR02933 (fun t => firstHarm_STR02935 f t ^ 2))
    (W := normInt_STR02933 (fun t => compl_STR02935 f t ^ 2))
    (b := bForm_STR02935 f g)
    (by linarith) hb hPq hW (Real.exp_pos (-(2 * |h|))).le (Real.exp_pos (2 * |h|)).le
    (exp_pair_STR02936 |h|) (ell_absorb_STR02936 hs0 hh) H1 H2
  rw [sq_abs] at key
  linarith

/-- STR029.36, the numerical absorption and its consequence for STR029.05. -/
theorem str029_36_numerical_absorption_cross_form_estimate :
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 / 1000 →
      99 / 100 ≤ cFun_STR02935 s ∧ ellFun_STR02935 s ≤ 24 / 25 ∧
        Real.exp (2 * s) ≤ 101 / 100 ∧
        Real.exp (2 * s) * ellFun_STR02935 s ^ 2 / cFun_STR02935 s ≤ 1) ∧
    (∀ h : ℝ, |h| ≤ 1 / 1000 → ∀ f g : ℝ → ℝ, IsPeriodicWeakDerivative_STR02933 f g →
      normInt_STR02933 (fun t => g t ^ 2 * qT_STR02904 h t)
        ≥ (1 - h ^ 2) * varQ_STR02935 h (fun t => f t - normInt_STR02933 f)) := by
  refine ⟨fun s hs0 hs => ⟨cFun_lower_STR02936 hs0 hs, ell_le_STR02936 hs0 hs,
    exp_two_le_STR02936 hs0 hs, exp_ell_ratio_STR02936 hs0 hs⟩, ?_⟩
  intro h hh f g hfg
  have hT := str029_35_quantitative_weighted_cross_form_estimate h hh f g hfg
  exact str029_36_numerical_absorption_cross_form_estimate_implication hh hfg hT.1 hT.2

end DGPS.Frontier.STR029
