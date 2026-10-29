import DGPS.Frontier.EX049.T39
import DGPS.Frontier.EX049.T50

/-!
# EX049.51: Monotonicity and derivative sign of the profile

Task id and title: EX049.51, "Monotonicity and derivative sign of the profile" (node EX049, frontier
unit, leaf formalization, verification level V1). For real `h ≥ 2` let `A = 2 / (1 - e^{-2h})`,
`N u = A (1 - e^{-hu}) - u` and `Q u = N u / (u (2 - u))`. The specification states that `r_h` is
nonincreasing on `[0,2]` and that `r_h'(u) ≤ 0` for every `u ∈ [0,2]`. Here `r_h` is `Q` on `(0,2)`,
and its values and derivatives at the endpoints are those of the smooth extension of EX049.39.

## Provides

* `DGPS.Frontier.EX049.ex049_51_monotonicity_derivative_sign_profile`: for real `h` with `2 ≤ h`,
  the conjunction of (i) a smooth extension `g` of `Q` to an open set `U ⊇ [0,2]` exists (EX049.39),
  and (ii) every such extension is antitone on `[0,2]` and has `deriv g u ≤ 0` for `u ∈ [0,2]`.
* `DGPS.Frontier.EX049.antitoneOn_profile_EX04951`: helper; `Q` is antitone on the open interval
  `(0,2)`, from the positive triangle formula of EX049.50.
* `DGPS.Frontier.EX049.antitoneOn_extension_EX04951`: helper; statement (ii) for one given smooth
  extension, from the antitone property on `(0,2)` and the continuity of `g` and `deriv g` on `U`.

## R5 notes

* The only hypothesis of the main statement is `2 ≤ h`, the specification's "every `h ≥ 2`", kept
  verbatim. It gives `0 < h` and `exp (-(2 * h)) < 1`, which make `1 - e^{-2h}` and `A` positive.
  No hypothesis is added or weakened.
* Domain of `r_h`. The specification defines `r_h(u) = N_h(u) / (u (2 - u))` only for `0 < u < 2`,
  and its proof obtains the endpoint statements "for any smooth extension agreeing on the interval".
  Statement (ii) is therefore read as a statement about every smooth extension `g` of `Q`: an open
  set `U ⊇ [0,2]`, `ContDiffOn ℝ ∞ g U`, and `g u = Q u` for `u ∈ (0,2)`. The values of `r_h` on
  `[0,2]` are the values of `g` there.
* Non-vacuity. Statement (i) is the existence part of EX049.39, so some extension exists. The
  uniqueness part (ii) of EX049.39 is not needed and is not used: the conclusion is proved for every
  extension at once.
* `ContDiffOn ℝ ∞ g U` is the `∞` (top) smoothness class, as in EX049.39.
* "Nonincreasing on `[0,2]`" is read as Mathlib `AntitoneOn g (Set.Icc 0 2)`, which is non-strict.
* `r_h'(u)` is read as `deriv g u`, the derivative of `g : ℝ → ℝ` at `u`. It exists on `[0,2]`
  because `U` is open and `g` is `C^∞` on `U`. At the endpoints it is the two-sided derivative of
  the extension, not a one-sided derivative.
* Interior monotonicity uses the closed form of EX049.50, `Q u = A h^2 ∫∫ e^{-h(α u + 2β)}`, with
  its two finiteness conjuncts as integrability inputs and `integral_mono_on` in both variables. The
  derivative sign on `(0,2)` uses `AntitoneOn.derivWithin_nonpos`. No derivative is taken under an
  integral sign.
* Endpoints. The sign at `0` and `2` is obtained from the continuity of `deriv g` on `U`, by taking
  limits of the interior signs along `𝓝[>] 0` and `𝓝[<] 2`. Monotonicity on `[0,2]` is obtained from
  `antitoneOn_of_deriv_nonpos`, using continuity on `[0,2]` and the sign on the interior.
* The quotient is written with `A` expanded to `2 / (1 - Real.exp (-(2 * h)))` in the helper
  statements. This is the same real number as the `let`-bound `A` of the main statement.
* Exponents carry explicit parentheses, `-(h * (α * u + 2 * β))`, as in EX049.50.
* Not claimed here: the binding of `r_h` to the campaign object `corr` and of the derivative to the
  campaign objects of EX049.25, which is an open task. No theorem beyond EX049.39 and EX049.50 is used.
-/

open scoped ContDiff

namespace DGPS.Frontier.EX049

/-- On the open interval `(0,2)` the quotient profile `u ↦ (A (1 - e^{-hu}) - u) / (u (2 - u))`,
with `A = 2 / (1 - e^{-2h})`, is antitone, for every real `h ≥ 2`. -/
lemma antitoneOn_profile_EX04951 (h : ℝ) (hh : 2 ≤ h) :
    AntitoneOn (fun u : ℝ => (2 / (1 - Real.exp (-(2 * h))) * (1 - Real.exp (-(h * u))) - u) /
      (u * (2 - u))) (Set.Ioo (0:ℝ) 2) := by
  have hhpos : (0:ℝ) < h := by linarith
  have hlt1 : Real.exp (-(2 * h)) < 1 := by
    have h0 : Real.exp (-(2 * h)) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rwa [Real.exp_zero] at h0
  have hC1 : (0:ℝ) < 1 - Real.exp (-(2 * h)) := sub_pos.mpr hlt1
  have hAh : (0:ℝ) ≤ 2 / (1 - Real.exp (-(2 * h))) * h ^ 2 :=
    mul_nonneg (div_nonneg (by norm_num) hC1.le) (sq_nonneg h)
  intro u1 hu1 u2 hu2 h12
  have key1 : (2 / (1 - Real.exp (-(2 * h))) * (1 - Real.exp (-(h * u1))) - u1) /
      (u1 * (2 - u1)) = 2 / (1 - Real.exp (-(2 * h))) * h ^ 2 *
        (∫ α in (0:ℝ)..1, ∫ β in (0:ℝ)..(1 - α), Real.exp (-(h * (α * u1 + 2 * β)))) :=
    (ex049_50_positive_triangle_formula_open_interval h hh u1 hu1).1
  have key2 : (2 / (1 - Real.exp (-(2 * h))) * (1 - Real.exp (-(h * u2))) - u2) /
      (u2 * (2 - u2)) = 2 / (1 - Real.exp (-(2 * h))) * h ^ 2 *
        (∫ α in (0:ℝ)..1, ∫ β in (0:ℝ)..(1 - α), Real.exp (-(h * (α * u2 + 2 * β)))) :=
    (ex049_50_positive_triangle_formula_open_interval h hh u2 hu2).1
  have hF2 := (ex049_50_positive_triangle_formula_open_interval h hh u2 hu2).2.2
  have hF1 := (ex049_50_positive_triangle_formula_open_interval h hh u1 hu1).2.2
  have hI : (∫ α in (0:ℝ)..1, ∫ β in (0:ℝ)..(1 - α), Real.exp (-(h * (α * u2 + 2 * β)))) ≤
      ∫ α in (0:ℝ)..1, ∫ β in (0:ℝ)..(1 - α), Real.exp (-(h * (α * u1 + 2 * β))) := by
    refine intervalIntegral.integral_mono_on zero_le_one hF2 hF1 ?_
    intro α hα
    have hα0 : 0 ≤ α := hα.1
    have hαu : α * u1 ≤ α * u2 := mul_le_mul_of_nonneg_left h12 hα0
    refine intervalIntegral.integral_mono_on (by linarith [hα.2])
      ((ex049_50_positive_triangle_formula_open_interval h hh u2 hu2).2.1 α hα)
      ((ex049_50_positive_triangle_formula_open_interval h hh u1 hu1).2.1 α hα) ?_
    intro β _
    have hhm : h * (α * u1 + 2 * β) ≤ h * (α * u2 + 2 * β) :=
      mul_le_mul_of_nonneg_left (by linarith) hhpos.le
    exact Real.exp_le_exp.mpr (by linarith)
  show (2 / (1 - Real.exp (-(2 * h))) * (1 - Real.exp (-(h * u2))) - u2) /
      (u2 * (2 - u2)) ≤
    (2 / (1 - Real.exp (-(2 * h))) * (1 - Real.exp (-(h * u1))) - u1) / (u1 * (2 - u1))
  rw [key1, key2]
  exact mul_le_mul_of_nonneg_left hI hAh

/-- For a smooth extension `g` of the quotient profile to an open set `U ⊇ [0,2]`, `g` is
nonincreasing on `[0,2]` and `deriv g u ≤ 0` for every `u ∈ [0,2]`, for every real `h ≥ 2`. -/
lemma antitoneOn_extension_EX04951 (h : ℝ) (hh : 2 ≤ h) (U : Set ℝ) (g : ℝ → ℝ)
    (hU : IsOpen U) (hIcc : Set.Icc (0:ℝ) 2 ⊆ U) (hc : ContDiffOn ℝ ∞ g U)
    (hgQ : ∀ u ∈ Set.Ioo (0:ℝ) 2,
      g u = (2 / (1 - Real.exp (-(2 * h))) * (1 - Real.exp (-(h * u))) - u) / (u * (2 - u))) :
    AntitoneOn g (Set.Icc (0:ℝ) 2) ∧ ∀ u ∈ Set.Icc (0:ℝ) 2, deriv g u ≤ 0 := by
  have hn : (1 : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hn0 : (∞ : WithTop ℕ∞) ≠ 0 := (lt_of_lt_of_le zero_lt_one hn).ne'
  have hanti_open : AntitoneOn g (Set.Ioo (0:ℝ) 2) := by
    intro a ha b hb hab
    rw [hgQ a ha, hgQ b hb]
    exact antitoneOn_profile_EX04951 h hh ha hb hab
  have hderiv_open : ∀ x ∈ Set.Ioo (0:ℝ) 2, deriv g x ≤ 0 := by
    intro x hx
    have h1 : derivWithin g (Set.Ioo (0:ℝ) 2) x ≤ 0 := hanti_open.derivWithin_nonpos
    rwa [derivWithin_of_isOpen isOpen_Ioo hx] at h1
  have hdiff : DifferentiableOn ℝ g (Set.Ioo (0:ℝ) 2) :=
    (hc.differentiableOn hn0).mono (fun x hx => hIcc (Set.Ioo_subset_Icc_self hx))
  have hanti : AntitoneOn g (Set.Icc (0:ℝ) 2) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc (0:ℝ) 2) (hc.continuousOn.mono hIcc)
    · rw [interior_Icc]
      exact hdiff
    · rw [interior_Icc]
      exact hderiv_open
  refine ⟨hanti, ?_⟩
  have hdc : ContinuousOn (deriv g) U := hc.continuousOn_deriv_of_isOpen hU hn
  intro u hu
  obtain ⟨hu0, hu2⟩ := hu
  rcases eq_or_lt_of_le hu0 with h0 | h0
  · subst h0
    have h0U : (0:ℝ) ∈ U := hIcc (show (0:ℝ) ∈ Set.Icc (0:ℝ) 2 from ⟨le_rfl, by norm_num⟩)
    have hcont : ContinuousAt (deriv g) 0 := hdc.continuousAt (hU.mem_nhds h0U)
    refine le_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))) ?_
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 2 by norm_num)] with x hx
    exact hderiv_open x hx
  · rcases eq_or_lt_of_le hu2 with h2 | h2
    · subst h2
      have h2U : (2:ℝ) ∈ U := hIcc (show (2:ℝ) ∈ Set.Icc (0:ℝ) 2 from ⟨by norm_num, le_rfl⟩)
      have hcont : ContinuousAt (deriv g) 2 := hdc.continuousAt (hU.mem_nhds h2U)
      refine le_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (2:ℝ)))) ?_
      filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 2 by norm_num)] with x hx
      exact hderiv_open x hx
    · exact hderiv_open u ⟨h0, h2⟩

/-- EX049.51, monotonicity and derivative sign of the profile. For every real `h ≥ 2` the profile
`r_h` on `[0,2]` is given by a smooth extension of `Q(u) = (A (1 - e^{-hu}) - u) / (u (2 - u))` with
`A = 2 / (1 - e^{-2h})`, and such an extension exists. Every smooth extension `g` of `Q` to an open
set `U ⊇ [0,2]` is nonincreasing on `[0,2]` and satisfies `deriv g u ≤ 0` for every `u ∈ [0,2]`. -/
theorem ex049_51_monotonicity_derivative_sign_profile (h : ℝ) (hh : 2 ≤ h) :
    let A : ℝ := 2 / (1 - Real.exp (-(2 * h)))
    let N : ℝ → ℝ := fun u => A * (1 - Real.exp (-(h * u))) - u
    let Q : ℝ → ℝ := fun u => N u / (u * (2 - u))
    (∃ g : ℝ → ℝ, ∃ U : Set ℝ, IsOpen U ∧ Set.Icc (0:ℝ) 2 ⊆ U ∧ ContDiffOn ℝ ∞ g U ∧
        ∀ u ∈ Set.Ioo (0:ℝ) 2, g u = Q u) ∧
      ∀ (U : Set ℝ) (g : ℝ → ℝ), IsOpen U → Set.Icc (0:ℝ) 2 ⊆ U → ContDiffOn ℝ ∞ g U →
        (∀ u ∈ Set.Ioo (0:ℝ) 2, g u = Q u) →
        AntitoneOn g (Set.Icc (0:ℝ) 2) ∧ ∀ u ∈ Set.Icc (0:ℝ) 2, deriv g u ≤ 0 := by
  intro A N Q
  obtain ⟨g, U, hU, hIcc, hc, hgQ, -, -⟩ := (ex049_39_glue_smooth_correction_derivative h hh).1
  refine ⟨⟨g, U, hU, hIcc, hc, hgQ⟩, ?_⟩
  intro U' g' hU' hIcc' hc' hgQ'
  exact antitoneOn_extension_EX04951 h hh U' g' hU' hIcc' hc' hgQ'

end DGPS.Frontier.EX049
