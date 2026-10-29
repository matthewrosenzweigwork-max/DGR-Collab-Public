import DGPS.Frontier.STR029.T24
import DGPS.Frontier.STR029.T50

/-!
# STR029.64: Full Euler ordinary differential equation for the branch

Task id: STR029.64 (node STR029, frontier unit, leaf formalization).
Title: Full Euler ordinary differential equation for the branch.

On the common branch interval, including `h = 0`, the branch logarithm `u(h)` of the even branch
`j = 0` satisfies `u(h)'' = P_0 [3 h sin 3t u(h)' - u(h)'^2 / 2 - r(h) u(h)]`, where
`P_0 f = f - ∫ f dm`, `dm = dt / (2π)`, and `r(h) = 1 + h^2 s(h)` with `s(h) = Z 0 h 2`.

## Provides

* `DGPS.Frontier.STR029.str029_64_full_euler_ordinary_differential_equation_branch`: the existence
  conclusion of STR029.24, restated in full, with one further clause appended to its `δ`-block:
  for every `h` in `Set.Ioo (-δ) δ` and every `t`, the Euler equation above holds for the branch
  `j = 0`.
* `DGPS.Frontier.STR029.eulerF_STR02964`: the forcing `3 h sin 3t u' - u'^2 / 2 - r u`.
* `DGPS.Frontier.STR029.P0_STR02964`: the mean projection `f ↦ f - ∫ f dm` on functions of `t`.
* `DGPS.Frontier.STR029.meanT_add_const_STR02964`: the Haar mean of `f + c` is that of `f` plus `c`.
* `DGPS.Frontier.STR029.meanT_dd_zero_STR02964`: for a `C^{2,1/2}` periodic `u`, `∫ u'' dm = 0`.
* `DGPS.Frontier.STR029.euler_pointwise_STR02964`: for real `h` and `γ` and a `C^{2,1/2}` periodic
  `u` with `G = 0` pointwise, the Euler equation holds at every `t`.

## R5 notes

* Proof route. STR029.24 supplies `G = 0` and `ρ > 0` on the branch (its clause (A)). Dividing by
  `ρ` gives the bracket identity. Integrating it over one period, with the periodic integration by
  parts `∫ u'' dm = 0`, identifies the constant term as `-P_0 F`, which gives the ODE.
* The Haar-mean-zero property of `u` is not used. The projection `P_0` absorbs the term
  `r ∫ u dm`, so the ODE holds without it.
* The statement restates the existence conclusion of STR029.24 verbatim and appends the Euler
  clause to its `δ`-block. The branch is therefore the constructed data, not an arbitrary
  hypothesis. No hypothesis is added.
* Non-literal reading: "the branch" is read as the chart function
  `chartU_STR02924 ψ h (Z 0 h)`, the even branch `j = 0` that the spec chooses. The same proof
  gives the identity for every `j : Fin 3`, but only `j = 0` is stated.
* `u(h)''` is `deriv (deriv u) t` and `u(h)'` is `deriv u t`, as functions of the variable
  `t = 2π x` on all of `ℝ`. The equation is pointwise for every real `t`.
* `∫ f dm` is `meanT_STR02901 f = (2π)⁻¹ ∫_0^{2π} f`, and `P0_STR02964 f t = f t - meanT f`.
* The carrier is `IsC2Alpha_STR02901 (1 / 2)`, as supplied by `chartU_isC2_STR02924`.
* The interval is `Set.Ioo (-δ) δ` from STR029.24, which contains `h = 0`. The argument is uniform
  in `h`, so the value at `h = 0` needs no separate case.
* `r(h)` is written `1 + h ^ 2 * Z 0 h 2`, which is `1 + γ` with `γ = h^2 s` as in the clauses of
  STR029.24.
* Length: the file is longer than the 85–110 line estimate, because the STR029.24 conclusion is
  restated in full in the main statement.
-/

open scoped ContDiff
open Topology

namespace DGPS.Frontier.STR029

/-- The Euler forcing `F(t) = 3 h sin 3t u'(t) - u'(t)^2 / 2 - r u(t)` of STR029.64, with the
coefficient `r` passed as an argument. -/
noncomputable def eulerF_STR02964 (h r : ℝ) (u : ℝ → ℝ) : ℝ → ℝ :=
  fun t => 3 * h * Real.sin (3 * t) * deriv u t - (1 / 2) * deriv u t ^ 2 - r * u t

/-- The mean projection `P_0 f = f - ∫ f dm` of a function of `t`, evaluated pointwise. -/
noncomputable def P0_STR02964 (f : ℝ → ℝ) : ℝ → ℝ :=
  fun t => f t - meanT_STR02901 f

/-- The Haar mean of `f + c` is the Haar mean of `f` plus `c`, for continuous `f`. -/
theorem meanT_add_const_STR02964 {f : ℝ → ℝ} (hf : Continuous f) (c : ℝ) :
    meanT_STR02901 (fun t => f t + c) = meanT_STR02901 f + c := by
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  unfold meanT_STR02901
  rw [intervalIntegral.integral_add (hf.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const, smul_eq_mul]
  field_simp
  ring

/-- Periodic integration by parts: for a `C^{2,1/2}` periodic `u`, the Haar mean of `u''` is
zero, because `u'` is periodic. -/
theorem meanT_dd_zero_STR02964 {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u) :
    meanT_STR02901 (deriv (deriv u)) = 0 := by
  have hd : ∀ x ∈ Set.uIcc (0 : ℝ) (2 * Real.pi), HasDerivAt (deriv u) (deriv (deriv u) x) x :=
    fun x _ => (hu.2.2.1 x).hasDerivAt
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (hu.2.2.2.1.intervalIntegrable 0 (2 * Real.pi))
  have hper := deriv_periodic_STR02924 hu 0
  simp only [zero_add] at hper
  unfold meanT_STR02901
  rw [hint, hper, sub_self, mul_zero]

/-- Pointwise Euler equation. If `G = 0` for a `C^{2,1/2}` periodic `u`, then
`u'' = P_0 F` with `F = eulerF`, at every `t`. The bracket of `G` gives `u'' = F + c`
for a constant `c`, and integrating over one period identifies `c = -∫ F dm`. -/
theorem euler_pointwise_STR02964 (h γ : ℝ) {u : ℝ → ℝ} (hu : IsC2Alpha_STR02901 (1 / 2) u)
    (hG : ∀ t, gradG_STR02950 h γ u t = 0) :
    ∀ t, deriv (deriv u) t = P0_STR02964 (eulerF_STR02964 h (1 + γ) u) t := by
  have hc : Continuous u := hu.2.1.continuous
  have hc1 : Continuous (deriv u) := hu.2.2.1.continuous
  have hFc : Continuous (eulerF_STR02964 h (1 + γ) u) := by
    unfold eulerF_STR02964
    fun_prop
  have hmean0 := meanT_dd_zero_STR02964 hu
  have hB : ∀ t, -2 * deriv (deriv u) t + 6 * h * Real.sin (3 * t) * deriv u t
      - deriv u t ^ 2 - 2 * (1 + γ) * u t
      - meanT_STR02901 (fun r => deriv u r ^ 2 * rhoT_STR02901 h u r)
      + 2 * (1 + γ) * meanT_STR02901 (fun r => u r * rhoT_STR02901 h u r) = 0 := by
    intro t
    have h1 := hG t
    unfold gradG_STR02950 at h1
    rcases mul_eq_zero.mp h1 with h0 | h0
    · exact absurd h0 (rhoT_pos_STR02901 h hc t).ne'
    · exact h0
  set I := meanT_STR02901 (fun r => deriv u r ^ 2 * rhoT_STR02901 h u r)
  set E := meanT_STR02901 (fun r => u r * rhoT_STR02901 h u r)
  have hpt : ∀ t, deriv (deriv u) t =
      eulerF_STR02964 h (1 + γ) u t + (-I + 2 * (1 + γ) * E) / 2 := by
    intro t
    have hBt := hB t
    simp only [eulerF_STR02964]
    linear_combination (-1 / 2 : ℝ) * hBt
  have hfun : deriv (deriv u) =
      fun t => eulerF_STR02964 h (1 + γ) u t + (-I + 2 * (1 + γ) * E) / 2 :=
    funext hpt
  rw [hfun, meanT_add_const_STR02964 hFc] at hmean0
  intro t
  have hP : P0_STR02964 (eulerF_STR02964 h (1 + γ) u) t =
      eulerF_STR02964 h (1 + γ) u t - meanT_STR02901 (eulerF_STR02964 h (1 + γ) u) := rfl
  rw [hP, hpt t]
  linarith

/-- STR029.64, full Euler ordinary differential equation for the branch. The conclusion of
STR029.24 is restated, and its `δ`-block carries one further clause: for `h` in
`Set.Ioo (-δ) δ` and every `t`, the branch `j = 0` satisfies
`u(h)'' = P_0 [3 h sin 3t u(h)' - u(h)'^2 / 2 - r(h) u(h)]` with `r(h) = 1 + h^2 Z 0 h 2`. -/
theorem str029_64_full_euler_ordinary_differential_equation_branch :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∃ (O : Set (ℝ × (Fin 3 → ℝ))) (E : ℝ × (Fin 3 → ℝ) → ℝ),
        IsOpen O ∧ (∀ z : Fin 3 → ℝ, ((0 : ℝ), z) ∈ O) ∧ ContDiffOn ℝ ∞ E O ∧
        (∀ (h : ℝ) (z : Fin 3 → ℝ), (h, z) ∈ O → h ≠ 0 →
          E (h, z) = Fred_STR02956 ψ (h * z 0, h * z 1) (h, h ^ 2 * z 2) / h ^ 4) ∧
        (∀ z : Fin 3 → ℝ, E ((0 : ℝ), z) =
          Jred_STR02918 (z 0) (z 1) - z 2 * ((z 0 ^ 2 + z 1 ^ 2) / 2)) ∧
        ∃ η : ℝ, 0 < η ∧
          ∃ (N : Fin 3 → Set (Fin 3 → ℝ)) (Z : Fin 3 → ℝ → (Fin 3 → ℝ)),
            IsOpen (N 0) ∧ IsOpen (N 1) ∧ IsOpen (N 2) ∧
            N 0 ∈ 𝓝 (![2, 0, -16 / 15] : Fin 3 → ℝ) ∧
            N 1 ∈ 𝓝 (![-1, Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
            N 2 ∈ 𝓝 (![-1, -Real.sqrt 3, -16 / 15] : Fin 3 → ℝ) ∧
            (∀ i j : Fin 3, i ≠ j → Disjoint (N i) (N j)) ∧
            (∀ z : Fin 3 → ℝ, z ∈ N 0 ↔ (![z 0, -z 1, z 2] : Fin 3 → ℝ) ∈ N 0) ∧
            N 1 = rot_STR02923 '' N 0 ∧ N 2 = rot_STR02923 '' N 1 ∧
            (∀ j : Fin 3, ContDiffOn ℝ ∞ (Z j) (Set.Ioo (-η) η)) ∧
            (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, Z j h ∈ N j) ∧
            (∀ h ∈ Set.Ioo (-η) η, Z 1 h = rot_STR02923 (Z 0 h) ∧ Z 2 h = rot_STR02923 (Z 1 h)) ∧
            (∀ h ∈ Set.Ioo (-η) η, ∀ j : Fin 3, Z j h 2 = Z 0 h 2) ∧
            (∀ j : Fin 3, ∀ h ∈ Set.Ioo (-η) η, ∀ z ∈ N j,
              Kfun_STR02923 E (h, z) = 0 ↔ z = Z j h) ∧
            ∃ δ : ℝ, 0 < δ ∧ δ ≤ η ∧
              (∀ h ∈ Set.Ioo (-δ) δ, ∀ j : Fin 3,
                (∀ t, 0 < rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h)) t) ∧
                (∀ t, gradG_STR02950 h (h ^ 2 * Z j h 2) (chartU_STR02924 ψ h (Z j h)) t = 0) ∧
                (h ≠ 0 →
                  0 < entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) ∧
                  fisherChart_STR02949 h (chartU_STR02924 ψ h (Z j h)) /
                    (2 * entropyChart_STR02949 h (chartU_STR02924 ψ h (Z j h))) =
                    1 + h ^ 2 * Z j h 2)) ∧
              (∀ h ∈ Set.Ioo (-δ) δ, h ≠ 0 → ∀ i j : Fin 3, i ≠ j →
                rhoT_STR02901 h (chartU_STR02924 ψ h (Z i h)) ≠
                  rhoT_STR02901 h (chartU_STR02924 ψ h (Z j h))) ∧
              (∀ j : Fin 3, rhoT_STR02901 0 (chartU_STR02924 ψ 0 (Z j 0)) = qT_STR02901 0 ∧
                ∀ t, gradG_STR02950 0 0 (chartU_STR02924 ψ 0 (Z j 0)) t = 0) ∧
              (∀ h ∈ Set.Ioo (-δ) δ, ∀ t,
                deriv (deriv (chartU_STR02924 ψ h (Z 0 h))) t =
                  P0_STR02964
                    (eulerF_STR02964 h (1 + h ^ 2 * Z 0 h 2) (chartU_STR02924 ψ h (Z 0 h))) t) := by
  obtain ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC, hval, hzero, η,
    hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2, hZC, hZN, hZrot, hZs,
    hKuniq, δ, hδ, hδη, hA, hB, hC⟩ := str029_24_lift_reduced_branches_full_critical_densities
  refine ⟨U, V, ψ, hUo, hU0, hVo, hV0, hψC, hψ0, hψV, hR, O, E, hOo, hOmem, hEC, hval, hzero, η,
    hη, N, Z, hN0, hN1, hN2, hn0, hn1, hn2, hdisj, hsym, hrot1, hrot2, hZC, hZN, hZrot, hZs,
    hKuniq, δ, hδ, hδη, hA, hB, hC, ?_⟩
  intro h hh t
  exact euler_pointwise_STR02964 h (h ^ 2 * Z 0 h 2) (chartU_isC2_STR02924 ψ h (Z 0 h))
    (hA h hh 0).2.1 t

end DGPS.Frontier.STR029
