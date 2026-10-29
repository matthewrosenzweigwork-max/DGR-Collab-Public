import DGPS.Frontier.EX049.T06
import DGPS.Frontier.EX049.T25
import DGPS.Frontier.EX049.T51

/-!
# EX049.52: Exact pointwise square completion

Task id and title: EX049.52, "Exact pointwise square completion" (node EX049, frontier unit,
leaf formalization). For real `h ≥ 2` and real `θ`, put `U = 1 - cos θ`, `a = h + r_h(U)`,
`b = -a sin θ`, `𝒱 = b²/4 + b'/2` and `g = -b cos θ / 2`. The specification states that these
are smooth and periodic, that `b` and `𝒱` are the campaign drift `driftB h` and ground potential
`groundPot h`, and, at every real angle, the exact identity

`𝒱 - g² + g' = (h/2) U - 1 + (a sin²θ/2 - 1)² + (1/2) r_h(U) U - (1/2) r_h'(U) U sin²θ`

together with its consequence `𝒱 - g² + g' ≥ (h/2) U - 1`.

## Provides

* `DGPS.Frontier.EX049.ex049_52_exact_pointwise_square_completion`: for real `h` with `2 ≤ h`,
  the conjunction of (i) smoothness of `a`, `b`, `𝒱`, `g` on `ℝ`, (ii) their `2π`-periodicity,
  (iii) the binding `driftB h = b` and `groundPot h = 𝒱`, (iv) the exact identity at every real
  `θ`, and (v) the lower bound at every real `θ`.
* `DGPS.Frontier.EX049.mem_Icc_one_sub_cos_EX04952`: `1 - cos θ` lies in `[0, 2]`.
* `DGPS.Frontier.EX049.integrand_eq_quot_EX04952`: `r_h` equals the quotient `Q` on `(0,2)`.
* `DGPS.Frontier.EX049.hasDerivAt_profile_EX04952`: derivative of `θ ↦ r_h(1 - cos θ)`.
* `DGPS.Frontier.EX049.hasDerivAt_drift_EX04952`: derivative of `θ ↦ -(h + r_h(1 - cos θ)) sin θ`.
* `DGPS.Frontier.EX049.nonneg_profile_EX04952`: `0 ≤ r_h` on `[0,2]` (from EX049.06).
* `DGPS.Frontier.EX049.deriv_nonpos_profile_EX04952`: `r_h' ≤ 0` on `[0,2]` (from EX049.51).

## R5 notes

* Hypothesis. The only hypothesis is `2 ≤ h`, the specification's "for every `h ≥ 2`", kept
  verbatim. It gives `0 < h`, which the campaign lemmas of EX049.25 and the Examples layer require.
  No hypothesis is added or weakened.
* The profile `r_h`. It is read as the campaign object `DGPS.Examples.EngineeredRankOne.integrand h`
  of EX049.25. This is the totalized `r_h`: it equals `N_h(u) / (u (2 - u))` for `u ∉ {0, 2}`, and
  it is `C^∞` on all of `ℝ`. Its values on `[0,2]` are the values of `r_h` in the specification,
  and it is a smooth extension of `Q` in the sense of EX049.06 and EX049.51.
* The derivative `r_h'(U)` is read as `deriv (integrand h) U`, the ordinary derivative of that
  `C^∞` function on `ℝ`. At the critical angles `cos θ = ±1` (where `U ∈ {0, 2}`) it is the
  two-sided derivative. No claim is made about other smooth extensions: EX049.51 is applied to
  `integrand h` itself, with the open set `U = ℝ`.
* Smooth and periodic. "Define smooth periodic functions" is formalized as conjuncts (i) and (ii):
  `a`, `b`, `𝒱`, `g` are `ContDiff ℝ ∞` on `ℝ` and `Function.Periodic _ (2π)`. Smoothness of `b`
  and periodicity of `b` and `𝒱` are inherited from `contDiff_driftB`, `driftB_periodic` and
  `groundPot_periodic` after binding; `a` and `g` are checked directly from the formulas.
* Binding. `b = driftB h` uses `driftB_eq`, which is stated with the totalized `integrand`, not
  with the quotient. So the angles with `cos θ = ±1` are included without any side condition.
  `𝒱 = groundPot h` unfolds `groundPot` and uses the first binding. The `b'` in `𝒱` and `g` is
  `deriv b`, which after binding is `deriv (driftB h)`.
* Exact identity. It is proved as an equality of polynomial expressions in `sin θ`, `cos θ`, `a θ`,
  `r_h(U)` and `r_h'(U)`, after the chain-rule formulas for `b'` and `g'` and the relation
  `sin²θ + cos²θ = 1`. There is no division by `sin θ`, `U` or `2 - U`, so the two critical angles
  are included.
* Lower bound. It uses only the displayed identity, `U ∈ [0,2]`, `r_h ≥ 0` on `[0,2]` (EX049.06)
  and `r_h' ≤ 0` on `[0,2]` (EX049.51). The three remainder terms are nonnegative.
* Non-literal reading. The displayed inequality is stated for every real angle, as in the
  specification. The circle reading of `b` and `𝒱` is the one of EX049.25, through the lifted angle.
-/

open scoped ContDiff
open DGPS.Examples.EngineeredRankOne

namespace DGPS.Frontier.EX049

/-- For every real `θ`, `1 - cos θ` lies in the closed interval `[0, 2]`. -/
theorem mem_Icc_one_sub_cos_EX04952 (θ : ℝ) : 1 - Real.cos θ ∈ Set.Icc (0:ℝ) 2 :=
  ⟨by linarith [Real.cos_le_one θ], by linarith [Real.neg_one_le_cos θ]⟩

/-- On the open interval `(0,2)` the totalized profile `integrand h` is the quotient
`(A (1 - e^{-hu}) - u) / (u (2 - u))` with `A = 2 / (1 - e^{-2h})`. -/
theorem integrand_eq_quot_EX04952 (h : ℝ) (h0 : 0 < h) :
    ∀ u ∈ Set.Ioo (0:ℝ) 2,
      integrand h u = (2 / (1 - Real.exp (-(2 * h))) * (1 - Real.exp (-(h * u))) - u) /
        (u * (2 - u)) :=
  fun _ hu => integrand_eq_rsrc_EX04925 h h0 hu.1.ne' hu.2.ne

/-- The profile `r_h` is nonnegative on `[0,2]` for every real `h ≥ 2` (EX049.06). -/
theorem nonneg_profile_EX04952 (h : ℝ) (hh : 2 ≤ h) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 2) :
    0 ≤ integrand h u := by
  have h0 : (0:ℝ) < h := by linarith
  obtain ⟨-, hbd⟩ := ex049_06_pointwise_correction_derivative_bounds h hh
  exact (hbd (integrand h) Set.univ isOpen_univ (Set.subset_univ _)
    (contDiff_integrand h h0).contDiffOn (integrand_eq_quot_EX04952 h h0)).1 u hu

/-- The derivative of the profile `r_h` is nonpositive on `[0,2]` for every real `h ≥ 2`
(EX049.51). -/
theorem deriv_nonpos_profile_EX04952 (h : ℝ) (hh : 2 ≤ h) {u : ℝ} (hu : u ∈ Set.Icc (0:ℝ) 2) :
    deriv (integrand h) u ≤ 0 := by
  have h0 : (0:ℝ) < h := by linarith
  obtain ⟨-, hall⟩ := ex049_51_monotonicity_derivative_sign_profile h hh
  exact (hall Set.univ (integrand h) isOpen_univ (Set.subset_univ _)
    (contDiff_integrand h h0).contDiffOn (integrand_eq_quot_EX04952 h h0)).2 u hu

/-- Chain rule for `θ ↦ r_h(1 - cos θ)`. -/
theorem hasDerivAt_profile_EX04952 (h : ℝ) (h0 : 0 < h) (θ : ℝ) :
    HasDerivAt (fun t => integrand h (1 - Real.cos t))
      (deriv (integrand h) (1 - Real.cos θ) * Real.sin θ) θ := by
  have hd : DifferentiableAt ℝ (integrand h) (1 - Real.cos θ) :=
    (contDiff_integrand h h0).differentiable (by simp) _
  have hc : HasDerivAt (fun t => 1 - Real.cos t) (Real.sin θ) θ :=
    ((Real.hasDerivAt_cos θ).const_sub 1).congr_deriv (by ring)
  exact hd.hasDerivAt.comp θ hc

/-- Derivative of `θ ↦ -(h + r_h(1 - cos θ)) sin θ`, that is of the drift `b` in terms of `r_h`. -/
theorem hasDerivAt_drift_EX04952 (h : ℝ) (h0 : 0 < h) (θ : ℝ) :
    HasDerivAt (fun t => -((h + integrand h (1 - Real.cos t)) * Real.sin t))
      (-((deriv (integrand h) (1 - Real.cos θ) * Real.sin θ) * Real.sin θ +
        (h + integrand h (1 - Real.cos θ)) * Real.cos θ)) θ :=
  (((hasDerivAt_profile_EX04952 h h0 θ).const_add h).mul (Real.hasDerivAt_sin θ)).neg

/-- EX049.52, exact pointwise square completion. For every real `h ≥ 2`, with `U = 1 - cos θ`,
`a = h + r_h(U)`, `b = -a sin θ`, `𝒱 = b²/4 + b'/2` and `g = -b cos θ / 2`: `a`, `b`, `𝒱`, `g` are
smooth and `2π`-periodic on `ℝ`; `b = driftB h` and `𝒱 = groundPot h`; at every real `θ`,
`𝒱 - g² + g' = (h/2) U - 1 + (a sin²θ/2 - 1)² + (1/2) r_h(U) U - (1/2) r_h'(U) U sin²θ`; and at
every real `θ`, `𝒱 - g² + g' ≥ (h/2) U - 1`. -/
theorem ex049_52_exact_pointwise_square_completion (h : ℝ) (hh : 2 ≤ h) :
    let U : ℝ → ℝ := fun θ => 1 - Real.cos θ
    let a : ℝ → ℝ := fun θ => h + integrand h (U θ)
    let b : ℝ → ℝ := fun θ => -(a θ * Real.sin θ)
    let V : ℝ → ℝ := fun θ => b θ ^ 2 / 4 + deriv b θ / 2
    let g : ℝ → ℝ := fun θ => -(b θ * Real.cos θ) / 2
    (ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧ ContDiff ℝ ∞ V ∧ ContDiff ℝ ∞ g) ∧
      (Function.Periodic a (2 * Real.pi) ∧ Function.Periodic b (2 * Real.pi) ∧
        Function.Periodic V (2 * Real.pi) ∧ Function.Periodic g (2 * Real.pi)) ∧
      (driftB h = b ∧ groundPot h = V) ∧
      (∀ θ : ℝ, V θ - g θ ^ 2 + deriv g θ =
        h / 2 * U θ - 1 + (a θ * Real.sin θ ^ 2 / 2 - 1) ^ 2 +
          1 / 2 * integrand h (U θ) * U θ -
            1 / 2 * deriv (integrand h) (U θ) * U θ * Real.sin θ ^ 2) ∧
      (∀ θ : ℝ, h / 2 * U θ - 1 ≤ V θ - g θ ^ 2 + deriv g θ) := by
  intro U a b V g
  have h0 : (0:ℝ) < h := by linarith
  have ha : ∀ θ : ℝ, a θ = h + integrand h (1 - Real.cos θ) := fun θ => rfl
  have hb : ∀ θ : ℝ, b θ = -((h + integrand h (1 - Real.cos θ)) * Real.sin θ) := fun θ => rfl
  have hU : ∀ θ : ℝ, U θ = 1 - Real.cos θ := fun θ => rfl
  have hV : ∀ θ : ℝ, V θ = b θ ^ 2 / 4 + deriv b θ / 2 := fun θ => rfl
  have hg : ∀ θ : ℝ, g θ = -(b θ * Real.cos θ) / 2 := fun θ => rfl
  have hbd : ∀ θ : ℝ, deriv b θ =
      -((deriv (integrand h) (1 - Real.cos θ) * Real.sin θ) * Real.sin θ +
        (h + integrand h (1 - Real.cos θ)) * Real.cos θ) :=
    fun θ => (hasDerivAt_drift_EX04952 h h0 θ).deriv
  have hbd' : ∀ θ : ℝ, HasDerivAt b (deriv b θ) θ :=
    fun θ => (hasDerivAt_drift_EX04952 h h0 θ).differentiableAt.hasDerivAt
  have hgd : ∀ θ : ℝ, deriv g θ = -(deriv b θ * Real.cos θ + b θ * -Real.sin θ) / 2 :=
    fun θ => (((hbd' θ).mul (Real.hasDerivAt_cos θ)).neg.div_const 2).deriv
  have hdrift : driftB h = b := funext fun t => (driftB_eq h h0 t).trans (neg_mul _ _)
  have hgp : groundPot h = V := by
    funext t
    show driftB h t ^ 2 / 4 + deriv (driftB h) t / 2 = b t ^ 2 / 4 + deriv b t / 2
    rw [hdrift]
  -- smoothness
  have hca : ContDiff ℝ ∞ a := by
    show ContDiff ℝ ∞ (fun θ => h + integrand h (1 - Real.cos θ))
    exact contDiff_const.add ((contDiff_integrand h h0).comp
      ((contDiff_const (c := (1:ℝ))).sub Real.contDiff_cos))
  have hcb : ContDiff ℝ ∞ b := by
    rw [← hdrift]
    exact DGPS.Examples.EngineeredGroundState.contDiff_driftB h h0
  have hdb_smooth : ContDiff ℝ ∞ (deriv b) := by
    rw [← hdrift]
    exact (contDiff_infty_iff_deriv.mp
      (DGPS.Examples.EngineeredGroundState.contDiff_driftB h h0)).2
  have hcV : ContDiff ℝ ∞ V := by
    show ContDiff ℝ ∞ (fun θ => b θ ^ 2 / 4 + deriv b θ / 2)
    exact ((hcb.pow 2).div_const 4).add (hdb_smooth.div_const 2)
  have hcg : ContDiff ℝ ∞ g := by
    show ContDiff ℝ ∞ (fun θ => -(b θ * Real.cos θ) / 2)
    exact ((hcb.mul Real.contDiff_cos).neg.div_const 2)
  -- periodicity
  have hpa : Function.Periodic a (2 * Real.pi) := fun t => by
    show h + integrand h (1 - Real.cos (t + 2 * Real.pi)) = h + integrand h (1 - Real.cos t)
    rw [Real.cos_add_two_pi]
  have hpb : Function.Periodic b (2 * Real.pi) := by
    rw [← hdrift]
    exact DGPS.Examples.EngineeredGroundState.driftB_periodic h h0
  have hpV : Function.Periodic V (2 * Real.pi) := by
    rw [← hgp]
    exact DGPS.Examples.EngineeredGroundState.groundPot_periodic h h0
  have hpg : Function.Periodic g (2 * Real.pi) := fun t => by
    rw [hg, hg, hpb t, Real.cos_add_two_pi]
  -- the exact identity
  have hid : ∀ θ : ℝ, V θ - g θ ^ 2 + deriv g θ =
      h / 2 * U θ - 1 + (a θ * Real.sin θ ^ 2 / 2 - 1) ^ 2 +
        1 / 2 * integrand h (U θ) * U θ - 1 / 2 * deriv (integrand h) (U θ) * U θ * Real.sin θ ^ 2 := by
    intro θ
    rw [hV θ, hgd θ, hg θ, hbd θ, hb θ, ha θ, hU θ]
    linear_combination ((h + integrand h (1 - Real.cos θ)) / 2 -
      (h + integrand h (1 - Real.cos θ)) ^ 2 * Real.sin θ ^ 2 / 4) * Real.sin_sq_add_cos_sq θ
  -- the lower bound
  have hlow : ∀ θ : ℝ, h / 2 * U θ - 1 ≤ V θ - g θ ^ 2 + deriv g θ := by
    intro θ
    have hU0 : (0:ℝ) ≤ U θ := (mem_Icc_one_sub_cos_EX04952 θ).1
    have hr0 : 0 ≤ integrand h (U θ) :=
      nonneg_profile_EX04952 h hh (mem_Icc_one_sub_cos_EX04952 θ)
    have hp0 : deriv (integrand h) (U θ) ≤ 0 :=
      deriv_nonpos_profile_EX04952 h hh (mem_Icc_one_sub_cos_EX04952 θ)
    rw [hid θ]
    nlinarith [sq_nonneg (a θ * Real.sin θ ^ 2 / 2 - 1), mul_nonneg hr0 hU0,
      mul_nonneg (mul_nonneg (neg_nonneg.2 hp0) hU0) (sq_nonneg (Real.sin θ))]
  exact ⟨⟨hca, hcb, hcV, hcg⟩, ⟨hpa, hpb, hpV, hpg⟩, ⟨hdrift, hgp⟩, hid, hlow⟩

end DGPS.Frontier.EX049
