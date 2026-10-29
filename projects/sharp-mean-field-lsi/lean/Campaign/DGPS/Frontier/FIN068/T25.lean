import Mathlib

/-!
Task id and title: FIN068.25, Three scalar Taylor bounds for q (module
`DGPS.Frontier.FIN068.T25`).

Provides:
* `DGPS.Frontier.FIN068.fin068_25_three_scalar_taylor_bounds_q`: for a function `q : ℝ → ℝ`
  that is `C^∞` on an open set `U` containing a closed symmetric interval `Set.Icc (-δ) δ`, with
  `|q'''| ≤ M` on that interval, `q'(0) = 0` and `q''(0) = -2 c₄`, every `z` in the interval
  satisfies `|q z - q 0 + c₄ z²| ≤ M |z|³/6`, `|q' z + 2 c₄ z| ≤ M z²/2` and
  `|q'' z + 2 c₄| ≤ M |z|`.
* Helper declarations, all with suffix `_FIN06825` and not part of the interface:
  `pos_FIN06825` (one-sided comparison `|h z| ≤ P z` on `[0, R]` from a derivative bound by `p`,
  via monotonicity of `P ∓ h`), and `sym_FIN06825` (the same on `[-R, R]`, with the bound written
  in `|t|`, by reflection `t ↦ -t` for negative `z`).

Proof: the first bound is the mean value inequality for `q''` (its derivative `q'''` is bounded by
`M`), giving `|q'' z + 2c₄| ≤ M |z|`. Let `h₂ = q' + 2c₄ id`; then `h₂(0) = 0` and
`|h₂'(t)| ≤ M|t|`, so `sym_FIN06825` gives `|h₂ z| ≤ M z²/2`. Let `h₃ = q - q(0) + c₄ id²`;
then `h₃(0) = 0` and `h₃' = h₂`, so `sym_FIN06825` with `P(t) = M t³/6` gives the first bound.

R5 notes:
* Domain: the "smooth domain" is read as an arbitrary open set `U ⊆ ℝ` with
  `Set.Icc (-δ) δ ⊆ U` and `q` `C^∞` on `U`. No particular domain (such as the rectangle of
  FIN068.04 or the interval `Set.Ioo (-δz) δz` of FIN068.09) is fixed; any such choice is an
  instance. The closed interval is `Set.Icc (-δ) δ`, with no sign assumption on `δ` (for `δ < 0`
  the statement is vacuous). Openness of `U` is needed so that the Lean derivatives are two-sided
  derivatives at every point of the interval.
* `C^∞` is taken literally (`ContDiffOn ℝ ∞`); the proof uses only `C^3`.
* `M_q ≥ 0` is included as the hypothesis `_hM0`. It is not used in the proof: the bounds hold
  for any `M` that dominates `|q'''|` on the interval. The bound hypothesis `|q'''| ≤ M` is required
  only on the closed interval `Set.Icc (-δ) δ`, not on `U`.
* `q'''` is read as `deriv (deriv (deriv q))`, `q'` as `deriv q` and `q''` as `deriv (deriv q)`.
* The hypotheses `deriv q 0 = 0` and `deriv (deriv q) 0 = -2 * c₄` are taken as hypotheses, with
  `c₄` an arbitrary real number. In FIN068.09 they are the facts `q'(0) = 0` and
  `q''(0) = -2 c₄` (with `c₄ = b d / (10240 A)`), but the value of `c₄` is not used here.
  The value `q(0)` is not identified with `ψ(w₋)`; the first bound is relative to `q 0`, as in
  the specification.
* The bounds concern both signs of `z`. The negative side is handled by the reflection inside
  `sym_FIN06825` (the interval orientation is reversed explicitly), not by a separate argument.
* No Campaign module is imported (only `Mathlib`): the statement is scalar and generic in `q`.
  The prerequisites FIN068.07 and FIN068.09 are not imported. The FIN068.09 function
  `q z = J(a z, z)` is an instance of this statement and is the intended consumer's input
  (FIN068.26), where the domain would be `Set.Ioo (-δz) δz`.
-/

open scoped ContDiff

namespace DGPS.Frontier.FIN068

/-- One-sided comparison. If `h` has derivative `h'` on `[0, R]`, `|h' t| ≤ p t` there, `h 0 = 0`
and `P` has derivative `p` everywhere with `P 0 = 0`, then `|h z| ≤ P z` on `[0, R]`. -/
lemma pos_FIN06825 {R : ℝ} {h h' p P : ℝ → ℝ}
    (hh : ∀ t ∈ Set.Icc 0 R, HasDerivAt h (h' t) t)
    (hP : ∀ t, HasDerivAt P (p t) t)
    (hb : ∀ t ∈ Set.Icc 0 R, |h' t| ≤ p t) (h0 : h 0 = 0) (P0 : P 0 = 0) :
    ∀ z ∈ Set.Icc 0 R, |h z| ≤ P z := by
  have key : ∀ g g' : ℝ → ℝ, (∀ t ∈ Set.Icc 0 R, HasDerivAt g (g' t) t) →
      (∀ t ∈ Set.Icc 0 R, 0 ≤ g' t) → ∀ z ∈ Set.Icc 0 R, g 0 ≤ g z := by
    intro g g' hg hg' z hz
    have hR : (0 : ℝ) ≤ R := hz.1.trans hz.2
    have hmono : MonotoneOn g (Set.Icc 0 R) := by
      refine monotoneOn_of_hasDerivWithinAt_nonneg (f := g) (f' := g') (convex_Icc 0 R) ?_ ?_ ?_
      · intro t ht
        exact (hg t ht).continuousAt.continuousWithinAt
      · intro x hx
        exact (hg x (interior_subset hx)).hasDerivWithinAt
      · intro x hx
        exact hg' x (interior_subset hx)
    exact hmono ⟨le_rfl, hR⟩ hz hz.1
  intro z hz
  have h1 := key (fun t => P t - h t) (fun t => p t - h' t)
    (fun t ht => (hP t).sub (hh t ht))
    (fun t ht => by linarith [le_abs_self (h' t), hb t ht]) z hz
  have h2 := key (fun t => P t + h t) (fun t => p t + h' t)
    (fun t ht => (hP t).add (hh t ht))
    (fun t ht => by linarith [neg_abs_le (h' t), hb t ht]) z hz
  simp only [h0, P0] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-- Symmetric comparison. If `h` has derivative `h'` on `[-R, R]`, `|h' t| ≤ p |t|` there,
`h 0 = 0`, and `P` has derivative `p` everywhere with `P 0 = 0`, then `|h z| ≤ P |z|` on
`[-R, R]`. -/
lemma sym_FIN06825 {R : ℝ} {h h' p P : ℝ → ℝ}
    (hh : ∀ t ∈ Set.Icc (-R) R, HasDerivAt h (h' t) t)
    (hP : ∀ t, HasDerivAt P (p t) t)
    (hb : ∀ t ∈ Set.Icc (-R) R, |h' t| ≤ p |t|) (h0 : h 0 = 0) (P0 : P 0 = 0) :
    ∀ z ∈ Set.Icc (-R) R, |h z| ≤ P |z| := by
  intro z hz
  rcases le_total 0 z with hz0 | hz0
  · rw [abs_of_nonneg hz0]
    refine pos_FIN06825 (R := R) (h := h) (h' := h') (p := p) (P := P) ?_ hP ?_ h0 P0 z
      ⟨hz0, hz.2⟩
    · intro t ht
      exact hh t ⟨by linarith [ht.1, ht.2], ht.2⟩
    · intro t ht
      have h3 := hb t ⟨by linarith [ht.1, ht.2], ht.2⟩
      rwa [abs_of_nonneg ht.1] at h3
  · rw [abs_of_nonpos hz0]
    have hneg := pos_FIN06825 (R := R) (h := fun t => h (-t)) (h' := fun t => h' (-t) * -1)
      (p := p) (P := P)
      (fun t ht => (hh (-t) ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩).comp t
        (hasDerivAt_neg t))
      hP
      (fun t ht => by
        have h3 := hb (-t) ⟨by linarith [ht.1, ht.2], by linarith [ht.1, ht.2]⟩
        rw [abs_neg, abs_of_nonneg ht.1] at h3
        rw [abs_mul, abs_neg, abs_one, mul_one]
        exact h3)
      (by simp [h0]) P0 (-z) ⟨by linarith [hz0], by linarith [hz.1]⟩
    simpa only [neg_neg] using hneg

/-- Three scalar Taylor bounds for `q`. For `q` that is `C^∞` on an open set `U` containing the
closed symmetric interval `[-δ, δ]`, with `|q'''| ≤ M` on that interval, `q'(0) = 0` and
`q''(0) = -2 c₄`, every `z` in `[-δ, δ]` satisfies the three bounds. -/
theorem fin068_25_three_scalar_taylor_bounds_q (q : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (δ c₄ M : ℝ) (hsub : Set.Icc (-δ) δ ⊆ U) (hq : ContDiffOn ℝ ∞ q U) (_hM0 : 0 ≤ M)
    (hM : ∀ t ∈ Set.Icc (-δ) δ, |deriv (deriv (deriv q)) t| ≤ M)
    (hq1 : deriv q 0 = 0) (hq2 : deriv (deriv q) 0 = -2 * c₄) :
    ∀ z ∈ Set.Icc (-δ) δ,
      |q z - q 0 + c₄ * z ^ 2| ≤ M * |z| ^ 3 / 6 ∧
      |deriv q z + 2 * c₄ * z| ≤ M * z ^ 2 / 2 ∧
      |deriv (deriv q) z + 2 * c₄| ≤ M * |z| := by
  have hq3 : ContDiffOn ℝ 3 q U := hq.of_le (by norm_num)
  have hf1 : ContDiffOn ℝ 2 (deriv q) U := hq3.deriv_of_isOpen hU (by norm_num)
  have hf2 : ContDiffOn ℝ 1 (deriv (deriv q)) U := hf1.deriv_of_isOpen hU (by norm_num)
  have hdq : ∀ t ∈ U, DifferentiableAt ℝ q t := fun t ht =>
    (hq3.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)
  have hdq' : ∀ t ∈ U, DifferentiableAt ℝ (deriv q) t := fun t ht =>
    (hf1.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)
  have hdq'' : ∀ t ∈ U, DifferentiableAt ℝ (deriv (deriv q)) t := fun t ht =>
    (hf2.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds ht)
  -- the second bound's ingredient: `q''` is `M`-Lipschitz on the interval, `q''(0) = -2c₄`
  have hlip : ∀ z ∈ Set.Icc (-δ) δ, |deriv (deriv q) z + 2 * c₄| ≤ M * |z| := by
    intro z hz
    have h0mem : (0 : ℝ) ∈ Set.Icc (-δ) δ :=
      ⟨by linarith [hz.1, hz.2], by linarith [hz.1, hz.2]⟩
    have key := Convex.norm_image_sub_le_of_norm_deriv_le (f := deriv (deriv q))
      (s := Set.Icc (-δ) δ) (C := M) (fun t ht => hdq'' t (hsub ht))
      (fun t ht => by rw [Real.norm_eq_abs]; exact hM t ht) (convex_Icc _ _) h0mem hz
    rw [hq2] at key
    simp only [Real.norm_eq_abs, sub_zero] at key
    have e : deriv (deriv q) z + 2 * c₄ = deriv (deriv q) z - -2 * c₄ := by ring
    rw [e]
    exact key
  -- the first derivative: `h₂ = q' + 2c₄ id`, `h₂(0) = 0`, `|h₂'| ≤ M|t|`
  have hgrad : ∀ z ∈ Set.Icc (-δ) δ, |deriv q z + 2 * c₄ * z| ≤ M * z ^ 2 / 2 := by
    have hs := sym_FIN06825 (R := δ) (h := fun t => deriv q t + 2 * c₄ * t)
      (h' := fun t => deriv (deriv q) t + 2 * c₄) (p := fun t => M * t)
      (P := fun t => M * t ^ 2 / 2)
      (fun t ht => by
        have h1 := (hdq' t (hsub ht)).hasDerivAt.add ((hasDerivAt_id' t).const_mul (2 * c₄))
        exact h1.congr_deriv (by ring))
      (fun t => by
        have h1 := ((hasDerivAt_pow 2 t).const_mul M).div_const 2
        exact h1.congr_deriv (by norm_num; ring))
      (fun s hs => hlip s hs)
      (by simp [hq1]) (by simp)
    intro z hz
    have h4 := hs z hz
    rw [sq_abs] at h4
    exact h4
  -- the value: `h₃ = q - q(0) + c₄ id²`, `h₃(0) = 0`, `h₃' = h₂`
  have hval : ∀ z ∈ Set.Icc (-δ) δ, |q z - q 0 + c₄ * z ^ 2| ≤ M * |z| ^ 3 / 6 := by
    have hs := sym_FIN06825 (R := δ) (h := fun t => q t - q 0 + c₄ * t ^ 2)
      (h' := fun t => deriv q t + 2 * c₄ * t) (p := fun t => M * t ^ 2 / 2)
      (P := fun t => M * t ^ 3 / 6)
      (fun t ht => by
        have h1 := ((hdq t (hsub ht)).hasDerivAt.sub_const (q 0)).add
          ((hasDerivAt_pow 2 t).const_mul c₄)
        exact h1.congr_deriv (by norm_num; ring))
      (fun t => by
        have h1 := ((hasDerivAt_pow 3 t).const_mul M).div_const 6
        exact h1.congr_deriv (by norm_num; ring))
      (fun s hs => by
        show |deriv q s + 2 * c₄ * s| ≤ M * |s| ^ 2 / 2
        rw [sq_abs]
        exact hgrad s hs)
      (by simp) (by simp)
    intro z hz
    exact hs z hz
  intro z hz
  exact ⟨hval z hz, hgrad z hz, hlip z hz⟩

end DGPS.Frontier.FIN068
