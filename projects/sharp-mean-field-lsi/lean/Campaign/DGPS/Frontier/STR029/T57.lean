import DGPS.Frontier.STR029.T09
import DGPS.Frontier.STR029.T17
import DGPS.Frontier.STR029.T18

/-!
# STR029.57: Weighted fourth jet of the reduced functional

Task id: STR029.57 (node STR029). Title: Weighted fourth jet of the reduced functional.
Prerequisites: STR029.09 (`Jzero_STR02909`, `J4_STR02909` and the fourth-order coefficient bound),
STR029.17 (`str029_17_assemble_independent_second_range_jet`, the graph and the scaled range jet),
STR029.18 (`Jred_STR02918` and the starred coefficients `Cstar_STR02918`, `Dstar_STR02918`,
`Estar_STR02918`, `Fstar_STR02918`).

Statement formalized. Assign weight one to `a, b, h` and weight two to `γ`. Let `ψ` be the graph of
STR029.17 and let `F(a, b, h, γ) = Jchart h γ (a cos t + b sin t + ψ(a, b, h, γ))`. For every compact
set `K` of triples `(A, B, s)` there are `δ > 0` and `M ≥ 0` such that, for `(A, B, s) ∈ K` and
`|h| ≤ δ`, the scaled point `(hA, hB, h, h²s)` lies in `U`, and `F(hA, hB, h, h²s)` differs from the
weight-four polynomial `poly19` of STR029.19 by at most `M |h|⁵`.

Provides (every declaration is in the namespace `DGPS.Frontier.STR029`):

* `DGPS.Frontier.STR029.str029_57_weighted_fourth_jet_reduced_functional`: the main statement. It
  gives open sets `U ∋ 0` and `V ∋ 0`, the graph `ψ`, and the uniform scaled bound stated above.

Supporting declarations (all carry the suffix `_STR02957`):

* `meanT_sub_le_STR02957`, `meanT_abs_le_STR02957`, `meanT_ge_STR02957`: the normalized mean is
  controlled by the sup norm of a difference, by the sup norm of a function, and from below.
* `log_sub_le_STR02957`, `log_lip_STR02957`, `exp_lip_STR02957`: elementary Lipschitz bounds for
  `log` on `[c, ∞)` and for `exp` on `(-∞, M]`.
* `meanT_div_STR02957`: the normalized mean commutes with division by a constant.
* `entropy_split_STR02957`: the entropy chart written through normalized means.
* `ratio_bound_STR02957`, `entropy_combine_STR02957`: quotient and combined perturbation bounds.
* `entropy_lip_STR02957`: for each sup bound `L`, the entropy chart is Lipschitz in the sup norm on
  functions bounded by `L`, uniformly for `|h| ≤ 1`.
* `vE_STR02957`: the underlying periodic function of an element of the carrier `E`.
* `vE_isC2_STR02957`, `vE_mean_STR02957`, `vE_c2Norm_STR02957`, `vE_sup_STR02957`: its
  `C^{2,1/2}` membership, zero mean, norm identity, and sup bound by `‖x‖`.
* `vE_sub_apply_STR02957`, `vE_smul_apply_STR02957`: the underlying function of a difference and of
  a scalar multiple.
* `coef_bound_STR02957`: the starred coefficients are bounded by `C + C²` when `|A|, |B| ≤ C`.
* `abs_pFun_STR02957`, `abs_qFun_STR02957`, `uFun_bound_STR02957`: sup bounds for the trigonometric
  jets `p`, `q` and for `u = h p + h² q` with `|h| ≤ 1`.
* `qstar_apply_STR02957`: the periodic function of `q_*(A, B) ∈ E` is the trigonometric jet with
  the starred coefficients.
* `poly19_STR02957`: the weight-four polynomial of STR029.19 in `(a, b, h, γ)`.
* `poly19_scaled_STR02957`: on the scaled ray it equals `h⁴ (J_4^red - s (A² + B²) / 2)`.
* `jchart_gamma_STR02957`: the `γ`-dependence of `Jchart` is `-2γ` times the entropy chart.
* `relE_STR02957`: the order-three remainder `h⁻³ (ψ(hA, hB, h, h²s) - h² q_*)` for `|h| ≤ δ`,
  and `0` otherwise.
* `relE_eq_STR02957`, `relE_norm_STR02957`: `h³ • relE` is the remainder of `ψ`, and `relE` is
  bounded by `M` for every `h`.
* `psi_val_STR02957`: the periodic function of `ψ(hA, hB, h, h²s)` is `h²` times the starred jet
  plus `h³` times the periodic function of `relE`.

R5 notes:

1. Weights. Weight one for `a, b, h` and weight two for `γ` organize the monomials of the
   expansion. The statement uses the substitution `γ = h² s`, that is `s = γ / h²`.
2. Non-literal reading of "the Taylor polynomial through weight four is exactly the polynomial of
   STR029.19". The proved statement is that the difference `F(hA, hB, h, h²s) - poly19(...)` is at
   most `M |h|⁵` uniformly for `(A, B, s)` in a compact set and `|h| ≤ δ`. This is the weight-five
   remainder on the scaled ray. No formal power series is constructed. The exact coefficient
   identity through weight four is `poly19_scaled_STR02957` together with the quartic identity
   `Jred_eq_STR02918` of STR029.18.
3. The polynomial. `poly19_STR02957` is the displayed polynomial of STR029.19,
   `-γR₀²/2 - 9h²R₀²/20 - h(a³ - 3ab²)/12 + R₀⁴/48` with `R₀ = √(a² + b²)`. No Lean file for
   STR029.19 is in the worktree, so the polynomial is transcribed from the node text. The
   remainder `ℰ` of STR029.19 is not part of this unit.
4. Graph. `ψ`, `U`, `V` and the graph conjuncts (open sets, `ContDiffOn ℝ ∞`, `ψ 0 = 0`, the
   solution equivalence) are those of STR029.17, taken over unchanged. The uniqueness conjunct
   `Rpar_STR02916 p w = 0 ↔ w = ψ p` is carried through but not used in the proof. No hypothesis
   is added.
5. Chart functional. `F` is read as `Jchart_STR02950 h γ` (STR029.50) applied to the periodic
   function `a cos t + b sin t + vE(ψ)`, where `vE` is the underlying function of the carrier
   element (STR029.69). `Jchart` is the fisher chart minus `2(1 + γ)` times the entropy chart,
   matching the node's `J = I - 2(1 + γ) H`. No other chart, density domain or normalization is
   restated.
6. Cutoff. The order-three remainder is set to `0` for `|h| > δ`, so that `relE` is defined and
   bounded by `M` for every `h`. This is the uniform form needed to apply STR029.09. The claimed
   estimate is only for `|h| ≤ δ`.
7. Uniformity. "Uniformly for `(A, B, s)` in compact sets" is read as `K : Set (ℝ × ℝ × ℝ)` with
   `IsCompact K`, coordinates ordered `(A, B, s)`. The constants `δ` and `M` do not depend on the
   point of `K`. The bound `C0` on `|A|, |B|, |s|` over `K` comes from compactness, and the
   STR029.09 radius is `C0 + C0² + M17 + 1`.
8. Norm. `‖·‖_E` is the norm of STR029.69. Only its sup bound and its norm identity are used.
9. Angular normalization. The angular variable carries the normalized measure `dt/(2π)`
   (`meanT_STR02901`). No rescaling by `a₀ = 4π²` enters.
10. Unused prerequisite. STR029.56 is listed in the brief but is not imported. The estimate uses
    the STR029.09 bounds and the entropy Lipschitz bound, and does not use the amplitude factor.
-/

open scoped ContDiff
open DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-! ### Mean and logarithm estimates -/

theorem meanT_sub_le_STR02957 (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (M : ℝ)
    (h : ∀ t, |f t - g t| ≤ M) : |meanT_STR02901 f - meanT_STR02901 g| ≤ M := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hI : ∫ t in (0:ℝ)..(2 * Real.pi), (f t - g t) =
      (∫ t in (0:ℝ)..(2 * Real.pi), f t) - ∫ t in (0:ℝ)..(2 * Real.pi), g t :=
    intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
  have hb : ‖∫ t in (0:ℝ)..(2 * Real.pi), (f t - g t)‖ ≤ M * |2 * Real.pi - 0| :=
    intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => by
      rw [Real.norm_eq_abs]; exact h t
  rw [Real.norm_eq_abs, sub_zero, abs_of_pos hpi] at hb
  unfold meanT_STR02901
  rw [← mul_sub, ← hI, abs_mul, abs_of_pos (inv_pos.2 hpi)]
  calc (2 * Real.pi)⁻¹ * |∫ t in (0:ℝ)..(2 * Real.pi), (f t - g t)|
      ≤ (2 * Real.pi)⁻¹ * (M * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hb (inv_nonneg.2 hpi.le)
    _ = M := by rw [mul_comm M, ← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]

theorem meanT_abs_le_STR02957 (f : ℝ → ℝ) (hf : Continuous f) (M : ℝ)
    (h : ∀ t, |f t| ≤ M) : |meanT_STR02901 f| ≤ M := by
  have h0 : meanT_STR02901 (fun _ => (0:ℝ)) = 0 := by simp [meanT_STR02901]
  have := meanT_sub_le_STR02957 f (fun _ => 0) hf continuous_const M
    (fun t => by simpa using h t)
  rw [h0, sub_zero] at this
  exact this

theorem meanT_ge_STR02957 (f : ℝ → ℝ) (hf : Continuous f) (c : ℝ) (h : ∀ t, c ≤ f t) :
    c ≤ meanT_STR02901 f := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hnn : 0 ≤ ∫ t in (0:ℝ)..(2 * Real.pi), (f t - c) :=
    intervalIntegral.integral_nonneg hpi.le fun t _ => by linarith [h t]
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _)] at hnn
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hnn
  have h1 : 2 * Real.pi * c ≤ ∫ t in (0:ℝ)..(2 * Real.pi), f t := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hpi.le)
  unfold meanT_STR02901
  rw [← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul] at h2
  exact h2

theorem log_sub_le_STR02957 {c x y : ℝ} (hc : 0 < c) (hy : c ≤ y) (hxy : y ≤ x) :
    Real.log x - Real.log y ≤ (x - y) / c := by
  have hy0 : 0 < y := lt_of_lt_of_le hc hy
  have hx0 : 0 < x := lt_of_lt_of_le hy0 hxy
  have h1 : Real.log (x / y) ≤ x / y - 1 := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
  rw [Real.log_div hx0.ne' hy0.ne', div_sub_one hy0.ne'] at h1
  have h2 : (x - y) / y ≤ (x - y) / c := div_le_div_of_nonneg_left (sub_nonneg.2 hxy) hc hy
  linarith

theorem log_lip_STR02957 {c x y : ℝ} (hc : 0 < c) (hx : c ≤ x) (hy : c ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| / c := by
  rcases le_total y x with h | h
  · have h1 := log_sub_le_STR02957 hc hy h
    have h2 : Real.log y ≤ Real.log x := Real.log_le_log (lt_of_lt_of_le hc hy) h
    rw [abs_of_nonneg (sub_nonneg.2 h2), abs_of_nonneg (sub_nonneg.2 h)]
    exact h1
  · have h1 := log_sub_le_STR02957 hc hx h
    have h2 : Real.log x ≤ Real.log y := Real.log_le_log (lt_of_lt_of_le hc hx) h
    rw [abs_sub_comm (Real.log x), abs_sub_comm x, abs_of_nonneg (sub_nonneg.2 h2),
      abs_of_nonneg (sub_nonneg.2 h)]
    exact h1

theorem exp_lip_STR02957 {x y M : ℝ} (hx : x ≤ M) (hy : y ≤ M) :
    |Real.exp x - Real.exp y| ≤ Real.exp M * |x - y| := by
  have key : ∀ a b : ℝ, a ≤ b → b ≤ M → Real.exp b - Real.exp a ≤ Real.exp M * (b - a) := by
    intro a b hab hb
    have e1 := Real.add_one_le_exp (a - b)
    have e2 : Real.exp b * Real.exp (a - b) = Real.exp a := by
      rw [← Real.exp_add]; ring_nf
    have e3 : Real.exp b ≤ Real.exp M := Real.exp_le_exp.2 hb
    have e4 := mul_le_mul_of_nonneg_left e1 (Real.exp_pos b).le
    have e5 := mul_le_mul_of_nonneg_right e3 (sub_nonneg.2 hab)
    nlinarith
  have hM := Real.exp_pos M
  rcases le_total x y with h | h
  · have k := key x y h hy
    have hm : y - x ≤ |x - y| := by rw [abs_sub_comm]; exact le_abs_self _
    have hE := mul_le_mul_of_nonneg_left hm hM.le
    have hx' := Real.exp_le_exp.2 h
    have hnn := mul_nonneg hM.le (abs_nonneg (x - y))
    rw [abs_le]; constructor <;> linarith
  · have k := key y x h hx
    have hm : x - y ≤ |x - y| := le_abs_self _
    have hE := mul_le_mul_of_nonneg_left hm hM.le
    have hy' := Real.exp_le_exp.2 h
    have hnn := mul_nonneg hM.le (abs_nonneg (x - y))
    rw [abs_le]; constructor <;> linarith

/-! ### The entropy of the chart -/

theorem meanT_div_STR02957 (g : ℝ → ℝ) (c : ℝ) :
    meanT_STR02901 (fun t => g t / c) = meanT_STR02901 g / c := by
  unfold meanT_STR02901
  rw [intervalIntegral.integral_div]
  ring

theorem entropy_split_STR02957 (h : ℝ) (u : ℝ → ℝ) :
    entropyChart_STR02949 h u =
      meanT_STR02901 (fun t => u t * Real.exp (h * Real.cos (3 * t) + u t)) /
          meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s)) -
        Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s))) +
        Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s)))) := by
  unfold entropyChart_STR02949 rhoT_STR02901
  have hfun : (fun t => u t * (Real.exp (h * Real.cos (3 * t) + u t) /
      meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s)))) =
      fun t => (u t * Real.exp (h * Real.cos (3 * t) + u t)) /
        meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u s)) := by
    funext t; ring
  rw [hfun, meanT_div_STR02957]

theorem ratio_bound_STR02957 {Pu Pv Nu Nv c α Q β : ℝ} (hc : 0 < c) (hNu : c ≤ Nu)
    (hNv : c ≤ Nv) (hP : |Pu - Pv| ≤ α) (hQ : |Pv| ≤ Q) (hN : |Nu - Nv| ≤ β) :
    |Pu / Nu - Pv / Nv| ≤ α / c + Q * β / (c * c) := by
  have hNu0 : 0 < Nu := lt_of_lt_of_le hc hNu
  have hNv0 : 0 < Nv := lt_of_lt_of_le hc hNv
  have hQ0 : 0 ≤ Q := (abs_nonneg _).trans hQ
  have hβ : 0 ≤ β := (abs_nonneg _).trans hN
  have hcc : 0 < c * c := mul_pos hc hc
  have hcc' : c * c ≤ Nu * Nv := mul_le_mul hNu hNv hc.le hNu0.le
  have key : Pu / Nu - Pv / Nv = (Pu - Pv) / Nu + Pv * (Nv - Nu) / (Nu * Nv) := by
    field_simp
    ring
  rw [key]
  refine (abs_add_le _ _).trans ?_
  have t1 : |(Pu - Pv) / Nu| ≤ α / c := by
    rw [abs_div, abs_of_pos hNu0]
    exact (div_le_div_of_nonneg_left (abs_nonneg _) hc hNu).trans
      (div_le_div_of_nonneg_right hP hc.le)
  have t2 : |Pv * (Nv - Nu) / (Nu * Nv)| ≤ Q * β / (c * c) := by
    rw [abs_div, abs_mul, abs_of_pos (mul_pos hNu0 hNv0), abs_sub_comm Nv Nu]
    have hnum : |Pv| * |Nu - Nv| ≤ Q * β :=
      mul_le_mul hQ hN (abs_nonneg _) hQ0
    exact (div_le_div_of_nonneg_right hnum (mul_pos hNu0 hNv0).le).trans
      (div_le_div_of_nonneg_left (mul_nonneg hQ0 hβ) hcc hcc')
  linarith

theorem entropy_combine_STR02957 {Pu Pv Nu Nv Z c α Q β : ℝ} (hc : 0 < c) (hNu : c ≤ Nu)
    (hNv : c ≤ Nv) (hP : |Pu - Pv| ≤ α) (hQ : |Pv| ≤ Q) (hN : |Nu - Nv| ≤ β) :
    |(Pu / Nu - Real.log Nu + Z) - (Pv / Nv - Real.log Nv + Z)| ≤
      α / c + Q * β / (c * c) + β / c := by
  have hrat := ratio_bound_STR02957 hc hNu hNv hP hQ hN
  have hlog := log_lip_STR02957 hc hNu hNv
  have hlog' : |Real.log Nu - Real.log Nv| ≤ β / c :=
    hlog.trans (div_le_div_of_nonneg_right hN hc.le)
  have key : (Pu / Nu - Real.log Nu + Z) - (Pv / Nv - Real.log Nv + Z) =
      (Pu / Nu - Pv / Nv) - (Real.log Nu - Real.log Nv) := by ring
  rw [key]
  have h3 := abs_add_le (Pu / Nu - Pv / Nv) (-(Real.log Nu - Real.log Nv))
  rw [abs_neg, ← sub_eq_add_neg] at h3
  linarith

/-- Pointwise Lipschitz bound for the entropy of the chart on sup-bounded continuous
functions, with the constant depending only on the sup bound `L`. -/
theorem entropy_lip_STR02957 (L : ℝ) (hL : 0 ≤ L) :
    ∃ Lc : ℝ, 0 ≤ Lc ∧ ∀ (h ε : ℝ) (u v : ℝ → ℝ), |h| ≤ 1 → Continuous u → Continuous v →
      (∀ t, |u t| ≤ L) → (∀ t, |v t| ≤ L) → (∀ t, |u t - v t| ≤ ε) →
      |entropyChart_STR02949 h u - entropyChart_STR02949 h v| ≤ Lc * ε := by
  have hE1 : (0:ℝ) < Real.exp (1 + L) := Real.exp_pos _
  have hc0 : (0:ℝ) < Real.exp (-(1 + L)) := Real.exp_pos _
  refine ⟨(L + 2) * Real.exp (1 + L) / Real.exp (-(1 + L)) +
      L * Real.exp (1 + L) ^ 2 / (Real.exp (-(1 + L)) * Real.exp (-(1 + L))), ?_, ?_⟩
  · have h1 : 0 ≤ (L + 2) * Real.exp (1 + L) / Real.exp (-(1 + L)) :=
      div_nonneg (mul_nonneg (by linarith) hE1.le) hc0.le
    have h2 : 0 ≤ L * Real.exp (1 + L) ^ 2 / (Real.exp (-(1 + L)) * Real.exp (-(1 + L))) :=
      div_nonneg (mul_nonneg hL (sq_nonneg _)) (mul_pos hc0 hc0).le
    linarith
  intro h ε u v hh hu hv hBu hBv hdiff
  have hcosb : ∀ t : ℝ, |h * Real.cos (3 * t)| ≤ 1 := fun t => by
    rw [abs_mul]
    exact (mul_le_mul hh (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one).trans (by norm_num)
  have hx_le : ∀ (w : ℝ → ℝ), (∀ t, |w t| ≤ L) → ∀ t, h * Real.cos (3 * t) + w t ≤ 1 + L := by
    intro w hw t
    have := (abs_le.1 (hcosb t)).2
    have := (abs_le.1 (hw t)).2
    linarith
  have hx_ge : ∀ (w : ℝ → ℝ), (∀ t, |w t| ≤ L) → ∀ t, -(1 + L) ≤ h * Real.cos (3 * t) + w t := by
    intro w hw t
    have := (abs_le.1 (hcosb t)).1
    have := (abs_le.1 (hw t)).1
    linarith
  have hexp_le : ∀ (w : ℝ → ℝ), (∀ t, |w t| ≤ L) → ∀ t,
      Real.exp (h * Real.cos (3 * t) + w t) ≤ Real.exp (1 + L) :=
    fun w hw t => Real.exp_le_exp.2 (hx_le w hw t)
  have hexp_ge : ∀ (w : ℝ → ℝ), (∀ t, |w t| ≤ L) → ∀ t,
      Real.exp (-(1 + L)) ≤ Real.exp (h * Real.cos (3 * t) + w t) :=
    fun w hw t => Real.exp_le_exp.2 (hx_ge w hw t)
  have hNu_c : Continuous (fun s => Real.exp (h * Real.cos (3 * s) + u s)) := by fun_prop
  have hNv_c : Continuous (fun s => Real.exp (h * Real.cos (3 * s) + v s)) := by fun_prop
  have hPu_c : Continuous (fun t => u t * Real.exp (h * Real.cos (3 * t) + u t)) := by fun_prop
  have hPv_c : Continuous (fun t => v t * Real.exp (h * Real.cos (3 * t) + v t)) := by fun_prop
  have hdiff_exp : ∀ t, |Real.exp (h * Real.cos (3 * t) + u t) -
      Real.exp (h * Real.cos (3 * t) + v t)| ≤ Real.exp (1 + L) * ε := by
    intro t
    have h1 := exp_lip_STR02957 (hx_le u hBu t) (hx_le v hBv t)
    have h2 : |h * Real.cos (3 * t) + u t - (h * Real.cos (3 * t) + v t)| ≤ ε := by
      have : h * Real.cos (3 * t) + u t - (h * Real.cos (3 * t) + v t) = u t - v t := by ring
      rw [this]; exact hdiff t
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hE1.le)
  have hdiff_P : ∀ t, |u t * Real.exp (h * Real.cos (3 * t) + u t) -
      v t * Real.exp (h * Real.cos (3 * t) + v t)| ≤
      L * (Real.exp (1 + L) * ε) + ε * Real.exp (1 + L) := by
    intro t
    have hsplit : u t * Real.exp (h * Real.cos (3 * t) + u t) -
        v t * Real.exp (h * Real.cos (3 * t) + v t) =
        u t * (Real.exp (h * Real.cos (3 * t) + u t) - Real.exp (h * Real.cos (3 * t) + v t)) +
        (u t - v t) * Real.exp (h * Real.cos (3 * t) + v t) := by ring
    rw [hsplit]
    have ε0 : 0 ≤ ε := (abs_nonneg _).trans (hdiff t)
    have e1 : |u t * (Real.exp (h * Real.cos (3 * t) + u t) -
        Real.exp (h * Real.cos (3 * t) + v t))| ≤ L * (Real.exp (1 + L) * ε) := by
      rw [abs_mul]
      exact mul_le_mul (hBu t) (hdiff_exp t) (abs_nonneg _) hL
    have e2 : |(u t - v t) * Real.exp (h * Real.cos (3 * t) + v t)| ≤ ε * Real.exp (1 + L) := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul (hdiff t) (hexp_le v hBv t) (Real.exp_pos _).le ε0
    exact (abs_add_le _ _).trans (add_le_add e1 e2)
  have hN_diff := meanT_sub_le_STR02957 _ _ hNu_c hNv_c _ hdiff_exp
  have hP_diff := meanT_sub_le_STR02957 _ _ hPu_c hPv_c _ hdiff_P
  have hQ : |meanT_STR02901 (fun t => v t * Real.exp (h * Real.cos (3 * t) + v t))| ≤
      L * Real.exp (1 + L) := by
    apply meanT_abs_le_STR02957 _ hPv_c
    intro t
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (hBv t) (hexp_le v hBv t) (Real.exp_pos _).le hL
  have hNu_lb := meanT_ge_STR02957 _ hNu_c _ (hexp_ge u hBu)
  have hNv_lb := meanT_ge_STR02957 _ hNv_c _ (hexp_ge v hBv)
  rw [entropy_split_STR02957 h u, entropy_split_STR02957 h v]
  refine (entropy_combine_STR02957 hc0 hNu_lb hNv_lb hP_diff hQ hN_diff).trans (le_of_eq ?_)
  ring

/-! ### The carrier `E` as functions -/

/-- The underlying `2π`-periodic function of an element of the carrier `E`. -/
noncomputable def vE_STR02957 (x : E_STR02969) : ℝ → ℝ := PeriodicC2_STR02969.val x.1

theorem vE_isC2_STR02957 (x : E_STR02969) : IsC2Alpha_STR02901 (1 / 2) (vE_STR02957 x) :=
  PeriodicC2_STR02969.isC2 x.1

theorem vE_mean_STR02957 (x : E_STR02969) : meanT_STR02901 (vE_STR02957 x) = 0 :=
  ((str029_69_completeness_closed_complements_range_spaces_E.1 x.1).1 x.2).1

theorem vE_c2Norm_STR02957 (x : E_STR02969) :
    c2Norm_STR02901 (1 / 2) (vE_STR02957 x) = ‖x‖ :=
  rfl

theorem vE_sup_STR02957 (x : E_STR02969) (t : ℝ) : |vE_STR02957 x t| ≤ ‖x‖ := by
  have h1 := Bdd.abs_le_supNorm (bdd_parts_STR02969 (vE_isC2_STR02957 x)).1 t
  have h2 := (le_c2Norm_STR02969 (vE_STR02957 x)).1
  rw [← vE_c2Norm_STR02957 x]
  linarith

theorem vE_sub_apply_STR02957 (x y : E_STR02969) (t : ℝ) :
    vE_STR02957 (x - y) t = vE_STR02957 x t - vE_STR02957 y t :=
  rfl

theorem vE_smul_apply_STR02957 (c : ℝ) (x : E_STR02969) (t : ℝ) :
    vE_STR02957 (c • x) t = c * vE_STR02957 x t :=
  rfl

/-! ### Elementary coefficient and trigonometric bounds -/

theorem coef_bound_STR02957 {A B C : ℝ} (hA : |A| ≤ C) (hB : |B| ≤ C) (hC : 0 ≤ C) :
    |Cstar_STR02918 A B| ≤ C + C ^ 2 ∧ |Dstar_STR02918 A B| ≤ C + C ^ 2 ∧
      |Estar_STR02918 A| ≤ C + C ^ 2 ∧ |Fstar_STR02918 B| ≤ C + C ^ 2 := by
  have hA' := abs_le.1 hA
  have hB' := abs_le.1 hB
  have hA2 : A ^ 2 ≤ C ^ 2 := sq_le_sq' hA'.1 hA'.2
  have hB2 : B ^ 2 ≤ C ^ 2 := sq_le_sq' hB'.1 hB'.2
  have hAB : |A * B| ≤ C ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul hA hB (abs_nonneg _) hC
  have hAB' := abs_le.1 hAB
  have hA2' : 0 ≤ A ^ 2 := sq_nonneg A
  have hB2' : 0 ≤ B ^ 2 := sq_nonneg B
  have hC2 : 0 ≤ C ^ 2 := sq_nonneg C
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold Cstar_STR02918
    rw [abs_le]
    constructor <;> linarith [hA'.1, hA'.2]
  · unfold Dstar_STR02918
    rw [abs_le]
    constructor <;> linarith [hB'.1, hB'.2, hAB'.1, hAB'.2]
  · unfold Estar_STR02918
    rw [abs_le]
    constructor <;> linarith [hA'.1, hA'.2]
  · unfold Fstar_STR02918
    rw [abs_le]
    constructor <;> linarith [hB'.1, hB'.2]

theorem abs_pFun_STR02957 (A B t : ℝ) : |pFun_STR02945 A B t| ≤ |A| + |B| := by
  unfold pFun_STR02945
  have h1 : |A * Real.cos t| ≤ |A| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one t)
  have h2 : |B * Real.sin t| ≤ |B| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one t)
  exact (abs_add_le _ _).trans (add_le_add h1 h2)

theorem abs_qFun_STR02957 (C D E F t : ℝ) :
    |qFun_STR02945 C D E F t| ≤ |C| + |D| + |E| + |F| := by
  unfold qFun_STR02945
  have h1 : |C * Real.cos (2 * t)| ≤ |C| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h2 : |D * Real.sin (2 * t)| ≤ |D| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have h3 : |E * Real.cos (4 * t)| ≤ |E| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  have h4 : |F * Real.sin (4 * t)| ≤ |F| := by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have e1 := abs_add_le (C * Real.cos (2 * t)) (D * Real.sin (2 * t))
  have e2 := abs_add_le (C * Real.cos (2 * t) + D * Real.sin (2 * t)) (E * Real.cos (4 * t))
  have e3 := abs_add_le (C * Real.cos (2 * t) + D * Real.sin (2 * t) + E * Real.cos (4 * t))
    (F * Real.sin (4 * t))
  linarith

theorem uFun_bound_STR02957 (A B C D E F h t : ℝ) (hh : |h| ≤ 1) :
    |uFun_STR02945 A B C D E F h t| ≤ (|A| + |B|) + (|C| + |D| + |E| + |F|) := by
  have hp := abs_pFun_STR02957 A B t
  have hq := abs_qFun_STR02957 C D E F t
  have hh2 : |h ^ 2| ≤ 1 := by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hh
  have e1 : |h * pFun_STR02945 A B t| ≤ |pFun_STR02945 A B t| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hh
  have e2 : |h ^ 2 * qFun_STR02945 C D E F t| ≤ |qFun_STR02945 C D E F t| := by
    rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hh2
  have e3 := abs_add_le (h * pFun_STR02945 A B t) (h ^ 2 * qFun_STR02945 C D E F t)
  unfold uFun_STR02945
  linarith

theorem qstar_apply_STR02957 (A B t : ℝ) :
    vE_STR02957 (qstar_STR02917 A B) t =
      qFun_STR02945 (Cstar_STR02918 A B) (Dstar_STR02918 A B) (Estar_STR02918 A)
        (Fstar_STR02918 B) t := by
  unfold qFun_STR02945
  rw [show vE_STR02957 (qstar_STR02917 A B) t = qstarFn_STR02917 A B t from rfl,
    qstarFn_fourier_STR02918]

/-! ### The weight-four polynomial of STR029.19 -/

/-- The weight-four polynomial of STR029.19 in `(a, b, h, γ)`. -/
noncomputable def poly19_STR02957 (a b h γ : ℝ) : ℝ :=
  -(γ * R0_STR02918 a b ^ 2 / 2) - 9 * h ^ 2 * R0_STR02918 a b ^ 2 / 20 -
    h * (a ^ 3 - 3 * a * b ^ 2) / 12 + R0_STR02918 a b ^ 4 / 48

/-- On the scaled ray `(hA, hB, h, h²s)` the polynomial equals `h⁴ (J_4^red - s(A² + B²)/2)`. -/
theorem poly19_scaled_STR02957 (A B s h : ℝ) :
    poly19_STR02957 (h * A) (h * B) h (h ^ 2 * s) =
      h ^ 4 * Jred_STR02918 A B - 2 * (h ^ 2 * s) * (h ^ 2 * ((A ^ 2 + B ^ 2) / 4)) := by
  have hR2 : R0_STR02918 (h * A) (h * B) ^ 2 = h ^ 2 * (A ^ 2 + B ^ 2) := by
    rw [R0_sq_STR02918]; ring
  have hR4 : R0_STR02918 (h * A) (h * B) ^ 4 = (h ^ 2 * (A ^ 2 + B ^ 2)) ^ 2 := by
    rw [← hR2]; ring
  unfold poly19_STR02957
  rw [hR4, hR2, Jred_eq_STR02918]
  ring

theorem jchart_gamma_STR02957 (h γ : ℝ) (u : ℝ → ℝ) :
    Jchart_STR02950 h γ u = Jchart_STR02950 h 0 u - 2 * γ * entropyChart_STR02949 h u := by
  unfold Jchart_STR02950
  ring

/-! ### The cutoff remainder -/

/-- The order-three remainder `h⁻³ (ψ(hA, hB, h, h²s) - h² q_*)` for `|h| ≤ δ`, and `0` otherwise. -/
noncomputable def relE_STR02957 (ψ : Par_STR02916 → E_STR02969) (δ : ℝ) (A B s h : ℝ) :
    E_STR02969 :=
  if |h| ≤ δ then
    (h ^ 3)⁻¹ • (ψ ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916) - h ^ 2 • qstar_STR02917 A B)
  else 0

theorem relE_eq_STR02957 (ψ : Par_STR02916 → E_STR02969) (hψ0 : ψ 0 = 0) (δ : ℝ)
    (A B s h : ℝ) (hh : |h| ≤ δ) :
    h ^ 3 • relE_STR02957 ψ δ A B s h =
      ψ ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916) - h ^ 2 • qstar_STR02917 A B := by
  unfold relE_STR02957
  simp only [hh, ↓reduceIte]
  by_cases h0 : h = 0
  · subst h0
    have hz : ((0 * A, 0 * B, (0:ℝ), (0:ℝ) ^ 2 * s) : Par_STR02916) = 0 := by
      simp [Prod.ext_iff]
    rw [hz, hψ0]
    simp
  · rw [smul_smul, mul_inv_cancel₀ (pow_ne_zero 3 h0), one_smul]

theorem relE_norm_STR02957 (ψ : Par_STR02916 → E_STR02969) (δ M : ℝ) (hM : 0 ≤ M)
    (A B s : ℝ)
    (hb : ∀ h : ℝ, |h| ≤ δ →
      ‖ψ ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916) - h ^ 2 • qstar_STR02917 A B‖ ≤
        M * |h| ^ 3)
    (h : ℝ) : ‖relE_STR02957 ψ δ A B s h‖ ≤ M := by
  unfold relE_STR02957
  split_ifs with hh
  · rcases eq_or_ne h 0 with h0 | h0
    · subst h0
      simp [hM]
    · have hp : 0 < |h| ^ 3 := pow_pos (abs_pos.2 h0) 3
      rw [norm_smul, norm_inv, norm_pow, Real.norm_eq_abs, ← div_eq_inv_mul, div_le_iff₀ hp]
      exact hb h hh
  · simp [hM]

theorem psi_val_STR02957 (ψ : Par_STR02916 → E_STR02969) (hψ0 : ψ 0 = 0) (δ : ℝ)
    (A B s h : ℝ) (hh : |h| ≤ δ) (t : ℝ) :
    vE_STR02957 (ψ ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916)) t =
      h ^ 2 * qFun_STR02945 (Cstar_STR02918 A B) (Dstar_STR02918 A B) (Estar_STR02918 A)
        (Fstar_STR02918 B) t + h ^ 3 * vE_STR02957 (relE_STR02957 ψ δ A B s h) t := by
  have h1 : h ^ 3 * vE_STR02957 (relE_STR02957 ψ δ A B s h) t =
      vE_STR02957 (ψ ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916)) t -
        h ^ 2 * vE_STR02957 (qstar_STR02917 A B) t := by
    rw [← vE_smul_apply_STR02957, relE_eq_STR02957 ψ hψ0 δ A B s h hh,
      vE_sub_apply_STR02957, vE_smul_apply_STR02957]
  rw [qstar_apply_STR02957] at h1
  linarith

/-! ### The entropy of the chart on the scaled jet -/

/-- **STR029.57.** There are open neighbourhoods `U` of `0` in `ℝ⁴` and `V` of `0` in `E` and a
smooth map `ψ` of STR029.17. For every compact `K` of triples `(A, B, s)` there are `δ > 0` and
`M ≥ 0` such that for `(A, B, s) ∈ K` and `|h| ≤ δ` the scaled point `(hA, hB, h, h²s)` lies in `U`
and the reduced functional `F = Jchart h γ (a cos t + b sin t + ψ(a, b, h, γ))` at `(a, b, h, γ) =
(hA, hB, h, h²s)` differs from the polynomial of STR029.19 by at most `M |h|⁵`. -/
theorem str029_57_weighted_fourth_jet_reduced_functional :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K →
        ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ A B s : ℝ, (A, B, s) ∈ K →
          ∀ h : ℝ, |h| ≤ δ →
            ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916) ∈ U ∧
            |Jchart_STR02950 h (h ^ 2 * s)
                (uT_STR02901 (h * A) (h * B)
                  (vE_STR02957 (ψ ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916)))) -
              poly19_STR02957 (h * A) (h * B) h (h ^ 2 * s)| ≤ M * |h| ^ 5 := by
  obtain ⟨U, V, ψ, hU, h0U, hV, h0V, hψ, hψ0, hψV, hiff, hK⟩ :=
    str029_17_assemble_independent_second_range_jet
  refine ⟨U, V, ψ, hU, h0U, hV, h0V, hψ, hψ0, hψV, hiff, ?_⟩
  intro K hKc
  obtain ⟨δ, hδ, M17, hM17, hall⟩ := hK K hKc
  obtain ⟨C0, hC0, hCb⟩ : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ A B s : ℝ, (A, B, s) ∈ K →
      |A| ≤ C0 ∧ |B| ≤ C0 ∧ |s| ≤ C0 := by
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn
      (f := fun p : ℝ × ℝ × ℝ => |p.1| + |p.2.1| + |p.2.2|)
      (Continuous.continuousOn (by fun_prop))
    refine ⟨max C 0, le_max_right _ _, fun A B s hABs => ?_⟩
    have hnn : 0 ≤ |A| + |B| + |s| := by positivity
    have h1 : ‖|A| + |B| + |s|‖ ≤ C := hC (A, B, s) hABs
    rw [Real.norm_eq_abs, abs_of_nonneg hnn] at h1
    refine ⟨?_, ?_, ?_⟩ <;> linarith [abs_nonneg A, abs_nonneg B, abs_nonneg s, le_max_left C 0]
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = C0 + C0 ^ 2 + M17 + 1 := ⟨_, rfl⟩
  have hR' : M17 ≤ R ∧ C0 ≤ R ∧ 0 ≤ R := by
    have := sq_nonneg C0
    refine ⟨?_, ?_, ?_⟩ <;> linarith
  obtain ⟨hMR, hCR, hR0⟩ := hR'
  have hCR2 : C0 + C0 ^ 2 ≤ R := by
    have := sq_nonneg C0
    linarith
  obtain ⟨h0, hh0, K0, hK0, hT09⟩ :=
    str029_09_fourth_order_coefficient_explicit_information_functional R
  obtain ⟨Lc, hLc, hLip⟩ :=
    entropy_lip_STR02957 (2 * C0 + 4 * R + M17) (by linarith)
  refine ⟨min (min h0 δ) 1, lt_min (lt_min hh0 hδ) one_pos,
    K0 + 2 * C0 * (Lc * M17 + K0), ?_, ?_⟩
  · have h1 := mul_nonneg hLc hM17
    have h2 := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hC0) (add_nonneg h1 hK0)
    linarith
  intro A B s hABs h hh
  have hh1 : |h| ≤ h0 := hh.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hh2 : |h| ≤ δ := hh.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hh3 : |h| ≤ 1 := hh.trans (min_le_right _ _)
  obtain ⟨hA, hB, hs⟩ := hCb A B s hABs
  refine ⟨(hall A B s hABs h hh2).1, ?_⟩
  have hbound : ∀ σ : ℝ, |σ| ≤ δ →
      ‖ψ ((σ * A, σ * B, σ, σ ^ 2 * s) : Par_STR02916) - σ ^ 2 • qstar_STR02917 A B‖ ≤
        M17 * |σ| ^ 3 :=
    fun σ hσ => (hall A B s hABs σ hσ).2
  have hrelN : ∀ σ : ℝ, ‖relE_STR02957 ψ δ A B s σ‖ ≤ M17 :=
    fun σ => relE_norm_STR02957 ψ δ M17 hM17 A B s hbound σ
  have hvN : ∀ σ t : ℝ, |vE_STR02957 (relE_STR02957 ψ δ A B s σ) t| ≤ M17 :=
    fun σ t => (vE_sup_STR02957 _ t).trans (hrelN σ)
  obtain ⟨hC1, hD1, hE1, hF1⟩ := coef_bound_STR02957 hA hB hC0
  have hCsR := hC1.trans hCR2
  have hDsR := hD1.trans hCR2
  have hEsR := hE1.trans hCR2
  have hFsR := hF1.trans hCR2
  obtain ⟨c1, c2, c3⟩ := hT09 A B (Cstar_STR02918 A B) (Dstar_STR02918 A B)
    (Estar_STR02918 A) (Fstar_STR02918 B) (hA.trans hCR) (hB.trans hCR) hCsR hDsR hEsR hFsR h hh1
  have hJ4 : J4_STR02909 A B (Cstar_STR02918 A B) (Dstar_STR02918 A B) (Estar_STR02918 A)
      (Fstar_STR02918 B) = Jred_STR02918 A B := by
    rw [str029_18_exact_reduced_quartic_square_completion]
    ring
  obtain ⟨u3, hu3def⟩ : ∃ u3 : ℝ → ℝ, u3 = fun t =>
      h * pFun_STR02945 A B t + h ^ 2 * qFun_STR02945 (Cstar_STR02918 A B) (Dstar_STR02918 A B)
        (Estar_STR02918 A) (Fstar_STR02918 B) t +
        h ^ 3 * vE_STR02957 (relE_STR02957 ψ δ A B s h) t := ⟨_, rfl⟩
  have hu3t : ∀ t, u3 t = h * pFun_STR02945 A B t + h ^ 2 * qFun_STR02945 (Cstar_STR02918 A B)
      (Dstar_STR02918 A B) (Estar_STR02918 A) (Fstar_STR02918 B) t +
        h ^ 3 * vE_STR02957 (relE_STR02957 ψ δ A B s h) t := fun t => by
    subst hu3def
    rfl
  obtain ⟨u2, hu2def⟩ : ∃ u2 : ℝ → ℝ, u2 = uFun_STR02945 A B (Cstar_STR02918 A B)
      (Dstar_STR02918 A B) (Estar_STR02918 A) (Fstar_STR02918 B) h := ⟨_, rfl⟩
  have hu2t : ∀ t, u2 t = h * pFun_STR02945 A B t + h ^ 2 * qFun_STR02945 (Cstar_STR02918 A B)
      (Dstar_STR02918 A B) (Estar_STR02918 A) (Fstar_STR02918 B) t := fun t => by
    subst hu2def
    rfl
  have hX3 : |Jzero_STR02909 h u3 - h ^ 4 * Jred_STR02918 A B| ≤ K0 * |h| ^ 5 := by
    have := c3 (fun σ t => vE_STR02957 (relE_STR02957 ψ δ A B s σ) t)
      (fun σ => vE_isC2_STR02957 (relE_STR02957 ψ δ A B s σ))
      (fun σ => vE_mean_STR02957 (relE_STR02957 ψ δ A B s σ))
      (fun σ => by
        show c2Norm_STR02901 (1 / 2) (vE_STR02957 (relE_STR02957 ψ δ A B s σ)) ≤ R
        rw [vE_c2Norm_STR02957]
        linarith [hrelN σ])
    rw [hJ4] at this
    rw [hu3def]
    exact this
  have hu2c : Continuous u2 := by
    rw [show u2 = fun t => h * pFun_STR02945 A B t + h ^ 2 * qFun_STR02945 (Cstar_STR02918 A B)
      (Dstar_STR02918 A B) (Estar_STR02918 A) (Fstar_STR02918 B) t from funext hu2t]
    unfold pFun_STR02945 qFun_STR02945
    fun_prop
  have hu3c : Continuous u3 := by
    have hv := (vE_isC2_STR02957 (relE_STR02957 ψ δ A B s h)).2.1.continuous
    rw [hu3def]
    unfold pFun_STR02945 qFun_STR02945
    fun_prop
  have hbd2 : ∀ t, |u2 t| ≤ 2 * C0 + 4 * R := by
    intro t
    rw [hu2def]
    exact (uFun_bound_STR02957 A B (Cstar_STR02918 A B) (Dstar_STR02918 A B)
      (Estar_STR02918 A) (Fstar_STR02918 B) h t hh3).trans (by linarith)
  have hdiff : ∀ t, |u3 t - u2 t| ≤ |h| ^ 3 * M17 := by
    intro t
    have e : u3 t - u2 t = h ^ 3 * vE_STR02957 (relE_STR02957 ψ δ A B s h) t := by
      rw [hu3t t, hu2t t]
      ring
    rw [e, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_left (hvN h t) (pow_nonneg (abs_nonneg h) 3)
  have hbd3 : ∀ t, |u3 t| ≤ 2 * C0 + 4 * R + M17 := by
    intro t
    have e := abs_add_le (u3 t - u2 t) (u2 t)
    rw [sub_add_cancel] at e
    have h3 : |h| ^ 3 * M17 ≤ M17 :=
      mul_le_of_le_one_left hM17 (pow_le_one₀ (abs_nonneg h) hh3)
    linarith [hdiff t, hbd2 t]
  have hbd2L : ∀ t, |u2 t| ≤ 2 * C0 + 4 * R + M17 := fun t => by
    linarith [hbd2 t]
  have hEd := hLip h (|h| ^ 3 * M17) u3 u2 hh3 hu3c hu2c hbd3 hbd2L hdiff
  have hX2 : |entropyChart_STR02949 h u2 - h ^ 2 * ((A ^ 2 + B ^ 2) / 4)| ≤ K0 * |h| ^ 3 := by
    rw [← chartEntropy_eq_entropyChart_STR02909 h hu2c, hu2def]
    exact c2
  have hEY : |entropyChart_STR02949 h u3 - h ^ 2 * ((A ^ 2 + B ^ 2) / 4)| ≤
      (Lc * M17 + K0) * |h| ^ 3 := by
    have e := abs_add_le (entropyChart_STR02949 h u3 - entropyChart_STR02949 h u2)
      (entropyChart_STR02949 h u2 - h ^ 2 * ((A ^ 2 + B ^ 2) / 4))
    rw [sub_add_sub_cancel] at e
    linarith [hEd, hX2]
  have hpoly := poly19_scaled_STR02957 A B s h
  have heq : Jchart_STR02950 h (h ^ 2 * s) u3 - poly19_STR02957 (h * A) (h * B) h (h ^ 2 * s) =
      (Jzero_STR02909 h u3 - h ^ 4 * Jred_STR02918 A B) -
        2 * (h ^ 2 * s) * (entropyChart_STR02949 h u3 - h ^ 2 * ((A ^ 2 + B ^ 2) / 4)) := by
    rw [jchart_gamma_STR02957, ← Jzero_eq_Jchart_STR02909 h hu3c, hpoly]
    ring
  have hu3eq : uT_STR02901 (h * A) (h * B)
      (vE_STR02957 (ψ ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916))) = u3 := by
    funext t
    rw [hu3t t]
    unfold uT_STR02901 pFun_STR02945
    rw [psi_val_STR02957 ψ hψ0 δ A B s h hh2 t]
    ring
  have hsplit : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    have e := abs_add_le a (-b)
    rw [abs_neg, ← sub_eq_add_neg] at e
    exact e
  have hs2 : |2 * (h ^ 2 * s) * (entropyChart_STR02949 h u3 -
      h ^ 2 * ((A ^ 2 + B ^ 2) / 4))| ≤ 2 * C0 * (Lc * M17 + K0) * |h| ^ 5 := by
    have ea : |2 * (h ^ 2 * s) * (entropyChart_STR02949 h u3 -
        h ^ 2 * ((A ^ 2 + B ^ 2) / 4))| =
        2 * h ^ 2 * (|s| * |entropyChart_STR02949 h u3 - h ^ 2 * ((A ^ 2 + B ^ 2) / 4)|) := by
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2), abs_mul,
        abs_of_nonneg (sq_nonneg h)]
      ring
    have h5 : |h| ^ 5 = h ^ 2 * |h| ^ 3 := by
      rw [← sq_abs h]
      ring
    have hsY := mul_le_mul hs hEY (abs_nonneg _) hC0
    have hm := mul_le_mul_of_nonneg_left hsY (by positivity : (0:ℝ) ≤ 2 * h ^ 2)
    have e3 : 2 * C0 * (Lc * M17 + K0) * (h ^ 2 * |h| ^ 3) =
        2 * h ^ 2 * (C0 * ((Lc * M17 + K0) * |h| ^ 3)) := by ring
    rw [ea, h5, e3]
    exact hm
  rw [hu3eq, heq]
  exact le_trans (hsplit _ _) ((add_le_add hX3 hs2).trans (le_of_eq (by ring)))

end DGPS.Frontier.STR029
