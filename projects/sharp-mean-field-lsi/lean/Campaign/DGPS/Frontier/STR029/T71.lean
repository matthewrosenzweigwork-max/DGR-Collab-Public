import DGPS.Frontier.STR029.T14
import DGPS.Frontier.STR029.T16
import DGPS.Frontier.STR029.T70

/-!
# STR029.71: Scaled implicit derivatives and the uniform range remainder

Task id: STR029.71 (node STR029), "Scaled implicit derivatives and the uniform range remainder".

Statement formalized.  Let `ψ` be the smooth range graph of STR029.16 (parameters
`p = (a, b, h, γ) ∈ ℝ⁴`, values in the Hölder carrier `E`).  For every compact set `K` of triples
`(A, B, s)` there are `δ > 0` and `M ≥ 0` such that, for every `(A, B, s) ∈ K`, the curve
`h ↦ ψ (h A, h B, h, h² s)` stays in the graph domain for `|h| ≤ δ`, is `C^∞` on `[-δ, δ]`,
has value `0` and first derivative `0` at `0`, has second derivative `2 q_*(A, B)` at `0`, has
third derivative of `E`-norm at most `M` on `[-δ, δ]`, and satisfies
`‖ψ (h A, h B, h, h² s) - h² q_*(A, B)‖_E ≤ M |h|³` for `|h| ≤ δ`.

Provides:

Every declaration below is in the namespace `DGPS.Frontier.STR029`.

* `DGPS.Frontier.STR029.str029_71_scaled_implicit_derivatives_uniform_range_remainder`: main
  statement, for any open set `U ∋ 0` and any map `ψ` that is `C^∞` on `U` with `ψ 0 = 0` and
  `Rpar p (ψ p) = 0` on `U`, and any compact `K`; the conclusion is the list above, with the
  curve `scaledCurve_STR02971 ψ A B s`.
* `DGPS.Frontier.STR029.str029_71_scaled_implicit_derivatives_uniform_range_remainder_graph`:
  the same conclusion for the graph `(U, V, ψ)` of `str029_16_unique_smooth_range_graph`, with no
  further hypotheses (the graph properties of STR029.16 are restated and the conclusion is
  quantified over all compact `K`).

Supporting declarations (all carry the suffix `_STR02971`):

* `qstar_STR02971`: the explicit target `q_*(A, B) ∈ E`.
* `scaledCurve_STR02971`: the curve `h ↦ ψ (h A, h B, h, h² s)`.
* `forcingY_qstar_STR02971`, `eq_of_forcingY_zero_STR02971`: `q_*` has vanishing order-two forcing
  and a profile with vanishing forcing is unique (via the bounded isomorphism of STR029.14).
* `deriv_zero_of_rangeeq_STR02971`, `forcing_zero_of_rangeeq_STR02971`: the first-order and
  second-order consequences of the identically zero range equation along the scaled curve.
* `taylor_remainder_STR02971`, `uniform_slab_STR02971`: the Banach-valued Taylor remainder and
  the compactness argument giving a common `δ` and bound `M`.

R5 notes:

* Which `ψ`.  The main theorem is stated for an arbitrary pair `(U, ψ)` whose hypotheses are
  exactly what the graph of STR029.16 provides: `U` open with `0 ∈ U`, `ψ` smooth on `U`,
  `ψ 0 = 0`, and the range equation `Rpar_STR02916 p (ψ p) = 0` for `p ∈ U`.  The `_graph` form
  instantiates this with the graph of `str029_16_unique_smooth_range_graph` (the equation holds
  there because `ψ p ∈ V`).  No hypothesis beyond these is used.  The conclusion carries two
  conjuncts beyond the displayed list of the specification, namely that the scaled curve stays in
  `U` for `|h| ≤ δ` and that it is `C^∞` on `[-δ, δ]` (see "Derivatives" below); both only
  strengthen the conclusion.
* Range map.  `Rpar_STR02916` is the variational range map `Rvar_STR02915` of STR029.15 and
  STR029.16, which is also the map in STR029.70.  The Euler range map is not used and is not
  assumed to coincide with it.
* Parameter conventions.  `Par_STR02916 = ℝ × ℝ × ℝ × ℝ` carries `(a, b, h, γ)`; the scaled
  variables are `a = h A`, `b = h B`, `γ = h² s`, so `s = γ / h²`.  All quantities are the
  angular ones of STR029.14 to STR029.16 and STR029.70.  No angular-to-physical rate conversion
  (multiplication by `a₀ = 4π²`) occurs in this unit, and the entropy, Fisher and deficit
  conventions and the absolute-density domain of STR029.01 are not touched.
* Carriers.  The values live in `E_STR02969`, with the `C^{2,1/2}` norm of STR029.69, so the
  remainder bound `‖·‖ ≤ M |h|³` is the stated `O_{C^{2,α}}(|h|³)` with `α = 1/2`.
* The target `q_*`.  STR029.17 is not part of this branch, so `q_*` is defined here as
  `(A/2 - (A²-B²)/12) cos 2t + (-B/2 - A B/6) sin 2t - (A/10) cos 4t - (B/10) sin 4t`, which is
  the solution of the four coefficient equations displayed in the proof sketch.  At
  `(A, B) = (2, 0)` it equals `(2/3) cos 2t - (1/5) cos 4t`, the `h²` coefficient of the frozen
  logarithmic-density expansion.  It is shown to lie in `E` and to have vanishing forcing
  (`forcingY_qstar_STR02971`); uniqueness of the zero of the forcing is
  `eq_of_forcingY_zero_STR02971`.
* Compact parameter sets.  "Every compact set of `(A, B, s)`" is `K : Set (ℝ × ℝ × ℝ)` with
  `IsCompact K`, in the order `(A, B, s)`.  The "common closed field interval" is `[-δ, δ]`, with
  `δ` and the bound `M` independent of the point of `K`.  Smallness of `δ` is what places the
  scaled curves in the graph domain `U` (first conjunct), via a tube argument and compactness.
* Derivatives.  The derivatives are Mathlib's `deriv` and `iteratedDeriv` of the curve
  `ℝ → E`.  Because these are junk-valued off differentiability, the conclusion also states
  `ContDiffOn ℝ ∞ (scaledCurve ψ A B s) (Set.Icc (-δ) δ)`, and the proof identifies
  `iteratedDeriv 2` and `iteratedDeriv 3` with genuine second and third derivatives on an open
  neighbourhood of `[-δ, δ]`.
* Remainder constant.  The proof sketch bounds the Taylor remainder by `M |h|³ / 6`.  The proof
  here uses three successive mean value estimates and yields the constant `M` (a bound for the
  third derivative) instead of `M / 6`.  This is the same uniform `O_{C^{2,α}}(|h|³)` claim that
  the statement asks for.
* Proof route.  The first derivative is obtained from the chain rule applied to
  `h ↦ Fp ((h A, h B, h, h² s), f h) = 0` at `0`, the quadratic bound of STR029.70 on the range
  map at `q = 0`, and injectivity of the derivative in the `E` variable (STR029.16); the second
  coefficient `q = ½ f''(0)` is shown to have vanishing order-two forcing by comparing
  `Fp (cur h, f h) = 0` with `Fp (cur h, h² q) = h² · forcing + O(h³)` through a local
  Lipschitz bound of `Fp` and the `_small` estimate of STR029.70; then `q = q_*` follows from
  `eq_of_forcingY_zero_STR02971`, which rests on the bounded isomorphism of STR029.14.
* Not formalized.  The "Moreover" clause (smooth extension of the remainder divided by `h³` by the
  integral formula, with uniformly bounded derivatives of every finite order on smaller compact
  parameter sets) is the optional stretch clause and is not included.
-/

open scoped ContDiff Topology
open Filter DGPS.Analysis.PeriodicHolder

namespace DGPS.Frontier.STR029

/-! ### Elementary mean value estimates -/

/-- A mean value estimate with a power bound: if `g (0) = 0` and `‖g' y‖ ≤ C |y|^k` on `[-δ, δ]`
then `‖g x‖ ≤ C |x|^(k+1)` there. -/
theorem mvt_pow_STR02971 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g g' : ℝ → F} {δ C : ℝ} {k : ℕ} (hC : 0 ≤ C)
    (hg : ∀ y, |y| ≤ δ → HasDerivAt g (g' y) y)
    (hb : ∀ y, |y| ≤ δ → ‖g' y‖ ≤ C * |y| ^ k) (h0 : g 0 = 0) {x : ℝ} (hx : |x| ≤ δ) :
    ‖g x‖ ≤ C * |x| ^ (k + 1) := by
  have hmem : ∀ y ∈ Set.uIcc (0 : ℝ) x, |y| ≤ |x| := by
    intro y hy
    rw [Set.mem_uIcc] at hy
    refine abs_le.2 ⟨?_, ?_⟩
    · rcases hy with ⟨h1, _⟩ | ⟨h1, _⟩
      · linarith [abs_nonneg x]
      · linarith [neg_abs_le x]
    · rcases hy with ⟨_, h2⟩ | ⟨_, h2⟩
      · linarith [le_abs_self x]
      · linarith [abs_nonneg x]
  have key := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := g) (f' := g')
    (s := Set.uIcc 0 x) (C := C * |x| ^ k)
    (fun y hy => (hg y ((hmem y hy).trans hx)).hasDerivWithinAt)
    (fun y hy => (hb y ((hmem y hy).trans hx)).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (abs_nonneg _) (hmem y hy) k) hC))
    (convex_uIcc 0 x) Set.left_mem_uIcc Set.right_mem_uIcc
  rw [h0, sub_zero, sub_zero, Real.norm_eq_abs] at key
  calc ‖g x‖ ≤ C * |x| ^ k * |x| := key
    _ = C * |x| ^ (k + 1) := by ring

/-- If a vector is bounded by a multiple of every small positive number, it vanishes. -/
theorem eq_zero_of_le_mul_STR02971 {F : Type*} [NormedAddCommGroup F] {v : F} {c r : ℝ}
    (hc : 0 ≤ c) (hr : 0 < r) (h : ∀ t : ℝ, 0 < t → t ≤ r → ‖v‖ ≤ c * t) : v = 0 := by
  by_contra hv
  have hn : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hq : 0 < ‖v‖ / (2 * (c + 1)) := by positivity
  have ht0 : 0 < min r (‖v‖ / (2 * (c + 1))) := lt_min hr hq
  have h1 := h _ ht0 (min_le_left _ _)
  have h2 : min r (‖v‖ / (2 * (c + 1))) ≤ ‖v‖ / (2 * (c + 1)) := min_le_right _ _
  have h3 : c * min r (‖v‖ / (2 * (c + 1))) ≤ c * (‖v‖ / (2 * (c + 1))) := by gcongr
  have h4 : c * (‖v‖ / (2 * (c + 1))) < ‖v‖ := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith
  linarith

/-- A function with `g 0 = 0`, derivative `v` at `0`, and `‖g h‖ ≤ C h²` near `0` has `v = 0`. -/
theorem deriv_eq_zero_of_sq_STR02971 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : ℝ → F} {v : F} {C r : ℝ} (hg : HasDerivAt g v 0) (h0 : g 0 = 0) (hr : 0 < r)
    (hb : ∀ h : ℝ, |h| < r → ‖g h‖ ≤ C * h ^ 2) : v = 0 := by
  have hs := hg.tendsto_slope_zero
  have h2 : Tendsto (fun t : ℝ => t⁻¹ • (g (0 + t) - g 0)) (𝓝[≠] 0) (𝓝 0) := by
    refine squeeze_zero_norm' (f := fun t : ℝ => t⁻¹ • (g (0 + t) - g 0))
      (a := fun t : ℝ => |C| * |t|) ?_ ?_
    · filter_upwards [mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds (0 : ℝ) hr),
        self_mem_nhdsWithin] with t ht ht0
      have htr : |t| < r := by simpa [Real.dist_eq] using ht
      have ht0' : t ≠ 0 := ht0
      rw [zero_add, h0, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs]
      have := hb t htr
      have hpos : 0 < |t| := abs_pos.2 ht0'
      rw [inv_mul_le_iff₀ hpos]
      calc ‖g t‖ ≤ C * t ^ 2 := this
        _ ≤ |C| * t ^ 2 := by gcongr; exact le_abs_self C
        _ = |t| * (|C| * |t|) := by rw [← sq_abs t]; ring
    · have : Tendsto (fun t : ℝ => |C| * |t|) (𝓝 0) (𝓝 (|C| * |(0 : ℝ)|)) :=
        (continuous_const.mul continuous_abs).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hs h2

/-! ### Harmonics in `C^{2,1/2}` -/

/-- The harmonic `a cos (n t) + b sin (n t)` for a natural frequency `n`. -/
noncomputable def trig_STR02971 (n : ℕ) (a b : ℝ) : ℝ → ℝ :=
  fun t => a * Real.cos ((n : ℝ) * t) + b * Real.sin ((n : ℝ) * t)

theorem trig_hasDerivAt_STR02971 (n : ℕ) (a b t : ℝ) :
    HasDerivAt (trig_STR02971 n a b) (trig_STR02971 n (b * n) (-(a * n)) t) t := by
  have h1 : HasDerivAt (fun y : ℝ => (n : ℝ) * y) n t := by
    simpa using (hasDerivAt_id t).const_mul (n : ℝ)
  have h2 := (h1.cos.const_mul a).add (h1.sin.const_mul b)
  have h3 : trig_STR02971 n a b =
      (fun y => a * Real.cos ((n : ℝ) * y)) + fun y => b * Real.sin ((n : ℝ) * y) := rfl
  rw [h3]
  convert h2 using 1
  simp only [trig_STR02971]
  ring

theorem deriv_trig_STR02971 (n : ℕ) (a b : ℝ) :
    deriv (trig_STR02971 n a b) = trig_STR02971 n (b * n) (-(a * n)) :=
  funext fun t => (trig_hasDerivAt_STR02971 n a b t).deriv

theorem deriv2_trig_STR02971 (n : ℕ) (a b : ℝ) :
    deriv (deriv (trig_STR02971 n a b)) = trig_STR02971 n (-(a * (n : ℝ) ^ 2)) (-(b * (n : ℝ) ^ 2)) := by
  rw [deriv_trig_STR02971, deriv_trig_STR02971]
  funext t
  simp only [trig_STR02971]
  ring

theorem trig_differentiable_STR02971 (n : ℕ) (a b : ℝ) : Differentiable ℝ (trig_STR02971 n a b) :=
  fun t => (trig_hasDerivAt_STR02971 n a b t).differentiableAt

theorem harm_eq_trig_STR02971 (j : ℕ) (a b : ℝ) :
    harm_STR02970 j a b = trig_STR02971 (j + 1) a b := rfl

theorem harm_isC2_STR02971 (j : ℕ) (a b : ℝ) :
    IsC2Alpha_STR02901 (1 / 2) (harm_STR02970 j a b) := by
  unfold IsC2Alpha_STR02901
  refine ⟨(harm_isPerHolder_STR02970 j a b).1, ?_, ?_, ?_, ?_⟩
  · rw [harm_eq_trig_STR02971]; exact trig_differentiable_STR02971 _ _ _
  · rw [harm_eq_trig_STR02971, deriv_trig_STR02971]; exact trig_differentiable_STR02971 _ _ _
  · rw [harm_eq_trig_STR02971, deriv2_trig_STR02971, ← harm_eq_trig_STR02971]
    exact harm_cont_STR02970 j _ _
  · rw [harm_eq_trig_STR02971, deriv2_trig_STR02971, ← harm_eq_trig_STR02971]
    exact (harm_isPerHolder_STR02970 j _ _).2.2

/-! ### The target `q_*` -/

/-- The explicit function `q_*(A, B)`, namely
`(A/2 - (A²-B²)/12) cos 2t + (-B/2 - AB/6) sin 2t - (A/10) cos 4t - (B/10) sin 4t`. -/
noncomputable def qstarFun_STR02971 (A B : ℝ) : ℝ → ℝ := fun t =>
  (A / 2 - (A ^ 2 - B ^ 2) / 12) * Real.cos (2 * t) + (-(B / 2) - A * B / 6) * Real.sin (2 * t) +
    (-(A / 10)) * Real.cos (4 * t) + (-(B / 10)) * Real.sin (4 * t)

theorem qstarFun_eq_harm_STR02971 (A B : ℝ) :
    qstarFun_STR02971 A B = fun t =>
      harm_STR02970 1 (A / 2 - (A ^ 2 - B ^ 2) / 12) (-(B / 2) - A * B / 6) t +
        harm_STR02970 3 (-(A / 10)) (-(B / 10)) t := by
  funext t
  rw [harm1_STR02970, harm3_STR02970]
  simp only [qstarFun_STR02971]
  ring

theorem qstarFun_isC2_STR02971 (A B : ℝ) : IsC2Alpha_STR02901 (1 / 2) (qstarFun_STR02971 A B) := by
  rw [qstarFun_eq_harm_STR02971]
  exact c2_add_STR02969 (harm_isC2_STR02971 1 _ _) (harm_isC2_STR02971 3 _ _)

theorem qstarFun_inE_STR02971 (A B : ℝ) : InE_STR02901 (qstarFun_STR02971 A B) := by
  rw [qstarFun_eq_harm_STR02971]
  exact inE_add_STR02970 (harm_inE_STR02970 1 le_rfl _ _) (harm_inE_STR02970 3 (by norm_num) _ _)
    (harm_cont_STR02970 1 _ _) (harm_cont_STR02970 3 _ _)

/-- The target `q_*(A, B) ∈ E`. -/
noncomputable def qstar_STR02971 (A B : ℝ) : E_STR02969 :=
  ⟨PeriodicC2_STR02969.mk (qstarFun_STR02971 A B) (qstarFun_isC2_STR02971 A B),
    (str029_69_completeness_closed_complements_range_spaces_E.1 _).2 (qstarFun_inE_STR02971 A B)⟩

theorem qstar_val_STR02971 (A B : ℝ) :
    ((qstar_STR02971 A B : E_STR02969) : PeriodicC2_STR02969).val = qstarFun_STR02971 A B := rfl

theorem deriv2_qstar_STR02971 (A B t : ℝ) :
    deriv (deriv (((qstar_STR02971 A B : E_STR02969) : PeriodicC2_STR02969).val)) t =
      -4 * ((A / 2 - (A ^ 2 - B ^ 2) / 12) * Real.cos (2 * t) +
        (-(B / 2) - A * B / 6) * Real.sin (2 * t)) +
      -16 * ((-(A / 10)) * Real.cos (4 * t) + (-(B / 10)) * Real.sin (4 * t)) := by
  rw [qstar_val_STR02971, qstarFun_eq_harm_STR02971]
  have e : (fun t => harm_STR02970 1 (A / 2 - (A ^ 2 - B ^ 2) / 12) (-(B / 2) - A * B / 6) t +
        harm_STR02970 3 (-(A / 10)) (-(B / 10)) t) =
      trig_STR02971 2 (A / 2 - (A ^ 2 - B ^ 2) / 12) (-(B / 2) - A * B / 6) +
        trig_STR02971 4 (-(A / 10)) (-(B / 10)) := rfl
  rw [e]
  rw [deriv_add_fun_STR02969 (trig_differentiable_STR02971 _ _ _) (trig_differentiable_STR02971 _ _ _)]
  rw [deriv_add_fun_STR02969 (by rw [deriv_trig_STR02971]; exact trig_differentiable_STR02971 _ _ _)
    (by rw [deriv_trig_STR02971]; exact trig_differentiable_STR02971 _ _ _)]
  rw [deriv_trig_STR02971, deriv_trig_STR02971, deriv_trig_STR02971, deriv_trig_STR02971]
  simp only [Pi.add_apply, trig_STR02971]
  push_cast
  ring

/-- Pointwise: `forcing (q_*) = 0`. -/
theorem forcingY_qstar_STR02971 (A B : ℝ) :
    forcingY_STR02970 A B (qstar_STR02971 A B) = 0 := by
  refine Submodule.coe_eq_zero.1 (PeriodicHolder_STR02968.val_eq_zero.1 ?_)
  funext t
  have h := forcing_val_STR02970 A B (qstar_STR02971 A B) t
  show (forcing_STR02970 A B (qstar_STR02971 A B)).val t = 0
  rw [h, deriv2_qstar_STR02971, qstar_val_STR02971]
  simp only [qstarFun_STR02971]
  ring

/-- The forcing is affine in `q`, with linear part `-2 (∂² + 1)`. -/
theorem forcingY_sub_STR02971 (A B : ℝ) (q q' : E_STR02969) :
    forcingY_STR02970 A B q - forcingY_STR02970 A B q' = (-2 : ℝ) • bij_STR02914 (q - q') := by
  refine Subtype.ext (phext_STR02914 ?_)
  funext t
  have h1 := forcing_val_STR02970 A B q t
  have h2 := forcing_val_STR02970 A B q' t
  have h3 := (deriv2_sub_STR02969 (q : PeriodicC2_STR02969).isC2 (q' : PeriodicC2_STR02969).isC2).2
  have h4 := congrFun h3 t
  simp only [Pi.sub_apply] at h4
  show (forcing_STR02970 A B q).val t - (forcing_STR02970 A B q').val t =
    -2 * (deriv (deriv ((q : PeriodicC2_STR02969) - (q' : PeriodicC2_STR02969)).val) t +
      ((q : PeriodicC2_STR02969) - (q' : PeriodicC2_STR02969)).val t)
  rw [h1, h2, PeriodicC2_STR02969.val_sub, h4]
  simp only [Pi.sub_apply]
  ring

/-- Uniqueness: two profiles with vanishing forcing coincide. -/
theorem eq_of_forcingY_zero_STR02971 (A B : ℝ) {q q' : E_STR02969}
    (h : forcingY_STR02970 A B q = 0) (h' : forcingY_STR02970 A B q' = 0) : q = q' := by
  have h1 := forcingY_sub_STR02971 A B q q'
  rw [h, h', sub_zero] at h1
  have h2 : bij_STR02914 (q - q') = 0 := by
    have := h1.symm
    rcases smul_eq_zero.1 this with h3 | h3
    · norm_num at h3
    · exact h3
  have h3 : q - q' = 0 := by
    have := bij_STR02914.injective (h2.trans (map_zero bij_STR02914).symm)
    exact this
  exact sub_eq_zero.1 h3

/-! ### Slice derivatives and a uniform slab -/

/-- The partial derivative in the last (real) variable of a map on `X × ℝ`. -/
noncomputable def Dh_STR02971 {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (H : X × ℝ → F) (z : X × ℝ) : F :=
  fderiv ℝ H z (0, 1)

theorem contDiffOn_Dh_STR02971 {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {H : X × ℝ → F} {W : Set (X × ℝ)}
    (hH : ContDiffOn ℝ ∞ H W) (hW : IsOpen W) : ContDiffOn ℝ ∞ (Dh_STR02971 H) W := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ H) W := hH.fderiv_of_isOpen hW (by simp)
  exact h1.clm_apply contDiffOn_const

theorem hasDerivAt_slice_STR02971 {X F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {H : X × ℝ → F} {W : Set (X × ℝ)}
    (hH : ContDiffOn ℝ ∞ H W) (hW : IsOpen W) {x : X} {h : ℝ} (hxh : (x, h) ∈ W) :
    HasDerivAt (fun y : ℝ => H (x, y)) (Dh_STR02971 H (x, h)) h := by
  have hd : DifferentiableAt ℝ H (x, h) :=
    (hH.differentiableOn (by simp)).differentiableAt (hW.mem_nhds hxh)
  have hc : HasDerivAt (fun y : ℝ => (x, y)) ((0 : X), (1 : ℝ)) h :=
    (hasDerivAt_const h x).prodMk (hasDerivAt_id h)
  exact hd.hasFDerivAt.comp_hasDerivAt_of_eq h hc rfl

theorem iteratedDeriv_two_STR02971 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) : iteratedDeriv 2 f = deriv (deriv f) := by
  rw [iteratedDeriv_succ, iteratedDeriv_one]

theorem iteratedDeriv_three_STR02971 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) : iteratedDeriv 3 f = deriv (deriv (deriv f)) := by
  rw [iteratedDeriv_succ, iteratedDeriv_two_STR02971]

theorem deriv_deriv_slice_STR02971 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g g1 g2 : ℝ → F} {O : Set ℝ} (hO : IsOpen O)
    (h1 : ∀ y ∈ O, HasDerivAt g (g1 y) y) (h2 : ∀ y ∈ O, HasDerivAt g1 (g2 y) y)
    {y : ℝ} (hy : y ∈ O) : deriv (deriv g) y = g2 y := by
  have e : deriv g =ᶠ[𝓝 y] g1 :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds hy) (fun z hz => (h1 z hz).deriv)
  rw [e.deriv_eq]
  exact (h2 y hy).deriv

theorem deriv_deriv_deriv_slice_STR02971 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g g1 g2 g3 : ℝ → F} {O : Set ℝ} (hO : IsOpen O)
    (h1 : ∀ y ∈ O, HasDerivAt g (g1 y) y) (h2 : ∀ y ∈ O, HasDerivAt g1 (g2 y) y)
    (h3 : ∀ y ∈ O, HasDerivAt g2 (g3 y) y) {y : ℝ} (hy : y ∈ O) :
    deriv (deriv (deriv g)) y = g3 y := by
  have e : deriv (deriv g) =ᶠ[𝓝 y] g2 :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds hy)
      (fun z hz => deriv_deriv_slice_STR02971 hO h1 h2 hz)
  rw [e.deriv_eq]
  exact (h3 y hy).deriv

/-- A compactness argument: if `K` is compact, `W ⊆ X × ℝ` is open and contains `K × {0}`, and `g`
is continuous on `W`, then there is a common slab `|h| ≤ δ` inside `W` over all of `K`, on which
`g` is uniformly bounded. -/
theorem uniform_slab_STR02971 {X F : Type*} [TopologicalSpace X] [NormedAddCommGroup F]
    {K : Set X} (hK : IsCompact K) {W : Set (X × ℝ)} (hW : IsOpen W)
    (hKW : ∀ x ∈ K, (x, (0 : ℝ)) ∈ W) {g : X × ℝ → F} (hg : ContinuousOn g W) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ K, ∀ h : ℝ, |h| ≤ δ → (x, h) ∈ W ∧ ‖g (x, h)‖ ≤ M := by
  have hsub : K ×ˢ ({0} : Set ℝ) ⊆ W := by
    rintro ⟨x, h⟩ ⟨hx, hh⟩
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hKW x hx
  obtain ⟨u, v, hu, hv, hKu, h0v, huv⟩ := generalized_tube_lemma hK isCompact_singleton hW hsub
  obtain ⟨ε, hε, hεv⟩ := Metric.isOpen_iff.1 hv 0 (h0v (Set.mem_singleton 0))
  have hcpt : IsCompact (K ×ˢ Set.Icc (-(ε / 2)) (ε / 2)) := hK.prod isCompact_Icc
  have hsub2 : K ×ˢ Set.Icc (-(ε / 2)) (ε / 2) ⊆ W := by
    rintro ⟨x, h⟩ ⟨hx, hh⟩
    refine huv ⟨hKu hx, hεv ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    exact lt_of_le_of_lt (abs_le.2 hh) (by linarith)
  obtain ⟨C, hC⟩ := hcpt.exists_bound_of_continuousOn (hg.mono hsub2)
  refine ⟨ε / 2, by positivity, max C 0, le_max_right _ _, fun x hx h hh => ?_⟩
  have hmem : (x, h) ∈ K ×ˢ Set.Icc (-(ε / 2)) (ε / 2) := ⟨hx, abs_le.1 hh⟩
  exact ⟨hsub2 hmem, (hC _ hmem).trans (le_max_left _ _)⟩

/-! ### The one-dimensional Taylor remainder -/

/-- If `f 0 = 0`, the first derivative of `f` vanishes at `0`, the derivatives chain
`f → D1 → D2 → D3` on `[-δ, δ]` and `‖D3‖ ≤ M` there, then `f h = h² (½ D2 0) + R` with
`‖R‖ ≤ M |h|³`. -/
theorem taylor_remainder_STR02971 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f D1 D2 D3 : ℝ → F} {δ M : ℝ} (hM : 0 ≤ M) (h0 : f 0 = 0) (hD10 : D1 0 = 0)
    (hf : ∀ y : ℝ, |y| ≤ δ → HasDerivAt f (D1 y) y)
    (h1 : ∀ y : ℝ, |y| ≤ δ → HasDerivAt D1 (D2 y) y)
    (h2 : ∀ y : ℝ, |y| ≤ δ → HasDerivAt D2 (D3 y) y)
    (hb : ∀ y : ℝ, |y| ≤ δ → ‖D3 y‖ ≤ M) {h : ℝ} (hh : |h| ≤ δ) :
    ‖f h - h ^ 2 • ((1 / 2 : ℝ) • D2 0)‖ ≤ M * |h| ^ 3 := by
  have ha : ∀ y : ℝ, |y| ≤ δ → ‖D2 y - D2 0‖ ≤ M * |y| ^ 1 := by
    intro y hy
    have := mvt_pow_STR02971 (g := fun z => D2 z - D2 0) (g' := D3) (k := 0) hM
      (fun z hz => (h2 z hz).sub_const _) (fun z hz => by simpa using hb z hz) (by simp) hy
    simpa using this
  have hc : ∀ y : ℝ, |y| ≤ δ → ‖D1 y - y • D2 0‖ ≤ M * |y| ^ 2 := by
    intro y hy
    refine mvt_pow_STR02971 (g := fun z => D1 z - z • D2 0) (g' := fun z => D2 z - D2 0)
      (k := 1) hM ?_ ha (by simp [hD10]) hy
    intro z hz
    have h5 : HasDerivAt (fun z : ℝ => z • D2 0) (D2 0) z := by
      simpa using (hasDerivAt_id z).smul_const (D2 0)
    exact (h1 z hz).sub h5
  have hd : ‖f h - (h ^ 2 / 2) • D2 0‖ ≤ M * |h| ^ 3 := by
    refine mvt_pow_STR02971 (g := fun z => f z - (z ^ 2 / 2) • D2 0)
      (g' := fun z => D1 z - z • D2 0) (k := 2) hM ?_ hc (by simp [h0]) hh
    intro z hz
    have h3 : HasDerivAt (fun z : ℝ => z ^ 2 / 2) z z := by
      have := (hasDerivAt_pow 2 z).div_const 2
      convert this using 1
      push_cast
      ring
    exact (hf z hz).sub (h3.smul_const (D2 0))
  have e : h ^ 2 • ((1 / 2 : ℝ) • D2 0) = (h ^ 2 / 2) • D2 0 := by
    rw [smul_smul]
    congr 1
    ring
  rw [e]
  exact hd

/-! ### The scaled curve and the range map along it -/

/-- The curve `h ↦ ψ (h A, h B, h, h² s)`. -/
noncomputable def scaledCurve_STR02971 (ψ : Par_STR02916 → E_STR02969) (A B s : ℝ) :
    ℝ → E_STR02969 :=
  fun h => ψ (h * A, h * B, h, h ^ 2 * s)

/-- The scaling map `((A, B, s), h) ↦ (h A, h B, h, h² s)`. -/
def curZ_STR02971 (z : (ℝ × ℝ × ℝ) × ℝ) : Par_STR02916 :=
  (z.2 * z.1.1, z.2 * z.1.2.1, z.2, z.2 ^ 2 * z.1.2.2)

theorem curZ_contDiff_STR02971 : ContDiff ℝ ∞ curZ_STR02971 := by
  unfold curZ_STR02971
  fun_prop

theorem cur_zero_STR02971 (A B s : ℝ) :
    ((((0 : ℝ) * A, (0 : ℝ) * B, (0 : ℝ), (0 : ℝ) ^ 2 * s) : Par_STR02916)) = 0 := by
  simp [Prod.ext_iff]

theorem cur_hasDerivAt_STR02971 (A B s : ℝ) :
    HasDerivAt (fun h : ℝ => ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916)) (A, B, 1, 0) 0 := by
  have h1 : HasDerivAt (fun h : ℝ => h * A) A 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const A
  have h2 : HasDerivAt (fun h : ℝ => h * B) B 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const B
  have h3 : HasDerivAt (fun h : ℝ => h) 1 0 := hasDerivAt_id (0 : ℝ)
  have h4 : HasDerivAt (fun h : ℝ => h ^ 2 * s) 0 0 := by
    simpa using (hasDerivAt_pow 2 (0 : ℝ)).mul_const s
  exact h1.prodMk (h2.prodMk (h3.prodMk h4))

/-- First order: if `f 0 = 0`, `f` is differentiable at `0`, and `Fp (cur h, f h) = 0` near `0`,
then `f' 0 = 0`. -/
theorem deriv_zero_of_rangeeq_STR02971 (A B s : ℝ) {f : ℝ → E_STR02969} {v : E_STR02969}
    (hf : HasDerivAt f v 0) (hf0 : f 0 = 0)
    (hroot : ∀ᶠ h in 𝓝 (0 : ℝ),
      Fp_STR02916 (((h * A, h * B, h, h ^ 2 * s) : Par_STR02916), f h) = 0) : v = 0 := by
  set L := fderiv ℝ Fp_STR02916 ((0 : Par_STR02916), (0 : E_STR02969)) with hL
  have hFd : HasFDerivAt Fp_STR02916 L ((0 : Par_STR02916), (0 : E_STR02969)) :=
    ((Fp_smooth_STR02916.differentiable (by simp)) _).hasFDerivAt
  have hc := cur_hasDerivAt_STR02971 A B s
  have hpair : HasDerivAt
      (fun h : ℝ => (((h * A, h * B, h, h ^ 2 * s) : Par_STR02916), f h))
      (((A, B, 1, 0) : Par_STR02916), v) 0 := hc.prodMk hf
  have hcomp := hFd.comp_hasDerivAt_of_eq (0 : ℝ) hpair
    (by show ((0 : Par_STR02916), (0 : E_STR02969)) = _; rw [cur_zero_STR02971, hf0])
  have hz : (fun _ : ℝ => (0 : Y_STR02969)) =ᶠ[𝓝 (0 : ℝ)]
      (Fp_STR02916 ∘ fun h : ℝ => (((h * A, h * B, h, h ^ 2 * s) : Par_STR02916), f h)) :=
    hroot.mono (fun h hh => hh.symm)
  have h1 := hcomp.congr_of_eventuallyEq hz
  have hL1 : L (((A, B, 1, 0) : Par_STR02916), v) = 0 :=
    ((hasDerivAt_const (0 : ℝ) (0 : Y_STR02969)).unique h1).symm
  -- the same expansion with `v` replaced by `0`
  have hpair0 : HasDerivAt
      (fun h : ℝ => (((h * A, h * B, h, h ^ 2 * s) : Par_STR02916), (0 : E_STR02969)))
      (((A, B, 1, 0) : Par_STR02916), (0 : E_STR02969)) 0 :=
    hc.prodMk (hasDerivAt_const (0 : ℝ) (0 : E_STR02969))
  have hg : HasDerivAt
      (fun h : ℝ => Fp_STR02916 (((h * A, h * B, h, h ^ 2 * s) : Par_STR02916), (0 : E_STR02969)))
      (L (((A, B, 1, 0) : Par_STR02916), (0 : E_STR02969))) 0 :=
    hFd.comp_hasDerivAt_of_eq (0 : ℝ) hpair0
      (by show ((0 : Par_STR02916), (0 : E_STR02969)) = _; rw [cur_zero_STR02971])
  have hg0 : Fp_STR02916 ((((0 : ℝ) * A, (0 : ℝ) * B, (0 : ℝ), (0 : ℝ) ^ 2 * s) : Par_STR02916),
      (0 : E_STR02969)) = 0 := by
    rw [cur_zero_STR02971]
    exact Fp_zero_STR02916
  obtain ⟨r, hr, C, hC0, hCb⟩ := str029_70_explicit_order_two_forcing_weighted_variational_small
    (|A| + |B| + |s|)
  set F0 := forcingY_STR02970 A B 0 with hF0
  have hbd : ∀ h : ℝ, |h| < min r 1 →
      ‖Fp_STR02916 (((h * A, h * B, h, h ^ 2 * s) : Par_STR02916), (0 : E_STR02969))‖ ≤
        (C + ‖F0‖) * h ^ 2 := by
    intro h hh
    have hhr : |h| ≤ r := (lt_min_iff.1 hh).1.le
    have hh1 : |h| < 1 := (lt_min_iff.1 hh).2
    have hk := hCb A B s h 0 (by linarith [abs_nonneg B, abs_nonneg s])
      (by linarith [abs_nonneg A, abs_nonneg s]) (by linarith [abs_nonneg A, abs_nonneg B])
      (by simp; positivity) hhr
    rw [smul_zero] at hk
    have hsq : ‖h ^ 2 • F0‖ = h ^ 2 * ‖F0‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_pow, sq_abs]
    have h3 : |h| ^ 3 ≤ h ^ 2 := by
      have : |h| ^ 3 = |h| * h ^ 2 := by rw [← sq_abs h]; ring
      rw [this]
      nlinarith [abs_nonneg h, sq_nonneg h]
    calc ‖Fp_STR02916 (((h * A, h * B, h, h ^ 2 * s) : Par_STR02916), (0 : E_STR02969))‖
        = ‖(Rvar_STR02915 (h * A, h * B, h, h ^ 2 * s, 0) - h ^ 2 • F0) + h ^ 2 • F0‖ := by
          rw [sub_add_cancel]; rfl
      _ ≤ ‖Rvar_STR02915 (h * A, h * B, h, h ^ 2 * s, 0) - h ^ 2 • F0‖ + ‖h ^ 2 • F0‖ :=
          norm_add_le _ _
      _ ≤ C * |h| ^ 3 + h ^ 2 * ‖F0‖ := by rw [hsq]; gcongr
      _ ≤ C * h ^ 2 + h ^ 2 * ‖F0‖ := by gcongr
      _ = (C + ‖F0‖) * h ^ 2 := by ring
  have hL2 : L (((A, B, 1, 0) : Par_STR02916), (0 : E_STR02969)) = 0 :=
    deriv_eq_zero_of_sq_STR02971 hg hg0 (lt_min hr one_pos) hbd
  have hsplit : L (((A, B, 1, 0) : Par_STR02916), v) =
      L (((A, B, 1, 0) : Par_STR02916), (0 : E_STR02969)) +
        (L ∘L ContinuousLinearMap.inr ℝ Par_STR02916 E_STR02969) v := by
    rw [ContinuousLinearMap.comp_apply, ← map_add]
    simp
  rw [hL1, hL2, zero_add] at hsplit
  obtain ⟨e, he⟩ := Fp_inv_STR02916
  have hinj : Function.Injective (L ∘L ContinuousLinearMap.inr ℝ Par_STR02916 E_STR02969) := by
    rw [← he]
    exact e.injective
  exact hinj (hsplit.symm.trans (map_zero _).symm)

/-- Second order: if `f 0 = 0`, `f` is continuous at `0`, `f h = h² q + O(h³)` and
`Fp (cur h, f h) = 0` near `0`, then the explicit order-two forcing of `q` vanishes. -/
theorem forcing_zero_of_rangeeq_STR02971 (A B s : ℝ) {f : ℝ → E_STR02969} {q : E_STR02969}
    (hfc : ContinuousAt f 0) (hf0 : f 0 = 0)
    (hroot : ∀ᶠ h in 𝓝 (0 : ℝ),
      Fp_STR02916 (((h * A, h * B, h, h ^ 2 * s) : Par_STR02916), f h) = 0)
    {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hrem : ∀ h : ℝ, |h| ≤ r → ‖f h - h ^ 2 • q‖ ≤ M * |h| ^ 3) :
    forcingY_STR02970 A B q = 0 := by
  obtain ⟨Kl, t, ht, hLip⟩ :=
    ((Fp_smooth_STR02916.contDiffAt (x := ((0 : Par_STR02916), (0 : E_STR02969)))).of_le
      (by simp)).exists_lipschitzOnWith
  have hcc : Continuous (fun h : ℝ => ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916)) := by
    fun_prop
  have hc1 : ContinuousAt
      (fun h : ℝ => (((h * A, h * B, h, h ^ 2 * s) : Par_STR02916), f h)) 0 :=
    hcc.continuousAt.prodMk hfc
  have hc2 : ContinuousAt
      (fun h : ℝ => (((h * A, h * B, h, h ^ 2 * s) : Par_STR02916), h ^ 2 • q)) 0 :=
    hcc.continuousAt.prodMk (by fun_prop)
  have hv1 : ∀ᶠ h in 𝓝 (0 : ℝ),
      (((h * A, h * B, h, h ^ 2 * s) : Par_STR02916), f h) ∈ t :=
    hc1.preimage_mem_nhds (by
      show t ∈ 𝓝 (((0 : ℝ) * A, (0 : ℝ) * B, (0 : ℝ), (0 : ℝ) ^ 2 * s), f 0)
      rw [cur_zero_STR02971, hf0]
      exact ht)
  have hv2 : ∀ᶠ h in 𝓝 (0 : ℝ),
      (((h * A, h * B, h, h ^ 2 * s) : Par_STR02916), h ^ 2 • q) ∈ t :=
    hc2.preimage_mem_nhds (by
      show t ∈ 𝓝 (((0 : ℝ) * A, (0 : ℝ) * B, (0 : ℝ), (0 : ℝ) ^ 2 * s), (0 : ℝ) ^ 2 • q)
      have h0 : (0 : ℝ) ^ 2 • q = 0 := by simp
      rw [cur_zero_STR02971, h0]
      exact ht)
  obtain ⟨ε, hε, hεt⟩ := Metric.eventually_nhds_iff.1 (hv1.and (hv2.and hroot))
  obtain ⟨r2, hr2, Cc, hCc0, hCb⟩ := str029_70_explicit_order_two_forcing_weighted_variational_small
    (|A| + |B| + |s| + ‖q‖)
  have hρ : 0 < min (min (ε / 2) r) (min r2 1) :=
    lt_min (lt_min (by positivity) hr) (lt_min hr2 one_pos)
  refine eq_zero_of_le_mul_STR02971 (c := (Kl : ℝ) * M + Cc) (r := min (min (ε / 2) r) (min r2 1))
    (by positivity) hρ ?_
  intro τ hτ hτρ
  have hτ1 : τ ≤ ε / 2 := (hτρ.trans (min_le_left _ _)).trans (min_le_left _ _)
  have hτ2 : τ ≤ r := (hτρ.trans (min_le_left _ _)).trans (min_le_right _ _)
  have hτ3 : τ ≤ r2 := (hτρ.trans (min_le_right _ _)).trans (min_le_left _ _)
  have hτ4 : τ ≤ 1 := (hτρ.trans (min_le_right _ _)).trans (min_le_right _ _)
  have hτa : |τ| = τ := abs_of_pos hτ
  have hτε : dist τ 0 < ε := by
    rw [Real.dist_eq, sub_zero, hτa]
    linarith
  obtain ⟨hm1, hm2, hm3⟩ := hεt hτε
  have hrem' := hrem τ (by rw [hτa]; exact hτ2)
  rw [hτa] at hrem'
  have hlip : ‖Fp_STR02916 (((τ * A, τ * B, τ, τ ^ 2 * s) : Par_STR02916), τ ^ 2 • q)‖ ≤
      (Kl : ℝ) * ‖f τ - τ ^ 2 • q‖ := by
    have h := hLip.dist_le_mul _ hm2 _ hm1
    have e1 : dist (Fp_STR02916 (((τ * A, τ * B, τ, τ ^ 2 * s) : Par_STR02916), τ ^ 2 • q))
        (Fp_STR02916 (((τ * A, τ * B, τ, τ ^ 2 * s) : Par_STR02916), f τ)) =
        ‖Fp_STR02916 (((τ * A, τ * B, τ, τ ^ 2 * s) : Par_STR02916), τ ^ 2 • q)‖ := by
      rw [dist_eq_norm, hm3, sub_zero]
    have e2 : dist ((((τ * A, τ * B, τ, τ ^ 2 * s) : Par_STR02916), τ ^ 2 • q) :
        Par_STR02916 × E_STR02969) (((τ * A, τ * B, τ, τ ^ 2 * s) : Par_STR02916), f τ) =
        ‖f τ - τ ^ 2 • q‖ := by
      rw [Prod.dist_eq]
      dsimp only
      rw [dist_self, max_eq_right dist_nonneg, dist_eq_norm, norm_sub_rev]
    rw [e1, e2] at h
    exact h
  have hT := hCb A B s τ q (by linarith [abs_nonneg B, abs_nonneg s, norm_nonneg q])
    (by linarith [abs_nonneg A, abs_nonneg s, norm_nonneg q])
    (by linarith [abs_nonneg A, abs_nonneg B, norm_nonneg q])
    (by linarith [abs_nonneg A, abs_nonneg B, abs_nonneg s]) (by rw [hτa]; exact hτ3)
  rw [hτa] at hT
  set F := forcingY_STR02970 A B q with hF
  set Fa := Fp_STR02916 (((τ * A, τ * B, τ, τ ^ 2 * s) : Par_STR02916), τ ^ 2 • q) with hFa
  have hT' : ‖Fa - τ ^ 2 • F‖ ≤ Cc * τ ^ 3 := hT
  have hsq : ‖τ ^ 2 • F‖ = τ ^ 2 * ‖F‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_pow, sq_abs]
  have hmain : τ ^ 2 * ‖F‖ ≤ τ ^ 2 * (((Kl : ℝ) * M + Cc) * τ) := by
    calc τ ^ 2 * ‖F‖ = ‖τ ^ 2 • F‖ := hsq.symm
      _ = ‖Fa - (Fa - τ ^ 2 • F)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖Fa‖ + ‖Fa - τ ^ 2 • F‖ := norm_sub_le _ _
      _ ≤ (Kl : ℝ) * (M * τ ^ 3) + Cc * τ ^ 3 := by
          gcongr
          exact hlip.trans (by gcongr)
      _ = τ ^ 2 * (((Kl : ℝ) * M + Cc) * τ) := by ring
  exact le_of_mul_le_mul_left hmain (by positivity)

/-! ### The main statement -/

/-- **STR029.71.** Let `ψ` be a `C^∞` map on an open neighbourhood `U` of the origin of the
parameter space `ℝ⁴`, with values in the Hölder carrier `E`, such that `ψ 0 = 0` and `ψ p` solves
the range equation `R(p, ψ p) = 0` for every `p ∈ U` (for example the implicit graph of STR029.16).
Then for every compact set `K` of triples `(A, B, s)` there are `δ > 0` and `M ≥ 0` such that for
all `(A, B, s) ∈ K` the scaled curve `h ↦ ψ (h A, h B, h, h² s)` stays in the domain for `|h| ≤ δ`,
is `C^∞` on `[-δ, δ]`, vanishes at `0` together with its first derivative, has second derivative
`2 q_*(A, B)` at `0`, has third derivative of `E`-norm at most `M` on `[-δ, δ]`, and satisfies the
remainder bound `‖ψ (h A, h B, h, h² s) - h² q_*(A, B)‖_E ≤ M |h|³`. -/
theorem str029_71_scaled_implicit_derivatives_uniform_range_remainder
    {U : Set Par_STR02916} {ψ : Par_STR02916 → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : Par_STR02916) ∈ U) (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0)
    (hroot : ∀ p ∈ U, Rpar_STR02916 p (ψ p) = 0)
    {K : Set (ℝ × ℝ × ℝ)} (hK : IsCompact K) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ A B s : ℝ, (A, B, s) ∈ K →
      (∀ h : ℝ, |h| ≤ δ → ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916) ∈ U) ∧
      ContDiffOn ℝ ∞ (scaledCurve_STR02971 ψ A B s) (Set.Icc (-δ) δ) ∧
      scaledCurve_STR02971 ψ A B s 0 = 0 ∧
      deriv (scaledCurve_STR02971 ψ A B s) 0 = 0 ∧
      iteratedDeriv 2 (scaledCurve_STR02971 ψ A B s) 0 = (2 : ℝ) • qstar_STR02971 A B ∧
      (∀ h : ℝ, |h| ≤ δ → ‖iteratedDeriv 3 (scaledCurve_STR02971 ψ A B s) h‖ ≤ M) ∧
      (∀ h : ℝ, |h| ≤ δ →
        ‖scaledCurve_STR02971 ψ A B s h - h ^ 2 • qstar_STR02971 A B‖ ≤ M * |h| ^ 3) := by
  set W : Set ((ℝ × ℝ × ℝ) × ℝ) := {z | curZ_STR02971 z ∈ U} with hWdef
  have hW : IsOpen W := hU.preimage curZ_contDiff_STR02971.continuous
  set G : (ℝ × ℝ × ℝ) × ℝ → E_STR02969 := fun z => ψ (curZ_STR02971 z) with hGdef
  have hG : ContDiffOn ℝ ∞ G W :=
    hψ.comp curZ_contDiff_STR02971.contDiffOn (fun z hz => hz)
  have hD1 : ContDiffOn ℝ ∞ (Dh_STR02971 G) W := contDiffOn_Dh_STR02971 hG hW
  have hD2 : ContDiffOn ℝ ∞ (Dh_STR02971 (Dh_STR02971 G)) W := contDiffOn_Dh_STR02971 hD1 hW
  have hD3 : ContDiffOn ℝ ∞ (Dh_STR02971 (Dh_STR02971 (Dh_STR02971 G))) W :=
    contDiffOn_Dh_STR02971 hD2 hW
  have hKW : ∀ x ∈ K, (x, (0 : ℝ)) ∈ W := by
    intro x hx
    show curZ_STR02971 (x, 0) ∈ U
    have : curZ_STR02971 (x, 0) = 0 := by
      simp [curZ_STR02971, Prod.ext_iff]
    rw [this]
    exact h0U
  obtain ⟨δ, hδ, M, hM, hslab⟩ := uniform_slab_STR02971 hK hW hKW hD3.continuousOn
  refine ⟨δ, hδ, M, hM, ?_⟩
  intro A B s hAK
  set x : ℝ × ℝ × ℝ := (A, B, s) with hx
  set f : ℝ → E_STR02969 := scaledCurve_STR02971 ψ A B s with hf
  set O : Set ℝ := {y | (x, y) ∈ W} with hO
  have hOopen : IsOpen O := hW.preimage (by fun_prop : Continuous fun y : ℝ => (x, y))
  have hOδ : ∀ y : ℝ, |y| ≤ δ → y ∈ O := fun y hy => (hslab x hAK y hy).1
  have h0O : (0 : ℝ) ∈ O := hOδ 0 (by simpa using hδ.le)
  have hs1 : ∀ y ∈ O, HasDerivAt f (Dh_STR02971 G (x, y)) y :=
    fun y hy => hasDerivAt_slice_STR02971 hG hW hy
  have hs2 : ∀ y ∈ O, HasDerivAt (fun y => Dh_STR02971 G (x, y))
      (Dh_STR02971 (Dh_STR02971 G) (x, y)) y :=
    fun y hy => hasDerivAt_slice_STR02971 hD1 hW hy
  have hs3 : ∀ y ∈ O, HasDerivAt (fun y => Dh_STR02971 (Dh_STR02971 G) (x, y))
      (Dh_STR02971 (Dh_STR02971 (Dh_STR02971 G)) (x, y)) y :=
    fun y hy => hasDerivAt_slice_STR02971 hD2 hW hy
  have hit3 : ∀ y ∈ O, iteratedDeriv 3 f y =
      Dh_STR02971 (Dh_STR02971 (Dh_STR02971 G)) (x, y) := by
    intro y hy
    rw [iteratedDeriv_three_STR02971]
    exact deriv_deriv_deriv_slice_STR02971 hOopen hs1 hs2 hs3 hy
  have hit2 : iteratedDeriv 2 f 0 = Dh_STR02971 (Dh_STR02971 G) (x, 0) := by
    rw [iteratedDeriv_two_STR02971]
    exact deriv_deriv_slice_STR02971 hOopen hs1 hs2 h0O
  have hf0 : f 0 = 0 := by
    show ψ ((0 : ℝ) * A, (0 : ℝ) * B, (0 : ℝ), (0 : ℝ) ^ 2 * s) = 0
    rw [cur_zero_STR02971]
    exact hψ0
  have hrootO : ∀ᶠ y in 𝓝 (0 : ℝ),
      Fp_STR02916 (((y * A, y * B, y, y ^ 2 * s) : Par_STR02916), f y) = 0 :=
    Filter.eventually_of_mem (hOopen.mem_nhds h0O)
      (fun y hy => hroot ((y * A, y * B, y, y ^ 2 * s) : Par_STR02916) hy)
  have hD10 : Dh_STR02971 G (x, 0) = 0 :=
    deriv_zero_of_rangeeq_STR02971 A B s (hs1 0 h0O) hf0 hrootO
  have hrem : ∀ h : ℝ, |h| ≤ δ →
      ‖f h - h ^ 2 • ((1 / 2 : ℝ) • Dh_STR02971 (Dh_STR02971 G) (x, 0))‖ ≤ M * |h| ^ 3 :=
    fun h hh => taylor_remainder_STR02971 (f := f) (D1 := fun y => Dh_STR02971 G (x, y))
      (D2 := fun y => Dh_STR02971 (Dh_STR02971 G) (x, y))
      (D3 := fun y => Dh_STR02971 (Dh_STR02971 (Dh_STR02971 G)) (x, y)) hM hf0 hD10
      (fun y hy => hs1 y (hOδ y hy)) (fun y hy => hs2 y (hOδ y hy))
      (fun y hy => hs3 y (hOδ y hy)) (fun y hy => (hslab x hAK y hy).2) hh
  have hforce : forcingY_STR02970 A B ((1 / 2 : ℝ) • Dh_STR02971 (Dh_STR02971 G) (x, 0)) = 0 :=
    forcing_zero_of_rangeeq_STR02971 A B s (hs1 0 h0O).continuousAt hf0 hrootO hδ hM hrem
  have hq : (1 / 2 : ℝ) • Dh_STR02971 (Dh_STR02971 G) (x, 0) = qstar_STR02971 A B :=
    eq_of_forcingY_zero_STR02971 A B hforce (forcingY_qstar_STR02971 A B)
  have hD2q : Dh_STR02971 (Dh_STR02971 G) (x, 0) = (2 : ℝ) • qstar_STR02971 A B := by
    rw [← hq, smul_smul]
    norm_num
  have hcd : ContDiffOn ℝ ∞ f O :=
    hG.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun y hy => hy)
  refine ⟨fun h hh => (hslab x hAK h hh).1,
    hcd.mono (fun y hy => hOδ y (abs_le.2 ⟨hy.1, hy.2⟩)), hf0,
    ((hs1 0 h0O).deriv.trans hD10), hit2.trans hD2q, ?_, ?_⟩
  · intro h hh
    rw [hit3 h (hOδ h hh)]
    exact (hslab x hAK h hh).2
  · intro h hh
    rw [← hq]
    exact hrem h hh

/-- **STR029.71, graph form.** For the implicit graph `ψ : U → V` of the range equation
(STR029.16), the conclusion of `str029_71_scaled_implicit_derivatives_uniform_range_remainder`
holds for every compact set of triples `(A, B, s)`. -/
theorem str029_71_scaled_implicit_derivatives_uniform_range_remainder_graph :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K →
        ∃ δ : ℝ, 0 < δ ∧ ∃ M : ℝ, 0 ≤ M ∧ ∀ A B s : ℝ, (A, B, s) ∈ K →
          (∀ h : ℝ, |h| ≤ δ → ((h * A, h * B, h, h ^ 2 * s) : Par_STR02916) ∈ U) ∧
          ContDiffOn ℝ ∞ (scaledCurve_STR02971 ψ A B s) (Set.Icc (-δ) δ) ∧
          scaledCurve_STR02971 ψ A B s 0 = 0 ∧
          deriv (scaledCurve_STR02971 ψ A B s) 0 = 0 ∧
          iteratedDeriv 2 (scaledCurve_STR02971 ψ A B s) 0 = (2 : ℝ) • qstar_STR02971 A B ∧
          (∀ h : ℝ, |h| ≤ δ → ‖iteratedDeriv 3 (scaledCurve_STR02971 ψ A B s) h‖ ≤ M) ∧
          (∀ h : ℝ, |h| ≤ δ →
            ‖scaledCurve_STR02971 ψ A B s h - h ^ 2 • qstar_STR02971 A B‖ ≤ M * |h| ^ 3) := by
  obtain ⟨U, V, ψ, hU, h0U, hV, h0V, hψ, hψ0, hψV, hiff, -⟩ :=
    str029_16_unique_smooth_range_graph
  refine ⟨U, V, ψ, hU, h0U, hV, h0V, hψ, hψ0, hψV, hiff, ?_⟩
  intro K hK
  exact str029_71_scaled_implicit_derivatives_uniform_range_remainder hU h0U hψ hψ0
    (fun p hp => (hiff p hp (ψ p) (hψV p hp)).2 rfl) hK

end DGPS.Frontier.STR029
