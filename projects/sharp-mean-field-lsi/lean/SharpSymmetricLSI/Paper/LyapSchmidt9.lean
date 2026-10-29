import Mathlib

/-!
# Section 4.2 (lane s42; R14): a reduced energy satisfying PL vanishes

Manuscript, text after (4.6): if `φ ≥ 0` near `0`, `φ(0) = 0` is not needed beyond `∇φ(0) = 0`,
`∇φ` is `L`-Lipschitz on a ball, and `c φ ≤ |∇φ|²` with `2L < c`, then `φ = 0` on a smaller
ball. (For `|x| < r/2`, `y = x - ∇φ(x)/L` stays in the ball and the descent lemma gives
`0 ≤ φ(y) ≤ φ(x) - |∇φ(x)|²/(2L)`, so `c φ ≤ |∇φ|² ≤ 2L φ`.) The gradient is encoded as
`b : E → E` with `Dφ(x) v = ⟪b x, v⟫`.
-/

noncomputable section
open Metric Set

namespace SharpLSI

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The descent lemma on a convex set. -/
theorem descent_lemma {Φ : E → ℝ} {b : E → E} {s : Set E} (hs : Convex ℝ s) {L : ℝ}
    (hd : ∀ x ∈ s, HasFDerivAt Φ (innerSL ℝ (b x)) x)
    (hbL : ∀ x ∈ s, ∀ y ∈ s, ‖b x - b y‖ ≤ L * ‖x - y‖) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    Φ y ≤ Φ x + inner ℝ (b x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set v := y - x with hv
  have hseg : ∀ t ∈ Icc (0 : ℝ) 1, x + t • v ∈ s := fun t ht => by
    have := hs.add_smul_sub_mem hx hy ht
    simpa [hv] using this
  set q : ℝ → ℝ := fun t => Φ (x + t • v) - t * inner ℝ (b x) v - L * t ^ 2 * ‖v‖ ^ 2 / 2 with hq
  have hgd : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun t => Φ (x + t • v)) (inner ℝ (b (x + t • v)) v) t := fun t ht => by
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have := (hd _ (hseg t ht)).comp_hasDerivAt t h1
    rw [innerSL_apply_apply] at this
    exact this
  have hqd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt q
      (inner ℝ (b (x + t • v)) v - inner ℝ (b x) v - L * t * ‖v‖ ^ 2) t := fun t ht => by
    have h1 := hgd t ht
    have h2 : HasDerivAt (fun t : ℝ => t * inner ℝ (b x) v) (inner ℝ (b x) v) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (b x) v)
    have h3 : HasDerivAt (fun t : ℝ => L * t ^ 2 * ‖v‖ ^ 2 / 2) (L * t * ‖v‖ ^ 2) t := by
      have := (((hasDerivAt_pow 2 t).const_mul L).mul_const (‖v‖ ^ 2)).div_const 2
      convert this using 1; push_cast; ring
    exact (h1.sub h2).sub h3
  have hqn : ∀ t ∈ interior (Icc (0 : ℝ) 1),
      inner ℝ (b (x + t • v)) v - inner ℝ (b x) v - L * t * ‖v‖ ^ 2 ≤ 0 := fun t ht => by
    rw [interior_Icc] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    have h1 : inner ℝ (b (x + t • v)) v - inner ℝ (b x) v = inner ℝ (b (x + t • v) - b x) v :=
      (inner_sub_left _ _ _).symm
    have h2 : inner ℝ (b (x + t • v) - b x) v ≤ ‖b (x + t • v) - b x‖ * ‖v‖ :=
      real_inner_le_norm _ _
    have h3 : ‖b (x + t • v) - b x‖ ≤ L * (t * ‖v‖) := by
      have := hbL _ (hseg t ht') x hx
      simpa [norm_smul, abs_of_nonneg ht'.1] using this
    have hv0 := norm_nonneg v
    nlinarith [mul_le_mul_of_nonneg_right h3 hv0]
  have hanti : AntitoneOn q (Icc 0 1) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) ?_ ?_ hqn
    · exact fun t ht => (hqd t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hqd t (interior_subset ht)).hasDerivWithinAt
  have := hanti (left_mem_Icc.mpr zero_le_one) (right_mem_Icc.mpr zero_le_one) zero_le_one
  simp only [hq, zero_smul, add_zero, zero_mul, sub_zero, one_smul, one_mul, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div, one_pow] at this
  rw [hv, add_sub_cancel] at this
  linarith

/-- **PL with a small Lipschitz gradient forces vanishing.** -/
theorem eq_zero_of_PL {Φ : E → ℝ} {b : E → E} {r L c : ℝ} (hL : 0 < L) (hLc : 2 * L < c)
    (hΦ0 : ∀ x ∈ ball (0 : E) r, 0 ≤ Φ x)
    (hd : ∀ x ∈ ball (0 : E) r, HasFDerivAt Φ (innerSL ℝ (b x)) x)
    (hb0 : b 0 = 0) (hbL : ∀ x ∈ ball (0 : E) r, ∀ y ∈ ball (0 : E) r, ‖b x - b y‖ ≤ L * ‖x - y‖)
    (hPL : ∀ x ∈ ball (0 : E) r, c * Φ x ≤ ‖b x‖ ^ 2) :
    ∀ x ∈ ball (0 : E) (r / 2), Φ x = 0 := by
  intro x hx
  rw [mem_ball_zero_iff] at hx
  have hr : 0 < r := by linarith [norm_nonneg x]
  have hxr : x ∈ ball (0 : E) r := by rw [mem_ball_zero_iff]; linarith
  have h0r : (0 : E) ∈ ball (0 : E) r := mem_ball_self hr
  have hbx : ‖b x‖ ≤ L * ‖x‖ := by
    have := hbL x hxr 0 h0r
    rwa [hb0, sub_zero, sub_zero] at this
  set y := x - (1 / L) • b x with hy
  have hyr : y ∈ ball (0 : E) r := by
    rw [mem_ball_zero_iff, hy]
    calc ‖x - (1 / L) • b x‖ ≤ ‖x‖ + ‖(1 / L) • b x‖ := norm_sub_le _ _
      _ = ‖x‖ + 1 / L * ‖b x‖ := by rw [norm_smul, Real.norm_of_nonneg (by positivity)]
      _ ≤ ‖x‖ + 1 / L * (L * ‖x‖) := by gcongr
      _ = 2 * ‖x‖ := by field_simp; ring
      _ < r := by linarith
  have hdes := descent_lemma (convex_ball (0 : E) r) hd hbL hxr hyr
  have hyx : y - x = -((1 / L) • b x) := by rw [hy]; abel
  rw [hyx, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq, norm_neg,
    norm_smul, Real.norm_of_nonneg (by positivity)] at hdes
  have hΦy := hΦ0 y hyr
  have hkey : ‖b x‖ ^ 2 ≤ 2 * L * Φ x := by
    have e : Φ x + -(1 / L * ‖b x‖ ^ 2) + L / 2 * (1 / L * ‖b x‖) ^ 2 =
        Φ x - ‖b x‖ ^ 2 / (2 * L) := by field_simp; ring
    rw [e] at hdes
    have := le_trans hΦy hdes
    rw [sub_nonneg, div_le_iff₀ (by positivity)] at this
    linarith
  have h1 := hPL x hxr
  have h2 := hΦ0 x hxr
  nlinarith

end SharpLSI
