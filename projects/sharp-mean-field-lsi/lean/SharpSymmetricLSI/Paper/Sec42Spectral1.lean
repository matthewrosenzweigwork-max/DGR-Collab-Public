import Mathlib

/-!
# Section 4.2 (lane s42; R15): nondegenerate ⇒ coercive for `I + compact`

Manuscript, end of the contraction argument: "Since `I + T ≥ 0` is the identity plus a compact
selfadjoint operator [and `ker(I+T) = 0`], there exists `σ > 0` such that `I + T ≥ σ I`" (4.13).

Abstract form: in a real Hilbert space, let `A = 1 + R + F` with `‖R‖ < 1` and `F` of finite
rank, `M` a closed subspace (a predicate `P`), `A` symmetric and nonnegative on `M`, mapping `M`
into itself, with `⟨u, A u⟩ = 0 ⇒ u = 0` on `M`. Then `⟨u, A u⟩ ≥ σ ‖u‖²` on `M` for some
`σ > 0`. (A minimizing unit sequence has `A uₖ → 0`; `F uₖ` has a convergent subsequence in the
finite-dimensional range, hence so has `uₖ = (1+R)⁻¹(A uₖ - F uₖ)`; its limit is a unit vector
of `M` with `⟨u, A u⟩ = 0`.)
-/

noncomputable section
open Filter Topology

namespace SharpLSI

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

/-- Cauchy–Schwarz for a symmetric nonnegative form on a subspace. -/
theorem inner_sq_le_of_nonneg {A : H →L[ℝ] H} {P : H → Prop}
    (hP : ∀ u v (t : ℝ), P u → P v → P (v + t • u))
    (hsymm : ∀ u v, P u → P v → ⟪v, A u⟫ = ⟪u, A v⟫)
    (hpos : ∀ u, P u → 0 ≤ ⟪u, A u⟫) {u v : H} (hu : P u) (hv : P v) :
    ⟪v, A u⟫ ^ 2 ≤ ⟪v, A v⟫ * ⟪u, A u⟫ := by
  have h : ∀ t : ℝ, 0 ≤ ⟪u, A u⟫ * (t * t) + 2 * ⟪v, A u⟫ * t + ⟪v, A v⟫ := fun t => by
    have := hpos (v + t • u) (hP u v t hu hv)
    simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, RCLike.conj_to_real] at this
    rw [← hsymm u v hu hv] at this
    nlinarith [this]
  have := discrim_le_zero h
  unfold discrim at this
  nlinarith [this]

/-- `‖A u‖² ≤ ‖A‖ ⟨u, A u⟩` on `M`. -/
theorem norm_sq_apply_le {A : H →L[ℝ] H} {P : H → Prop}
    (hP : ∀ u v (t : ℝ), P u → P v → P (v + t • u)) (hAP : ∀ u, P u → P (A u))
    (hsymm : ∀ u v, P u → P v → ⟪v, A u⟫ = ⟪u, A v⟫)
    (hpos : ∀ u, P u → 0 ≤ ⟪u, A u⟫) {u : H} (hu : P u) :
    ‖A u‖ ^ 2 ≤ ‖A‖ * ⟪u, A u⟫ := by
  have h1 := inner_sq_le_of_nonneg hP hsymm hpos hu (hAP u hu)
  rw [real_inner_self_eq_norm_sq] at h1
  have h2 : ⟪A u, A (A u)⟫ ≤ ‖A‖ * ‖A u‖ ^ 2 := by
    calc ⟪A u, A (A u)⟫ ≤ ‖A u‖ * ‖A (A u)‖ := real_inner_le_norm _ _
      _ ≤ ‖A u‖ * (‖A‖ * ‖A u‖) := mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
      _ = ‖A‖ * ‖A u‖ ^ 2 := by ring
  have h3 := hpos u hu
  have h4 : ‖A u‖ ^ 2 * ‖A u‖ ^ 2 ≤ ‖A‖ * ‖A u‖ ^ 2 * ⟪u, A u⟫ := by
    calc ‖A u‖ ^ 2 * ‖A u‖ ^ 2 = (‖A u‖ ^ 2) ^ 2 := by ring
      _ ≤ ⟪A u, A (A u)⟫ * ⟪u, A u⟫ := h1
      _ ≤ ‖A‖ * ‖A u‖ ^ 2 * ⟪u, A u⟫ := mul_le_mul_of_nonneg_right h2 h3
  rcases (sq_nonneg ‖A u‖).eq_or_lt with h5 | h5
  · rw [← h5]; exact mul_nonneg (norm_nonneg _) h3
  · nlinarith

/-- **Nondegenerate ⇒ coercive** for `1 + R + F`, `‖R‖ < 1`, `F` of finite rank. -/
theorem exists_coercive {R F : H →L[ℝ] H} (hR : ‖R‖ < 1)
    (hF : FiniteDimensional ℝ (LinearMap.range (F : H →ₗ[ℝ] H))) {P : H → Prop}
    (hPc : IsClosed {u | P u}) (hP : ∀ u v (t : ℝ), P u → P v → P (v + t • u))
    (hAP : ∀ u, P u → P ((1 + R + F) u))
    (hsymm : ∀ u v, P u → P v → ⟪v, (1 + R + F) u⟫ = ⟪u, (1 + R + F) v⟫)
    (hpos : ∀ u, P u → 0 ≤ ⟪u, (1 + R + F) u⟫)
    (hdef : ∀ u, P u → ⟪u, (1 + R + F) u⟫ = 0 → u = 0) :
    ∃ σ : ℝ, 0 < σ ∧ ∀ u, P u → σ * ‖u‖ ^ 2 ≤ ⟪u, (1 + R + F) u⟫ := by
  set A : H →L[ℝ] H := 1 + R + F with hA
  by_contra hcon
  push_neg at hcon
  -- a minimizing unit sequence
  have hseq : ∀ k : ℕ, ∃ v : H, P v ∧ ‖v‖ = 1 ∧ ⟪v, A v⟫ < 1 / ((k : ℝ) + 1) := by
    intro k
    obtain ⟨u, hu, hlt⟩ := hcon (1 / ((k : ℝ) + 1)) (by positivity)
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at hlt
    have hn : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    refine ⟨‖u‖⁻¹ • u, ?_, ?_, ?_⟩
    · have := hP u 0 (‖u‖⁻¹) hu (by simpa using hP u u (-1) hu hu)
      simpa using this
    · rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hn.le), inv_mul_cancel₀ hn.ne']
    · rw [map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
      have h2 : ‖u‖⁻¹ * (‖u‖⁻¹ * ⟪u, A u⟫) = ⟪u, A u⟫ / ‖u‖ ^ 2 := by
        field_simp
      rw [h2, div_lt_iff₀ (by positivity)]
      linarith
  choose v hvP hv1 hvA using hseq
  have hvA0 : ∀ k, 0 ≤ ⟪v k, A (v k)⟫ := fun k => hpos _ (hvP k)
  have htend0 : Tendsto (fun k => ⟪v k, A (v k)⟫) atTop (𝓝 0) := by
    refine squeeze_zero hvA0 (fun k => (hvA k).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- `A vₖ → 0`
  have hAv : Tendsto (fun k => A (v k)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h1 : ∀ k, ‖A (v k)‖ ≤ Real.sqrt (‖A‖ * ⟪v k, A (v k)⟫) := fun k =>
      Real.le_sqrt_of_sq_le (norm_sq_apply_le hP hAP hsymm hpos (hvP k))
    refine squeeze_zero (fun k => norm_nonneg _) h1 ?_
    have := (htend0.const_mul ‖A‖).sqrt
    simpa using this
  -- `F vₖ` has a convergent subsequence
  set V := LinearMap.range (F : H →ₗ[ℝ] H)
  have hFv : ∀ k, (F : H →ₗ[ℝ] H) (v k) ∈ V := fun k => ⟨v k, rfl⟩
  set w : ℕ → V := fun k => ⟨F (v k), hFv k⟩
  have hwb : ∀ k, w k ∈ Metric.closedBall (0 : V) ‖F‖ := fun k => by
    rw [Metric.mem_closedBall, dist_zero_right]
    show ‖F (v k)‖ ≤ ‖F‖
    calc ‖F (v k)‖ ≤ ‖F‖ * ‖v k‖ := F.le_opNorm _
      _ = ‖F‖ := by rw [hv1, mul_one]
  obtain ⟨w₀, -, φs, hφs, hw⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hwb
  have hFw : Tendsto (fun k => F (v (φs k))) atTop (𝓝 (w₀ : H)) :=
    (continuous_subtype_val.tendsto _).comp hw
  -- `(1 + R) vₖ → -w₀`
  have h1R : Tendsto (fun k => (1 + R) (v (φs k))) atTop (𝓝 (-(w₀ : H))) := by
    have := (hAv.comp hφs.tendsto_atTop).sub hFw
    simp only [zero_sub] at this
    refine this.congr fun k => ?_
    simp [hA, ContinuousLinearMap.add_apply]
  set B : (H →L[ℝ] H)ˣ := Units.oneSub (-R) (by rwa [norm_neg]) with hBdef
  have hB : (B : H →L[ℝ] H) = 1 + R := by rw [hBdef, Units.val_oneSub, sub_neg_eq_add]
  have hvB : ∀ k, v (φs k) = (↑B⁻¹ : H →L[ℝ] H) ((1 + R) (v (φs k))) := fun k => by
    rw [← hB, ← ContinuousLinearMap.mul_apply, B.inv_mul, ContinuousLinearMap.one_apply]
  set vlim := (↑B⁻¹ : H →L[ℝ] H) (-(w₀ : H))
  have hconv : Tendsto (fun k => v (φs k)) atTop (𝓝 vlim) := by
    have := ((↑B⁻¹ : H →L[ℝ] H).continuous.tendsto _).comp h1R
    exact this.congr fun k => (hvB k).symm
  -- the limit
  have hPlim : P vlim := hPc.mem_of_tendsto hconv (Eventually.of_forall fun k => hvP (φs k))
  have hnlim : ‖vlim‖ = 1 := by
    have := (continuous_norm.tendsto _).comp hconv
    have h' : Tendsto (fun k => ‖v (φs k)‖) atTop (𝓝 1) := by simp [hv1]
    exact tendsto_nhds_unique this h'
  have hQlim : ⟪vlim, A vlim⟫ = 0 := by
    have hc : Continuous fun u : H => ⟪u, A u⟫ := continuous_id.inner A.continuous
    have := (hc.tendsto _).comp hconv
    exact tendsto_nhds_unique this (htend0.comp hφs.tendsto_atTop)
  have := hdef vlim hPlim hQlim
  rw [this, norm_zero] at hnlim
  exact zero_ne_one hnlim

end SharpLSI
