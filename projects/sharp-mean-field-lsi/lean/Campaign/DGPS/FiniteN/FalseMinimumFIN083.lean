import DGPS.FiniteN.FalseMinimumFIN082
import DGPS.Foundations.Entropy

/-!
# FIN083: the entropy factor `N` and the variance of the false-minimum branch cutoff

In the setting of FIN082 (`κ > 2`, `0 < h < h_c(κ)`, the roots `s1, s2, tp` of
`FalseMinimumGeometryFIN076`, `G = G_- = ψ(-s2) - ψ(tp) > 0`, a fixed small `δ`, and a smooth
cutoff `χ` with `0 ≤ χ ≤ 1`, `χ = 1` on `m ≤ m_b - δ`, `χ = 0` on `m ≥ m_b + δ`), put
`f_N = χ (m_N)` and `n_N = P_N(f_N²)`.  Then

* `Ent_{P_N}(f_N²) = -n_N log n_N + P_N(f_N² log f_N²)` exactly, and the correction term is bounded
  in absolute value by the transition probability `P_N(m_N ∈ [m_b - δ, m_b + δ])`, which is
  exponentially smaller than `n_N`;
* `Ent_{P_N}(f_N²) = N G n_N (1 + o(1))`;
* `Var_{P_N}(f_N) = n_N (1 + o(1))`.

The main theorem is `DGPS.FiniteN.false_minimum_branch_entropy_factor_n`.
-/

open MeasureTheory Filter Topology
open scoped ContDiff ENNReal
open DGPS.Circle.BesselMoments DGPS.FiniteN.EmpiricalCosineCramerFIN080
  DGPS.FiniteN.FalseMinimumFIN081 DGPS.FiniteN.FalseMinimumFIN082
  DGPS.FiniteN.FalseMinimumFIN076 DGPS.Models DGPS.FiniteN.ScalarFoldFIN056

namespace DGPS.FiniteN.FalseMinimumFIN083

section Measure

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

theorem mul_log_abs_le_FIN083 {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : |y * Real.log y| ≤ 1 := by
  rcases h0.eq_or_lt with h | hy
  · rw [← h]; simp
  · have hl : Real.log y ≤ 0 := Real.log_nonpos h0 h1
    have hge : 1 - y⁻¹ ≤ Real.log y := Real.one_sub_inv_le_log_of_pos hy
    have h2 := mul_le_mul_of_nonneg_left hge hy.le
    have h3 : y * (1 - y⁻¹) = y - 1 := by field_simp
    rw [abs_le]
    constructor
    · linarith
    · nlinarith

theorem integrable_sq_FIN083 {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) : Integrable (fun x => F x ^ 2) P := by
  refine Integrable.of_bound (hF.pow_const 2).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have := h0 x
  have := h1 x
  nlinarith

theorem integrable_sq_log_FIN083 {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) : Integrable (fun x => F x ^ 2 * Real.log (F x ^ 2)) P := by
  refine Integrable.of_bound
    ((hF.pow_const 2).mul (Real.measurable_log.comp (hF.pow_const 2))).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  refine mul_log_abs_le_FIN083 (sq_nonneg _) ?_
  have := h0 x
  have := h1 x
  nlinarith

/-- The entropy of `F²` is `ofReal (P(F² log F²) - n log n)` with `n = P(F²)`. -/
theorem entropy_formula_FIN083 {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) :
    homogeneousEntropy P (fun x => F x ^ 2) =
      ENNReal.ofReal (-((∫ x, F x ^ 2 ∂P) * Real.log (∫ x, F x ^ 2 ∂P))
        + ∫ x, F x ^ 2 * Real.log (F x ^ 2) ∂P) := by
  rw [homogeneousEntropy_eq_formula (Filter.Eventually.of_forall fun x => sq_nonneg (F x))
    (integrable_sq_FIN083 hF h0 h1) (integrable_sq_log_FIN083 hF h0 h1)]
  congr 1
  ring

/-- The `f² log f²` correction is bounded by the probability of the set where `f ∉ {0, 1}`. -/
theorem neg_term_bound_FIN083 {F : Ω → ℝ} (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) {T : Set Ω} (hT : MeasurableSet T)
    (hTF : ∀ x, x ∉ T → F x = 0 ∨ F x = 1) :
    |∫ x, F x ^ 2 * Real.log (F x ^ 2) ∂P| ≤ (P T).toReal := by
  have hint : Integrable (T.indicator fun _ : Ω => (1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hT
  have h1' : ∫ x, T.indicator (fun _ : Ω => (1 : ℝ)) x ∂P = (P T).toReal := by
    rw [integral_indicator hT]; simp [measureReal_def]
  rw [← h1', ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ T
  · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]
    refine mul_log_abs_le_FIN083 (sq_nonneg _) ?_
    have := h0 x
    have := h1 x
    nlinarith
  · rw [Set.indicator_of_notMem hx, Real.norm_eq_abs]
    rcases hTF x hx with h | h <;> simp [h]

/-- Cauchy–Schwarz: `(P F)² ≤ P(S) P(F²)` for `F` supported in `S`. -/
theorem sq_integral_le_FIN083 {F : Ω → ℝ} (hF : Measurable F) (h0 : ∀ x, 0 ≤ F x)
    (h1 : ∀ x, F x ≤ 1) {S : Set Ω} (hS : MeasurableSet S) (hSF : ∀ x, x ∉ S → F x = 0) :
    (∫ x, F x ∂P) ^ 2 ≤ (P S).toReal * ∫ x, F x ^ 2 ∂P := by
  have hi1 : Integrable F P := by
    refine Integrable.of_bound hF.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]; exact h1 x
  have hi2 := integrable_sq_FIN083 (P := P) hF h0 h1
  have hiS : Integrable (S.indicator fun _ : Ω => (1 : ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hS
  have hS' : ∫ x, S.indicator (fun _ : Ω => (1 : ℝ)) x ∂P = (P S).toReal := by
    rw [integral_indicator hS]; simp [measureReal_def]
  have key : ∀ t : ℝ, 0 ≤ (P S).toReal * (t * t) + (-2 * ∫ x, F x ∂P) * t + ∫ x, F x ^ 2 ∂P := by
    intro t
    have hpt : ∀ x, 0 ≤ F x ^ 2 - 2 * t * F x + t ^ 2 * S.indicator (fun _ : Ω => (1 : ℝ)) x := by
      intro x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]; nlinarith [sq_nonneg (F x - t)]
      · rw [Set.indicator_of_notMem hx, hSF x hx]; simp
    have hnn : 0 ≤ ∫ x, (F x ^ 2 - 2 * t * F x
        + t ^ 2 * S.indicator (fun _ : Ω => (1 : ℝ)) x) ∂P := integral_nonneg hpt
    have hint : ∫ x, (F x ^ 2 - 2 * t * F x + t ^ 2 * S.indicator (fun _ : Ω => (1 : ℝ)) x) ∂P
        = ∫ x, F x ^ 2 ∂P - 2 * t * ∫ x, F x ∂P + t ^ 2 * (P S).toReal := by
      have hA : Integrable (fun x => F x ^ 2 - 2 * t * F x) P := hi2.sub (hi1.const_mul _)
      have hB : Integrable (fun x => t ^ 2 * S.indicator (fun _ : Ω => (1 : ℝ)) x) P :=
        hiS.const_mul _
      rw [integral_add hA hB, integral_sub hi2 (hi1.const_mul _), integral_const_mul,
        integral_const_mul, hS']
    rw [hint] at hnn
    nlinarith
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

end Measure

section Asymptotics

theorem tendsto_exp_mul_FIN083 {d : ℝ} (hd : d < 0) :
    Tendsto (fun N : ℕ+ => Real.exp ((N : ℝ) * d)) atTop (𝓝 0) :=
  Real.tendsto_exp_atBot.comp
    ((tendsto_natCast_atTop_atTop.comp tendsto_PNat_val_atTop_atTop).atTop_mul_const_of_neg hd)

variable {n p : ℕ+ → ℝ} {G : ℝ}

theorem eventually_pos_FIN083 (hn0 : ∀ N, 0 ≤ n N) (hG : 0 < G)
    (ht : Tendsto (fun N : ℕ+ => ((N : ℝ)⁻¹) * Real.log (n N)) atTop (𝓝 (-G))) :
    ∀ᶠ N : ℕ+ in atTop, 0 < n N := by
  have hev : ∀ᶠ N : ℕ+ in atTop, ((N : ℝ)⁻¹) * Real.log (n N) < 0 :=
    ht.eventually (gt_mem_nhds (by linarith))
  filter_upwards [hev] with N hN
  rcases (hn0 N).eq_or_lt with h | h
  · rw [← h] at hN; simp at hN
  · exact h

theorem exp_lt_FIN083 (hn0 : ∀ N, 0 ≤ n N) (hG : 0 < G)
    (ht : Tendsto (fun N : ℕ+ => ((N : ℝ)⁻¹) * Real.log (n N)) atTop (𝓝 (-G))) {c : ℝ}
    (hc : c < -G) : ∀ᶠ N : ℕ+ in atTop, Real.exp ((N : ℝ) * c) < n N := by
  have hev := ht.eventually (lt_mem_nhds hc)
  filter_upwards [hev, eventually_pos_FIN083 hn0 hG ht] with N hN hpos
  have hNp : (0 : ℝ) < N := by positivity
  have h1 : (N : ℝ) * c < Real.log (n N) := by
    have := mul_lt_mul_of_pos_left hN hNp
    rwa [← mul_assoc, mul_inv_cancel₀ hNp.ne', one_mul] at this
  rwa [Real.lt_log_iff_exp_lt hpos] at h1

theorem lt_exp_FIN083 (hn0 : ∀ N, 0 ≤ n N) (hG : 0 < G)
    (ht : Tendsto (fun N : ℕ+ => ((N : ℝ)⁻¹) * Real.log (n N)) atTop (𝓝 (-G))) {c : ℝ}
    (hc : -G < c) : ∀ᶠ N : ℕ+ in atTop, n N < Real.exp ((N : ℝ) * c) := by
  have hev := ht.eventually (gt_mem_nhds hc)
  filter_upwards [hev, eventually_pos_FIN083 hn0 hG ht] with N hN hpos
  have hNp : (0 : ℝ) < N := by positivity
  have h1 : Real.log (n N) < (N : ℝ) * c := by
    have := mul_lt_mul_of_pos_left hN hNp
    rwa [← mul_assoc, mul_inv_cancel₀ hNp.ne', one_mul] at this
  rwa [Real.log_lt_iff_lt_exp hpos] at h1

theorem tendsto_zero_of_exp_FIN083 (hp0 : ∀ N, 0 ≤ p N) {c : ℝ} (hc : c < 0)
    (hpc : ∀ᶠ N : ℕ+ in atTop, p N ≤ Real.exp ((N : ℝ) * c)) : Tendsto p atTop (𝓝 0) :=
  squeeze_zero' (Filter.Eventually.of_forall hp0) hpc (tendsto_exp_mul_FIN083 hc)

theorem tendsto_n_zero_FIN083 (hn0 : ∀ N, 0 ≤ n N) (hG : 0 < G)
    (ht : Tendsto (fun N : ℕ+ => ((N : ℝ)⁻¹) * Real.log (n N)) atTop (𝓝 (-G))) :
    Tendsto n atTop (𝓝 0) :=
  tendsto_zero_of_exp_FIN083 hn0 (c := -G / 2) (by linarith)
    ((lt_exp_FIN083 hn0 hG ht (c := -G / 2) (by linarith)).mono fun _ h => h.le)

theorem ratio_tendsto_FIN083 (hn0 : ∀ N, 0 ≤ n N) (hG : 0 < G)
    (ht : Tendsto (fun N : ℕ+ => ((N : ℝ)⁻¹) * Real.log (n N)) atTop (𝓝 (-G))) {c : ℝ}
    (hc : c < -G) (hp0 : ∀ N, 0 ≤ p N)
    (hpc : ∀ᶠ N : ℕ+ in atTop, p N ≤ Real.exp ((N : ℝ) * c)) :
    Tendsto (fun N => p N / n N) atTop (𝓝 0) := by
  have hc' : (c + -G) / 2 < -G := by linarith
  have hcc : c < (c + -G) / 2 := by linarith
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => div_nonneg (hp0 N) (hn0 N)) ?_
    (tendsto_exp_mul_FIN083 (d := c - (c + -G) / 2) (by linarith))
  filter_upwards [hpc, exp_lt_FIN083 hn0 hG ht hc'] with N h1 h2
  calc p N / n N ≤ Real.exp ((N : ℝ) * c) / Real.exp ((N : ℝ) * ((c + -G) / 2)) :=
        div_le_div₀ (Real.exp_pos _).le h1 (Real.exp_pos _) h2.le
    _ = Real.exp ((N : ℝ) * (c - (c + -G) / 2)) := by
        rw [← Real.exp_sub]; congr 1; ring

theorem entropy_ratio_FIN083 {L : ℕ+ → ℝ} (hn0 : ∀ N, 0 ≤ n N) (hG : 0 < G)
    (ht : Tendsto (fun N : ℕ+ => ((N : ℝ)⁻¹) * Real.log (n N)) atTop (𝓝 (-G))) {c : ℝ}
    (hc : c < -G) (hp0 : ∀ N, 0 ≤ p N)
    (hpc : ∀ᶠ N : ℕ+ in atTop, p N ≤ Real.exp ((N : ℝ) * c)) (hL : ∀ N, |L N| ≤ p N) :
    Tendsto (fun N : ℕ+ => (-(n N * Real.log (n N)) + L N) / ((N : ℝ) * G * n N)) atTop
      (𝓝 1) := by
  have hpos := eventually_pos_FIN083 hn0 hG ht
  have hrat := ratio_tendsto_FIN083 hn0 hG ht hc hp0 hpc
  have hA : Tendsto (fun N : ℕ+ => -(((N : ℝ)⁻¹) * Real.log (n N)) / G) atTop (𝓝 1) := by
    have := (ht.neg).div_const G
    rwa [neg_neg, div_self hG.ne'] at this
  have hB : Tendsto (fun N : ℕ+ => L N / ((N : ℝ) * G * n N)) atTop (𝓝 0) := by
    have hr2 : Tendsto (fun N => p N / n N / G) atTop (𝓝 0) := by
      simpa using hrat.div_const G
    refine squeeze_zero_norm' (a := fun N => p N / n N / G) ?_ hr2
    filter_upwards [hpos] with N hN
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast N.pos
    have hGn : 0 < G * n N := mul_pos hG hN
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : 0 < (N : ℝ) * G * n N)]
    calc |L N| / ((N : ℝ) * G * n N) ≤ p N / ((N : ℝ) * G * n N) :=
          div_le_div_of_nonneg_right (hL N) (by positivity)
      _ ≤ p N / (G * n N) := by
          refine div_le_div_of_nonneg_left (hp0 N) hGn ?_
          rw [mul_assoc]; nlinarith
      _ = p N / n N / G := by field_simp
  have hAB := hA.add hB
  rw [add_zero] at hAB
  refine hAB.congr' ?_
  filter_upwards [hpos] with N hN
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hG' := hG.ne'
  have hn' := hN.ne'
  field_simp

theorem var_ratio_FIN083 {m s : ℕ+ → ℝ} (hn : ∀ᶠ N : ℕ+ in atTop, 0 < n N)
    (hm : ∀ N, m N ^ 2 ≤ s N * n N) (hs : Tendsto s atTop (𝓝 0)) :
    Tendsto (fun N => (n N - m N ^ 2) / n N) atTop (𝓝 1) := by
  have h0 : Tendsto (fun N => m N ^ 2 / n N) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hs
    · filter_upwards [hn] with N hN using div_nonneg (sq_nonneg _) hN.le
    · filter_upwards [hn] with N hN
      rw [div_le_iff₀ hN]; exact hm N
  have h1 := h0.const_sub 1
  rw [sub_zero] at h1
  refine h1.congr' ?_
  filter_upwards [hn] with N hN
  field_simp

theorem toReal_le_exp_FIN083 {q : ℝ≥0∞} (hq : q ≠ ⊤) {N : ℕ+} {c : ℝ}
    (h : (((N : ℝ)⁻¹ : ℝ) : EReal) * ENNReal.log q < (c : EReal)) :
    q.toReal ≤ Real.exp ((N : ℝ) * c) := by
  rcases eq_or_ne q 0 with h0 | h0
  · rw [h0]; simpa using (Real.exp_pos _).le
  · have hpos : 0 < q.toReal := ENNReal.toReal_pos h0 hq
    rw [← ENNReal.ofReal_toReal hq, ENNReal.log_ofReal_of_pos hpos, ← EReal.coe_mul,
      EReal.coe_lt_coe_iff] at h
    have hNp : (0 : ℝ) < N := by positivity
    have h1 : Real.log q.toReal < (N : ℝ) * c := by
      have := mul_lt_mul_of_pos_left h hNp
      rwa [← mul_assoc, mul_inv_cancel₀ hNp.ne', one_mul] at this
    exact ((Real.log_lt_iff_lt_exp hpos).1 h1).le

end Asymptotics

section Assembly

/-- The abstract assembly: the statements of FIN083 from the FIN082 exponent data. -/
theorem branch_FIN083 (κ h : ℝ) {χ : ℝ → ℝ} (hχc : Continuous χ) (hχ0 : ∀ x, 0 ≤ χ x)
    (hχ1 : ∀ x, χ x ≤ 1) {a b G : ℝ} (hG : 0 < G) (ha : ∀ x, x ≤ a → χ x = 1)
    (hb : ∀ x, b ≤ x → χ x = 0)
    (hmass : Tendsto (fun N : ℕ+ => ((N : ℝ)⁻¹) * Real.log (cutoffMassFIN082 κ h χ N)) atTop
      (𝓝 (-G)))
    {J : EReal}
    (hlim : Filter.limsup (fun N : ℕ+ => gibbsLogProbFIN081 κ h N (Set.Icc a b)) atTop ≤ -J)
    (hJ : -J < -(G : EReal)) :
    (∀ᶠ N : ℕ+ in atTop, 0 < cutoffMassFIN082 κ h χ N) ∧
    (∀ N : ℕ+, homogeneousEntropy (DGPS.particleLaw (scalarCosine κ h) N)
        (fun x => (χ (empTorusFIN081 N x)) ^ 2) =
      ENNReal.ofReal (-(cutoffMassFIN082 κ h χ N * Real.log (cutoffMassFIN082 κ h χ N))
        + ∫ x, (χ (empTorusFIN081 N x)) ^ 2 * Real.log ((χ (empTorusFIN081 N x)) ^ 2)
            ∂(DGPS.particleLaw (scalarCosine κ h) N))) ∧
    (∀ N : ℕ+, |∫ x, (χ (empTorusFIN081 N x)) ^ 2 * Real.log ((χ (empTorusFIN081 N x)) ^ 2)
            ∂(DGPS.particleLaw (scalarCosine κ h) N)| ≤
      (DGPS.particleLaw (scalarCosine κ h) N {x | empTorusFIN081 N x ∈ Set.Icc a b}).toReal) ∧
    Tendsto (fun N : ℕ+ =>
      (homogeneousEntropy (DGPS.particleLaw (scalarCosine κ h) N)
          (fun x => (χ (empTorusFIN081 N x)) ^ 2)).toReal /
        ((N : ℝ) * G * cutoffMassFIN082 κ h χ N)) atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ+ =>
      ProbabilityTheory.variance (fun x => χ (empTorusFIN081 N x))
          (DGPS.particleLaw (scalarCosine κ h) N) / cutoffMassFIN082 κ h χ N) atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ+ =>
      (DGPS.particleLaw (scalarCosine κ h) N {x | empTorusFIN081 N x ∈ Set.Icc a b}).toReal /
        cutoffMassFIN082 κ h χ N) atTop (𝓝 0) := by
  have hprob : ∀ N : ℕ+, IsProbabilityMeasure (DGPS.particleLaw (scalarCosine κ h) N) :=
    fun N => DGPS.Particle.particleLaw_isProbabilityMeasure' (scalarCosine κ h) N
  have hFm : ∀ N : ℕ+, Measurable fun x => χ (empTorusFIN081 N x) := fun N =>
    (hχc.comp (continuous_empTorus_FIN082 N)).measurable
  have hn0 : ∀ N : ℕ+, 0 ≤ cutoffMassFIN082 κ h χ N := fun N =>
    integral_nonneg fun x => sq_nonneg _
  -- the transition probabilities
  set p : ℕ+ → ℝ := fun N =>
    (DGPS.particleLaw (scalarCosine κ h) N {x | empTorusFIN081 N x ∈ Set.Icc a b}).toReal with hp
  have hp0 : ∀ N, 0 ≤ p N := fun N => ENNReal.toReal_nonneg
  have hlt : Filter.limsup (fun N : ℕ+ => gibbsLogProbFIN081 κ h N (Set.Icc a b)) atTop <
      (((-G : ℝ)) : EReal) := by
    rw [EReal.coe_neg]; exact lt_of_le_of_lt hlim hJ
  obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have hc : c < -G := EReal.coe_lt_coe_iff.1 hc2
  have hev := Filter.eventually_lt_of_limsup_lt hc1
  have hpc : ∀ᶠ N : ℕ+ in atTop, p N ≤ Real.exp ((N : ℝ) * c) := by
    filter_upwards [hev] with N hN
    have := hprob N
    exact toReal_le_exp_FIN083 (measure_ne_top _ _) hN
  have hpos := eventually_pos_FIN083 hn0 hG hmass
  have hratio := ratio_tendsto_FIN083 hn0 hG hmass hc hp0 hpc
  have hnz := tendsto_n_zero_FIN083 hn0 hG hmass
  have hpz : Tendsto p atTop (𝓝 0) :=
    tendsto_zero_of_exp_FIN083 hp0 (by linarith) hpc
  -- exact entropy formula and the correction term
  have hEnt : ∀ N : ℕ+, homogeneousEntropy (DGPS.particleLaw (scalarCosine κ h) N)
        (fun x => (χ (empTorusFIN081 N x)) ^ 2) =
      ENNReal.ofReal (-(cutoffMassFIN082 κ h χ N * Real.log (cutoffMassFIN082 κ h χ N))
        + ∫ x, (χ (empTorusFIN081 N x)) ^ 2 * Real.log ((χ (empTorusFIN081 N x)) ^ 2)
            ∂(DGPS.particleLaw (scalarCosine κ h) N)) := by
    intro N
    have := hprob N
    exact entropy_formula_FIN083 (P := DGPS.particleLaw (scalarCosine κ h) N) (hFm N)
      (fun x => hχ0 _) (fun x => hχ1 _)
  have hL : ∀ N : ℕ+, |∫ x, (χ (empTorusFIN081 N x)) ^ 2 * Real.log ((χ (empTorusFIN081 N x)) ^ 2)
            ∂(DGPS.particleLaw (scalarCosine κ h) N)| ≤ p N := by
    intro N
    have := hprob N
    refine neg_term_bound_FIN083 (P := DGPS.particleLaw (scalarCosine κ h) N)
      (F := fun x => χ (empTorusFIN081 N x)) (fun x => hχ0 _) (fun x => hχ1 _)
      (measurable_set_emp_FIN082 N measurableSet_Icc) ?_
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · exact Or.inr (ha _ hx.le)
    · exact Or.inl (hb _ hx.le)
  refine ⟨hpos, hEnt, hL, ?_, ?_, hratio⟩
  · -- entropy
    have hx := entropy_ratio_FIN083 (L := fun N : ℕ+ =>
      ∫ x, (χ (empTorusFIN081 N x)) ^ 2 * Real.log ((χ (empTorusFIN081 N x)) ^ 2)
        ∂(DGPS.particleLaw (scalarCosine κ h) N)) hn0 hG hmass hc hp0 hpc hL
    have hev1 : ∀ᶠ N : ℕ+ in atTop, (1 / 2 : ℝ) <
        (-(cutoffMassFIN082 κ h χ N * Real.log (cutoffMassFIN082 κ h χ N))
          + ∫ x, (χ (empTorusFIN081 N x)) ^ 2 * Real.log ((χ (empTorusFIN081 N x)) ^ 2)
            ∂(DGPS.particleLaw (scalarCosine κ h) N)) /
        ((N : ℝ) * G * cutoffMassFIN082 κ h χ N) :=
      hx.eventually (lt_mem_nhds (by norm_num))
    refine hx.congr' ?_
    filter_upwards [hev1, hpos] with N h1 h2
    have hden : 0 < (N : ℝ) * G * cutoffMassFIN082 κ h χ N := by positivity
    have hnum : 0 < (-(cutoffMassFIN082 κ h χ N * Real.log (cutoffMassFIN082 κ h χ N))
          + ∫ x, (χ (empTorusFIN081 N x)) ^ 2 * Real.log ((χ (empTorusFIN081 N x)) ^ 2)
            ∂(DGPS.particleLaw (scalarCosine κ h) N)) := by
      by_contra hneg
      have := div_nonpos_of_nonpos_of_nonneg (not_lt.1 hneg) hden.le
      linarith
    rw [hEnt N, ENNReal.toReal_ofReal hnum.le]
  · -- variance
    have hs : Tendsto (fun N : ℕ+ =>
        (DGPS.particleLaw (scalarCosine κ h) N {x | empTorusFIN081 N x ∈ Set.Iio b}).toReal)
        atTop (𝓝 0) := by
      have hnp : Tendsto (fun N : ℕ+ => cutoffMassFIN082 κ h χ N + p N) atTop (𝓝 0) := by
        simpa using hnz.add hpz
      refine squeeze_zero (fun N => ENNReal.toReal_nonneg) (fun N => ?_) hnp
      have := hprob N
      have hsub : {x | empTorusFIN081 N x ∈ Set.Iio b} ⊆
          {x | empTorusFIN081 N x ∈ Set.Iio a} ∪ {x | empTorusFIN081 N x ∈ Set.Icc a b} := by
        intro x hx
        simp only [Set.mem_ofPred_eq, Set.mem_Iio, Set.mem_union, Set.mem_Icc] at hx ⊢
        by_cases hxa : empTorusFIN081 N x < a
        · exact Or.inl hxa
        · exact Or.inr ⟨not_lt.1 hxa, hx.le⟩
      have h1 := (measure_mono (μ := DGPS.particleLaw (scalarCosine κ h) N) hsub).trans
        (measure_union_le _ _)
      have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) h1
      rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h2
      have h3 := mass_ge_FIN082 κ h hχc hχ0 hχ1 N (S := Set.Iio a) measurableSet_Iio
        (fun x hx => ha x (Set.mem_Iio.1 hx).le)
      exact h2.trans (add_le_add h3 le_rfl)
    have hvar := var_ratio_FIN083 (n := fun N : ℕ+ => cutoffMassFIN082 κ h χ N)
      (m := fun N : ℕ+ => ∫ x, χ (empTorusFIN081 N x) ∂(DGPS.particleLaw (scalarCosine κ h) N))
      hpos (fun N => by
        have := hprob N
        exact sq_integral_le_FIN083 (P := DGPS.particleLaw (scalarCosine κ h) N)
          (F := fun x => χ (empTorusFIN081 N x)) (hFm N) (fun x => hχ0 _) (fun x => hχ1 _)
          (measurable_set_emp_FIN082 N measurableSet_Iio) (fun x hx => hb _
            (not_lt.1 (by simpa using hx)))) hs
    refine hvar.congr' (Filter.Eventually.of_forall fun N => ?_)
    have := hprob N
    have hmem : MemLp (fun x => χ (empTorusFIN081 N x)) 2
        (DGPS.particleLaw (scalarCosine κ h) N) :=
      MemLp.of_bound (hFm N).aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hχ0 _)]; exact hχ1 _)
    show _ = ProbabilityTheory.variance (fun x => χ (empTorusFIN081 N x))
      (DGPS.particleLaw (scalarCosine κ h) N) / _
    rw [ProbabilityTheory.variance_eq_sub hmem]
    simp [cutoffMassFIN082, Pi.pow_apply]

end Assembly

end DGPS.FiniteN.FalseMinimumFIN083


namespace DGPS.FiniteN

open DGPS.FiniteN.FalseMinimumFIN082 DGPS.FiniteN.FalseMinimumFIN081
  DGPS.FiniteN.FalseMinimumFIN076 DGPS.FiniteN.FalseMinimumFIN083 DGPS.Models
  DGPS.FiniteN.ScalarFoldFIN056

/-- **False-minimum branch entropy factor `N`.**

In the setting of `false_minimum_branch_cutoff_mass_exponent` (FIN082): for `κ > 2`,
`0 < h < h_c(κ)`, the roots `s1, s2, tp` of `FalseMinimumGeometryFIN076`
(`m_- = g(-s2)`, `m_b = g(-s1)`, `m_+ = g(tp)`), `G = G_- = ψ(-s2) - ψ(tp) > 0`, there is `δ₀ > 0`
such that for every `0 < δ ≤ δ₀` and every smooth cutoff `χ` with `0 ≤ χ ≤ 1`, `χ = 1` on
`m ≤ m_b - δ`, `χ = 0` on `m ≥ m_b + δ`, with `f_N = χ (m_N)` and `n_N = P_N(f_N²)`:

* `n_N > 0` eventually;
* `Ent_{P_N}(f_N²) = -n_N log n_N + P_N(f_N² log f_N²)` for every `N` (in `ℝ≥0∞`, via
  `DGPS.homogeneousEntropy`; in particular it is finite);
* `|P_N(f_N² log f_N²)| ≤ P_N(m_N ∈ [m_b - δ, m_b + δ])`, and this transition probability is
  exponentially smaller than `n_N`: `P_N(m_N ∈ [m_b - δ, m_b + δ]) / n_N → 0`;
* `Ent_{P_N}(f_N²) / (N G n_N) → 1`, i.e. `Ent_{P_N}(f_N²) = N G_- n_N (1 + o(1))`;
* `Var_{P_N}(f_N) / n_N → 1`, i.e. `Var_{P_N}(f_N) = n_N (1 + o(1))`. -/
theorem false_minimum_branch_entropy_factor_n :
    ∀ κ h : ℝ, 2 < κ → 0 < h → h < scalarFoldField κ →
      ∃ s1 s2 tp : ℝ, 0 < s1 ∧ s1 < scalarFoldPoint κ ∧ scalarFoldPoint κ < s2 ∧ 0 < tp ∧
        FalseMinimumGeometryFIN076 κ h s1 s2 tp ∧
        ∃ G : ℝ, 0 < G ∧ G = scalarPsi κ h (-s2) - scalarPsi κ h tp ∧
          ∃ δ0 : ℝ, 0 < δ0 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
            ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) →
              (∀ x, x ≤ besselRatio (-s1) - δ → χ x = 1) →
              (∀ x, besselRatio (-s1) + δ ≤ x → χ x = 0) →
              (∀ᶠ N : ℕ+ in Filter.atTop, 0 < cutoffMassFIN082 κ h χ N) ∧
              (∀ N : ℕ+, homogeneousEntropy (DGPS.particleLaw (scalarCosine κ h) N)
                  (fun x => (χ (empTorusFIN081 N x)) ^ 2) =
                ENNReal.ofReal
                  (-(cutoffMassFIN082 κ h χ N * Real.log (cutoffMassFIN082 κ h χ N))
                    + ∫ x, (χ (empTorusFIN081 N x)) ^ 2 * Real.log ((χ (empTorusFIN081 N x)) ^ 2)
                        ∂(DGPS.particleLaw (scalarCosine κ h) N))) ∧
              (∀ N : ℕ+, |∫ x, (χ (empTorusFIN081 N x)) ^ 2 *
                    Real.log ((χ (empTorusFIN081 N x)) ^ 2)
                      ∂(DGPS.particleLaw (scalarCosine κ h) N)| ≤
                (DGPS.particleLaw (scalarCosine κ h) N {x | empTorusFIN081 N x ∈
                  Set.Icc (besselRatio (-s1) - δ) (besselRatio (-s1) + δ)}).toReal) ∧
              Filter.Tendsto (fun N : ℕ+ =>
                (DGPS.particleLaw (scalarCosine κ h) N {x | empTorusFIN081 N x ∈
                    Set.Icc (besselRatio (-s1) - δ) (besselRatio (-s1) + δ)}).toReal /
                  cutoffMassFIN082 κ h χ N) Filter.atTop (nhds 0) ∧
              Filter.Tendsto (fun N : ℕ+ =>
                (homogeneousEntropy (DGPS.particleLaw (scalarCosine κ h) N)
                    (fun x => (χ (empTorusFIN081 N x)) ^ 2)).toReal /
                  ((N : ℝ) * G * cutoffMassFIN082 κ h χ N)) Filter.atTop (nhds 1) ∧
              Filter.Tendsto (fun N : ℕ+ =>
                ProbabilityTheory.variance (fun x => χ (empTorusFIN081 N x))
                    (DGPS.particleLaw (scalarCosine κ h) N) / cutoffMassFIN082 κ h χ N)
                Filter.atTop (nhds 1) := by
  intro κ h hκ hh0 hhc
  obtain ⟨s1, s2, tp, hs1, hs1', hs2', htp, hG, G, hGpos, hGdef, _, δ0, hδ0, hall⟩ :=
    false_minimum_branch_cutoff_mass_exponent κ h hκ hh0 hhc
  refine ⟨s1, s2, tp, hs1, hs1', hs2', htp, hG, G, hGpos, hGdef, δ0, hδ0, ?_⟩
  intro δ hδ hδle χ hχ hχ01 hχ1 hχ0
  obtain ⟨_, _, _, _, hmain⟩ := hall δ hδ hδle
  obtain ⟨hmass, hlim, hJ⟩ := hmain χ hχ hχ01 hχ1 hχ0
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := branch_FIN083 κ h hχ.continuous (fun x => (hχ01 x).1)
    (fun x => (hχ01 x).2) hGpos hχ1 hχ0 hmass hlim hJ
  exact ⟨h1, h2, h3, h6, h4, h5⟩

end DGPS.FiniteN
