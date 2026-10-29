import Mathlib

/-! # Laplace bounds at a quadratic minimum (FIN019) -/

namespace DGPS.FiniteN.Tools.QuadraticLaplace

open MeasureTheory Metric Set

lemma upper_of_second_deriv {g d1 d2 : ℝ → ℝ} {hi : ℝ}
    (hg : ∀ t, HasDerivAt g (d1 t) t) (hd1 : ∀ t, HasDerivAt d1 (d2 t) t)
    (h0 : d1 0 = 0) (hhi : ∀ t ∈ Icc (0:ℝ) 1, d2 t ≤ hi) :
    g 1 - g 0 ≤ hi / 2 := by
  have hA' : ∀ t, HasDerivAt (fun t => d1 t - hi * t) (d2 t - hi) t := fun t => by
    have := (hd1 t).sub ((hasDerivAt_id t).const_mul hi)
    convert this using 1
    · funext x; simp
    · ring
  have hA : AntitoneOn (fun t => d1 t - hi * t) (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hA' t).continuousAt.continuousWithinAt
    · exact fun t _ => (hA' t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hA' t).deriv]
      have := hhi t (interior_subset ht)
      linarith
  have h1 : ∀ t ∈ Icc (0:ℝ) 1, d1 t ≤ hi * t := by
    intro t ht
    have := hA ⟨le_rfl, zero_le_one⟩ ht ht.1
    simp [h0] at this
    linarith
  have hB' : ∀ t, HasDerivAt (fun t => g t - hi * t ^ 2 / 2) (d1 t - hi * t) t := fun t => by
    have := (hg t).sub (((hasDerivAt_pow 2 t).const_mul hi).div_const 2)
    convert this using 1
    simp
    ring
  have hB : AntitoneOn (fun t => g t - hi * t ^ 2 / 2) (Icc 0 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
    · exact fun t _ => (hB' t).continuousAt.continuousWithinAt
    · exact fun t _ => (hB' t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hB' t).deriv]
      have := h1 t (interior_subset ht)
      linarith
  have := hB ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩ zero_le_one
  simp at this
  linarith

lemma two_sided_of_second_deriv {g d1 d2 : ℝ → ℝ} {lo hi : ℝ}
    (hg : ∀ t, HasDerivAt g (d1 t) t) (hd1 : ∀ t, HasDerivAt d1 (d2 t) t)
    (h0 : d1 0 = 0) (hlo : ∀ t ∈ Icc (0:ℝ) 1, lo ≤ d2 t)
    (hhi : ∀ t ∈ Icc (0:ℝ) 1, d2 t ≤ hi) :
    lo / 2 ≤ g 1 - g 0 ∧ g 1 - g 0 ≤ hi / 2 := by
  refine ⟨?_, upper_of_second_deriv hg hd1 h0 hhi⟩
  have := upper_of_second_deriv (g := fun t => - g t) (d1 := fun t => - d1 t)
    (d2 := fun t => - d2 t) (hi := -lo) (fun t => (hg t).neg) (fun t => (hd1 t).neg)
    (by simp [h0]) (fun t ht => by simpa using hlo t ht)
  simp at this
  linarith


section Local

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma local_quadratic_bounds {ψ : E → ℝ} {w0 : E} (hψ : ContDiff ℝ 2 ψ)
    (hmin : ∀ w, ψ w0 ≤ ψ w)
    (hH : ∃ m > 0, ∀ v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ ψ) w0 v v) :
    ∃ δ > 0, ∃ m1 > 0, ∃ m2 > 0, ∀ w, dist w w0 ≤ δ →
      m1 * dist w w0 ^ 2 ≤ ψ w - ψ w0 ∧ ψ w - ψ w0 ≤ m2 * dist w w0 ^ 2 := by
  obtain ⟨m, hm, hHm⟩ := hH
  have hdiff : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hψ1 : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (m := 1) (by norm_num)
  have hdiff1 : Differentiable ℝ (fderiv ℝ ψ) := hψ1.differentiable (by norm_num)
  have hHc0 : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ ψ)) := hψ1.fderiv_right (m := 0) (by norm_num)
  have hNc : Continuous (fun w => ‖fderiv ℝ (fderiv ℝ ψ) w - fderiv ℝ (fderiv ℝ ψ) w0‖) :=
    (continuous_norm (E := E →L[ℝ] E →L[ℝ] ℝ)).comp (hHc0.continuous.sub continuous_const)
  have hT : Filter.Tendsto (fun w => ‖fderiv ℝ (fderiv ℝ ψ) w - fderiv ℝ (fderiv ℝ ψ) w0‖)
      (nhds w0) (nhds 0) := by
    have h := hNc.tendsto w0
    have h0 : ‖fderiv ℝ (fderiv ℝ ψ) w0 - fderiv ℝ (fderiv ℝ ψ) w0‖ = 0 := by
      rw [sub_self]; exact norm_zero (E := E →L[ℝ] E →L[ℝ] ℝ)
    rwa [h0] at h
  obtain ⟨δ, hδ, hδH⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hT (m / 2) (by positivity))
  have hloc : IsLocalMin ψ w0 := Filter.Eventually.of_forall hmin
  have hgrad : fderiv ℝ ψ w0 = 0 := hloc.fderiv_eq_zero
  refine ⟨δ / 2, by positivity, m / 4, by positivity,
    (‖fderiv ℝ (fderiv ℝ ψ) w0‖ + m / 2) / 2, by positivity, ?_⟩
  intro w hw
  set v := w - w0 with hv
  have hwv : w = w0 + v := by simp [hv]
  have hnv : ‖v‖ ≤ δ / 2 := by rw [hv, ← dist_eq_norm]; exact hw
  have hdist : dist w w0 = ‖v‖ := by rw [hv, dist_eq_norm]
  have hl : ∀ t : ℝ, HasDerivAt (fun t : ℝ => w0 + t • v) v t := fun t => by
    simpa using ((hasDerivAt_id t).smul_const v).const_add w0
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ψ (w0 + t • v))
      (fderiv ℝ ψ (w0 + t • v) v) t := fun t =>
    (hdiff (w0 + t • v)).hasFDerivAt.comp_hasDerivAt t (hl t)
  have hd1 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => fderiv ℝ ψ (w0 + t • v) v)
      (fderiv ℝ (fderiv ℝ ψ) (w0 + t • v) v v) t := fun t => by
    have hF : HasDerivAt (fun t : ℝ => fderiv ℝ ψ (w0 + t • v))
        (fderiv ℝ (fderiv ℝ ψ) (w0 + t • v) v) t :=
      (hdiff1 (w0 + t • v)).hasFDerivAt.comp_hasDerivAt t (hl t)
    simpa using hF.clm_apply (hasDerivAt_const t v)
  have hbd : ∀ t ∈ Icc (0:ℝ) 1,
      (m / 2) * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ ψ) (w0 + t • v) v v ∧
      fderiv ℝ (fderiv ℝ ψ) (w0 + t • v) v v ≤
        (‖fderiv ℝ (fderiv ℝ ψ) w0‖ + m / 2) * ‖v‖ ^ 2 := by
    intro t ht
    have hts : ‖t • v‖ ≤ ‖v‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
      exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    have hdd : dist (w0 + t • v) w0 < δ := by
      rw [dist_eq_norm]; simp only [add_sub_cancel_left]; linarith
    have h1 : ‖fderiv ℝ (fderiv ℝ ψ) (w0 + t • v) - fderiv ℝ (fderiv ℝ ψ) w0‖ < m / 2 := by
      have h := hδH hdd
      rw [Real.dist_eq, sub_zero] at h
      exact lt_of_le_of_lt (le_abs_self _) h
    have h2 : |fderiv ℝ (fderiv ℝ ψ) (w0 + t • v) v v - fderiv ℝ (fderiv ℝ ψ) w0 v v|
        ≤ (m / 2) * ‖v‖ ^ 2 := by
      have : fderiv ℝ (fderiv ℝ ψ) (w0 + t • v) v v - fderiv ℝ (fderiv ℝ ψ) w0 v v =
          (fderiv ℝ (fderiv ℝ ψ) (w0 + t • v) - fderiv ℝ (fderiv ℝ ψ) w0) v v := by simp
      rw [this]
      calc |((fderiv ℝ (fderiv ℝ ψ) (w0 + t • v) - fderiv ℝ (fderiv ℝ ψ) w0) v) v|
          = ‖((fderiv ℝ (fderiv ℝ ψ) (w0 + t • v) - fderiv ℝ (fderiv ℝ ψ) w0) v) v‖ :=
            (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ (fderiv ℝ ψ) (w0 + t • v) - fderiv ℝ (fderiv ℝ ψ) w0‖ * ‖v‖ * ‖v‖ :=
            ContinuousLinearMap.le_opNorm₂ _ _ _
        _ ≤ (m / 2) * ‖v‖ * ‖v‖ := by gcongr
        _ = (m / 2) * ‖v‖ ^ 2 := by ring
    have h3 := hHm v
    have h4 : fderiv ℝ (fderiv ℝ ψ) w0 v v ≤ ‖fderiv ℝ (fderiv ℝ ψ) w0‖ * ‖v‖ ^ 2 := by
      calc fderiv ℝ (fderiv ℝ ψ) w0 v v ≤ ‖fderiv ℝ (fderiv ℝ ψ) w0 v v‖ := le_abs_self _
        _ ≤ ‖fderiv ℝ (fderiv ℝ ψ) w0‖ * ‖v‖ * ‖v‖ := ContinuousLinearMap.le_opNorm₂ _ _ _
        _ = _ := by ring
    rw [abs_le] at h2
    constructor <;> nlinarith [h2.1, h2.2]
  have key := two_sided_of_second_deriv (g := fun t : ℝ => ψ (w0 + t • v))
    (d1 := fun t : ℝ => fderiv ℝ ψ (w0 + t • v) v)
    (d2 := fun t : ℝ => fderiv ℝ (fderiv ℝ ψ) (w0 + t • v) v v)
    (lo := (m / 2) * ‖v‖ ^ 2) (hi := (‖fderiv ℝ (fderiv ℝ ψ) w0‖ + m / 2) * ‖v‖ ^ 2)
    hg hd1 (by simp [hgrad]) (fun t ht => (hbd t ht).1) (fun t ht => (hbd t ht).2)
  simp only [one_smul, zero_smul, add_zero] at key
  rw [← hwv] at key
  rw [hdist]
  constructor <;> nlinarith [key.1, key.2]

end Local


section Core

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

lemma gaussian_integrable {b : ℝ} (hb : 0 < b) (w0 : E) :
    Integrable (fun w : E => Real.exp (-b * ‖w - w0‖ ^ 2)) := by
  have h : Integrable (fun v : E => Real.exp (-b * ‖v‖ ^ 2)) := by
    apply Integrable.of_integral_ne_zero
    rw [GaussianFourier.integral_rexp_neg_mul_sq_norm hb]
    positivity
  exact h.comp_sub_right w0

lemma gaussian_integral {b : ℝ} (hb : 0 < b) (w0 : E) :
    ∫ w : E, Real.exp (-b * ‖w - w0‖ ^ 2) = (Real.pi / b) ^ ((Module.finrank ℝ E : ℝ) / 2) := by
  rw [integral_sub_right_eq_self (fun v : E => Real.exp (-b * ‖v‖ ^ 2)) w0,
    GaussianFourier.integral_rexp_neg_mul_sq_norm hb]

lemma exp_neg_le_pow_neg {s c : ℝ} (hs : 0 ≤ s) (hc : 0 < c) :
    ∃ C > 0, ∀ N : ℝ, 0 < N → Real.exp (-(c * N)) ≤ C * N ^ (-s) := by
  have key : ∃ C > 0, ∀ N : ℝ, 0 < N → N ^ s ≤ C * Real.exp (c * N) := by
    rcases hs.eq_or_lt with h | h
    · refine ⟨1, one_pos, fun N hN => ?_⟩
      rw [← h, Real.rpow_zero]
      have : (1 : ℝ) ≤ Real.exp (c * N) := Real.one_le_exp (by positivity)
      linarith
    · refine ⟨(s / c) ^ s, by positivity, fun N hN => ?_⟩
      have h1 : N = (s / c) * (c * N / s) := by field_simp
      have h2 : c * N / s ≤ Real.exp (c * N / s) := by
        linarith [Real.add_one_le_exp (c * N / s)]
      calc N ^ s = ((s / c) * (c * N / s)) ^ s := by rw [← h1]
        _ = (s / c) ^ s * (c * N / s) ^ s := Real.mul_rpow (by positivity) (by positivity)
        _ ≤ (s / c) ^ s * (Real.exp (c * N / s)) ^ s := by
            gcongr
        _ = (s / c) ^ s * Real.exp (c * N) := by
            rw [← Real.exp_mul]; congr 2; field_simp
  obtain ⟨C, hC, hC'⟩ := key
  refine ⟨C, hC, fun N hN => ?_⟩
  have hp : 0 < N ^ s := Real.rpow_pos_of_pos hN s
  have h3 := hC' N hN
  rw [Real.rpow_neg hN.le]
  have h4 : Real.exp (-(c * N)) * N ^ s ≤ C := by
    calc Real.exp (-(c * N)) * N ^ s ≤ Real.exp (-(c * N)) * (C * Real.exp (c * N)) :=
          mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
      _ = C := by
          rw [mul_left_comm, ← Real.exp_add]; simp
  rw [← div_eq_mul_inv, le_div_iff₀ hp]
  exact h4


/-- Hypotheses of the Laplace estimates for the shifted potential `f = ψ - ψ(w0)`. -/
structure LaplaceHyp (f : E → ℝ) (w0 : E) : Prop where
  cont : Continuous f
  nonneg : ∀ w, 0 ≤ f w
  pos : ∀ w, w ≠ w0 → 0 < f w
  loc : ∃ δ > 0, ∃ m1 > 0, ∃ m2 > 0, ∀ w, dist w w0 ≤ δ →
    m1 * dist w w0 ^ 2 ≤ f w ∧ f w ≤ m2 * dist w w0 ^ 2
  grow : ∃ b > 0, ∃ C : ℝ, ∀ w, b * dist w w0 ^ 2 - C ≤ f w

variable {f : E → ℝ} {w0 : E}

lemma LaplaceHyp.integrable_one (h : LaplaceHyp f w0) :
    Integrable (fun w => Real.exp (-f w)) := by
  obtain ⟨b, hb, C, hC⟩ := h.grow
  refine Integrable.mono' ((gaussian_integrable hb w0).const_mul (Real.exp C))
    (by have := h.cont; fun_prop) (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := hC w
  rw [dist_eq_norm] at this
  linarith

lemma LaplaceHyp.integrable (h : LaplaceHyp f w0) {N : ℝ} (hN : 1 ≤ N) :
    Integrable (fun w => Real.exp (-(N * f w))) := by
  refine Integrable.mono' h.integrable_one (by have := h.cont; fun_prop)
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  apply Real.exp_le_exp.mpr
  nlinarith [h.nonneg w]

omit [MeasurableSpace E] [BorelSpace E] in
lemma LaplaceHyp.gap (h : LaplaceHyp f w0) {r : ℝ} (hr : 0 < r) :
    ∃ c0 > 0, ∀ w, r ≤ dist w w0 → c0 ≤ f w := by
  obtain ⟨b, hb, C, hC⟩ := h.grow
  set R2 : ℝ := (|C| + 1) / b + 1 with hR2
  have hfar : ∀ w, R2 ≤ dist w w0 → 1 ≤ f w := by
    intro w hw
    have hR1 : 1 ≤ R2 := by rw [hR2]; have : 0 ≤ (|C| + 1) / b := by positivity
                            linarith
    have hd1 : 1 ≤ dist w w0 := le_trans hR1 hw
    have hdd : dist w w0 ≤ dist w w0 ^ 2 := by nlinarith
    have h1 : (|C| + 1) / b ≤ dist w w0 := by rw [hR2] at hw; linarith
    have h2 : |C| + 1 ≤ b * dist w w0 := by
      have := (div_le_iff₀ hb).mp h1
      linarith
    have h3 := hC w
    have h4 := le_abs_self C
    nlinarith
  have hKc : IsCompact (Metric.closedBall w0 R2 ∩ {w | r ≤ dist w w0}) :=
    (isCompact_closedBall w0 R2).inter_right
      (isClosed_le continuous_const (continuous_id.dist continuous_const))
  by_cases hK : (Metric.closedBall w0 R2 ∩ {w | r ≤ dist w w0}).Nonempty
  · obtain ⟨x, hxK, hxmin⟩ := hKc.exists_isMinOn hK h.cont.continuousOn
    have hxne : x ≠ w0 := by
      intro hx
      have : r ≤ dist x w0 := hxK.2
      rw [hx, dist_self] at this
      linarith
    have hfx := h.pos x hxne
    refine ⟨min (f x) 1, lt_min hfx one_pos, fun w hw => ?_⟩
    by_cases hwR : dist w w0 ≤ R2
    · exact le_trans (min_le_left _ _) (hxmin ⟨Metric.mem_closedBall.mpr hwR, hw⟩)
    · exact le_trans (min_le_right _ _) (hfar w (not_le.mp hwR).le)
  · refine ⟨1, one_pos, fun w hw => ?_⟩
    by_cases hwR : dist w w0 ≤ R2
    · exact absurd ⟨w, Metric.mem_closedBall.mpr hwR, hw⟩ hK
    · exact hfar w (not_le.mp hwR).le

lemma LaplaceHyp.tail (h : LaplaceHyp f w0) {r : ℝ} (hr : 0 < r) :
    ∃ c0 > 0, ∀ N : ℝ, 1 ≤ N →
      ∫ w in {w | r ≤ dist w w0}, Real.exp (-(N * f w)) ≤
        Real.exp (-(c0 * (N - 1))) * ∫ w, Real.exp (-f w) := by
  obtain ⟨c0, hc0, hgap⟩ := h.gap hr
  refine ⟨c0, hc0, fun N hN => ?_⟩
  have hs : MeasurableSet {w : E | r ≤ dist w w0} :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
  have hI1 := h.integrable_one
  calc ∫ w in {w | r ≤ dist w w0}, Real.exp (-(N * f w))
      ≤ ∫ w in {w | r ≤ dist w w0}, Real.exp (-(c0 * (N - 1))) * Real.exp (-f w) := by
        refine setIntegral_mono_on (h.integrable hN).integrableOn
          (hI1.const_mul _).integrableOn hs (fun w hw => ?_)
        rw [← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have := hgap w hw
        nlinarith
    _ ≤ ∫ w, Real.exp (-(c0 * (N - 1))) * Real.exp (-f w) :=
        setIntegral_le_integral (hI1.const_mul _)
          (Filter.Eventually.of_forall fun w => by positivity)
    _ = _ := integral_const_mul _ _


lemma rpow_neg_half_eq (N : ℝ) (hN : 0 < N) (d : ℕ) :
    ((Real.sqrt N)⁻¹) ^ d = N ^ (-((d : ℝ) / 2)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hN.le, ← Real.rpow_natCast, ← Real.rpow_mul hN.le]
  congr 1
  ring

lemma LaplaceHyp.lower (h : LaplaceHyp f w0) :
    ∃ L > 0, ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
      L * N ^ (-((Module.finrank ℝ E : ℝ) / 2)) ≤ ∫ w, Real.exp (-(N * f w)) := by
  obtain ⟨δ, hδ, m1, hm1, m2, hm2, hloc⟩ := h.loc
  have hV : 0 < (volume : Measure E).real (Metric.ball (0 : E) 1) :=
    ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne
  refine ⟨Real.exp (-m2) * (volume : Measure E).real (Metric.ball (0 : E) 1),
    mul_pos (Real.exp_pos _) hV, max 1 (δ⁻¹ ^ 2), le_max_left _ _, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : 0 < N := by linarith
  have hNδ : δ⁻¹ ^ 2 ≤ N := le_trans (le_max_right _ _) hN
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  set r := (Real.sqrt N)⁻¹ with hr
  have hr0 : 0 < r := inv_pos.mpr hsq
  have hrδ : r ≤ δ := by
    have h1 : δ⁻¹ ≤ Real.sqrt N :=
      calc δ⁻¹ = Real.sqrt (δ⁻¹ ^ 2) := (Real.sqrt_sq (inv_nonneg.2 hδ.le)).symm
        _ ≤ Real.sqrt N := Real.sqrt_le_sqrt hNδ
    exact inv_le_of_inv_le₀ hδ h1
  have hr2 : r ^ 2 * N = 1 := by
    rw [hr, inv_pow, Real.sq_sqrt hN0.le]
    field_simp
  have hI := h.integrable hN1
  have hball : (volume : Measure E).real (Metric.closedBall w0 r) =
      r ^ (Module.finrank ℝ E) * (volume : Measure E).real (Metric.ball (0 : E) 1) :=
    Measure.addHaar_real_closedBall (volume : Measure E) w0 hr0.le
  calc Real.exp (-m2) * (volume : Measure E).real (Metric.ball (0 : E) 1) *
        N ^ (-((Module.finrank ℝ E : ℝ) / 2))
      = ∫ w in Metric.closedBall w0 r, Real.exp (-m2) := by
        rw [setIntegral_const, hball, smul_eq_mul, hr, rpow_neg_half_eq N hN0]
        ring
    _ ≤ ∫ w in Metric.closedBall w0 r, Real.exp (-(N * f w)) := by
        refine setIntegral_mono_on (integrableOn_const measure_closedBall_lt_top.ne)
          hI.integrableOn Metric.isClosed_closedBall.measurableSet (fun w hw => ?_)
        apply Real.exp_le_exp.mpr
        have hd : dist w w0 ≤ r := Metric.mem_closedBall.mp hw
        have h1 := (hloc w (le_trans hd hrδ)).2
        have h2 : dist w w0 ^ 2 ≤ r ^ 2 := by gcongr
        have h3 : f w ≤ m2 * r ^ 2 := h1.trans (by gcongr)
        have h4 := mul_le_mul_of_nonneg_left h3 hN0.le
        have h5 : N * (m2 * r ^ 2) = m2 := by
          calc N * (m2 * r ^ 2) = m2 * (r ^ 2 * N) := by ring
            _ = m2 := by rw [hr2]; ring
        linarith
    _ ≤ ∫ w, Real.exp (-(N * f w)) :=
        setIntegral_le_integral hI (Filter.Eventually.of_forall fun w => (Real.exp_pos _).le)

lemma LaplaceHyp.upper (h : LaplaceHyp f w0) :
    ∃ A > 0, ∀ N : ℝ, 1 ≤ N →
      ∫ w, Real.exp (-(N * f w)) ≤ A * N ^ (-((Module.finrank ℝ E : ℝ) / 2)) := by
  obtain ⟨δ, hδ, m1, hm1, m2, hm2, hloc⟩ := h.loc
  obtain ⟨c0, hc0, htail⟩ := h.tail hδ
  obtain ⟨C, hC, hexp⟩ := exp_neg_le_pow_neg (s := (Module.finrank ℝ E : ℝ) / 2) (c := c0)
    (by positivity) hc0
  have hI1 : 0 ≤ ∫ w, Real.exp (-f w) := integral_nonneg fun w => (Real.exp_pos _).le
  refine ⟨(Real.pi / m1) ^ ((Module.finrank ℝ E : ℝ) / 2) +
    Real.exp c0 * (∫ w, Real.exp (-f w)) * C, by positivity, fun N hN => ?_⟩
  have hN0 : 0 < N := by linarith
  have hI := h.integrable hN
  have hs : MeasurableSet (Metric.ball w0 δ) := Metric.isOpen_ball.measurableSet
  have hcompl : {w : E | δ ≤ dist w w0} = (Metric.ball w0 δ)ᶜ := by
    ext w; simp [Metric.mem_ball, not_lt]
  have hin : ∫ w in Metric.ball w0 δ, Real.exp (-(N * f w)) ≤
      (Real.pi / m1) ^ ((Module.finrank ℝ E : ℝ) / 2) *
        N ^ (-((Module.finrank ℝ E : ℝ) / 2)) := by
    have hb : 0 < N * m1 := by positivity
    have hg := gaussian_integrable hb w0
    calc ∫ w in Metric.ball w0 δ, Real.exp (-(N * f w))
        ≤ ∫ w in Metric.ball w0 δ, Real.exp (-(N * m1) * ‖w - w0‖ ^ 2) := by
          refine setIntegral_mono_on hI.integrableOn hg.integrableOn hs (fun w hw => ?_)
          apply Real.exp_le_exp.mpr
          have hd : dist w w0 ≤ δ := (Metric.mem_ball.mp hw).le
          have h1 := (hloc w hd).1
          rw [dist_eq_norm] at h1
          nlinarith
      _ ≤ ∫ w, Real.exp (-(N * m1) * ‖w - w0‖ ^ 2) :=
          setIntegral_le_integral hg (Filter.Eventually.of_forall fun w => (Real.exp_pos _).le)
      _ = (Real.pi / (N * m1)) ^ ((Module.finrank ℝ E : ℝ) / 2) := gaussian_integral hb w0
      _ = _ := by
          rw [show Real.pi / (N * m1) = (Real.pi / m1) * N⁻¹ by field_simp,
            Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hN0.le,
            ← Real.rpow_neg hN0.le]
  have hout : ∫ w in (Metric.ball w0 δ)ᶜ, Real.exp (-(N * f w)) ≤
      Real.exp c0 * (∫ w, Real.exp (-f w)) * C *
        N ^ (-((Module.finrank ℝ E : ℝ) / 2)) := by
    rw [← hcompl]
    refine (htail N hN).trans ?_
    have h1 : Real.exp (-(c0 * (N - 1))) = Real.exp c0 * Real.exp (-(c0 * N)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h1]
    have h2 := hexp N hN0
    calc Real.exp c0 * Real.exp (-(c0 * N)) * ∫ w, Real.exp (-f w)
        ≤ Real.exp c0 * (C * N ^ (-((Module.finrank ℝ E : ℝ) / 2))) * ∫ w, Real.exp (-f w) := by
          gcongr
      _ = _ := by ring
  rw [← integral_add_compl hs hI]
  linarith

end Core

end DGPS.FiniteN.Tools.QuadraticLaplace

namespace DGPS.FiniteN

open MeasureTheory Metric Set DGPS.FiniteN.Tools.QuadraticLaplace

/-- Laplace bounds at a nondegenerate quadratic global minimum, with gap tails.
`ψ` is `C²` on a finite-dimensional real inner product space `E` of dimension `d`, with unique
global minimizer `w0`, positive Hessian at `w0`, and quadratic growth.  Then
`Z_N = ∫ e^{-Nψ}` is two-sided comparable to `N^{-d/2} e^{-Nψ(w0)}` for `N ≥ N0`, and the mass
outside any fixed ball around `w0` is at most `C e^{-cN} Z_N`. -/
theorem quadratic_minimum_laplace_bounds_and_gap_tails
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    {ψ : E → ℝ} {w0 : E} (hψ : ContDiff ℝ 2 ψ)
    (hmin : ∀ w, ψ w0 ≤ ψ w) (huniq : ∀ w, ψ w = ψ w0 → w = w0)
    (hH : ∃ m > 0, ∀ v, m * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ ψ) w0 v v)
    (hgrow : ∃ b > 0, ∃ C : ℝ, ∀ w, b * dist w w0 ^ 2 - C ≤ ψ w - ψ w0) :
    (∃ L > 0, ∃ A > 0, ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
        L * N ^ (-((Module.finrank ℝ E : ℝ) / 2)) * Real.exp (-(N * ψ w0)) ≤
          ∫ w, Real.exp (-(N * ψ w)) ∧
        ∫ w, Real.exp (-(N * ψ w)) ≤
          A * N ^ (-((Module.finrank ℝ E : ℝ) / 2)) * Real.exp (-(N * ψ w0))) ∧
    ∀ r : ℝ, 0 < r → ∃ c > 0, ∃ C > 0, ∃ N0 : ℝ, 1 ≤ N0 ∧ ∀ N : ℝ, N0 ≤ N →
      ∫ w in {w | r ≤ dist w w0}, Real.exp (-(N * ψ w)) ≤
        C * Real.exp (-(c * N)) * ∫ w, Real.exp (-(N * ψ w)) := by
  set f : E → ℝ := fun w => ψ w - ψ w0 with hf
  have hcont : Continuous ψ := hψ.continuous
  have hh : LaplaceHyp f w0 :=
    { cont := by have := hcont; fun_prop
      nonneg := fun w => sub_nonneg.mpr (hmin w)
      pos := fun w hw => sub_pos.mpr (lt_of_le_of_ne (hmin w) (fun h => hw (huniq w h.symm)))
      loc := local_quadratic_bounds hψ hmin hH
      grow := hgrow }
  have hsplit : ∀ (N : ℝ) (S : Set E), ∫ w in S, Real.exp (-(N * ψ w)) =
      Real.exp (-(N * ψ w0)) * ∫ w in S, Real.exp (-(N * f w)) := by
    intro N S
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hf]
    rw [← Real.exp_add]
    congr 1
    ring
  have hsplit' : ∀ N : ℝ, ∫ w, Real.exp (-(N * ψ w)) =
      Real.exp (-(N * ψ w0)) * ∫ w, Real.exp (-(N * f w)) := by
    intro N
    have := hsplit N Set.univ
    simpa using this
  obtain ⟨L, hL, N0, hN0, hlow⟩ := hh.lower
  obtain ⟨A, hA, hup⟩ := hh.upper
  refine ⟨⟨L, hL, A, hA, N0, hN0, fun N hN => ⟨?_, ?_⟩⟩, fun r hr => ?_⟩
  · rw [hsplit']
    have := hlow N hN
    have hp := (Real.exp_pos (-(N * ψ w0))).le
    nlinarith
  · rw [hsplit']
    have := hup N (le_trans hN0 hN)
    have hp := (Real.exp_pos (-(N * ψ w0))).le
    nlinarith
  · obtain ⟨c0, hc0, htail⟩ := hh.tail hr
    have hd : (0:ℝ) ≤ (Module.finrank ℝ E : ℝ) / 2 := by positivity
    obtain ⟨K, hK, hexp⟩ := exp_neg_le_pow_neg hd (half_pos hc0)
    set I1 := ∫ w, Real.exp (-f w) with hI1
    have hI1n : 0 ≤ I1 := integral_nonneg fun w => (Real.exp_pos _).le
    refine ⟨c0 / 2, half_pos hc0, Real.exp c0 * I1 * K / L + 1, by positivity, N0, hN0,
      fun N hN => ?_⟩
    have hN1 : 1 ≤ N := le_trans hN0 hN
    have hNp : 0 < N := by linarith
    have hP : 0 < N ^ (-((Module.finrank ℝ E : ℝ) / 2)) := Real.rpow_pos_of_pos hNp _
    rw [hsplit, hsplit']
    set P := Real.exp (-(N * ψ w0)) with hP0
    have hPp : 0 < P := Real.exp_pos _
    set Z := ∫ w, Real.exp (-(N * f w)) with hZ
    have hZl : L * N ^ (-((Module.finrank ℝ E : ℝ) / 2)) ≤ Z := hlow N hN
    have ht := htail N hN1
    have h1 : Real.exp (-(c0 * (N - 1))) = Real.exp c0 * Real.exp (-(c0 * N)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (-(c0 * N)) = Real.exp (-(c0 / 2 * N)) * Real.exp (-(c0 / 2 * N)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h3 := hexp N hNp
    have hE : 0 < Real.exp (-(c0 / 2 * N)) := Real.exp_pos _
    -- tail ≤ e^{c0} e^{-c0N} I1;  e^{-c0N/2} ≤ K N^{-s} ≤ K Z / L
    have h4 : Real.exp (-(c0 / 2 * N)) ≤ K * Z / L := by
      rw [le_div_iff₀ hL]
      calc Real.exp (-(c0 / 2 * N)) * L ≤ K * N ^ (-((Module.finrank ℝ E : ℝ) / 2)) * L := by
            gcongr
        _ = K * (L * N ^ (-((Module.finrank ℝ E : ℝ) / 2))) := by ring
        _ ≤ K * Z := by gcongr
    have h5 : ∫ w in {w | r ≤ dist w w0}, Real.exp (-(N * f w)) ≤
        (Real.exp c0 * I1 * K / L) * Real.exp (-(c0 / 2 * N)) * Z := by
      refine ht.trans ?_
      rw [h1, h2]
      have : Real.exp c0 * (Real.exp (-(c0 / 2 * N)) * Real.exp (-(c0 / 2 * N))) * I1 ≤
          Real.exp c0 * (Real.exp (-(c0 / 2 * N)) * (K * Z / L)) * I1 := by gcongr
      refine this.trans (le_of_eq ?_)
      field_simp
    have h6 : (Real.exp c0 * I1 * K / L) * Real.exp (-(c0 / 2 * N)) * Z ≤
        (Real.exp c0 * I1 * K / L + 1) * Real.exp (-(c0 / 2 * N)) * Z := by
      have : 0 ≤ Real.exp (-(c0 / 2 * N)) * Z := by
        have : 0 ≤ Z := integral_nonneg fun w => (Real.exp_pos _).le
        positivity
      nlinarith
    have := h5.trans h6
    nlinarith
end DGPS.FiniteN
