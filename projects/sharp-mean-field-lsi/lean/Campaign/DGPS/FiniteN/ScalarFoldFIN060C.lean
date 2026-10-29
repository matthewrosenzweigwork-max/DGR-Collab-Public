import DGPS.FiniteN.ScalarFoldFIN060B

/-!
# FIN060 (part C): bounded smooth test functions for the fold auxiliary Poincare inequality

The centered IMS globalization is stated for smooth compactly supported mean-zero test functions.
Here it is upgraded, by a cutoff argument, to smooth bounded functions with bounded gradient.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ContDiff

namespace DGPS.FiniteN.ScalarFoldFIN060

/-- A fixed smooth bump on `E1`, equal to `1` on the closed unit ball. -/
noncomputable def bumpFIN060 : ContDiffBump (0 : E1) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The rescaled cutoff `x ↦ bump(x / (n+1))`. -/
noncomputable def cutFIN060 (n : ℕ) (x : E1) : ℝ := bumpFIN060 (((n : ℝ) + 1)⁻¹ • x)

theorem contDiff_bump_FIN060 : ContDiff ℝ ∞ bumpFIN060 := bumpFIN060.contDiff

theorem contDiff_cut_FIN060 (n : ℕ) : ContDiff ℝ ∞ (cutFIN060 n) :=
  contDiff_bump_FIN060.comp (contDiff_const_smul _)

theorem cut_nonneg_FIN060 (n : ℕ) (x : E1) : 0 ≤ cutFIN060 n x := bumpFIN060.nonneg

theorem cut_le_one_FIN060 (n : ℕ) (x : E1) : cutFIN060 n x ≤ 1 := bumpFIN060.le_one

theorem cut_eq_one_FIN060 (x : E1) : ∀ᶠ n : ℕ in atTop, cutFIN060 n x = 1 := by
  filter_upwards [eventually_ge_atTop (⌈‖x‖⌉₊)] with n hn
  refine bumpFIN060.one_of_mem_closedBall ?_
  have h1 : ‖x‖ ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simp only [mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_pos hpos]
  show ((n : ℝ) + 1)⁻¹ * ‖x‖ ≤ bumpFIN060.rIn
  have : bumpFIN060.rIn = 1 := rfl
  rw [this, inv_mul_le_iff₀ hpos]
  linarith

theorem cut_hasCompactSupport_FIN060 (n : ℕ) : HasCompactSupport (cutFIN060 n) := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E1)
    (2 * ((n : ℝ) + 1))) fun x hx => ?_
  by_contra hxn
  apply hx
  refine bumpFIN060.zero_of_le_dist ?_
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  simp only [mem_closedBall, dist_zero_right, not_le] at hxn
  simp only [dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos]
  show bumpFIN060.rOut ≤ _
  have : bumpFIN060.rOut = 2 := rfl
  rw [this]
  rw [← div_eq_inv_mul, le_div_iff₀ hpos]
  linarith

/-- Bounds of a smooth compactly supported function and its derivative. -/
theorem bdd_of_cs_FIN060 {f : E1 → ℝ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ D : ℝ, 0 ≤ D ∧ (∀ x, |f x| ≤ D) ∧ ∀ x, ‖fderiv ℝ f x‖ ≤ D := by
  have h1 : Continuous f := hf.continuous
  have h2 : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have h3 : HasCompactSupport (fderiv ℝ f) := hc.fderiv ℝ
  obtain ⟨A, hA⟩ := h1.bounded_above_of_compact_support hc
  obtain ⟨A', hA'⟩ := h2.bounded_above_of_compact_support h3
  refine ⟨max (max A A') 0, le_max_right _ _, fun x => ?_, fun x => ?_⟩
  · have := hA x
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left A A').trans (le_max_left _ _))
  · exact (hA' x).trans ((le_max_right A A').trans (le_max_left _ _))

theorem norm_fderiv_cut_FIN060 : ∃ D : ℝ, 0 ≤ D ∧ ∀ (n : ℕ) (x : E1),
    ‖fderiv ℝ (cutFIN060 n) x‖ ≤ D * ((n : ℝ) + 1)⁻¹ := by
  obtain ⟨D, hD0, -, hD⟩ := bdd_of_cs_FIN060 contDiff_bump_FIN060 bumpFIN060.hasCompactSupport
  refine ⟨D, hD0, fun n x => ?_⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hd : HasFDerivAt (fun y : E1 => (((n : ℝ) + 1)⁻¹ • y)) (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ E1) x :=
    (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ E1).hasFDerivAt
  have hb : HasFDerivAt (cutFIN060 n) ((fderiv ℝ bumpFIN060 (((n : ℝ) + 1)⁻¹ • x)).comp
      (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ E1)) x :=
    ((contDiff_bump_FIN060.differentiable (by simp) _).hasFDerivAt).comp x hd
  rw [hb.fderiv]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hpos]
  have : ‖ContinuousLinearMap.id ℝ E1‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  calc ‖fderiv ℝ bumpFIN060 (((n : ℝ) + 1)⁻¹ • x)‖ * (((n : ℝ) + 1)⁻¹ * ‖ContinuousLinearMap.id ℝ E1‖)
      ≤ D * (((n : ℝ) + 1)⁻¹ * 1) := by
        gcongr
        · exact hD _
    _ = _ := by ring

theorem integrable_bdd_FIN060 (η : Measure E1) [IsFiniteMeasure η] {f : E1 → ℝ}
    (hf : Continuous f) {C : ℝ} (h : ∀ x, |f x| ≤ C) : Integrable f η :=
  Integrable.of_bound hf.aestronglyMeasurable C (Eventually.of_forall fun x => by
    simpa [Real.norm_eq_abs] using h x)

/-- **Cutoff.** A Poincare inequality for smooth compactly supported mean-zero functions extends
to smooth bounded functions with bounded gradient. -/
theorem cutoff_poincare_FIN060 (η : Measure E1) [IsProbabilityMeasure η] {c : ℝ}
    (H : ∀ F : E1 → ℝ, ContDiff ℝ ∞ F → HasCompactSupport F → ∫ x, F x ∂η = 0 →
      c * ∫ x, F x ^ 2 ∂η ≤ ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂η)
    (ξ : E1 → ℝ) (hξ : ContDiff ℝ ∞ ξ) (hξc : HasCompactSupport ξ) (hξ1 : ∫ x, ξ x ∂η = 1)
    (G : E1 → ℝ) (hG : ContDiff ℝ ∞ G) {B : ℝ} (hB : ∀ x, |G x| ≤ B) {B' : ℝ}
    (hB' : ∀ x, ‖fderiv ℝ G x‖ ≤ B') :
    c * ∫ x, (G x - ∫ y, G y ∂η) ^ 2 ∂η ≤ ∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂η := by
  set m : ℝ := ∫ y, G y ∂η with hm
  have hGint : Integrable G η := integrable_bdd_FIN060 η hG.continuous hB
  have hmB : |m| ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := η) (f := G) (C := B)
      (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hB x)
    simpa [hm, Real.norm_eq_abs] using this
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  set Bb : ℝ := B + B with hBb
  have hb_bdd : ∀ x, |G x - m| ≤ Bb := fun x =>
    (abs_sub _ _).trans (add_le_add (hB x) hmB)
  obtain ⟨Dξ, hDξ0, hDξ, hDξ'⟩ := bdd_of_cs_FIN060 hξ hξc
  obtain ⟨D, hD0, hD⟩ := norm_fderiv_cut_FIN060
  have hBb0 : 0 ≤ Bb := by positivity
  have hdb : ∀ x, fderiv ℝ (fun y => G y - m) x = fderiv ℝ G x := fun x => fderiv_sub_const _
  have hb_smooth : ContDiff ℝ ∞ (fun y => G y - m) := hG.sub contDiff_const
  have hbc : ∀ n x, |(G x - m) * cutFIN060 n x| ≤ Bb := fun n x => by
    rw [abs_mul]
    calc |G x - m| * |cutFIN060 n x| ≤ Bb * 1 := by
          gcongr
          · exact hb_bdd x
          · rw [abs_of_nonneg (cut_nonneg_FIN060 n x)]; exact cut_le_one_FIN060 n x
      _ = Bb := mul_one _
  -- the mean parameters
  set e : ℕ → ℝ := fun n => ∫ x, (G x - m) * cutFIN060 n x ∂η with he
  have hint_bc : ∀ n, Integrable (fun x => (G x - m) * cutFIN060 n x) η := fun n =>
    integrable_bdd_FIN060 η (hb_smooth.continuous.mul (contDiff_cut_FIN060 n).continuous)
      (C := Bb) (hbc n)
  have he_bd : ∀ n, |e n| ≤ Bb := fun n => by
    have := norm_integral_le_of_norm_le_const (μ := η) (f := fun x => (G x - m) * cutFIN060 n x)
      (C := Bb) (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hbc n x)
    simpa [he, Real.norm_eq_abs] using this
  have he_lim : Tendsto e atTop (𝓝 0) := by
    have h0 : ∫ x, (G x - m) ∂η = 0 := by
      rw [integral_sub hGint (integrable_const _)]
      simp [hm]
    have := tendsto_integral_of_dominated_convergence (μ := η)
      (F := fun n x => (G x - m) * cutFIN060 n x) (f := fun x => G x - m)
      (bound := fun _ => Bb)
      (fun n => ((hb_smooth.continuous.mul (contDiff_cut_FIN060 n).continuous)).aestronglyMeasurable)
      (integrable_const _)
      (fun n => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hbc n x)
      (Eventually.of_forall fun x => by
        have : Tendsto (fun n => (G x - m) * cutFIN060 n x) atTop (𝓝 ((G x - m) * 1)) := by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [cut_eq_one_FIN060 x] with n hn
          rw [hn]
        simpa using this)
    rw [h0] at this
    exact this
  -- the test functions
  set F : ℕ → E1 → ℝ := fun n x => (G x - m) * cutFIN060 n x - e n * ξ x with hF
  have hF_smooth : ∀ n, ContDiff ℝ ∞ (F n) := fun n =>
    (hb_smooth.mul (contDiff_cut_FIN060 n)).sub (contDiff_const.mul hξ)
  have hF_cs : ∀ n, HasCompactSupport (F n) := fun n => by
    have h1 : HasCompactSupport (fun x => (G x - m) * cutFIN060 n x) :=
      (cut_hasCompactSupport_FIN060 n).mul_left
    have h2 : HasCompactSupport (fun x => e n * ξ x) := hξc.mul_left
    exact h1.sub h2
  have hF_mean : ∀ n, ∫ x, F n x ∂η = 0 := fun n => by
    simp only [hF]
    rw [integral_sub (hint_bc n) ((integrable_bdd_FIN060 η hξ.continuous (C := Dξ) hDξ).const_mul _),
      integral_const_mul, hξ1]
    simp [he]
  have hmain : ∀ n, c * ∫ x, F n x ^ 2 ∂η ≤ ∫ x, ‖fderiv ℝ (F n) x‖ ^ 2 ∂η := fun n =>
    H (F n) (hF_smooth n) (hF_cs n) (hF_mean n)
  -- bounds
  have hF_bd : ∀ n x, |F n x| ≤ Bb + Bb * Dξ := fun n x => by
    simp only [hF]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · exact hbc n x
    · rw [abs_mul]
      exact mul_le_mul (he_bd n) (hDξ x) (abs_nonneg _) hBb0
  have hF_lim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (G x - m)) := fun x => by
    have h1 : Tendsto (fun n => (G x - m) * cutFIN060 n x) atTop (𝓝 (G x - m)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [cut_eq_one_FIN060 x] with n hn
      rw [hn, mul_one]
    have h2 : Tendsto (fun n => e n * ξ x) atTop (𝓝 0) := by
      simpa using he_lim.mul_const (ξ x)
    simpa using h1.sub h2
  have hlim1 : Tendsto (fun n => ∫ x, F n x ^ 2 ∂η) atTop (𝓝 (∫ x, (G x - m) ^ 2 ∂η)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => (Bb + Bb * Dξ) ^ 2)
      (fun n => ((hF_smooth n).continuous.pow 2).aestronglyMeasurable) (integrable_const _)
      (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => (hF_lim x).pow 2)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hF_bd n x) 2
  -- derivatives
  have hdF : ∀ n x, fderiv ℝ (F n) x = (G x - m) • fderiv ℝ (cutFIN060 n) x
      + cutFIN060 n x • fderiv ℝ G x - e n • fderiv ℝ ξ x := fun n x => by
    have h1 : HasFDerivAt (fun y => G y - m) (fderiv ℝ G x) x := by
      rw [← hdb x]
      exact ((hb_smooth.differentiable (by simp)) x).hasFDerivAt
    have h2 := ((contDiff_cut_FIN060 n).differentiable (by simp) x).hasFDerivAt
    have h3 := ((hξ.differentiable (by simp)) x).hasFDerivAt
    exact ((h1.mul h2).sub (h3.const_mul (e n))).fderiv
  have hdF_bd : ∀ n x, ‖fderiv ℝ (F n) x‖ ≤ Bb * D + B' + Bb * Dξ := fun n x => by
    rw [hdF]
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hinv : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
    refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
    · rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul (hb_bdd x) ((hD n x).trans ?_) (norm_nonneg _) hBb0
      calc D * ((n : ℝ) + 1)⁻¹ ≤ D * 1 := by gcongr
        _ = D := mul_one _
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (cut_nonneg_FIN060 n x)]
      calc cutFIN060 n x * ‖fderiv ℝ G x‖ ≤ 1 * B' :=
            mul_le_mul (cut_le_one_FIN060 n x) (hB' x) (norm_nonneg _) zero_le_one
        _ = B' := one_mul _
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (he_bd n) (hDξ' x) (norm_nonneg _) hBb0
  have hdF_lim : ∀ x, Tendsto (fun n => ‖fderiv ℝ (F n) x‖ ^ 2) atTop
      (𝓝 (‖fderiv ℝ G x‖ ^ 2)) := fun x => by
    have hA : Tendsto (fun n : ℕ => (G x - m) • fderiv ℝ (cutFIN060 n) x) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun n : ℕ => |G x - m| * (D * ((n : ℝ) + 1)⁻¹)) (fun n => ?_) ?_
      · rw [norm_smul, Real.norm_eq_abs]
        gcongr
        exact hD n x
      · have : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
          tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
        simpa using (this.const_mul D).const_mul |G x - m|
    have hBt : Tendsto (fun n : ℕ => cutFIN060 n x • fderiv ℝ G x) atTop (𝓝 (fderiv ℝ G x)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [cut_eq_one_FIN060 x] with n hn
      rw [hn, one_smul]
    have hC : Tendsto (fun n : ℕ => e n • fderiv ℝ ξ x) atTop (𝓝 0) := by
      simpa using he_lim.smul_const (fderiv ℝ ξ x)
    have := ((hA.add hBt).sub hC).norm.pow 2
    simp only [zero_add, sub_zero] at this
    refine this.congr fun n => ?_
    rw [hdF]
  have hlim2 : Tendsto (fun n => ∫ x, ‖fderiv ℝ (F n) x‖ ^ 2 ∂η) atTop
      (𝓝 (∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂η)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun _ => (Bb * D + B' + Bb * Dξ) ^ 2)
      (fun n => ((((hF_smooth n).continuous_fderiv (by simp)).norm).pow 2).aestronglyMeasurable)
      (integrable_const _) (fun n => Eventually.of_forall fun x => ?_)
      (Eventually.of_forall hdF_lim)
    rw [Real.norm_eq_abs, abs_pow, abs_of_nonneg (norm_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hdF_bd n x) 2
  exact le_of_tendsto_of_tendsto' (hlim1.const_mul c) hlim2 hmain

end DGPS.FiniteN.ScalarFoldFIN060
