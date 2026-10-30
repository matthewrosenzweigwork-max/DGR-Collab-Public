import DGPS.Examples.PolynomialSpeciesRangeGraphRayTaylor

/-! The actual graph's uniform scaled mixed jet, with independent tilt and
rate parameters. No selected-root differentiation or remainder hypothesis is
used. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

local instance : NormedAddCommGroup (PolynomialRangeParameters →L[ℝ] E_STR02969) := inferInstance
local instance : NormedSpace ℝ (PolynomialRangeParameters →L[ℝ] E_STR02969) := inferInstance

private theorem quadratic_lipschitz
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hD0 : fderiv ℝ ψ 0 = 0) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧ Metric.ball (0 : PolynomialRangeParameters) δ ⊆ U ∧
      ∀ p q : PolynomialRangeParameters, ‖p‖ < δ → ‖q‖ < δ →
        ‖ψ p - ψ q‖ ≤ K * max ‖p‖ ‖q‖ * ‖p - q‖ := by
  have hDs : ContDiffOn ℝ 1 (fderiv ℝ ψ) U := hψ.fderiv_of_isOpen hU (by simp)
  obtain ⟨K, T, hT, hLip⟩ := (hDs.contDiffAt (hU.mem_nhds h0U)).exists_lipschitzOnWith
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hT (hU.mem_nhds h0U))
  have h0ball : (0 : PolynomialRangeParameters) ∈ Metric.ball 0 δ := by
    simpa only [Metric.mem_ball, dist_self] using hδ
  have hballU : Metric.ball (0 : PolynomialRangeParameters) δ ⊆ U := fun p hp => (hball hp).2
  have hDbound : ∀ z : PolynomialRangeParameters, ‖z‖ < δ → ‖fderiv ℝ ψ z‖ ≤ K * ‖z‖ := by
    intro z hz
    have hzball : z ∈ Metric.ball (0 : PolynomialRangeParameters) δ := by
      simpa only [Metric.mem_ball, dist_zero_right] using hz
    have he := hLip.dist_le_mul z (hball hzball).1 0 (hball h0ball).1
    simpa only [hD0, dist_zero_right] using he
  refine ⟨δ, K, hδ, K.coe_nonneg, hballU, ?_⟩
  intro p q hp hq
  let R := max ‖p‖ ‖q‖
  have hR : R < δ := max_lt hp hq
  have hsmall : ∀ z ∈ Metric.closedBall (0 : PolynomialRangeParameters) R, ‖z‖ < δ := by
    intro z hz
    have hz' : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    exact hz'.trans_lt hR
  have he := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hψ.contDiffAt (hU.mem_nhds (hballU (by
      simpa only [Metric.mem_ball, dist_zero_right] using hsmall z hz)))).differentiableAt (by simp))
    (fun z hz => (hDbound z (hsmall z hz)).trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz) K.coe_nonneg))
    (convex_closedBall (0 : PolynomialRangeParameters) R)
    (show q ∈ Metric.closedBall (0 : PolynomialRangeParameters) R by
      simpa only [Metric.mem_closedBall, dist_zero_right] using le_max_right ‖p‖ ‖q‖)
    (show p ∈ Metric.closedBall (0 : PolynomialRangeParameters) R by
      simpa only [Metric.mem_closedBall, dist_zero_right] using le_max_left ‖p‖ ‖q‖)
  exact he

/-- A true full coefficient-box jet for the SAME interacting graph. The tilt
and normalized rate coordinates have their actual scaled sizes. The output is
an E-norm estimate, hence the original inherited C2 Holder norm estimate. -/
theorem polynomial_range_graph_scaled_mixed_remainder
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (hψ0 : ψ 0 = 0)
    (hgraph : ∀ p ∈ U, polynomialRangeMap (p, ψ p) = 0)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hfirst : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (M : ℝ) (hM : 1 ≤ M) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 < K ∧
      ∀ a b σ α h : ℝ, |a| ≤ M → |b| ≤ M → |σ| ≤ M → |α| ≤ M →
        0 ≤ h → h ≤ δ →
        ((h * a, h * b, (h, h ^ 4 * σ), h ^ 2 * α) : PolynomialRangeParameters) ∈ U ∧
        ‖ψ (h * a, h * b, (h, h ^ 4 * σ), h ^ 2 * α) -
          (h ^ 2 / 2) • polynomialOriginMixedSecondCorrection a b‖ ≤ K * h ^ 3 := by
  obtain ⟨δ₁, K₁, hδ₁, hK₁, hray⟩ :=
    polynomial_range_graph_mixed_ray_remainder hU h0U hψ hψ0 hgraph hzero hfirst M hM
  obtain ⟨δ₂, K₂, hδ₂, hK₂, hballU, hquad⟩ := quadratic_lipschitz hU h0U hψ
    (polynomial_range_graph_full_derivative_zero hU h0U hψ hzero hfirst)
  let δ := min δ₁ (min 1 (δ₂ / (2 * M)))
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hδ : 0 < δ := lt_min hδ₁ (lt_min zero_lt_one (div_pos hδ₂ (by positivity)))
  refine ⟨δ, K₁ + K₂ * M ^ 2, hδ, add_pos_of_pos_of_nonneg hK₁ (by positivity), ?_⟩
  intro a b σ α h ha hb hσ hα hh hhδ
  have hh1 : h ≤ 1 := hhδ.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hhδ₁ : h ≤ δ₁ := hhδ.trans (min_le_left _ _)
  have hsize : h * M < δ₂ := by
    have hs : h ≤ δ₂ / (2 * M) := hhδ.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hs' := (le_div_iff₀ (by positivity : 0 < 2 * M)).1 hs
    nlinarith
  have h2 : h ^ 2 ≤ h := by nlinarith
  have h4 : h ^ 4 ≤ h ^ 2 := by
    have hs : h ^ 2 ≤ 1 := h2.trans hh1
    nlinarith [mul_nonneg (sq_nonneg h) (sub_nonneg.mpr hs)]
  have h4M : h ^ 4 * M ≤ h * M := mul_le_mul_of_nonneg_right (h4.trans h2) hMp.le
  have h2M : h ^ 2 * M ≤ h * M := mul_le_mul_of_nonneg_right h2 hMp.le
  have h42M : h ^ 4 * M ≤ h ^ 2 * M := mul_le_mul_of_nonneg_right h4 hMp.le
  let p : PolynomialRangeParameters := (h * a, h * b, (h, h ^ 4 * σ), h ^ 2 * α)
  let q : PolynomialRangeParameters := h • ((a, b, (1, 0), 0) : PolynomialRangeParameters)
  have hp : ‖p‖ ≤ h * M := by
    simp only [p, Prod.norm_def, Real.norm_eq_abs, abs_mul, abs_of_nonneg hh,
      abs_pow]
    exact max_le (mul_le_mul_of_nonneg_left ha hh) (max_le
      (mul_le_mul_of_nonneg_left hb hh) (max_le
        (max_le (le_mul_of_one_le_right hh hM)
          ((mul_le_mul_of_nonneg_left hσ (pow_nonneg hh 4)).trans h4M))
        ((mul_le_mul_of_nonneg_left hα (sq_nonneg h)).trans h2M)))
  have hq : ‖q‖ ≤ h * M := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hh]
    apply mul_le_mul_of_nonneg_left _ hh
    simp only [Prod.norm_def, Real.norm_eq_abs, abs_one, norm_zero, max_eq_left zero_le_one]
    exact max_le ha (max_le hb hM)
  have hpq : ‖p - q‖ ≤ h ^ 2 * M := by
    have he : p - q = ((0, 0, (0, h ^ 4 * σ), h ^ 2 * α) : PolynomialRangeParameters) := by
      ext <;> simp [p, q]
    rw [he]
    simp only [Prod.norm_def, norm_zero, Real.norm_eq_abs, abs_mul, abs_pow,
      abs_of_nonneg hh]
    apply max_le
    · positivity
    · apply max_le
      · positivity
      · apply max_le
        · exact max_le (by positivity)
            ((mul_le_mul_of_nonneg_left hσ (pow_nonneg hh 4)).trans h42M)
        · exact mul_le_mul_of_nonneg_left hα (sq_nonneg h)
  have hp' : ‖p‖ < δ₂ := hp.trans_lt hsize
  have hq' : ‖q‖ < δ₂ := hq.trans_lt hsize
  have hdiff : ‖ψ p - ψ q‖ ≤ K₂ * M ^ 2 * h ^ 3 := by
    calc
      _ ≤ K₂ * max ‖p‖ ‖q‖ * ‖p - q‖ := hquad p q hp' hq'
      _ ≤ K₂ * (h * M) * (h ^ 2 * M) := by gcongr; exact max_le hp hq
      _ = _ := by ring
  obtain ⟨_, hr⟩ := hray a b h ha hb hh hhδ₁
  refine ⟨hballU (by simpa only [Metric.mem_ball, dist_zero_right] using hp'), ?_⟩
  change ‖ψ p - (h ^ 2 / 2) • polynomialOriginMixedSecondCorrection a b‖ ≤ _
  calc
    _ ≤ ‖ψ p - ψ q‖ + ‖ψ q - (h ^ 2 / 2) • polynomialOriginMixedSecondCorrection a b‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ K₂ * M ^ 2 * h ^ 3 + K₁ * h ^ 3 := add_le_add hdiff hr
    _ = _ := by ring

end DGPS.Examples.PolynomialSpecies
