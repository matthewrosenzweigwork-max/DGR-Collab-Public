import DGPS.Examples.PolynomialSpeciesGapComparison

/-! Radial derivative control for the SAME actual gap graph. This derives the
positive amplitude factor needed by the sign-sensitive rate-envelope argument;
no radial estimate or amplitude scaling conclusion is a premise. -/

noncomputable section
open Filter Topology NormedSpace MeasureTheory
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem radial_integral (F : ℝ × ℝ → ℝ) (W : Set (ℝ × ℝ))
    (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W) (x : ℝ × ℝ)
    (hmem : ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ W) (hd0 : fderiv ℝ F 0 = 0) :
    fderiv ℝ F x x = ∫ t in (0 : ℝ)..1, fderiv ℝ (fderiv ℝ F) (t • x) x x := by
  have hDF : ContDiffOn ℝ 1 (fderiv ℝ F) W := hF.fderiv_of_isOpen hW (by simp)
  have hD2 : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ F)) W :=
    hDF.fderiv_of_isOpen hW (by simp)
  have hd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => fderiv ℝ F (s • x) x)
        (fderiv ℝ (fderiv ℝ F) (t • x) x x) t := by
    intro t ht
    have hFd := (hDF.contDiffAt (hW.mem_nhds (hmem t ht))).differentiableAt (by simp)
    have hs : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have hh := hFd.hasFDerivAt.comp_hasDerivAt t hs
    simpa using hh.clm_apply (hasDerivAt_const t x)
  have hc : ContinuousOn (fun t : ℝ => fderiv ℝ (fderiv ℝ F) (t • x) x x)
      (Set.Icc (0 : ℝ) 1) := by
    have hh := hD2.continuousOn.comp (continuous_id.smul continuous_const).continuousOn hmem
    exact (hh.clm_apply continuousOn_const).clm_apply continuousOn_const
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) (fun t ht => hd t (by simpa only [Set.uIcc_of_le zero_le_one] using ht))
    (hc.intervalIntegrable_of_Icc zero_le_one)
  simpa only [one_smul, zero_smul, hd0, zero_apply, sub_zero] using he.symm

private theorem segment_norm (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : ‖(θ, t • x)‖ ≤ ‖(θ, x)‖ := by
  change max ‖θ‖ ‖t • x‖ ≤ max ‖θ‖ ‖x‖
  apply max_le_max le_rfl
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
  exact mul_le_of_le_one_left (norm_nonneg x) ht.2

private theorem amp_norm_sq (x : ℝ × ℝ) : ‖x‖ ^ 2 ≤ x.1 ^ 2 + x.2 ^ 2 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  rcases le_total |x.1| |x.2| with h | h
  · rw [max_eq_right h, sq_abs]; nlinarith [sq_nonneg x.1]
  · rw [max_eq_left h, sq_abs]; nlinarith [sq_nonneg x.2]

/-- The actual radial gap derivative is R²/2 plus a uniform error tending to
zero with ALL independent parameters. Constants precede the parameters. -/
theorem polynomialReducedGap_radial_quadratic_error {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0) :
    ∃ δ K : ℝ, 0 < δ ∧ 0 ≤ K ∧
      (∀ (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ), ‖(θ, x)‖ < δ → polynomialGapSlice θ x ∈ U) ∧
      ∀ (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ), ‖(θ, x)‖ < δ →
        |fderiv ℝ (polynomialReducedGap ψ θ) x x - (x.1 ^ 2 + x.2 ^ 2) / 2| ≤
          K * ‖(θ, x)‖ * (x.1 ^ 2 + x.2 ^ 2) := by
  obtain ⟨δ, K, hδ, hK, hball, hLip⟩ := polynomialReducedGapHessian_lipschitz hU h0U hψ
  refine ⟨δ, K, hδ, hK, (fun θ x hx => hball (θ, x) hx), ?_⟩
  intro θ x hx
  let r := x.1 ^ 2 + x.2 ^ 2
  have hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, polynomialGapSlice θ (t • x) ∈ U :=
    fun t ht => hball _ ((segment_norm θ x t ht).trans_lt hx)
  have hψ0 : ψ (0 : PolynomialRangeParameters) = 0 := by
    have hp : ((0, 0, (0, 0), 0) : PolynomialRangeParameters) = 0 := by ext <;> rfl
    rw [← hp]
    exact hzero 0 0 0 (by rw [hp]; exact h0U)
  have hH0 : polynomialReducedGapHessian ψ 0 x x = r / 2 :=
    polynomialReducedGap_hessian_origin hU h0U hψ hψ0 hamp x.1 x.2
  have hbound (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      |polynomialReducedGapHessian ψ (θ, t • x) x x - r / 2| ≤ K * ‖(θ, x)‖ * r := by
    let A := polynomialReducedGapHessian ψ (θ, t • x) - polynomialReducedGapHessian ψ 0
    have hA : ‖A‖ ≤ K * ‖(θ, x)‖ :=
      (hLip _ ((segment_norm θ x t ht).trans_lt hx)).trans
        (mul_le_mul_of_nonneg_left (segment_norm θ x t ht) hK)
    calc
      _ = ‖A x x‖ := by rw [← hH0]; rfl
      _ ≤ ‖A x‖ * ‖x‖ := (A x).le_opNorm x
      _ ≤ (‖A‖ * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right (A.le_opNorm x) (norm_nonneg _)
      _ ≤ (K * ‖(θ, x)‖ * ‖x‖) * ‖x‖ := by gcongr
      _ = K * ‖(θ, x)‖ * ‖x‖ ^ 2 := by ring
      _ ≤ K * ‖(θ, x)‖ * r := mul_le_mul_of_nonneg_left (amp_norm_sq x)
        (mul_nonneg hK (norm_nonneg _))
  let W := polynomialGapSlice θ ⁻¹' U
  have hW : IsOpen W := hU.preimage (by
    have hs : ContDiff ℝ ∞ (polynomialGapSlice θ) :=
      contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const.prodMk contDiff_const))
    exact hs.continuous)
  have hF := polynomialReducedGap_smooth hψ θ
  have hD : ContDiffOn ℝ 1 (fderiv ℝ (polynomialReducedGap ψ θ)) W :=
    hF.fderiv_of_isOpen hW (by simp)
  have hDD : ContDiffOn ℝ 0 (fderiv ℝ (fderiv ℝ (polynomialReducedGap ψ θ))) W :=
    hD.fderiv_of_isOpen hW (by simp)
  have hcont : ContinuousOn (fun t : ℝ => polynomialReducedGapHessian ψ (θ, t • x) x x)
      (Set.Icc (0 : ℝ) 1) := by
    have hc := hDD.continuousOn.comp (continuous_id.smul continuous_const).continuousOn hseg
    exact (hc.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hInt : IntervalIntegrable (fun t : ℝ => polynomialReducedGapHessian ψ (θ, t • x) x x)
      volume 0 1 := hcont.intervalIntegrable_of_Icc zero_le_one
  have hd0 := (polynomialReducedGap_quadratic_factor hU hψ hzero θ x hseg).2.1
  have hFTC := radial_integral (polynomialReducedGap ψ θ) W hW hF x hseg hd0
  have he : (∫ t in (0 : ℝ)..1,
      polynomialReducedGapHessian ψ (θ, t • x) x x - r / 2) =
      fderiv ℝ (polynomialReducedGap ψ θ) x x - r / 2 := by
    rw [intervalIntegral.integral_sub hInt (intervalIntegrable_const)]
    change (∫ t in (0 : ℝ)..1, (fderiv ℝ (fderiv ℝ (polynomialReducedGap ψ θ)) (t • x)) x x) - _ = _
    rw [← hFTC, intervalIntegral.integral_const]
    simp

  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (C := K * ‖(θ, x)‖ * r)
    (f := fun t : ℝ => polynomialReducedGapHessian ψ (θ, t • x) x x - r / 2) (by
      intro t ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := by
        have hi : t ∈ Set.Ioc (0 : ℝ) 1 := by simpa only [Set.uIoc_of_le zero_le_one] using ht
        exact ⟨hi.1.le, hi.2⟩
      simpa only [Real.norm_eq_abs] using hbound t ht')
  rw [he] at hb
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hb

/-- In one smaller actual neighborhood the radial derivative has a strictly
positive squared-amplitude factor. This is independent of the sign of gamma. -/
theorem polynomialReducedGap_radial_comparison {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ), ‖(θ, x)‖ < δ →
      polynomialGapSlice θ x ∈ U ∧
      (x.1 ^ 2 + x.2 ^ 2) / 4 ≤ fderiv ℝ (polynomialReducedGap ψ θ) x x ∧
      fderiv ℝ (polynomialReducedGap ψ θ) x x ≤ 3 * (x.1 ^ 2 + x.2 ^ 2) / 4 := by
  obtain ⟨δ, K, hδ, hK, hball, hError⟩ := polynomialReducedGap_radial_quadratic_error hU h0U hψ hzero hamp
  let ε := min δ (1 / (4 * (K + 1)))
  have hK1 : 0 < K + 1 := by linarith
  have hε : 0 < ε := lt_min hδ (div_pos zero_lt_one (mul_pos (by norm_num) hK1))
  refine ⟨ε, hε, ?_⟩
  intro θ x hx
  have hxδ : ‖(θ, x)‖ < δ := hx.trans_le (min_le_left _ _)
  have hxK : ‖(θ, x)‖ < 1 / (4 * (K + 1)) := hx.trans_le (min_le_right _ _)
  have hsmall := (lt_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) hK1)).mp hxK
  have hk : K * ‖(θ, x)‖ ≤ 1 / 4 := by nlinarith [norm_nonneg (θ, x)]
  have hr : 0 ≤ x.1 ^ 2 + x.2 ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have he := (hError θ x hxδ).trans (mul_le_mul_of_nonneg_right hk hr)
  obtain ⟨hl, hu⟩ := abs_le.mp he
  refine ⟨hball θ x hxδ, ?_, ?_⟩ <;> linarith

end DGPS.Examples.PolynomialSpecies
