import DGPS.FiniteN.ScalarFoldFIN060F

/-!
# FIN060 (part G): the Hubbard auxiliary Poincare inequality for smooth bounded tests

From the `E1` inequality for `imsEta` (parts B, C) we derive `PoincareAt` for the Hubbard
auxiliary law of the scalar cosine model with test class `AuxSmoothFIN060`.
-/

open MeasureTheory ProbabilityTheory Matrix Set Metric
open scoped ContDiff ENNReal

namespace DGPS.FiniteN.ScalarFoldFIN060

open DGPS DGPS.Models DGPS.FiniteN.Tools.Hubbard DGPS.FiniteN.Tools.AuxiliaryTransfer
  DGPS.FiniteN.Tools.BoundedComparison

theorem integral_bump_pos_FIN060 {N : ℝ} {ψ : E1 → ℝ} (hψ : Continuous ψ)
    [hP : IsProbabilityMeasure (DGPS.FiniteN.imsEta N ψ)] :
    0 < ∫ x, bumpFIN060 x ∂(DGPS.FiniteN.imsEta N ψ) := by
  have hZt : ∫⁻ x, ENNReal.ofReal (Real.exp (-(N * ψ x))) ≠ ⊤ := by
    intro hT
    have := hP.measure_univ
    simp [DGPS.FiniteN.imsEta, hT] at this
  have hZ0 : ∫⁻ x, ENNReal.ofReal (Real.exp (-(N * ψ x))) ≠ 0 := by
    intro h0
    have h1 : (volume : Measure E1).withDensity
        (fun x => ENNReal.ofReal (Real.exp (-(N * ψ x)))) Set.univ = 0 := by
      rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]; exact h0
    have h2 := hP.measure_univ
    simp only [DGPS.FiniteN.imsEta, Measure.smul_apply, smul_eq_mul, h1, mul_zero] at h2
    exact zero_ne_one h2
  have hmeas : Measurable fun x : E1 => ENNReal.ofReal (Real.exp (-(N * ψ x))) :=
    (Real.continuous_exp.comp (continuous_const.mul hψ).neg).measurable.ennreal_ofReal
  unfold DGPS.FiniteN.imsEta
  rw [integral_smul_measure, integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine mul_pos ?_ ?_
  · exact ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 hZt) (ENNReal.inv_ne_top.2 hZ0)
  · have hc : Continuous fun x : E1 => (ENNReal.ofReal (Real.exp (-(N * ψ x)))).toReal • bumpFIN060 x := by
      simp_rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
      exact (Real.continuous_exp.comp (continuous_const.mul hψ).neg).smul bumpFIN060.continuous
    refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := 0) ?_ ?_ ?_
    · exact HasCompactSupport.smul_left (f := fun x : E1 => (ENNReal.ofReal (Real.exp (-(N * ψ x)))).toReal)
        bumpFIN060.hasCompactSupport
    · intro x
      simp only [Pi.zero_apply, smul_eq_mul]
      exact mul_nonneg ENNReal.toReal_nonneg bumpFIN060.nonneg
    · simp only [smul_eq_mul]
      rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
      exact (mul_pos (Real.exp_pos _) (bumpFIN060.pos_of_mem_ball (mem_ball_self bumpFIN060.rOut_pos))).ne'

/-- Chain rule for `G = g ∘ ofLp` on `E1`. -/
theorem fderiv_ofLp_comp_FIN060 {g : (Fin 1 → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (x : E1) (v : E1) :
    fderiv ℝ (fun y : E1 => g (WithLp.ofLp y)) x v = fderiv ℝ g (WithLp.ofLp x) (WithLp.ofLp v) := by
  have h := ((hg.differentiable (by simp)) (WithLp.ofLp x)).hasFDerivAt.comp x
    (PiLp.hasFDerivAt_ofLp 2 x)
  have h2 : fderiv ℝ (fun y : E1 => g (WithLp.ofLp y)) x = _ := h.fderiv
  rw [h2]
  rfl

theorem norm_fderiv_sq_FIN060 {g : (Fin 1 → ℝ) → ℝ} (hg : ContDiff ℝ ∞ g) (x : E1) :
    ‖fderiv ℝ (fun y : E1 => g (WithLp.ofLp y)) x‖ ^ 2 =
      ∑ j : Fin 1, (fderiv ℝ g (WithLp.ofLp x) (Pi.single j 1)) ^ 2 := by
  rw [norm_clm_E1_FIN060, fderiv_ofLp_comp_FIN060 hg, sq_abs, Fin.sum_univ_one]
  congr 2
  ext i
  fin_cases i
  simp [embFIN060]

theorem haux_FIN060 {κ : ℝ} (hκ : 2 < κ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℝ, ∀ N : ℕ+, N₀ ≤ (N : ℝ) →
      PoincareAt (auxLaw (dSFIN060 κ) (hSFIN060 (scalarFoldField κ)) uSFIN060 phiSFIN060
        (haar 1) N) AuxSmoothFIN060 auxGradSq (c * (N : ℝ) ^ (2 / 3 : ℝ))⁻¹ := by
  obtain ⟨c, hc, N₀, hB⟩ := fold_aux_poincare_FIN060 κ hκ
  refine ⟨c, hc, N₀, fun N hN => ?_⟩
  have hκ0 : 0 < κ := by linarith
  set h := scalarFoldField κ with hh
  have hyp := hubbardHyp_FIN060
  have hD := dSFIN060_posDef hκ0
  set μ := auxLaw (dSFIN060 κ) (hSFIN060 h) uSFIN060 phiSFIN060 (haar 1) N with hμ
  have hμP : IsProbabilityMeasure μ := isProbabilityMeasure_auxLaw hyp hD (hSFIN060 h) N
  set e := MeasurableEquiv.toLp 2 (Fin 1 → ℝ) with he
  set η := DGPS.FiniteN.imsEta (N : ℝ) (psiE (scalarPsi κ h)) with hη
  have hmap : μ.map e = η := auxLaw_map_FIN060 hκ0 h N
  have hηP : IsProbabilityMeasure η := by
    rw [← hmap]
    exact (Measure.isProbabilityMeasure_map_iff e.measurable.aemeasurable).2 hμP
  have hψc : Continuous (psiE (scalarPsi κ h)) :=
    (contDiff_psiE (ScalarFoldFIN057.scalarPsi_contDiff_FIN057 κ h)).continuous
  have hpos := integral_bump_pos_FIN060 (N := (N : ℝ)) hψc
  set ξ : E1 → ℝ := fun x => (∫ y, bumpFIN060 y ∂η)⁻¹ * bumpFIN060 x with hξdef
  have hξ : ContDiff ℝ ∞ ξ := contDiff_const.mul contDiff_bump_FIN060
  have hξc : HasCompactSupport ξ := bumpFIN060.hasCompactSupport.mul_left
  have hξ1 : ∫ x, ξ x ∂η = 1 := by
    rw [hξdef]
    simp only
    rw [integral_const_mul, inv_mul_cancel₀ hpos.ne']
  rintro g ⟨hg, ⟨B, hBg⟩, B', hB'g⟩
  set G : E1 → ℝ := fun x => g (WithLp.ofLp x) with hG
  have hGs : ContDiff ℝ ∞ G := hg.comp PiLp.contDiff_ofLp
  have hGB : ∀ x, |G x| ≤ B := fun x => hBg _
  have hderiv : ∀ x, ‖fderiv ℝ G x‖ ^ 2 ≤ B' := fun x => by
    rw [hG, norm_fderiv_sq_FIN060 hg]; exact hB'g _
  have hderiv' : ∀ x, ‖fderiv ℝ G x‖ ≤ B' + 1 := fun x => by
    have := hderiv x
    nlinarith [sq_nonneg (‖fderiv ℝ G x‖ - 1)]
  have hmain := cutoff_poincare_FIN060 η (c := c * (N : ℝ) ^ (2 / 3 : ℝ))
    (fun F hF hFc hF0 => hB (N : ℝ) hN F hF hFc hF0) ξ hξ hξc hξ1 G hGs hGB hderiv'
  have hlam : 0 < c * (N : ℝ) ^ (2 / 3 : ℝ) := mul_pos hc (Real.rpow_pos_of_pos (by positivity) _)
  have hmem : MemLp g 2 μ := MemLp.of_bound hg.continuous.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hBg x)
  have hGe : (G ∘ e) = g := rfl
  have hvar : variance g μ = ∫ x, (G x - ∫ y, G y ∂η) ^ 2 ∂η := by
    rw [← hGe, ← variance_map_equiv G e, hmap,
      variance_eq_integral hGs.continuous.aemeasurable]
  have hgrad : ∫⁻ w, auxGradSq g w ∂μ = ENNReal.ofReal (∫ x, ‖fderiv ℝ G x‖ ^ 2 ∂η) := by
    have hcont : Continuous fun x : E1 => ‖fderiv ℝ G x‖ ^ 2 :=
      ((hGs.continuous_fderiv (by simp)).norm).pow 2
    have hint : Integrable (fun x : E1 => ‖fderiv ℝ G x‖ ^ 2) η :=
      integrable_bdd_FIN060 η hcont (C := B') (fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]; exact hderiv x)
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _),
      ← hmap, lintegral_map_equiv]
    refine lintegral_congr fun w => ?_
    unfold auxGradSq
    rw [← norm_fderiv_sq_FIN060 hg]
    rfl
  show evariance g μ ≤ ENNReal.ofReal (c * (N : ℝ) ^ (2 / 3 : ℝ))⁻¹ * ∫⁻ w, auxGradSq g w ∂μ
  rw [← hmem.ofReal_variance_eq, hvar, hgrad, ← ENNReal.ofReal_mul (inv_nonneg.2 hlam.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [inv_mul_eq_div, le_div_iff₀ hlam]
  linarith [hmain]

end DGPS.FiniteN.ScalarFoldFIN060
