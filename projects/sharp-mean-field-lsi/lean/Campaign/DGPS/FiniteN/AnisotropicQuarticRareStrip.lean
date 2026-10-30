import DGPS.FiniteN.AnisotropicQuarticStableDirection
import DGPS.FiniteN.AnisotropicQuarticAuxiliaryMass

/-! Actual stable Gaussian integration on an enlarged rare strip. The width in the
longitudinal direction is fixed, while the entire Gaussian is retained. -/

open MeasureTheory Set
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066

namespace DGPS.FiniteN

/-- A real Gaussian upper bound for the actual enlarged latent strip. All constants
are chosen before particle number and transverse width; there is no rare-mass input. -/
theorem quartic_rare_strip_raw_upper :
    ∃ δ c K : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < c ∧ 0 < K ∧ ∀ N s L : ℝ,
      0 < N → 0 ≤ s → 0 ≤ L → s ^ 2 ≤ δ → N * s ^ 4 ≤ L →
      (∫ p : ℝ × ℝ in Icc (-δ) δ ×ˢ Icc (-s) s,
          Real.exp (-(N * quarticPsi_FIN066 !₂[-4 + p.1, p.2]))) ≤
        (Real.exp (K * L) * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0]))) *
          Real.sqrt (Real.pi / (N * c)) * (2 * s) := by
  obtain ⟨δ, c, K, hδ, hδ1, hc, hK, hpot⟩ := quartic_stable_direction_lower
  refine ⟨δ, c, K, hδ, hδ1, hc, hK, fun N s L hN hs hL hsδ hscale => ?_⟩
  let B := Real.exp (K * L) * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0]))
  let Q := Icc (-δ) δ ×ˢ Icc (-s) s
  have hQm : MeasurableSet Q := isClosed_Icc.measurableSet.prod isClosed_Icc.measurableSet
  have hQcompact : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hψ : Continuous (fun p : ℝ × ℝ => quarticPsi_FIN066 !₂[-4 + p.1, p.2]) :=
    quartic_potential_contDiff.continuous.comp (by fun_prop)
  have hfi : IntegrableOn (fun p : ℝ × ℝ =>
      Real.exp (-(N * quarticPsi_FIN066 !₂[-4 + p.1, p.2]))) Q :=
    (Real.continuous_exp.comp (hψ.const_mul N).neg).continuousOn.integrableOn_compact hQcompact
  have hgi : IntegrableOn (fun p : ℝ × ℝ =>
      (B * Real.exp (-(N * c) * p.1 ^ 2)) * (1 : ℝ)) Q :=
    (by fun_prop : Continuous (fun p : ℝ × ℝ =>
      (B * Real.exp (-(N * c) * p.1 ^ 2)) * (1 : ℝ))).continuousOn.integrableOn_compact hQcompact
  have hpoint : ∀ p ∈ Q, Real.exp (-(N * quarticPsi_FIN066 !₂[-4 + p.1, p.2])) ≤
      (B * Real.exp (-(N * c) * p.1 ^ 2)) * (1 : ℝ) := by
    intro p hp
    have hysq : p.2 ^ 2 ≤ s ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg p.2) (abs_le.mpr hp.2) 2
    have hy4 : p.2 ^ 4 ≤ s ^ 4 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg p.2) hysq 2
    have hp0 := mul_le_mul_of_nonneg_left
      (hpot p.1 p.2 (abs_le.mpr hp.1) (hysq.trans hsδ)) hN.le
    have he := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hy4 hN.le).trans hscale) hK.le
    dsimp only [B]
    rw [mul_one, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hp0, he]
  have hmono := setIntegral_mono_on hfi hgi hQm hpoint
  have hgI := integrable_exp_neg_mul_sq (mul_pos hN hc)
  have hgauss : (∫ u in Icc (-δ) δ, Real.exp (-(N * c) * u ^ 2)) ≤
      Real.sqrt (Real.pi / (N * c)) := by
    rw [← integral_gaussian (N * c)]
    exact setIntegral_le_integral hgI (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfinal := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgauss hB)
    (by positivity : 0 ≤ 2 * s)
  have hlength : (∫ _ : ℝ in Icc (-s) s, (1 : ℝ)) = 2 * s := by
    rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc_of_le (by linarith)]
    ring
  have hfactor : (∫ p : ℝ × ℝ in Q,
      (B * Real.exp (-(N * c) * p.1 ^ 2)) * (1 : ℝ)) =
      (B * ∫ u in Icc (-δ) δ, Real.exp (-(N * c) * u ^ 2)) * (2 * s) := by
    dsimp only [Q]
    rw [Measure.volume_eq_prod,
      setIntegral_prod_mul (fun u : ℝ => B * Real.exp (-(N * c) * u ^ 2))
        (fun _ : ℝ => (1 : ℝ)) (Icc (-δ) δ) (Icc (-s) s),
      integral_const_mul, hlength]
  rw [hfactor] at hmono
  exact hmono.trans hfinal

end DGPS.FiniteN
