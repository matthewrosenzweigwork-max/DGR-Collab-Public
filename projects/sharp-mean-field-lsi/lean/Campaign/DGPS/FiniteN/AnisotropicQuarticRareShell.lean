import DGPS.FiniteN.AnisotropicQuarticRareStrip

/-! Additional genuine exponential cost on the longitudinal derivative shell. -/

open MeasureTheory Set
open DGPS.Models DGPS.FiniteN.QuarticSaddleGlobalFIN066

namespace DGPS.FiniteN

/-- Half of the stable quadratic controls the fixed longitudinal shell, while
the other half is still integrated as a Gaussian. The quartic transverse error
costs only a fixed factor when its scaled width is bounded. -/
theorem quartic_rare_shell_raw_upper :
    ∃ δ c K : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < c ∧ 0 < K ∧ ∀ N s L r : ℝ,
      0 < N → 0 ≤ s → 0 ≤ L → 0 ≤ r → s ^ 2 ≤ δ → N * s ^ 4 ≤ L →
      (∫ p : ℝ × ℝ in (Icc (-δ) δ ∩ {u | r ≤ |u|}) ×ˢ Icc (-s) s,
          Real.exp (-(N * quarticPsi_FIN066 !₂[-4 + p.1, p.2]))) ≤
        (Real.exp (K * L) * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0])) *
          Real.exp (-(N * c / 2) * r ^ 2)) *
            Real.sqrt (Real.pi / (N * c / 2)) * (2 * s) := by
  obtain ⟨δ, c, K, hδ, hδ1, hc, hK, hpot⟩ := quartic_stable_direction_lower
  refine ⟨δ, c, K, hδ, hδ1, hc, hK, fun N s L r hN hs hL hr hsδ hscale => ?_⟩
  let B := Real.exp (K * L) * Real.exp (-(N * quarticPsi_FIN066 !₂[-4, 0])) *
    Real.exp (-(N * c / 2) * r ^ 2)
  let T := Icc (-δ) δ ∩ {u : ℝ | r ≤ |u|}
  let S := T ×ˢ Icc (-s) s
  let Q := Icc (-δ) δ ×ˢ Icc (-s) s
  have hSm : MeasurableSet S :=
    (measurableSet_Icc.inter (isClosed_le continuous_const continuous_abs).measurableSet).prod
      measurableSet_Icc
  have hSQ : S ⊆ Q := fun p hp => ⟨hp.1.1, hp.2⟩
  have hQcompact : IsCompact Q := isCompact_Icc.prod isCompact_Icc
  have hψ : Continuous (fun p : ℝ × ℝ => quarticPsi_FIN066 !₂[-4 + p.1, p.2]) :=
    quartic_potential_contDiff.continuous.comp (by fun_prop)
  have hfi : IntegrableOn (fun p : ℝ × ℝ =>
      Real.exp (-(N * quarticPsi_FIN066 !₂[-4 + p.1, p.2]))) S :=
    ((Real.continuous_exp.comp (hψ.const_mul N).neg).continuousOn.integrableOn_compact
      hQcompact).mono_set hSQ
  have hgi : IntegrableOn (fun p : ℝ × ℝ =>
      (B * Real.exp (-(N * c / 2) * p.1 ^ 2)) * (1 : ℝ)) S :=
    ((by fun_prop : Continuous (fun p : ℝ × ℝ =>
      (B * Real.exp (-(N * c / 2) * p.1 ^ 2)) * (1 : ℝ))).continuousOn.integrableOn_compact
        hQcompact).mono_set hSQ
  have hpoint : ∀ p ∈ S, Real.exp (-(N * quarticPsi_FIN066 !₂[-4 + p.1, p.2])) ≤
      (B * Real.exp (-(N * c / 2) * p.1 ^ 2)) * (1 : ℝ) := by
    intro p hp
    have hysq : p.2 ^ 2 ≤ s ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg p.2) (abs_le.mpr hp.2) 2
    have hy4 : p.2 ^ 4 ≤ s ^ 4 := by
      simpa only [← pow_mul] using pow_le_pow_left₀ (sq_nonneg p.2) hysq 2
    have hr2 : r ^ 2 ≤ p.1 ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hr hp.1.2 2
    have hp0 := mul_le_mul_of_nonneg_left
      (hpot p.1 p.2 (abs_le.mpr hp.1.1) (hysq.trans hsδ)) hN.le
    have he := mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left hy4 hN.le).trans hscale) hK.le
    have hshell := mul_le_mul_of_nonneg_left hr2 (by positivity : 0 ≤ N * c / 2)
    dsimp only [B]
    rw [mul_one, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith only [hp0, he, hshell]
  have hmono := setIntegral_mono_on hfi hgi hSm hpoint
  have hgI := integrable_exp_neg_mul_sq (by positivity : 0 < N * c / 2)
  have hgauss : (∫ u in T, Real.exp (-(N * c / 2) * u ^ 2)) ≤
      Real.sqrt (Real.pi / (N * c / 2)) := by
    rw [← integral_gaussian (N * c / 2)]
    exact setIntegral_le_integral hgI (Filter.Eventually.of_forall fun u => (Real.exp_pos _).le)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hfinal := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgauss hB)
    (by positivity : 0 ≤ 2 * s)
  have hlength : (∫ _ : ℝ in Icc (-s) s, (1 : ℝ)) = 2 * s := by
    rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc_of_le (by linarith)]
    ring
  have hfactor : (∫ p : ℝ × ℝ in S,
      (B * Real.exp (-(N * c / 2) * p.1 ^ 2)) * (1 : ℝ)) =
      (B * ∫ u in T, Real.exp (-(N * c / 2) * u ^ 2)) * (2 * s) := by
    dsimp only [S]
    rw [Measure.volume_eq_prod,
      setIntegral_prod_mul (fun u : ℝ => B * Real.exp (-(N * c / 2) * u ^ 2))
        (fun _ : ℝ => (1 : ℝ)) T (Icc (-s) s),
      integral_const_mul, hlength]
  rw [hfactor] at hmono
  exact hmono.trans hfinal

end DGPS.FiniteN
