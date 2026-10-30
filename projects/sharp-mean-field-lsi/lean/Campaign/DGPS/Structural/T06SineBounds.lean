import DGPS.Structural.AmplitudePoincare

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DGPS.Structural
variable {d : ℕ}

/-- Exact Haar variance and energy of the original-domain first sine mode. -/
theorem t06_sine_moments (p : Fin d) :
    weightedVariance (⟨haar d, inferInstance⟩ : ProbabilityMeasure (Torus d)) (sineTest p) = 1/2 ∧
      (∫ x, ‖smoothGrad (sineTest p) x‖ ^ 2 ∂haar d) = a0 / 2 := by
  have hmean : ∫ x, sineTest p x ∂haar d = 0 := by
    unfold sineTest
    rw [integral_haar_coordProj p continuous_sineMode]
    simpa using (integral_haar1_sine_comp id).trans integral_sin_two_pi_Ioc
  have hsq : ∫ x, sineTest p x ^ 2 ∂haar d = 1 / 2 := by
    unfold sineTest
    rw [integral_haar_coordProj p (F := fun z => sineMode z ^ 2) (continuous_sineMode.pow 2)]
    exact (integral_haar1_sine_comp (fun y => y ^ 2)).trans integral_sin_sq_Ioc
  constructor
  · unfold weightedVariance
    simp only [ProbabilityMeasure.coe_mk]
    rw [hmean]
    simpa using hsq
  · simp_rw [norm_smoothGrad_sineTest_sq]
    rw [integral_haar_coordProj p (F := fun z => coordPartial 0 sineMode z ^ 2)
      ((isSmoothPeriodic_sineMode.continuous_coordPartial 0).pow 2)]
    simp_rw [coordPartial_sineMode]
    calc (∫ z : Torus 1, (2 * Real.pi * Real.cos (2 * Real.pi * SharpLSI.secT z 0)) ^ 2 ∂haar 1)
        = ∫ t in Set.Ioc (0 : ℝ) 1, (2 * Real.pi * Real.cos (2 * Real.pi * t)) ^ 2 :=
          DGPS.Analysis.integral_haar1_secT (fun t : ℝ => (2 * Real.pi * Real.cos (2 * Real.pi * t)) ^ 2)
      _ = a0 / 2 := by
        simp_rw [mul_pow]
        rw [integral_const_mul, integral_cos_sq_Ioc]
        unfold a0
        ring

/-- A bounded reference transfers the sine Rayleigh test with exactly the
upper/lower density ratio, not its square. -/
theorem t06_sine_rayleigh_le_density_ratio (P : BoundedPositiveReference d)
    (p : Fin d) {c C M : ℝ} (hc : 0 < c)
    (hlow : ∀ᵐ x ∂haar d, c ≤ P.density x)
    (hup : ∀ᵐ x ∂haar d, P.density x ≤ C)
    (hratio : C ≤ Real.exp M * c) :
    let μ : ProbabilityMeasure (Torus d) := ⟨P.measure, P.isProbabilityMeasure⟩
    0 < weightedVariance μ (sineTest p) ∧
      (∫ x, ‖smoothGrad (sineTest p) x‖ ^ 2 ∂P.measure) /
        weightedVariance μ (sineTest p) ≤ a0 * Real.exp M := by
  let μ : ProbabilityMeasure (Torus d) := ⟨P.measure, P.isProbabilityMeasure⟩
  let m : ProbabilityMeasure (Torus d) := ⟨haar d, inferInstance⟩
  have hC : 0 < C := by
    obtain ⟨x, hx, hy⟩ := (hlow.and hup).exists
    exact hc.trans_le (hx.trans hy)
  have hu := isSmoothPeriodic_sineTest p
  have huμ : MemLp (sineTest p) 2 (μ : Measure (Torus d)) :=
    hu.continuous_torus.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hum : MemLp (sineTest p) 2 (m : Measure (Torus d)) := hu.isWeakGradient.memLp
  have hv := DGPS.Examples.ex007_variance_le (μ := μ) (ν := m) (inv_pos.mpr hc)
    (def025_haar_le_smul P hc hlow) hum huμ
  rw [(t06_sine_moments p).1] at hv
  have hvlow : c / 2 ≤ weightedVariance μ (sineTest p) := by
    have hh := mul_le_mul_of_nonneg_left hv hc.le
    rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul] at hh
    linarith
  have hvpos : 0 < weightedVariance μ (sineTest p) := (half_pos hc).trans_le hvlow
  have hi : Integrable (fun x => ‖smoothGrad (sineTest p) x‖ ^ 2) (haar d) :=
    hu.isWeakGradient.memLp_grad.norm.integrable_sq
  have hE : (∫ x, ‖smoothGrad (sineTest p) x‖ ^ 2 ∂P.measure) ≤ C * (a0 / 2) := by
    calc (∫ x, ‖smoothGrad (sineTest p) x‖ ^ 2 ∂P.measure)
        ≤ ∫ x, ‖smoothGrad (sineTest p) x‖ ^ 2 ∂(ENNReal.ofReal C • haar d) :=
          integral_mono_measure (def025_measure_le_smul P hup)
            (Filter.Eventually.of_forall fun _ => sq_nonneg _)
            (hi.smul_measure (by simp))
      _ = C * (a0 / 2) := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hC.le, smul_eq_mul,
          (t06_sine_moments p).2]
  refine ⟨hvpos, (div_le_iff₀ hvpos).mpr ?_⟩
  calc (∫ x, ‖smoothGrad (sineTest p) x‖ ^ 2 ∂P.measure)
      ≤ C * (a0 / 2) := hE
    _ ≤ (Real.exp M * c) * (a0 / 2) :=
      mul_le_mul_of_nonneg_right hratio (half_pos a0_pos).le
    _ = (a0 * Real.exp M) * (c / 2) := by ring
    _ ≤ (a0 * Real.exp M) * weightedVariance μ (sineTest p) :=
      mul_le_mul_of_nonneg_left hvlow (mul_pos a0_pos (Real.exp_pos M)).le

end DGPS.Structural
