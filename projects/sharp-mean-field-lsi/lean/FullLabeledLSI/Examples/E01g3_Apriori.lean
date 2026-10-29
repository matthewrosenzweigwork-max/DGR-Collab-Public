import FullLabeledLSI.Examples.E01g1_Basic

/-!
# Lane D, Task C (E01g3): a priori bounds along sequences with bounded scalar quotient
-/

open MeasureTheory InformationTheory Filter Topology
open scoped Real ENNReal ContDiff

namespace SharpLSI.FL.Ex.LaneD

open SharpLSI

theorem abs_convT_le {g ρ : Torus 1 → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ z, |g z| ≤ M)
    (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1) (x : Torus 1) : |convT g ρ x| ≤ M := by
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  rw [convT_eq_conv h0 h1]
  have := norm_integral_le_of_norm_le_const (μ := densMeasure ρ)
    (f := fun y => g (x - y)) (C := M) (Eventually.of_forall fun y => by simpa using hM (x - y))
  simpa using this

theorem log_one_add_le (y : ℝ) (hy : 0 ≤ y) : Real.log (1 + y) ≤ 2 * Real.sqrt y := by
  have h1 : 0 < 1 + y := by linarith
  have hs : Real.sqrt (1 + y) ≤ 1 + Real.sqrt y := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [Real.sq_sqrt hy, Real.sqrt_nonneg y]
  have hlog : Real.log (1 + y) = 2 * Real.log (Real.sqrt (1 + y)) := by
    rw [Real.log_sqrt h1.le]; ring
  have hpos : 0 < Real.sqrt (1 + y) := Real.sqrt_pos.2 h1
  have := Real.log_le_sub_one_of_pos hpos
  rw [hlog]; linarith

theorem IR_le_two_DR {C ρ : Torus 1 → ℝ} (hC : GoodKernel C) (h0 : ∀ x, 0 ≤ ρ x)
    (h1 : ∫ x, ρ x ∂haar 1 = 1) (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) {M : ℝ}
    (hM : ∀ z, |dT C z| ≤ M) : IR ρ ≤ 2 * DR C ρ + 2 * M ^ 2 := by
  have hρi := integrable_of_integral_eq_one' h1
  set w : Torus 1 → ℝ := fun x => weakGrad (fun y => Real.sqrt (ρ y)) x 0 with hw
  set b : Torus 1 → ℝ := convT (dT C) ρ with hb
  have hbM : ∀ x, |b x| ≤ M := abs_convT_le (continuous_of_smooth (isSmoothT_dT hC.smooth)) hM h0 h1
  have hwL : MemLp w 2 (haar 1) := memLp_weakGrad_zero hH
  have iD := integrable_DR_integrand hC h0 h1 hH
  have i1 : Integrable (fun x => (2 * w x) ^ 2) (haar 1) := (hwL.const_mul 2).integrable_sq
  have hbm : Measurable b := by
    have hs : IsSmoothT b := by
      haveI := isProbabilityMeasure_densMeasure' h0 h1
      rw [hb, convT_eq_conv h0 h1]; exact isSmoothT_conv (isSmoothT_dT hC.smooth) _
    exact (continuous_of_smooth hs).measurable
  have hρbM : ∀ x, ρ x * b x ^ 2 ≤ ρ x * M ^ 2 := fun x =>
    mul_le_mul_of_nonneg_left (by nlinarith [hbM x, abs_nonneg (b x), sq_abs (b x)]) (h0 x)
  have i2 : Integrable (fun x => ρ x * b x ^ 2) (haar 1) := by
    refine Integrable.mono' (hρi.mul_const (M ^ 2)) ?_ (Eventually.of_forall fun x => ?_)
    · exact hρi.aestronglyMeasurable.mul (hbm.pow_const 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 x) (sq_nonneg _))]
      exact hρbM x
  have hpt : ∀ x, (2 * w x) ^ 2 ≤ 2 * (2 * w x - Real.sqrt (ρ x) * b x) ^ 2 + 2 * (ρ x * b x ^ 2) := by
    intro x
    have h := Real.sq_sqrt (h0 x)
    nlinarith [sq_nonneg (2 * w x - 2 * (Real.sqrt (ρ x) * b x)), mul_pow (Real.sqrt (ρ x)) (b x) 2]
  have hIR : IR ρ = ∫ x, (2 * w x) ^ 2 ∂haar 1 := by
    unfold IR
    rw [← integral_const_mul]; congr 1; funext x; simp only [hw]; ring
  have iS : Integrable (fun x => 2 * (2 * w x - Real.sqrt (ρ x) * b x) ^ 2 + 2 * (ρ x * b x ^ 2))
      (haar 1) := (iD.const_mul 2).add (i2.const_mul 2)
  have hle := integral_mono i1 iS hpt
  rw [integral_add (iD.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul] at hle
  have hint2 : ∫ x, ρ x * b x ^ 2 ∂haar 1 ≤ M ^ 2 := by
    have := integral_mono i2 (hρi.mul_const (M ^ 2)) hρbM
    rwa [integral_mul_const, h1, one_mul] at this
  rw [hIR]
  unfold DR
  simp only [hb, hw] at *
  linarith

/-- `G ≤ H` (attractive interaction of positive type). -/
theorem GR_le_entR {C ρ : Torus 1 → ℝ} (hC : GoodKernel C) (hCpos : ∀ n : ℤ, n ≠ 0 → 0 ≤ chat C n)
    (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1) : GR C ρ ≤ entR ρ := by
  haveI := isProbabilityMeasure_densMeasure' h0 h1
  have hpos : ∀ k : Fin 1 → ℤ, 0 ≤ (cf C k).re := by
    intro k
    rw [eq_K1 k]
    by_cases hk : k 0 = 0
    · rw [hk]
      have : K1 0 = 0 := K1_zero
      rw [this, cf_zero_eq]
      simp [hC.meanZero]
    · rw [← chat_eq]; exact hCpos _ hk
  have := Sec8.Qint_nonneg_of_K hC.smooth hpos (densMeasure ρ)
  rw [Qint_eq_cqR (continuous_of_smooth hC.smooth) h0 h1] at this
  unfold GR; linarith

theorem IR_nonneg (ρ : Torus 1 → ℝ) : 0 ≤ IR ρ := by
  unfold IR; exact mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg _)

theorem entR_le_log {ρ : Torus 1 → ℝ} (h0 : ∀ x, 0 ≤ ρ x) (h1 : ∫ x, ρ x ∂haar 1 = 1)
    (hH : MemH1 (haar 1) (fun x => Real.sqrt (ρ x))) :
    entR ρ ≤ 6 * Real.log (1 + IR ρ / (12 * aCos)) := by
  have h := (circle_quantitative_lsi_aux h0 h1 hH).2.2.1
  have hf : (fisherInfo (densMeasure ρ) (haar 1)).toReal = IR ρ := by
    rw [fisherInfo_densMeasure_eq h0 h1 hH]
    exact ENNReal.toReal_ofReal (IR_nonneg ρ)
  rw [hf] at h
  exact h

/-- A priori bound: bounded scalar quotient implies bounded Fisher information. -/
theorem apriori {C : Torus 1 → ℝ} (hC : GoodKernel C) (hCpos : ∀ n : ℤ, n ≠ 0 → 0 ≤ chat C n)
    {L : ℝ} (hL : 0 ≤ L) :
    ∃ B : ℝ, ∀ ρ : Torus 1 → ℝ, (∀ x, 0 ≤ ρ x) → ∫ x, ρ x ∂haar 1 = 1 →
      MemH1 (haar 1) (fun x => Real.sqrt (ρ x)) → DR C ρ ≤ 2 * L * GR C ρ → IR ρ ≤ B := by
  have hc1 := continuous_of_smooth (isSmoothT_dT hC.smooth)
  obtain ⟨M0, hM0⟩ := (isCompact_univ (X := Torus 1)).exists_bound_of_continuousOn hc1.continuousOn
  have hM : ∀ z, |dT C z| ≤ M0 := fun z => by simpa using hM0 z (Set.mem_univ _)
  have ha : 0 < aCos := by unfold aCos; positivity
  set K : ℝ := 48 * L / Real.sqrt (12 * aCos) with hK
  refine ⟨K ^ 2 + 2 * (2 * M0 ^ 2), fun ρ h0 h1 hH hq => ?_⟩
  have e1 := IR_le_two_DR hC h0 h1 hH hM
  have e2 := GR_le_entR hC hCpos h0 h1
  have e3 := entR_le_log h0 h1 hH
  have hy : 0 ≤ IR ρ / (12 * aCos) := div_nonneg (IR_nonneg ρ) (by positivity)
  have e4 := log_one_add_le _ hy
  have hsq : Real.sqrt (IR ρ / (12 * aCos)) = Real.sqrt (IR ρ) / Real.sqrt (12 * aCos) := by
    rw [Real.sqrt_div (IR_nonneg ρ)]
  set s := Real.sqrt (IR ρ) with hs
  have hss : s ^ 2 = IR ρ := Real.sq_sqrt (IR_nonneg ρ)
  have e5 : IR ρ ≤ K * s + 2 * M0 ^ 2 := by
    have : IR ρ ≤ 4 * L * entR ρ + 2 * M0 ^ 2 := by nlinarith [mul_le_mul_of_nonneg_left e2 hL]
    have h6 : 4 * L * entR ρ ≤ 4 * L * (6 * (2 * (s / Real.sqrt (12 * aCos)))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc entR ρ ≤ 6 * Real.log (1 + IR ρ / (12 * aCos)) := e3
        _ ≤ 6 * (2 * Real.sqrt (IR ρ / (12 * aCos))) := by linarith
        _ = _ := by rw [hsq]
    have : 4 * L * (6 * (2 * (s / Real.sqrt (12 * aCos)))) = K * s := by rw [hK]; ring
    nlinarith
  have hKs : K * s ≤ (s ^ 2 + K ^ 2) / 2 := by nlinarith [sq_nonneg (s - K)]
  linarith [hss, e5, hKs]

end SharpLSI.FL.Ex.LaneD
