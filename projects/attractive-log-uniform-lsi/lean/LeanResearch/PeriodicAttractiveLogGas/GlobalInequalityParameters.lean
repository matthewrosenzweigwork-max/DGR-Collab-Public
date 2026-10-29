import LeanResearch.PeriodicAttractiveLogGas.GlobalDefectiveEntropy

/-! Simultaneous fixed parameter choices for the source's final assembly.
Every field below is an elementary kernel or scalar admissibility condition;
no functional inequality, far imbalance or asymptotic conclusion is a field. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace PeriodicAttractiveLogGas.GlobalInequalityParameters
open ConditionalLawEstimates GreenGradientOscillation ResidualFarExponential
  ResidualNearExponential ReferenceResidual

structure Parameters (β₀ : ℝ) where
  C₂ : ℝ
  kernel_nonneg : 0 ≤ C₂
  kernel_bound : KernelHessianBound C₂
  t : ℝ
  t_pos : 0 < t
  t_lt : t < occupationBound β₀
  J : ℕ
  mesh : 8 * (radius β₀ + 4) ≤ J
  residual_mesh : 8 * (chosenRadius β₀ C₂ + 1) ≤ J
  residual_small : 24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant *
    nearScale (chosenRadius β₀ C₂) * t ≤ 1
  reference_scale : 2 ≤ (J : ℝ) * Real.sqrt (2 * Real.pi * Real.exp 1 * t)
  reference_small : 4 * β₀ * kernelConstant * Real.sqrt (Real.pi * Real.exp 1 * t) ≤ 1
  near_mesh : OccupationNearContraction.nearMeshThreshold β₀ ≤ J
  heavy_mesh : HeavyScales.sourceResolution β₀ (t / 4) ≤ J
  inverse_mesh : 1 / (J ^ 2 : ℕ) < t / 8

private theorem exists_small_parameter (A C D : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ t : ℝ, 0 < t ∧ t < δ ∧ A * t ≤ 1 ∧ C * Real.sqrt (D * t) ≤ 1 := by
  have hlin : IsOpen {t : ℝ | A * t < 1} :=
    isOpen_lt (continuous_const.mul continuous_id) continuous_const
  have hsqrt : IsOpen {t : ℝ | C * Real.sqrt (D * t) < 1} :=
    isOpen_lt (continuous_const.mul (Real.continuous_sqrt.comp (continuous_const.mul continuous_id))) continuous_const
  have hn : {t : ℝ | A * t < 1} ∩ {t : ℝ | C * Real.sqrt (D * t) < 1} ∈ 𝓝 0 :=
    inter_mem (hlin.mem_nhds (by simp)) (hsqrt.mem_nhds (by simp))
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp hn
  let t : ℝ := min (r / 2) (δ / 2)
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htr : t < r := (min_le_left _ _).trans_lt (by linarith only [hr])
  have htδ : t < δ := (min_le_right _ _).trans_lt (by linarith only [hδ])
  have hmem : t ∈ Metric.ball 0 r := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos ht] using htr
  exact ⟨t, ht, htδ, (hb hmem).1.le, (hb hmem).2.le⟩

/-- Kernel, occupation scale, and spatial resolution are all chosen before
any particle threshold. The construction also covers beta_0 = 0. -/
theorem exists_parameters {β₀ : ℝ} (hβ₀ : 0 ≤ β₀) : Nonempty (Parameters β₀) := by
  obtain ⟨C₂, hC, hk⟩ := exists_kernelHessianBound
  have hδ := (chosen_parameters β₀ hβ₀).1
  obtain ⟨t, ht, htδ, hcap, hsmall⟩ := exists_small_parameter
    (24 * β₀ * (colorCount (chosenRadius β₀ C₂) : ℝ) * universalConstant * nearScale (chosenRadius β₀ C₂))
    (4 * β₀ * kernelConstant) (Real.pi * Real.exp 1) hδ
  have hs : 0 < Real.sqrt (2 * Real.pi * Real.exp 1 * t) := Real.sqrt_pos.mpr (by positivity)
  obtain ⟨J, hJ⟩ := exists_nat_gt
    (max (3 : ℝ) (max ((8 * (radius β₀ + 4) : ℕ) : ℝ)
      (max ((8 * (chosenRadius β₀ C₂ + 1) : ℕ) : ℝ)
        (max (OccupationNearContraction.nearMeshThreshold β₀ : ℝ)
          (max (HeavyScales.sourceResolution β₀ (t / 4))
            (max (2 / Real.sqrt (2 * Real.pi * Real.exp 1 * t)) (Real.sqrt (8 / t))))))))
  simp only [max_lt_iff] at hJ
  obtain ⟨hJ3, hmesh, hmeshY, hnear, hheavy, hscale, hinv⟩ := hJ
  have hJpos : (0 : ℝ) < J := lt_trans (by norm_num) hJ3
  have hinv' : 8 / t < (J : ℝ) ^ 2 := by
    have hh := Real.sq_sqrt (div_nonneg (by norm_num : (0 : ℝ) ≤ 8) ht.le)
    have hn := Real.sqrt_nonneg (8 / t)
    nlinarith only [hh, hn, hinv]
  have hsmallJ : 1 / (J : ℝ) ^ 2 < t / 8 := by
    have hh := (div_lt_iff₀ ht).mp hinv'
    apply (div_lt_iff₀ (sq_pos_of_pos hJpos)).mpr
    nlinarith only [hh]
  refine ⟨⟨C₂, hC.le, hk, t, ht, htδ, J, ?_, ?_, ?_, ?_, ?_, ?_, hheavy.le, ?_⟩⟩
  · exact_mod_cast hmesh.le
  · exact_mod_cast hmeshY.le
  · exact hcap
  · exact (div_le_iff₀ hs).mp hscale.le
  · simpa only [mul_assoc] using hsmall
  · exact_mod_cast hnear.le
  · simpa only [Nat.cast_pow] using hsmallJ

end PeriodicAttractiveLogGas.GlobalInequalityParameters
