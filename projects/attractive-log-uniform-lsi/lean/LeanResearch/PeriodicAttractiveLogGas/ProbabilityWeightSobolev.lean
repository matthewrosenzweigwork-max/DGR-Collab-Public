import LeanResearch.PeriodicAttractiveLogGas.WeightedCubeSobolev
import LeanResearch.PeriodicAttractiveLogGas.DensityMoments

/-! Normalization of the source weighted Sobolev inequality. The reference
mean remains the unweighted one. The upper bound on the normalizer is used
only after the actual measures have been compared. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal
namespace PeriodicAttractiveLogGas.ProbabilityWeightSobolev
variable {α : Type*} [MeasurableSpace α] {μ ν W : Measure α}

lemma eLpNorm_two_scaling {E : Type*} [NormedAddCommGroup E]
    {Z : ℝ} (hZ : 0 ≤ Z) (hW : W = ENNReal.ofReal Z • ν) (G : α → E) :
    eLpNorm G 2 W = ENNReal.ofReal (Real.sqrt Z) * eLpNorm G 2 ν := by
  rw [hW, eLpNorm_smul_measure_of_ne_zero_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
  norm_num only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul]
  rw [ENNReal.ofReal_rpow_of_nonneg hZ (by norm_num), ← Real.sqrt_eq_rpow]

lemma eLpNorm_two_comparison {E : Type*} [NormedAddCommGroup E]
    {Z : ℝ} (hZ : 0 ≤ Z) (hμν : μ ≤ ENNReal.ofReal Z • ν) (G : α → E) :
    eLpNorm G 2 μ ≤ ENNReal.ofReal (Real.sqrt Z) * eLpNorm G 2 ν := by
  exact (eLpNorm_mono_measure G hμν).trans_eq (eLpNorm_two_scaling hZ rfl G)

/-- Probability-weight version of the source Sobolev gain. No mean with
respect to the weighted probability is substituted for the reference mean. -/
theorem normalized_bound [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {f : α → ℝ} {G : α → E}
    {Z Zw S p : ℝ} (hZ : 1 ≤ Z) (hZZ : Z ≤ Zw) (hS : 0 ≤ S) (hp : 2 < p)
    (hW : W = ENNReal.ofReal Z • ν) (hμW : μ ≤ W)
    (hSob : eLpNorm (fun x => f x - ∫ y, f y ∂μ) (ENNReal.ofReal p) W ≤
      ENNReal.ofReal S * eLpNorm G 2 W) :
    eLpNorm f (ENNReal.ofReal p) ν ≤
      ENNReal.ofReal (Real.sqrt Zw * S) * eLpNorm G 2 ν +
        ENNReal.ofReal Zw * eLpNorm f 2 ν := by
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hZw : 1 ≤ Zw := hZ.trans hZZ
  have hZw0 : 0 ≤ Zw := zero_le_one.trans hZw
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hνW : ν ≤ W := by
    rw [hW]
    calc
      ν = (1 : ℝ≥0∞) • ν := (one_smul _ _).symm
      _ ≤ ENNReal.ofReal Z • ν := by
        gcongr
        rw [← ENNReal.ofReal_one]
        exact ENNReal.ofReal_le_ofReal hZ
  have hsqrt : Real.sqrt Z ≤ Zw :=
    (Real.sqrt_le_sqrt hZZ).trans (by
      have hs := Real.sq_sqrt hZw0
      have hn := Real.sqrt_nonneg Zw
      nlinarith)
  have hmean : ‖∫ x, f x ∂μ‖ₑ ≤ ENNReal.ofReal Zw * eLpNorm f 2 ν := by
    calc
      _ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm f
      _ ≤ eLpNorm f 1 μ := lintegral_enorm_le_eLpNorm_one
      _ ≤ eLpNorm f 2 μ := eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
      _ ≤ ENNReal.ofReal (Real.sqrt Z) * eLpNorm f 2 ν :=
        eLpNorm_two_comparison hZ0 (by rw [← hW]; exact hμW) f
      _ ≤ _ := by gcongr
  have hc : eLpNorm (fun _ : α => ∫ x, f x ∂μ) (ENNReal.ofReal p) ν = ‖∫ x, f x ∂μ‖ₑ := by
    rw [eLpNorm_const _ (ENNReal.ofReal_pos.mpr hp0).ne' (NeZero.ne ν)]
    simp
  have hsum : f = (fun x => f x - ∫ y, f y ∂μ) + (fun _ => ∫ y, f y ∂μ) := by
    funext x
    simp
  calc
    eLpNorm f (ENNReal.ofReal p) ν ≤
        eLpNorm (fun x => f x - ∫ y, f y ∂μ) (ENNReal.ofReal p) ν + ‖∫ x, f x ∂μ‖ₑ := by
      conv_lhs => rw [hsum]
      exact (eLpNorm_add_le hp1).trans_eq (congrArg _ hc)
    _ ≤ eLpNorm (fun x => f x - ∫ y, f y ∂μ) (ENNReal.ofReal p) W +
        ENNReal.ofReal Zw * eLpNorm f 2 ν := add_le_add (eLpNorm_mono_measure _ hνW) hmean
    _ ≤ ENNReal.ofReal S * eLpNorm G 2 W + ENNReal.ofReal Zw * eLpNorm f 2 ν :=
      add_le_add hSob le_rfl
    _ ≤ ENNReal.ofReal (Real.sqrt Zw * S) * eLpNorm G 2 ν +
        ENNReal.ofReal Zw * eLpNorm f 2 ν := by
      rw [eLpNorm_two_scaling hZ0 hW, ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      have hh : ENNReal.ofReal (Real.sqrt Z) ≤ ENNReal.ofReal (Real.sqrt Zw) :=
        ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hZZ)
      calc
        _ ≤ ENNReal.ofReal S * (ENNReal.ofReal (Real.sqrt Zw) * eLpNorm G 2 ν) + _ := by gcongr
        _ = _ := by ac_rfl

/-- The same conclusion as a finite real norm inequality. Finiteness of
both norms on the right is explicit and supplies the needed conversion. -/
theorem normalized_lpNorm_bound [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {f : α → ℝ} {G : α → E}
    {Z Zw S p : ℝ} (hZ : 1 ≤ Z) (hZZ : Z ≤ Zw) (hS : 0 ≤ S) (hp : 2 < p)
    (hW : W = ENNReal.ofReal Z • ν) (hμW : μ ≤ W)
    (hf : MemLp f 2 ν) (hG : MemLp G 2 ν)
    (hSob : eLpNorm (fun x => f x - ∫ y, f y ∂μ) (ENNReal.ofReal p) W ≤
      ENNReal.ofReal S * eLpNorm G 2 W) :
    lpNorm f (ENNReal.ofReal p) ν ≤ Real.sqrt Zw * S * lpNorm G 2 ν + Zw * lpNorm f 2 ν := by
  have hh := normalized_bound hZ hZZ hS hp hW hμW hSob
  have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
    ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG.eLpNorm_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top⟩) hh
  rw [ENNReal.toReal_add
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG.eLpNorm_ne_top)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.eLpNorm_ne_top)] at hr
  simpa only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg Zw) hS),
    ENNReal.toReal_ofReal (zero_le_one.trans (hZ.trans hZZ)), toReal_eLpNorm] using hr

end PeriodicAttractiveLogGas.ProbabilityWeightSobolev
