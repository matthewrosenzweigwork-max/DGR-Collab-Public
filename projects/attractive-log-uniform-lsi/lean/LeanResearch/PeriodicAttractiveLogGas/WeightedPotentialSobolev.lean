import LeanResearch.PeriodicAttractiveLogGas.WeightedHedberg

/-! Integrating the source Hedberg estimate against the original weight.
The maximal-function estimate has already been proved for that measure.
The exponent identities recover precisely the Sobolev exponent 2d/(d-2). -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology
namespace PeriodicAttractiveLogGas.WeightedPotentialSobolev
open WeightedCubeBounds CubeMaximal HedbergFar WeightedHedberg
variable {ι : Type*} [Fintype ι]

def exponent (ι : Type*) [Fintype ι] : ℝ :=
  2 * (Fintype.card ι : ℝ) / ((Fintype.card ι : ℝ) - 2)

theorem exponent_gt_two (hd : 2 < Fintype.card ι) : 2 < exponent ι :=
  (HedbergExponents.sobolev_exponent (by exact_mod_cast hd)).1

/-- The full weighted integral estimate. Its constant and exponents are
not hypotheses; they follow from the pointwise estimate and strong L2 bound. -/
theorem integral_bound (hd : 2 < Fintype.card ι) {w : EuclideanSpace ℝ ι → ℝ}
    {A : ℝ} {Z : Set (EuclideanSpace ℝ ι)} (h : Bounds w A Z)
    {f : EuclideanSpace ℝ ι → ℝ≥0∞} (hf : Measurable f)
    (hfinite : (∫⁻ y, f y ^ 2 ∂weightedMeasure w) ≠ ∞) :
    (∫⁻ x, potential f x ^ exponent ι ∂weightedMeasure w) ≤
      ENNReal.ofReal ((WeightedHedberg.coefficient ι) ^ exponent ι * (8 * 3 ^ Fintype.card ι * A)) *
        (∫⁻ y, f y ^ 2 ∂weightedMeasure w) ^ (exponent ι / 2) := by
  let I := ∫⁻ y, f y ^ 2 ∂weightedMeasure w
  let p := exponent ι
  have hp0 : 0 < p := (by norm_num : (0 : ℝ) < 2).trans (exponent_gt_two hd)
  have hexp := HedbergExponents.sobolev_exponent (show (2 : ℝ) < Fintype.card ι by exact_mod_cast hd)
  have hα : (1 - 2 / (Fintype.card ι : ℝ)) * p = 2 := hexp.2.1
  have hγ : p / (Fintype.card ι : ℝ) + 1 = p / 2 := hexp.2.2
  by_cases hIzero : I = 0
  · have hPzero := potential_zero_of_square_integral_zero h hf hIzero
    calc
      _ = ∫⁻ x, (0 : ℝ≥0∞) ∂weightedMeasure w := by
        apply lintegral_congr
        intro x
        rw [hPzero x, ENNReal.zero_rpow_of_pos hp0]
      _ = 0 := lintegral_zero
      _ ≤ _ := zero_le
  have hpoint (x : EuclideanSpace ℝ ι) : potential f x ^ p ≤
      ENNReal.ofReal (WeightedHedberg.coefficient ι) ^ p * I ^ (p / (Fintype.card ι : ℝ)) * maximal f x ^ 2 := by
    calc
      _ ≤ (ENNReal.ofReal (WeightedHedberg.coefficient ι) *
        maximal f x ^ (1 - 2 / (Fintype.card ι : ℝ)) * I ^ (1 / (Fintype.card ι : ℝ))) ^ p :=
          ENNReal.rpow_le_rpow (pointwise hd h hf hfinite x) hp0.le
      _ = _ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le, ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
          ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, hα, ENNReal.rpow_two,
          show (1 / (Fintype.card ι : ℝ)) * p = p / (Fintype.card ι : ℝ) by ring]
        ac_rfl
  have hM := strong_two h hf.aemeasurable
  have hIprod : I ^ (p / (Fintype.card ι : ℝ)) * I = I ^ (p / 2) := by
    calc
      _ = I ^ (p / (Fintype.card ι : ℝ)) * I ^ (1 : ℝ) := by rw [ENNReal.rpow_one]
      _ = I ^ (p / (Fintype.card ι : ℝ) + 1) := (ENNReal.rpow_add _ _ hIzero hfinite).symm
      _ = _ := by rw [hγ]
  have hH := (WeightedHedberg.coefficient_pos (ι := ι)).le
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (WeightedHedberg.coefficient ι) ^ p *
        I ^ (p / (Fintype.card ι : ℝ)) * maximal f x ^ 2 ∂weightedMeasure w :=
      lintegral_mono hpoint
    _ = (ENNReal.ofReal (WeightedHedberg.coefficient ι) ^ p * I ^ (p / (Fintype.card ι : ℝ))) *
        ∫⁻ x, maximal f x ^ 2 ∂weightedMeasure w :=
      lintegral_const_mul _ ((measurable_maximal f).pow_const 2)
    _ ≤ (ENNReal.ofReal (WeightedHedberg.coefficient ι) ^ p * I ^ (p / (Fintype.card ι : ℝ))) *
        (ENNReal.ofReal (8 * 3 ^ Fintype.card ι * A) * I) := by gcongr
    _ = _ := by
      rw [ENNReal.ofReal_mul (Real.rpow_nonneg hH _),
        ← ENNReal.ofReal_rpow_of_nonneg hH hp0.le]
      calc
        _ = ENNReal.ofReal (WeightedHedberg.coefficient ι) ^ p * ENNReal.ofReal (8 * 3 ^ Fintype.card ι * A) *
            (I ^ (p / (Fintype.card ι : ℝ)) * I) := by ac_rfl
        _ = _ := by rw [hIprod]

end PeriodicAttractiveLogGas.WeightedPotentialSobolev
