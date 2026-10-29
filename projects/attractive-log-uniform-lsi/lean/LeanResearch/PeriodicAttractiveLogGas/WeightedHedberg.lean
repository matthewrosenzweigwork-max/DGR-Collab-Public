import LeanResearch.PeriodicAttractiveLogGas.HedbergFar
import LeanResearch.PeriodicAttractiveLogGas.HedbergExponents

/-! The pointwise weighted Hedberg estimate of Appendix A. The radius is
chosen from the actual weighted square integral and the literal cube maximal
function. Zero norm, zero maximal value and infinite maximal value are included. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology
namespace PeriodicAttractiveLogGas.WeightedHedberg
open WeightedCubeBounds CubeMaximal HedbergFar
variable {ι : Type*} [Fintype ι]

def coefficient (ι : Type*) [Fintype ι] : ℝ :=
  (4 : ℝ) ^ Fintype.card ι + HedbergFar.coefficient ι

theorem coefficient_pos : 0 < coefficient ι :=
  add_pos_of_pos_of_nonneg (pow_pos (by norm_num) _) HedbergFar.coefficient_nonneg

lemma potential_zero_of_square_integral_zero {w : EuclideanSpace ℝ ι → ℝ}
    {A : ℝ} {Z : Set (EuclideanSpace ℝ ι)} (h : Bounds w A Z)
    {f : EuclideanSpace ℝ ι → ℝ≥0∞} (hf : Measurable f)
    (hzero : (∫⁻ y, f y ^ 2 ∂weightedMeasure w) = 0) (x : EuclideanSpace ℝ ι) :
    potential f x = 0 := by
  have hsq := (lintegral_eq_zero_iff (hf.pow_const 2)).mp hzero
  have hfzero : f =ᵐ[volume] 0 := by
    filter_upwards [h.volume_absolutelyContinuous.ae_le hsq] with y hy
    change f y ^ 2 = 0 at hy
    exact (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hy
  rw [potential]
  calc
    _ = ∫⁻ y, (0 : ℝ≥0∞) := by
      apply lintegral_congr_ae
      filter_upwards [hfzero] with y hy
      simp only [hy, Pi.zero_apply, mul_zero]
    _ = 0 := lintegral_zero

/-- Source pointwise estimate, with no positivity or finiteness assumption
on the maximal value. The square integral is the weighted one throughout. -/
theorem pointwise (hd : 2 < Fintype.card ι) {w : EuclideanSpace ℝ ι → ℝ}
    {A : ℝ} {Z : Set (EuclideanSpace ℝ ι)} (h : Bounds w A Z)
    {f : EuclideanSpace ℝ ι → ℝ≥0∞} (hf : Measurable f)
    (hfinite : (∫⁻ y, f y ^ 2 ∂weightedMeasure w) ≠ ∞) (x : EuclideanSpace ℝ ι) :
    potential f x ≤ ENNReal.ofReal (coefficient ι) *
      maximal f x ^ (1 - 2 / (Fintype.card ι : ℝ)) *
        (∫⁻ y, f y ^ 2 ∂weightedMeasure w) ^ (1 / (Fintype.card ι : ℝ)) := by
  let : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let I := ∫⁻ y, f y ^ 2 ∂weightedMeasure w
  have hd2 : (2 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < Fintype.card ι := by linarith
  have hpower : 0 < 1 - 2 / (Fintype.card ι : ℝ) := by
    apply sub_pos.mpr
    exact (div_lt_one hd0).mpr hd2
  by_cases hIzero : I = 0
  · rw [potential_zero_of_square_integral_zero h hf hIzero x]
    exact zero_le
  by_cases hMzero : maximal f x = 0
  · rw [potential, HedbergNear.potential_zero_of_maximal_zero hf x hMzero]
    exact zero_le
  by_cases hMtop : maximal f x = ∞
  · rw [hMtop, ENNReal.top_rpow_of_pos hpower,
      ENNReal.mul_top (ENNReal.ofReal_pos.mpr coefficient_pos).ne',
      ENNReal.top_mul (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hIzero) hfinite).ne']
    exact le_top
  let M := (maximal f x).toReal
  let E := I.toReal ^ (1 / 2 : ℝ)
  have hM : 0 < M := ENNReal.toReal_pos hMzero hMtop
  have hE : 0 < E := Real.rpow_pos_of_pos (ENNReal.toReal_pos hIzero hfinite) _
  have hMrepr : ENNReal.ofReal M = maximal f x := ENNReal.ofReal_toReal hMtop
  have hErepr : ENNReal.ofReal E = I ^ (1 / 2 : ℝ) := by
    rw [show E = I.toReal ^ (1 / 2 : ℝ) from rfl,
      ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hfinite]
  let r := (E / M) ^ (2 / (Fintype.card ι : ℝ))
  have hr : 0 < r := Real.rpow_pos_of_pos (div_pos hE hM) _
  have hb := HedbergExponents.radius_balance hd0 hE hM
  have hnear : (4 : ℝ) ^ Fintype.card ι * r * M =
      (4 : ℝ) ^ Fintype.card ι * (E ^ (2 / (Fintype.card ι : ℝ)) * M ^ (1 - 2 / (Fintype.card ι : ℝ))) := by
    rw [mul_assoc, hb.1]
  have hfar : HedbergFar.coefficient ι * r ^ (1 - (Fintype.card ι : ℝ) / 2) * E =
      HedbergFar.coefficient ι * (E ^ (2 / (Fintype.card ι : ℝ)) * M ^ (1 - 2 / (Fintype.card ι : ℝ))) := by
    rw [mul_assoc, hb.2]
  have hEpower : ENNReal.ofReal (E ^ (2 / (Fintype.card ι : ℝ))) =
      I ^ (1 / (Fintype.card ι : ℝ)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hE.le (by positivity), hErepr, ← ENNReal.rpow_mul]
    congr 1
    ring
  have hMpower : ENNReal.ofReal (M ^ (1 - 2 / (Fintype.card ι : ℝ))) =
      maximal f x ^ (1 - 2 / (Fintype.card ι : ℝ)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hM.le hpower.le, hMrepr]
  have hh := near_far_bound hd h hf x hr
  rw [← hMrepr, ← hErepr] at hh
  have hc0 := (coefficient_pos (ι := ι)).le
  have hcf0 := HedbergFar.coefficient_nonneg (ι := ι)
  calc
    potential f x ≤ ENNReal.ofReal ((4 : ℝ) ^ Fintype.card ι * r) * ENNReal.ofReal M +
      ENNReal.ofReal (HedbergFar.coefficient ι * r ^ (1 - (Fintype.card ι : ℝ) / 2)) * ENNReal.ofReal E := hh
    _ = ENNReal.ofReal ((4 : ℝ) ^ Fintype.card ι * r * M +
      HedbergFar.coefficient ι * r ^ (1 - (Fintype.card ι : ℝ) / 2) * E) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity : 0 ≤ (4 : ℝ) ^ Fintype.card ι * r),
        ENNReal.ofReal_mul (mul_nonneg hcf0 (Real.rpow_nonneg hr.le _))]
    _ = ENNReal.ofReal (coefficient ι * E ^ (2 / (Fintype.card ι : ℝ)) * M ^ (1 - 2 / (Fintype.card ι : ℝ))) := by
      rw [hnear, hfar]
      congr 1
      unfold coefficient
      ring
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hc0 (Real.rpow_nonneg hE.le _)),
        ENNReal.ofReal_mul hc0, hEpower, hMpower]
      ac_rfl

end PeriodicAttractiveLogGas.WeightedHedberg
