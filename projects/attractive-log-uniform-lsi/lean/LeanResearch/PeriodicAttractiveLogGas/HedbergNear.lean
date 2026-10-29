import LeanResearch.PeriodicAttractiveLogGas.CubeMaximalWeighted
import LeanResearch.PeriodicAttractiveLogGas.DyadicKernelBounds

/-! The near part of the source Hedberg estimate. Dyadic annuli and
actual cube averages supply exactly 2^(2d) times radius times maximal
function. Infinite and zero maximal values are not excluded. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.HedbergNear
open PhysicalCubes WeightedCubeBounds DyadicKernelBounds CubeMaximal
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma closedBall_lintegral_le_maximal (f : EuclideanSpace ℝ ι → ℝ≥0∞)
    (x : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in closedBall x r, f y) ≤
      ENNReal.ofReal ((2 * r) ^ Fintype.card ι) * maximal f x := by
  have hc := average_le_maximal f x (by positivity : 0 < 2 * r)
    (mem_openCube_self x (by positivity : 0 < 2 * r))
  rw [setLAverage_eq] at hc
  have hm := mul_le_mul_of_nonneg_left hc (zero_le : 0 ≤ volume (openCube x (2 * r)))
  rw [ENNReal.mul_div_cancel (openCube_volume_pos x (by positivity)).ne'
    (openCube_volume_ne_top x (by positivity)), openCube_volume x (by positivity)] at hm
  calc
    _ ≤ ∫⁻ y in cube x (2 * r), f y := lintegral_mono_set (closedBall_subset_cube x r)
    _ = ∫⁻ y in openCube x (2 * r), f y :=
      setLIntegral_congr (openCube_ae_eq_cube x (2 * r)).symm
    _ ≤ _ := hm

/-- Exact near-potential estimate in nonnegative extended integrals. -/
theorem near_bound {f : EuclideanSpace ℝ ι → ℝ≥0∞} (hf : Measurable f)
    (x : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in ball x r, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) * f y) ≤
      ENNReal.ofReal ((4 : ℝ) ^ Fintype.card ι * r) * maximal f x := by
  by_cases htop : maximal f x = ∞
  · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne']
    exact le_top
  let μ := volume.withDensity f
  have hb (R : ℝ) (hR : 0 < R) : μ (closedBall x R) ≤
      ENNReal.ofReal (((2 : ℝ) ^ Fintype.card ι * (maximal f x).toReal) * R ^ Fintype.card ι) := by
    rw [show μ (closedBall x R) = ∫⁻ y in closedBall x R, f y from withDensity_apply _ measurableSet_closedBall]
    apply (closedBall_lintegral_le_maximal f x hR).trans_eq
    rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul (by positivity)]
    simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
    congr 1
    rw [mul_pow]
    ring
  have hx0 : μ {x} = 0 := withDensity_absolutelyContinuous volume f (measure_singleton x)
  have hh := kernel_integral_le_of_ball_growth Fintype.card_pos x
    (by positivity : 0 ≤ (2 : ℝ) ^ Fintype.card ι * (maximal f x).toReal) hr hx0 hb
  calc
    _ = ∫⁻ y in ball x r, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) ∂μ := by
      rw [setLIntegral_withDensity_eq_setLIntegral_mul volume hf (by fun_prop) measurableSet_ball]
      apply lintegral_congr
      intro y
      exact mul_comm _ _
    _ ≤ ∫⁻ y in closedBall x r, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) ∂μ := lintegral_mono_set ball_subset_closedBall
    _ ≤ _ := hh
    _ = _ := by
      rw [← ENNReal.ofReal_toReal htop, ← ENNReal.ofReal_mul (by positivity)]
      simp only [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
      congr 1
      have he : (2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι = 4 ^ Fintype.card ι := by
        rw [← mul_pow]
        norm_num
      calc
        _ = ((2 : ℝ) ^ Fintype.card ι * 2 ^ Fintype.card ι) * r * (maximal f x).toReal := by ring
        _ = _ := by rw [he]

/-- Zero maximal value forces the entire potential to vanish, not merely
its restriction to one ball. The proof uses an actual countable exhaustion. -/
theorem potential_zero_of_maximal_zero {f : EuclideanSpace ℝ ι → ℝ≥0∞} (hf : Measurable f)
    (x : EuclideanSpace ℝ ι) (hx : maximal f x = 0) :
    (∫⁻ y, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) * f y) = 0 := by
  have hcover : (⋃ n : ℕ, ball x ((n : ℝ) + 1)) = univ := by
    apply eq_univ_iff_forall.mpr
    intro y
    obtain ⟨n, hn⟩ := exists_nat_gt (dist y x)
    exact mem_iUnion.mpr ⟨n, mem_ball.mpr (by linarith only [hn])⟩
  have hzero (n : ℕ) :
      (∫⁻ y in ball x ((n : ℝ) + 1), ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) * f y) = 0 := by
    have hh := near_bound hf x (by positivity : 0 < (n : ℝ) + 1)
    rw [hx, mul_zero] at hh
    exact le_antisymm hh zero_le
  apply le_antisymm _ zero_le
  calc
    _ = ∫⁻ y in ⋃ n : ℕ, ball x ((n : ℝ) + 1), ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) * f y := by
      rw [hcover, Measure.restrict_univ]
    _ ≤ ∑' n : ℕ, ∫⁻ y in ball x ((n : ℝ) + 1), ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) * f y := lintegral_iUnion_le _ _
    _ = 0 := by simp only [hzero, tsum_zero]

end PeriodicAttractiveLogGas.HedbergNear
