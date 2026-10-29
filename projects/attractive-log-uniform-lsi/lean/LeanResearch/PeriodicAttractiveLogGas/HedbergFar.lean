import LeanResearch.PeriodicAttractiveLogGas.HedbergNear
import LeanResearch.PeriodicAttractiveLogGas.RadialTail

/-! The far part of the Appendix A potential estimate. Cauchy--Schwarz,
the actual radial tail integral, and the proved lower bound on the weight
retain the weighted L2 norm, with the exact Euclidean coefficient. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology
namespace PeriodicAttractiveLogGas.HedbergFar
open WeightedCubeBounds CubeMaximal
variable {ι : Type*} [Fintype ι]

/-- The square root of the exact radial tail coefficient. -/
def coefficient (ι : Type*) [Fintype ι] : ℝ :=
  Real.sqrt ((Fintype.card ι : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ ι) 1) /
    ((Fintype.card ι : ℝ) - 2))

theorem coefficient_nonneg : 0 ≤ coefficient ι := Real.sqrt_nonneg _

lemma kernel_square_root_tail (hd : 2 < Fintype.card ι) (x : EuclideanSpace ℝ ι)
    {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in (ball x r)ᶜ, (‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ))) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal (coefficient ι * r ^ (1 - (Fintype.card ι : ℝ) / 2)) := by
  have hdr : (2 : ℝ) < Fintype.card ι := by exact_mod_cast hd
  have hC : 0 ≤ (Fintype.card ι : ℝ) * volume.real (ball (0 : EuclideanSpace ℝ ι) 1) /
      ((Fintype.card ι : ℝ) - 2) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg) (by linarith)
  simp_rw [← ENNReal.rpow_mul, show (1 - (Fintype.card ι : ℝ)) * 2 =
    2 - 2 * (Fintype.card ι : ℝ) by ring]
  rw [RadialTail.kernel_square_tail hd x hr,
    ENNReal.ofReal_rpow_of_nonneg (mul_nonneg hC (Real.rpow_nonneg hr.le _)) (by norm_num)]
  congr 1
  rw [Real.mul_rpow hC (Real.rpow_nonneg hr.le _), ← Real.rpow_mul hr.le,
    show (2 - (Fintype.card ι : ℝ)) * (1 / 2) = 1 - (Fintype.card ι : ℝ) / 2 by ring,
    ← Real.sqrt_eq_rpow]
  rfl

/-- The weight is discarded only in the upper bound for its reciprocal,
not in the norm on the right of the potential estimate. -/
theorem far_bound (hd : 2 < Fintype.card ι) {w : EuclideanSpace ℝ ι → ℝ}
    {A : ℝ} {Z : Set (EuclideanSpace ℝ ι)} (h : Bounds w A Z)
    {f : EuclideanSpace ℝ ι → ℝ≥0∞} (hf : Measurable f)
    (x : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in (ball x r)ᶜ, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) * f y) ≤
      ENNReal.ofReal (coefficient ι * r ^ (1 - (Fintype.card ι : ℝ) / 2)) *
        (∫⁻ y, f y ^ 2 ∂weightedMeasure w) ^ (1 / 2 : ℝ) := by
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hk : Measurable (fun y : EuclideanSpace ℝ ι => ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ))) := by fun_prop
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (ball x r)ᶜ)
    hpq hk.aemeasurable hf.aemeasurable
  rw [kernel_square_root_tail hd x hr] at hh
  simp only [Pi.mul_apply, ENNReal.rpow_two] at hh
  have he : (∫⁻ y in (ball x r)ᶜ, f y ^ 2) ≤ ∫⁻ y, f y ^ 2 ∂weightedMeasure w :=
    le_trans (by gcongr; exact Measure.restrict_le_self)
      (h.reference_lintegral_le (fun y => f y ^ 2) (hf.pow_const 2))
  exact hh.trans (mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow he (by norm_num)) zero_le)

def potential (f : EuclideanSpace ℝ ι → ℝ≥0∞) (x : EuclideanSpace ℝ ι) : ℝ≥0∞ :=
  ∫⁻ y, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) * f y

theorem measurable_potential {f : EuclideanSpace ℝ ι → ℝ≥0∞} (hf : Measurable f) :
    Measurable (potential f) := by
  apply Measurable.lintegral_prod_right
  fun_prop

/-- Source near/far splitting, valid even for infinite potential or maximal
function. Neither side's finiteness is used to split the nonnegative integral. -/
theorem near_far_bound (hd : 2 < Fintype.card ι) {w : EuclideanSpace ℝ ι → ℝ}
    {A : ℝ} {Z : Set (EuclideanSpace ℝ ι)} (h : Bounds w A Z)
    {f : EuclideanSpace ℝ ι → ℝ≥0∞} (hf : Measurable f)
    (x : EuclideanSpace ℝ ι) {r : ℝ} (hr : 0 < r) :
    potential f x ≤ ENNReal.ofReal ((4 : ℝ) ^ Fintype.card ι * r) * maximal f x +
      ENNReal.ofReal (coefficient ι * r ^ (1 - (Fintype.card ι : ℝ) / 2)) *
        (∫⁻ y, f y ^ 2 ∂weightedMeasure w) ^ (1 / 2 : ℝ) := by
  let : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  rw [potential, ← lintegral_add_compl _ measurableSet_ball]
  exact add_le_add (HedbergNear.near_bound hf x hr) (far_bound hd h hf x hr)

end PeriodicAttractiveLogGas.HedbergFar
