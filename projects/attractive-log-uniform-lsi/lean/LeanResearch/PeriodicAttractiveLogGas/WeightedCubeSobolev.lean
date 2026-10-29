import LeanResearch.PeriodicAttractiveLogGas.WeightedPotentialSobolev
import LeanResearch.PeriodicAttractiveLogGas.WeightedCubePoincareNeighborhood

/-! Appendix A weighted Sobolev gain. The cube centre is its unweighted
mean and the test is C1 on a neighborhood of the closed cube. The potential,
maximal-function estimate and weighted integral are the actual constructed ones. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.WeightedCubeSobolev
open PhysicalCubes WeightedCubeBounds WeightedPotentialSobolev HedbergFar
variable {ι : Type*} [Fintype ι]

def coefficient (ι : Type*) [Fintype ι] (A : ℝ) : ℝ :=
  ((Real.sqrt (Fintype.card ι)) ^ Fintype.card ι / Fintype.card ι) *
    WeightedHedberg.coefficient ι * (8 * 3 ^ Fintype.card ι * A) ^ (1 / exponent ι)

lemma coefficient_nonneg {A : ℝ} (hA : 0 ≤ A) : 0 ≤ coefficient ι A := by
  unfold coefficient
  have hH := (WeightedHedberg.coefficient_pos (ι := ι)).le
  positivity

lemma derivative_square_integral_ne_top {w : EuclideanSpace ℝ ι → ℝ} {A : ℝ}
    {Z : Set (EuclideanSpace ℝ ι)} (h : Bounds w A Z)
    (c : EuclideanSpace ℝ ι) (ℓ : ℝ)
    {Ω : Set (EuclideanSpace ℝ ι)} (hΩ : IsOpen Ω) (hSΩ : cube c ℓ ⊆ Ω)
    {u : EuclideanSpace ℝ ι → ℝ} (hu : ContDiffOn ℝ 1 u Ω) :
    (∫⁻ x in cube c ℓ, ‖fderiv ℝ u x‖ₑ ^ 2 ∂weightedMeasure w) ≠ ∞ := by
  let : IsLocallyFiniteMeasure (weightedMeasure w) := h.locallyFinite
  have hgc : ContinuousOn (fderiv ℝ u) (cube c ℓ) :=
    (hu.continuousOn_fderiv_of_isOpen hΩ (by norm_num)).mono hSΩ
  have hi : IntegrableOn (fun x => ‖fderiv ℝ u x‖ ^ 2) (cube c ℓ) (weightedMeasure w) :=
    (hgc.norm.pow 2).integrableOn_compact (isCompact_cube c ℓ)
  have he := ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun x => sq_nonneg ‖fderiv ℝ u x‖)
  have hpoint (x : EuclideanSpace ℝ ι) :
      ‖fderiv ℝ u x‖ₑ ^ 2 = ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  simp_rw [hpoint]
  rw [← he]
  exact ENNReal.ofReal_ne_top

/-- The full weighted Sobolev estimate on a physical cube. Neither a
Sobolev nor a weighted gradient bound is an input. -/
theorem eLpNorm_bound (hd : 2 < Fintype.card ι) {w : EuclideanSpace ℝ ι → ℝ} {A : ℝ}
    {Z : Set (EuclideanSpace ℝ ι)} (h : Bounds w A Z)
    (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Ω : Set (EuclideanSpace ℝ ι)} (hΩ : IsOpen Ω) (hSΩ : cube c ℓ ⊆ Ω)
    {u : EuclideanSpace ℝ ι → ℝ} (hu : ContDiffOn ℝ 1 u Ω) :
    eLpNorm (fun x => u x - ⨍ y in cube c ℓ, u y) (ENNReal.ofReal (exponent ι))
      ((weightedMeasure w).restrict (cube c ℓ)) ≤
        ENNReal.ofReal (coefficient ι A) *
          eLpNorm (fderiv ℝ u) 2 ((weightedMeasure w).restrict (cube c ℓ)) := by
  let : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let S := cube c ℓ
  let p := exponent ι
  let a := ⨍ y in S, u y
  let K : ℝ := (Real.sqrt (Fintype.card ι)) ^ Fintype.card ι / Fintype.card ι
  let H := WeightedHedberg.coefficient ι
  let C : ℝ := 8 * 3 ^ Fintype.card ι * A
  let V : EuclideanSpace ℝ ι → ℝ≥0∞ := S.indicator (fun y => ‖fderiv ℝ u y‖ₑ)
  let I := ∫⁻ y in S, ‖fderiv ℝ u y‖ₑ ^ 2 ∂weightedMeasure w
  have hp0 : 0 < p := (by norm_num : (0 : ℝ) < 2).trans (exponent_gt_two hd)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hH : 0 ≤ H := (WeightedHedberg.coefficient_pos (ι := ι)).le
  have hA : 0 ≤ A := zero_le_one.trans h.constant_ge_one
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hS : MeasurableSet S := measurableSet_cube c ℓ
  have hV : Measurable V := (measurable_fderiv ℝ u).enorm.indicator hS
  have hI : I ≠ ∞ := derivative_square_integral_ne_top h c ℓ hΩ hSΩ hu
  have hVI : (∫⁻ y, V y ^ 2 ∂weightedMeasure w) = I := by
    dsimp only [I]
    rw [← lintegral_indicator hS]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ S <;> simp [V, hy]
  have hP (x : EuclideanSpace ℝ ι) : potential V x =
      ∫⁻ y in S, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) * ‖fderiv ℝ u y‖ₑ := by
    rw [potential, ← lintegral_indicator hS]
    apply lintegral_congr
    intro y
    by_cases hy : y ∈ S <;> simp [V, hy]
  have hpoint (x : EuclideanSpace ℝ ι) (hx : x ∈ S) :
      ‖u x - a‖ₑ ≤ ENNReal.ofReal K * potential V x := by
    rw [hP]
    exact WeightedCubePoincare.pointwise_potential_of_contDiffOn c hℓ hΩ hSΩ hu hx
  have hPot := integral_bound hd h hV (by rw [hVI]; exact hI)
  rw [hVI] at hPot
  have hbound : (∫⁻ x in S, ‖u x - a‖ₑ ^ p ∂weightedMeasure w) ≤
      ENNReal.ofReal ((K * H) ^ p * C) * I ^ (p / 2) := by
    calc
      _ ≤ ∫⁻ x in S, (ENNReal.ofReal K * potential V x) ^ p ∂weightedMeasure w := by
        apply setLIntegral_mono' hS
        intro x hx
        exact ENNReal.rpow_le_rpow (hpoint x hx) hp0.le
      _ = ENNReal.ofReal K ^ p * ∫⁻ x in S, potential V x ^ p ∂weightedMeasure w := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0.le]
        exact lintegral_const_mul _ ((measurable_potential hV).pow_const p)
      _ ≤ ENNReal.ofReal K ^ p * ∫⁻ x, potential V x ^ p ∂weightedMeasure w := by
        gcongr
        exact Measure.restrict_le_self
      _ ≤ ENNReal.ofReal K ^ p * (ENNReal.ofReal (H ^ p * C) * I ^ (p / 2)) := by gcongr
      _ = _ := by
        rw [← mul_assoc, ENNReal.ofReal_rpow_of_nonneg hK hp0.le,
          ← ENNReal.ofReal_mul (Real.rpow_nonneg hK _), Real.mul_rpow hK hH]
        congr 1
        congr 1
        ring
  have hum : AEStronglyMeasurable (fun x => u x - a) ((weightedMeasure w).restrict S) :=
    ((hu.continuousOn.mono hSΩ).sub continuousOn_const).aestronglyMeasurable hS
  have hdm : AEStronglyMeasurable (fderiv ℝ u) ((weightedMeasure w).restrict S) :=
    (measurable_fderiv ℝ u).aestronglyMeasurable
  have hroot : ((K * H) ^ p * C) ^ (1 / p) = K * H * C ^ (1 / p) := by
    rw [Real.mul_rpow (Real.rpow_nonneg (mul_nonneg hK hH) _) hC,
      ← Real.rpow_mul (mul_nonneg hK hH), mul_one_div_cancel hp0.ne', Real.rpow_one]
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hp0).ne'
      ENNReal.ofReal_ne_top hum, ENNReal.toReal_ofReal hp0.le,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hdm]
  norm_num only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  calc
    _ ≤ (ENNReal.ofReal ((K * H) ^ p * C) * I ^ (p / 2)) ^ (1 / p) :=
      ENNReal.rpow_le_rpow hbound (by positivity)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
        ENNReal.ofReal_rpow_of_nonneg (mul_nonneg (Real.rpow_nonneg (mul_nonneg hK hH) _) hC) (by positivity),
        hroot, ← ENNReal.rpow_mul,
        show p / 2 * (1 / p) = (1 / 2 : ℝ) by field_simp [hp0.ne']]
      rfl

end PeriodicAttractiveLogGas.WeightedCubeSobolev
