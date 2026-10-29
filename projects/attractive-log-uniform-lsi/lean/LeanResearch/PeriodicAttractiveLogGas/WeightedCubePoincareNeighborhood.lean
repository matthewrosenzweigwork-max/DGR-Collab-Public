import LeanResearch.PeriodicAttractiveLogGas.WeightedCubePoincare
import LeanResearch.PeriodicAttractiveLogGas.WeightedCubeMeasure
import LeanResearch.PeriodicAttractiveLogGas.CubePotentialNeighborhood

/-! Appendix A weighted cube Poincare inequality for the full source test class.
The neighborhood regularity and ordinary weighted integrals are preserved. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.WeightedCubePoincare
open PhysicalCubes WeightedCubeBounds WeightedKernelBounds WeightedSchur
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma pointwise_potential_of_contDiffOn (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Ω : Set (EuclideanSpace ℝ ι)} (hΩ : IsOpen Ω) (hSΩ : cube c ℓ ⊆ Ω)
    {u : EuclideanSpace ℝ ι → ℝ} (hu : ContDiffOn ℝ 1 u Ω) {x : EuclideanSpace ℝ ι}
    (hx : x ∈ cube c ℓ) :
    ‖u x - ⨍ y in cube c ℓ, u y‖ₑ ≤
      ENNReal.ofReal ((Real.sqrt (Fintype.card ι)) ^ Fintype.card ι / Fintype.card ι) *
        ∫⁻ y in cube c ℓ, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) * ‖fderiv ℝ u y‖ₑ := by
  have hz : volume (cube c ℓ) ≠ 0 := by
    rw [cube_volume c hℓ.le]
    exact (ENNReal.ofReal_pos.mpr (pow_pos hℓ _)).ne'
  have hh := CubePotential.mean_oscillation_of_contDiffOn (μ := volume) (isCompact_cube c ℓ)
    (convex_cube c ℓ) hΩ hSΩ hu hx (cube_subset_ball_at_point c hℓ.le hx) hz
  simp only [finrank_euclideanSpace, potential_coefficient c hℓ] at hh
  simpa only [mul_comm (‖fderiv ℝ u _‖ₑ)] using hh

theorem poincare_lintegral_of_contDiffOn {w : EuclideanSpace ℝ ι → ℝ} {A : ℝ}
    {Z : Set (EuclideanSpace ℝ ι)} (h : Bounds w A Z)
    (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Ω : Set (EuclideanSpace ℝ ι)} (hΩ : IsOpen Ω) (hSΩ : cube c ℓ ⊆ Ω)
    {u : EuclideanSpace ℝ ι → ℝ} (hu : ContDiffOn ℝ 1 u Ω) :
    (∫⁻ x in cube c ℓ, ‖u x - ⨍ y in cube c ℓ, u y‖ₑ ^ 2 ∂weightedMeasure w) ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ) ^ (Fintype.card ι - 1) * 16 ^ Fintype.card ι * A * ℓ ^ 2) *
        ∫⁻ y in cube c ℓ, ‖fderiv ℝ u y‖ₑ ^ 2 ∂weightedMeasure w := by
  let K : ℝ := (Real.sqrt (Fintype.card ι)) ^ Fintype.card ι / Fintype.card ι
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hg : Measurable (fun y => ‖fderiv ℝ u y‖ₑ) := (measurable_fderiv ℝ u).enorm
  have hi := potential_square_bound h c hℓ hg
  have hm : Measurable (fun x : EuclideanSpace ℝ ι =>
      (∫⁻ y in cube c ℓ, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) * ‖fderiv ℝ u y‖ₑ) ^ 2) := by
    apply Measurable.pow_const
    apply Measurable.lintegral_prod_right
    fun_prop
  calc
    _ ≤ ∫⁻ x in cube c ℓ, (ENNReal.ofReal K *
        ∫⁻ y in cube c ℓ, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) * ‖fderiv ℝ u y‖ₑ) ^ 2 ∂weightedMeasure w := by
      apply setLIntegral_mono' (measurableSet_cube c ℓ)
      intro x hx
      exact pow_le_pow_left₀ zero_le (pointwise_potential_of_contDiffOn c hℓ hΩ hSΩ hu hx) 2
    _ = ENNReal.ofReal K ^ 2 * ∫⁻ x in cube c ℓ,
        (∫⁻ y in cube c ℓ, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) * ‖fderiv ℝ u y‖ₑ) ^ 2 ∂weightedMeasure w := by
      simp_rw [mul_pow]
      exact lintegral_const_mul _ hm
    _ ≤ ENNReal.ofReal K ^ 2 * (ENNReal.ofReal
        (((4 : ℝ) ^ Fintype.card ι * (Real.sqrt (Fintype.card ι) * ℓ)) ^ 2 * A) *
          ∫⁻ y in cube c ℓ, ‖fderiv ℝ u y‖ₑ ^ 2 ∂weightedMeasure w) := by gcongr
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_pow hK, ← ENNReal.ofReal_mul (sq_nonneg K)]
      rw [source_coefficient Fintype.card_pos]

/-- Ordinary weighted-integral version, with the original C1-neighborhood class,
unweighted centre and exact source constant. -/
theorem poincare {w : EuclideanSpace ℝ ι → ℝ} {A : ℝ}
    {Z : Set (EuclideanSpace ℝ ι)} (h : Bounds w A Z)
    (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Ω : Set (EuclideanSpace ℝ ι)} (hΩ : IsOpen Ω) (hSΩ : cube c ℓ ⊆ Ω)
    {u : EuclideanSpace ℝ ι → ℝ} (hu : ContDiffOn ℝ 1 u Ω) :
    (∫ x in cube c ℓ, w x * (u x - ⨍ y in cube c ℓ, u y) ^ 2) ≤
      ((Fintype.card ι : ℝ) ^ (Fintype.card ι - 1) * 16 ^ Fintype.card ι * A * ℓ ^ 2) *
        ∫ x in cube c ℓ, w x * ‖fderiv ℝ u x‖ ^ 2 := by
  let S := cube c ℓ
  let a := ⨍ y in S, u y
  let C : ℝ := (Fintype.card ι : ℝ) ^ (Fintype.card ι - 1) * 16 ^ Fintype.card ι * A * ℓ ^ 2
  have hA : 0 ≤ A := zero_le_one.trans h.constant_ge_one
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  letI := h.locallyFinite
  have huc : ContinuousOn u S := hu.continuousOn.mono hSΩ
  have hgc : ContinuousOn (fderiv ℝ u) S :=
    (hu.continuousOn_fderiv_of_isOpen hΩ (by norm_num)).mono hSΩ
  have hLInt : IntegrableOn (fun x => (u x - a) ^ 2) S (weightedMeasure w) :=
    ((huc.sub continuousOn_const).pow 2).integrableOn_compact (isCompact_cube c ℓ)
  have hRInt : IntegrableOn (fun x => ‖fderiv ℝ u x‖ ^ 2) S (weightedMeasure w) :=
    (hgc.norm.pow 2).integrableOn_compact (isCompact_cube c ℓ)
  have hL := ofReal_integral_eq_lintegral_ofReal hLInt (Eventually.of_forall fun x => sq_nonneg (u x - a))
  have hR := ofReal_integral_eq_lintegral_ofReal hRInt (Eventually.of_forall fun x => sq_nonneg ‖fderiv ℝ u x‖)
  have hleft (x : EuclideanSpace ℝ ι) : ‖u x - a‖ₑ ^ 2 = ENNReal.ofReal ((u x - a) ^ 2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  have hright (x : EuclideanSpace ℝ ι) : ‖fderiv ℝ u x‖ₑ ^ 2 = ENNReal.ofReal (‖fderiv ℝ u x‖ ^ 2) := by
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have hp := poincare_lintegral_of_contDiffOn h c hℓ hΩ hSΩ hu
  change (∫⁻ x in S, ‖u x - a‖ₑ ^ 2 ∂weightedMeasure w) ≤
    ENNReal.ofReal C * ∫⁻ x in S, ‖fderiv ℝ u x‖ₑ ^ 2 ∂weightedMeasure w at hp
  simp_rw [hleft, hright] at hp
  rw [← hL, ← hR] at hp
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC,
    ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg (u x - a)),
    ENNReal.toReal_ofReal (integral_nonneg fun x => sq_nonneg ‖fderiv ℝ u x‖)] at hr
  rw [h.setIntegral_weightedMeasure (measurableSet_cube c ℓ),
    h.setIntegral_weightedMeasure (measurableSet_cube c ℓ)] at hr
  exact hr

end PeriodicAttractiveLogGas.WeightedCubePoincare
