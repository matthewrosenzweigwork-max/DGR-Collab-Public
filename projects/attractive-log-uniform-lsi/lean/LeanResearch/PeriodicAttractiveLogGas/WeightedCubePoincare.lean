import LeanResearch.PeriodicAttractiveLogGas.WeightedKernelBounds
import LeanResearch.PeriodicAttractiveLogGas.WeightedSchur
import LeanResearch.PeriodicAttractiveLogGas.CubePotential

/-! Appendix A weighted Poincare argument on the actual physical cube.
The centre is the unweighted cube mean. The dyadic row/column bounds,
Cauchy--Schwarz and Tonelli give exactly the source coefficient. -/
set_option autoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal NNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.WeightedCubePoincare
open PhysicalCubes WeightedCubeBounds WeightedKernelBounds WeightedSchur
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma potential_coefficient (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    ENNReal.ofReal ((Real.sqrt (Fintype.card ι) * ℓ) ^ Fintype.card ι / Fintype.card ι) /
      volume (cube c ℓ) =
        ENNReal.ofReal ((Real.sqrt (Fintype.card ι)) ^ Fintype.card ι / Fintype.card ι) := by
  rw [cube_volume c hℓ.le, ← ENNReal.ofReal_div_of_pos (pow_pos hℓ _)]
  congr 1
  rw [mul_pow]
  field_simp [hℓ.ne']

lemma pointwise_potential (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {u : EuclideanSpace ℝ ι → ℝ} (hu : ContDiff ℝ 1 u) {x : EuclideanSpace ℝ ι}
    (hx : x ∈ cube c ℓ) :
    ‖u x - ⨍ y in cube c ℓ, u y‖ₑ ≤
      ENNReal.ofReal ((Real.sqrt (Fintype.card ι)) ^ Fintype.card ι / Fintype.card ι) *
        ∫⁻ y in cube c ℓ, ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) * ‖fderiv ℝ u y‖ₑ := by
  have hz : volume (cube c ℓ) ≠ 0 := by
    rw [cube_volume c hℓ.le]
    exact (ENNReal.ofReal_pos.mpr (pow_pos hℓ _)).ne'
  have hh := CubePotential.mean_oscillation (μ := volume) (isCompact_cube c ℓ)
    (convex_cube c ℓ) hu hx (cube_subset_ball_at_point c hℓ.le hx) hz
  simp only [finrank_euclideanSpace, potential_coefficient c hℓ] at hh
  simpa only [mul_comm (‖fderiv ℝ u _‖ₑ)] using hh

/-- The squared potential estimate retains the weight in the input integral. -/
theorem potential_square_bound {w : EuclideanSpace ℝ ι → ℝ} {A : ℝ}
    {Z : Set (EuclideanSpace ℝ ι)} (h : Bounds w A Z)
    (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ ι → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ x in cube c ℓ, (∫⁻ y in cube c ℓ,
      ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ)) * g y) ^ 2 ∂weightedMeasure w) ≤
      ENNReal.ofReal (((4 : ℝ) ^ Fintype.card ι * (Real.sqrt (Fintype.card ι) * ℓ)) ^ 2 * A) *
        ∫⁻ y in cube c ℓ, g y ^ 2 ∂weightedMeasure w := by
  let S := cube c ℓ
  let C : ℝ := (4 : ℝ) ^ Fintype.card ι * (Real.sqrt (Fintype.card ι) * ℓ)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hA : 0 ≤ A := zero_le_one.trans h.constant_ge_one
  let k := fun x y : EuclideanSpace ℝ ι => ‖x - y‖ₑ ^ (1 - (Fintype.card ι : ℝ))
  have hk : Measurable (Function.uncurry k) := by
    dsimp only [k, Function.uncurry]
    fun_prop
  letI : SFinite (weightedMeasure w) := weightedMeasure_sFinite w
  have hrow : ∀ᵐ x ∂(weightedMeasure w).restrict S, ∫⁻ y in S, k x y ≤ ENNReal.ofReal C := by
    filter_upwards [ae_restrict_mem (measurableSet_cube c ℓ)] with x hx
    exact unweighted_cube c hℓ hx
  have hcol : ∀ᵐ y ∂volume.restrict S,
      (∫⁻ x in S, k x y ∂weightedMeasure w) ≤ ENNReal.ofReal (C * A) * ENNReal.ofReal (w y) := by
    filter_upwards [ae_restrict_mem (measurableSet_cube c ℓ),
      ae_restrict_of_ae (compl_mem_ae_iff.mpr h.exceptional_null)] with y hy hyZ
    calc
      _ = ∫⁻ x in S, ‖y - x‖ₑ ^ (1 - (Fintype.card ι : ℝ)) ∂weightedMeasure w := by
        apply lintegral_congr
        intro x
        dsimp only [k]
        rw [enorm_sub_rev]
      _ ≤ ENNReal.ofReal (C * A * w y) := weighted_cube h c hℓ hy hyZ
      _ = _ := ENNReal.ofReal_mul (mul_nonneg hC hA)
  have hh := lintegral_rpow_lintegral_mul_le_weighted hk hg.aemeasurable
    (by norm_num : (1 : ℝ) ≤ 2) h.measurable.ennreal_ofReal.aemeasurable hrow hcol
  norm_num only [ENNReal.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at hh
  have hwg : Measurable (fun y => g y ^ 2) := hg.pow_const 2
  have hchange : (∫⁻ y in S, g y ^ 2 ∂weightedMeasure w) =
      ∫⁻ y in S, ENNReal.ofReal (w y) * g y ^ 2 := by
    rw [weightedMeasure, setLIntegral_withDensity_eq_setLIntegral_mul volume
      h.measurable.ennreal_ofReal hwg (measurableSet_cube c ℓ)]
    rfl
  rw [← hchange] at hh
  have hcoeff : ENNReal.ofReal C * ENNReal.ofReal (C * A) = ENNReal.ofReal (C ^ 2 * A) := by
    rw [← ENNReal.ofReal_mul hC]
    congr 1
    ring
  simpa only [hcoeff] using hh

lemma source_coefficient {d : ℕ} (hd : 1 ≤ d) (ℓ A : ℝ) :
    ((Real.sqrt d) ^ d / (d : ℝ)) ^ 2 * (((4 : ℝ) ^ d * (Real.sqrt d * ℓ)) ^ 2 * A) =
      (d : ℝ) ^ (d - 1) * 16 ^ d * A * ℓ ^ 2 := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have hs : (Real.sqrt (d : ℝ) ^ d) ^ 2 = (d : ℝ) ^ d := by
    rw [← pow_mul, Nat.mul_comm d 2, pow_mul, Real.sq_sqrt (by positivity)]
  have h4 : ((4 : ℝ) ^ d) ^ 2 = (16 : ℝ) ^ d := by
    rw [← pow_mul, Nat.mul_comm d 2, pow_mul]
    norm_num
  rw [div_pow, mul_pow, mul_pow, hs, h4, Real.sq_sqrt (by positivity)]
  rw [show (d : ℝ) ^ d = (d : ℝ) ^ (d - 1) * d by rw [← pow_succ, Nat.sub_add_cancel hd]]
  field_simp [hd0] <;> ring

/-- Source Lemma fixed-weighted-PI in lower-integral form, for globally C1 tests.
No Poincare estimate, potential bound or kernel estimate is assumed. -/
theorem poincare_lintegral {w : EuclideanSpace ℝ ι → ℝ} {A : ℝ}
    {Z : Set (EuclideanSpace ℝ ι)} (h : Bounds w A Z)
    (c : EuclideanSpace ℝ ι) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {u : EuclideanSpace ℝ ι → ℝ} (hu : ContDiff ℝ 1 u) :
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
      exact pow_le_pow_left₀ zero_le (pointwise_potential c hℓ hu hx) 2
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

end PeriodicAttractiveLogGas.WeightedCubePoincare
