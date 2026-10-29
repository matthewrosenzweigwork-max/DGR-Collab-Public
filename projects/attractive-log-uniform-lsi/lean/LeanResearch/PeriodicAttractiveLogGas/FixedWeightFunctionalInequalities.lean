import LeanResearch.PeriodicAttractiveLogGas.FixedWeightProbability

/-! Appendix A inequalities for the actual normalized distance weight.
The Euclidean cube derivative is identified with the full physical gradient
before transporting either estimate to the product torus. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal NNReal Topology BigOperators
namespace PeriodicAttractiveLogGas.FixedWeightFunctionalInequalities
open FixedWeightProbability PhysicalCubes WeightedCubeBounds

def poincareConstant (N : ℕ) (β₀ : ℝ) : ℝ :=
  (2 * (N : ℝ)) ^ (2 * N - 1) * 16 ^ (2 * N) * FixedParticleAOne.constant N β₀

def sobolevConstant (N : ℕ) (β₀ : ℝ) : ℝ :=
  WeightedCubeSobolev.coefficient (Fin N × Fin 2) (FixedParticleAOne.constant N β₀)

def firstConstant (N : ℕ) (β₀ : ℝ) : ℝ :=
  Real.sqrt (FixedParticleAOne.normalizationBound N β₀) * sobolevConstant N β₀

lemma constants_nonneg (N : ℕ) (β₀ : ℝ) :
    0 ≤ poincareConstant N β₀ ∧ 0 ≤ sobolevConstant N β₀ ∧ 0 ≤ firstConstant N β₀ := by
  have hA := zero_le_one.trans (FixedParticleAOne.constant_ge_one N β₀)
  have hS := WeightedCubeSobolev.coefficient_nonneg (ι := Fin N × Fin 2) hA
  refine ⟨?_, hS, mul_nonneg (Real.sqrt_nonneg _) hS⟩
  unfold poincareConstant
  positivity

lemma exponent_ratio {N : ℕ} (hN : 2 ≤ N) :
    WeightedPotentialSobolev.exponent (Fin N × Fin 2) /
      (WeightedPotentialSobolev.exponent (Fin N × Fin 2) - 2) = (N : ℝ) := by
  have hd : 2 < Fintype.card (Fin N × Fin 2) := by
    simp only [Fintype.card_prod, Fintype.card_fin]; omega
  have hdr : (2 : ℝ) < Fintype.card (Fin N × Fin 2) := by exact_mod_cast hd
  have hp := WeightedPotentialSobolev.exponent_gt_two hd
  have hc : WeightedPotentialSobolev.exponent (Fin N × Fin 2) *
      ((Fintype.card (Fin N × Fin 2) : ℝ) - 2) =
        2 * (Fintype.card (Fin N × Fin 2) : ℝ) :=
    div_mul_cancel₀ _ (by linarith)
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at hc
  apply (div_eq_iff (sub_pos.mpr hp).ne').mpr
  nlinarith only [hc]

lemma exponent_gt_two {N : ℕ} (hN : 2 ≤ N) :
    2 < WeightedPotentialSobolev.exponent (Fin N × Fin 2) := by
  apply WeightedPotentialSobolev.exponent_gt_two
  simp only [Fintype.card_prod, Fintype.card_fin]
  omega

lemma smooth_lift_derivative_norm {N : ℕ} (s : SmoothPair N) (X : Gradient N) :
    ‖fderiv ℝ (fun Y => s.value (configurationQuotient N Y)) X‖ =
      ‖s.gradient (configurationQuotient N X)‖ := by
  rw [(s.differential X).fderiv]
  exact (InnerProductSpace.toDual ℝ (Gradient N)).norm_map _

lemma reference_mean_cube {N : ℕ} (s : SmoothPair N) (c : Gradient N) :
    (⨍ X in cube c 1, s.value (configurationQuotient N X)) =
      ∫ X, s.value X ∂referenceMeasure N := by
  rw [setAverage_eq, cube_volume_real c zero_le_one, one_pow, inv_one, one_smul]
  exact integral_quotient_cube N c s.value.continuous.measurable

/-- Raw weighted cube Sobolev inequality transported through the actual
quotient map, retaining the unweighted reference mean. -/
lemma raw_sobolev {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀) (s : SmoothPair N) :
    eLpNorm (fun X => s.value X - ∫ Y, s.value Y ∂referenceMeasure N)
      (ENNReal.ofReal (WeightedPotentialSobolev.exponent (Fin N × Fin 2))) (raw N a) ≤
        ENNReal.ofReal (sobolevConstant N β₀) * eLpNorm s.gradient 2 (raw N a) := by
  let c : Gradient N := WithLp.toLp 2 (fun _ => (1 / 2 : ℝ))
  let W := (weightedMeasure (EuclideanCubeWeight.weight N a)).restrict (cube c 1)
  have h := periodic_bounds hN hβ₀ hsub ha haa
  have hq := quotient_weighted_cube N a c
  have hd : 2 < Fintype.card (Fin N × Fin 2) := by
    simp only [Fintype.card_prod, Fintype.card_fin]; omega
  have hh := WeightedCubeSobolev.eLpNorm_bound hd h c zero_lt_one isOpen_univ
    (subset_univ _) (s.smooth.of_le (by simp)).contDiffOn
  rw [reference_mean_cube] at hh
  have hgrad : eLpNorm (fderiv ℝ (fun Y => s.value (configurationQuotient N Y))) 2 W =
      eLpNorm s.gradient 2 (raw N a) := by
    calc
      _ = eLpNorm (s.gradient ∘ configurationQuotient N) 2 W :=
        eLpNorm_congr_norm_ae (measurable_fderiv ℝ _).aestronglyMeasurable
          (s.gradient.continuous.measurable.comp hq.measurable).aestronglyMeasurable
          (Eventually.of_forall (smooth_lift_derivative_norm s))
      _ = _ := eLpNorm_comp_measurePreserving s.gradient.continuous.measurable.aestronglyMeasurable hq
  have hval := eLpNorm_comp_measurePreserving
    (g := fun X => s.value X - ∫ Y, s.value Y ∂referenceMeasure N)
    (s.value.continuous.measurable.sub measurable_const).aestronglyMeasurable hq
      (p := ENNReal.ofReal (WeightedPotentialSobolev.exponent (Fin N × Fin 2)))
  simp only [Function.comp_def] at hval
  rw [hval, hgrad] at hh
  exact hh

lemma raw_poincare {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀) (s : SmoothPair N) :
    (∫ X, (s.value X - ∫ Y, s.value Y ∂referenceMeasure N) ^ 2 ∂raw N a) ≤
      poincareConstant N β₀ * ∫ X, ‖s.gradient X‖ ^ 2 ∂raw N a := by
  let : Nonempty (Fin N) := ⟨⟨0, by omega⟩⟩
  let c : Gradient N := WithLp.toLp 2 (fun _ => (1 / 2 : ℝ))
  have h := periodic_bounds hN hβ₀ hsub ha haa
  have hh := WeightedCubePoincare.poincare h c zero_lt_one isOpen_univ
    (subset_univ _) (s.smooth.of_le (by simp)).contDiffOn
  rw [← h.setIntegral_weightedMeasure (measurableSet_cube c 1),
    ← h.setIntegral_weightedMeasure (measurableSet_cube c 1)] at hh
  simp_rw [reference_mean_cube, smooth_lift_derivative_norm] at hh
  rw [integral_quotient_weighted_cube N a c
    (F := fun X => (s.value X - ∫ Y, s.value Y ∂referenceMeasure N) ^ 2)
    (s.value.continuous.measurable.sub measurable_const |>.pow_const 2),
    integral_quotient_weighted_cube N a c (s.gradient.continuous.measurable.norm.pow_const 2)] at hh
  simpa only [poincareConstant, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat,
    Nat.mul_comm N 2, mul_comm (N : ℝ) 2, one_pow, mul_one] using hh

/-- Poincare for the distance-weight probability, with no LSI input. -/
theorem poincare {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀) (s : SmoothPair N) :
    variance s.value (law N a) ≤ poincareConstant N β₀ * ∫ X, ‖s.gradient X‖ ^ 2 ∂law N a := by
  let : IsProbabilityMeasure (law N a) := law_probability hN hβ₀ hsub ha haa
  have hZ := zero_lt_one.trans_le (normalizer_bounds hN hβ₀ hsub ha haa).1
  apply (DensityMoments.variance_le_integral_sub_sq s.value.continuous.measurable
    (∫ Y, s.value Y ∂referenceMeasure N)).trans
  rw [law_integral hZ.le, law_integral hZ.le]
  have hh := mul_le_mul_of_nonneg_left (raw_poincare hN hβ₀ hsub ha haa s) (inv_nonneg.mpr hZ.le)
  simpa only [mul_left_comm (normalizer N a)⁻¹] using hh

/-- Source probability-weight Sobolev bound with its unweighted center
already accounted for by the proved normalization argument. -/
theorem sobolev {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀) (s : SmoothPair N) :
    lpNorm s.value (ENNReal.ofReal (WeightedPotentialSobolev.exponent (Fin N × Fin 2))) (law N a) ≤
      firstConstant N β₀ * lpNorm s.gradient 2 (law N a) +
        FixedParticleAOne.normalizationBound N β₀ * lpNorm s.value 2 (law N a) := by
  let : IsProbabilityMeasure (law N a) := law_probability hN hβ₀ hsub ha haa
  have hZ := normalizer_bounds hN hβ₀ hsub ha haa
  exact ProbabilityWeightSobolev.normalized_lpNorm_bound hZ.1 hZ.2 (constants_nonneg N β₀).2.1
    (exponent_gt_two hN) (raw_eq_smul_law (zero_lt_one.trans_le hZ.1)) (reference_le_raw N ha)
    (s.value_memLp _) (s.gradient_memLp _) (raw_sobolev hN hβ₀ hsub ha haa s)

/-- Fixed-particle defective entropy for the actual distance-weight law.
All constants use only N and beta0; the exponent a includes zero. -/
theorem defective_entropy {N : ℕ} (hN : 2 ≤ N) {β₀ a : ℝ}
    (hβ₀ : 0 ≤ β₀) (hsub : β₀ < 4) (ha : 0 ≤ a)
    (haa : a ≤ FixedWeightConstants.exponent N β₀) (s : SmoothPair N) :
    Rothaus.squareEntropy (law N a) s.value ≤
      2 * N * firstConstant N β₀ ^ 2 * (∫ X, ‖s.gradient X‖ ^ 2 ∂law N a) +
        N * (2 * FixedParticleAOne.normalizationBound N β₀ ^ 2 - 1) *
          ∫ X, s.value X ^ 2 ∂law N a := by
  let : IsProbabilityMeasure (law N a) := law_probability hN hβ₀ hsub ha haa
  have hSob := sobolev hN hβ₀ hsub ha haa s
  rw [DensityEntropy.lpNorm_two_sqrt s.gradient.continuous.measurable.aestronglyMeasurable] at hSob
  have hh := SobolevEntropy.defective s.value.continuous.measurable
    ⟨‖s.value‖, fun X => by simpa only [Real.norm_eq_abs] using s.value.norm_coe_le_norm X⟩
    (exponent_gt_two hN) (constants_nonneg N β₀).2.2
    (zero_le_one.trans (FixedParticleAOne.normalizationBound_ge_one N β₀))
    (integral_nonneg fun X => sq_nonneg ‖s.gradient X‖) hSob
  rw [exponent_ratio hN] at hh
  exact hh.trans_eq (by ring)

end PeriodicAttractiveLogGas.FixedWeightFunctionalInequalities
