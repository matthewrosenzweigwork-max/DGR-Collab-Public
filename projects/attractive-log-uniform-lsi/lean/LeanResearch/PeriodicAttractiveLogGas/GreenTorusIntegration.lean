import LeanResearch.PeriodicAttractiveLogGas.TorusSmoothCalculus
import LeanResearch.PeriodicAttractiveLogGas.GreenRegularizationL1

/-! Periodic weak first integration by parts across the Green pole.

The proof uses actual smooth regularizations, ordinary Haar integration by
parts, and the proved dominated L1 passage. In particular, integrability of
the classical gradient alone is not taken as a weak-derivative identity.
This is the Green representation step in source Lemma 3.1.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators RealInnerProductSpace

namespace PeriodicAttractiveLogGas

theorem integrable_regularGreenRepresentative_mul_continuous (F : C(Torus, ℝ)) :
    Integrable (fun z ↦ regularGreenRepresentative z * F z) torusMeasure :=
  regularGreenRepresentative_integrable.mul_bdd F.continuous.aestronglyMeasurable
    (Eventually.of_forall F.norm_coe_le_norm)

theorem integrable_greenGradient_inner_continuous (F : C(Torus, PlanarSpace)) :
    Integrable (fun z ↦ inner ℝ (greenGradient z) (F z)) torusMeasure := by
  apply (integrable_greenGradient.norm.mul_const ‖F‖).mono'
    (measurable_greenGradient.aestronglyMeasurable.inner F.continuous.aestronglyMeasurable)
  filter_upwards with z
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_left (F.norm_coe_le_norm z) (norm_nonneg _))

/-- The actual global periodic weak first-derivative identity. -/
theorem green_torus_integration_by_parts (f : SmoothPair 1) (v : PlanarSpace) :
    (∫ z, f.torusValue z * inner ℝ (greenGradient z) v ∂torusMeasure) =
      -(∫ z, regularGreenRepresentative z * inner ℝ (f.torusGradient z) v ∂torusMeasure) := by
  let ε : ℕ → ℝ := fun n ↦ (1 / 16 : ℝ) * (1 / ((n : ℝ) + 1))
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hs (n : ℕ) : ε n ≤ (1 / 16 : ℝ) := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
    have hi := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn
    dsimp [ε]
    nlinarith
  have ht : Tendsto ε atTop (𝓝 0) := by
    simpa only [ε, mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (1 / 16 : ℝ)
  let A : C(Torus, PlanarSpace) := ⟨fun z ↦ f.torusValue z • v, by fun_prop⟩
  let B : C(Torus, ℝ) := ⟨fun z ↦ inner ℝ (f.torusGradient z) v, by fun_prop⟩
  have hl := tendsto_integral_regularizedGreenGradient_inner ε hε hs ht A
  have hr := (tendsto_integral_regularizedGreen_mul ε hε hs ht B).neg
  have heq (n : ℕ) :
      (∫ z, inner ℝ (regularizedGreenGradient (ε n) (hε n) z) (A z) ∂torusMeasure) =
        -(∫ z, regularizedGreen (ε n) (hε n) z * B z ∂torusMeasure) := by
    have h := (SmoothPair.ofTorusContDiffLift
      ⟨regularizedGreen (ε n) (hε n), continuous_regularizedGreen (ε n) (hε n)⟩
      (contDiff_regularizedGreen_lift (ε n) (hε n) (hs n))).torus_integration_by_parts f v
    simp_rw [torusGradient_regularizedGreen (ε n) (hε n) (hs n)] at h
    simpa only [SmoothPair.ofTorusContDiffLift_torusValue, ContinuousMap.coe_mk,
      A, B, inner_smul_right, mul_comm] using h
  have hlim := tendsto_nhds_unique (hl.congr (fun n ↦ heq n)) hr
  simpa only [A, B, ContinuousMap.coe_mk, inner_smul_right, mul_comm] using hlim

theorem regularGreenRepresentative_weak_laplacian (f : SmoothPair 1) :
    (∫ z, regularGreenRepresentative z * (-f.laplacian.torusValue z) ∂torusMeasure) =
      (2 * Real.pi) * (f.torusValue 0 - ∫ z, f.torusValue z ∂torusMeasure) := by
  apply Eq.trans (integral_congr_ae ?_) (greenRealRepresentative_weak_laplacian f)
  filter_upwards [regularGreenRepresentative_ae] with z hz
  rw [hz]

/-- The distributional Green identity in the actual first-gradient pairing. -/
theorem green_torus_gradient_pairing (f : SmoothPair 1) :
    (∫ z, inner ℝ (greenGradient z) (f.torusGradient z) ∂torusMeasure) =
      (2 * Real.pi) * (f.torusValue 0 - ∫ z, f.torusValue z ∂torusMeasure) := by
  let D (j : Fin 2) := f.directionalDerivativePair (EuclideanSpace.single (0, j) 1)
  have hd (j : Fin 2) (z : Torus) :
      (D j).torusValue z = inner ℝ (f.torusGradient z) (EuclideanSpace.single j 1) := by
    simpa only [singleParticleCoordinates_single, D] using
      f.torus_directionalDerivative_value z (EuclideanSpace.single j 1)
  have hi (j : Fin 2) : Integrable
      (fun z ↦ (D j).torusValue z * inner ℝ (greenGradient z) (EuclideanSpace.single j 1))
      torusMeasure :=
    (integrable_greenGradient.inner_const (EuclideanSpace.single j 1)).bdd_mul
      (D j).torusValue.continuous.aestronglyMeasurable
      (Eventually.of_forall (D j).torusValue.norm_coe_le_norm)
  have hj (j : Fin 2) : Integrable
      (fun z ↦ regularGreenRepresentative z *
        inner ℝ ((D j).torusGradient z) (EuclideanSpace.single j 1)) torusMeasure :=
    integrable_regularGreenRepresentative_mul_continuous
      ⟨fun z ↦ inner ℝ ((D j).torusGradient z) (EuclideanSpace.single j 1), by fun_prop⟩
  calc
    (∫ z, inner ℝ (greenGradient z) (f.torusGradient z) ∂torusMeasure) =
        ∫ z, ∑ j : Fin 2, (D j).torusValue z *
          inner ℝ (greenGradient z) (EuclideanSpace.single j 1) ∂torusMeasure := by
      apply integral_congr_ae
      filter_upwards with z
      simp [hd, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
    _ = ∑ j : Fin 2, ∫ z, (D j).torusValue z *
          inner ℝ (greenGradient z) (EuclideanSpace.single j 1) ∂torusMeasure :=
      integral_finsetSum Finset.univ (fun j _ ↦ hi j)
    _ = ∑ j : Fin 2, -(∫ z, regularGreenRepresentative z *
          inner ℝ ((D j).torusGradient z) (EuclideanSpace.single j 1) ∂torusMeasure) := by
      apply Finset.sum_congr rfl
      intro j _
      exact green_torus_integration_by_parts (D j) (EuclideanSpace.single j 1)
    _ = -(∫ z, regularGreenRepresentative z * f.laplacian.torusValue z ∂torusMeasure) := by
      rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ (fun j _ ↦ hj j)]
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      rw [← Finset.mul_sum]
      congr 1
      simp only [SmoothPair.torusValue, SmoothPair.laplacian_value_apply,
        Fin.sum_univ_one, SmoothPair.secondDirectionalDerivativePair_value_apply,
        SmoothPair.torusGradient, ContinuousMap.coe_mk, inner_firstParticleCoordinates,
        singleParticleCoordinates_single, D]
    _ = ∫ z, regularGreenRepresentative z * (-f.laplacian.torusValue z) ∂torusMeasure := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with z
      ring
    _ = _ := regularGreenRepresentative_weak_laplacian f

/-- The exact signed gradient-convolution representation in source Lemma 3.1,
with its factor 1/(2π) and the ordinary two-dimensional gradient. -/
theorem green_gradient_convolution_representation (f : SmoothPair 1) (x : Torus) :
    f.torusValue x - (∫ z, f.torusValue z ∂torusMeasure) =
      -(1 / (2 * Real.pi)) *
        (∫ y, inner ℝ (greenGradient y) (f.torusGradient (x - y)) ∂torusMeasure) := by
  have h := green_torus_gradient_pairing (f.translateSub (singleConfiguration x))
  simp only [SmoothPair.translateSub_torusGradient, inner_neg_right, integral_neg,
    SmoothPair.translateSub_torusValue, sub_zero,
    integral_sub_left_eq_self f.torusValue torusMeasure x] at h
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith

end PeriodicAttractiveLogGas
