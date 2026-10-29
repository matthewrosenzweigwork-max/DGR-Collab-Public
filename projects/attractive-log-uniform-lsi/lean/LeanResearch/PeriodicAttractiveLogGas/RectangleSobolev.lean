import LeanResearch.PeriodicAttractiveLogGas.TorusSobolev
import LeanResearch.PeriodicAttractiveLogGas.RectangleReflection
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-! Source Lemma 3.1, with its exact constants and Lipschitz-on-closure class.
The torus proof, even reflection, normalized distribution and ordinary
derivative identities are assembled here. No Sobolev or gradient-compatibility
premise is added to either rectangle conclusion. -/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace PeriodicAttractiveLogGas

theorem isCompact_closedUnitSquare : IsCompact closedUnitSquare :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ ↦ isCompact_Icc)

theorem isCompact_closedDoubleRectangle : IsCompact closedDoubleRectangle :=
  (PiLp.homeomorph 2 (fun _ : Fin 2 ↦ ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ ↦ isCompact_Icc)

theorem aestronglyMeasurable_square {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) : AEStronglyMeasurable u squareLebesgue :=
  hu.continuousOn.aestronglyMeasurable measurableSet_closedUnitSquare

theorem aestronglyMeasurable_rectangle {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedDoubleRectangle) :
    AEStronglyMeasurable u rectangleLebesgue :=
  (hu.continuousOn.aestronglyMeasurable measurableSet_closedDoubleRectangle).smul_measure _

theorem memLp_square {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) (p : ℝ≥0∞) : MemLp u p squareLebesgue := by
  obtain ⟨C, hC⟩ := isCompact_closedUnitSquare.exists_bound_of_continuousOn hu.continuousOn
  apply MemLp.of_bound (aestronglyMeasurable_square hu) C
  filter_upwards [ae_restrict_mem measurableSet_closedUnitSquare] with x hx
  exact hC x hx

theorem memLp_rectangle {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedDoubleRectangle) (p : ℝ≥0∞) :
    MemLp u p rectangleLebesgue := by
  obtain ⟨C, hC⟩ := isCompact_closedDoubleRectangle.exists_bound_of_continuousOn hu.continuousOn
  apply MemLp.of_bound (aestronglyMeasurable_rectangle hu) C
  filter_upwards [ae_mem_openDoubleRectangle] with x hx
  exact hC x (fun j hj ↦ ⟨(hx j hj).1.le, (hx j hj).2.le⟩)

theorem measurable_rectangleOrdinaryGradient (u : PlanarSpace → ℝ) :
    Measurable (rectangleOrdinaryGradient u) :=
  (InnerProductSpace.toDual ℝ PlanarSpace).symm.continuous.measurable.comp
    (measurable_fderiv ℝ u)

theorem memLp_rectangleOrdinaryGradient_square {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) :
    MemLp (rectangleOrdinaryGradient u) 2 squareLebesgue := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_rectangleOrdinaryGradient u).aestronglyMeasurable).mpr
  simpa only [norm_rectangleOrdinaryGradient] using integrable_sq_norm_fderiv_on_square hu

theorem memLp_rectangleOrdinaryGradient_rectangle {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedDoubleRectangle) :
    MemLp (rectangleOrdinaryGradient u) 2 rectangleLebesgue := by
  apply (memLp_two_iff_integrable_sq_norm
    (measurable_rectangleOrdinaryGradient u).aestronglyMeasurable).mpr
  simpa only [norm_rectangleOrdinaryGradient] using integrable_sq_norm_fderiv_on_rectangle hu

theorem lpNorm_two_eq_sqrt_integral_sq {α E : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    lpNorm f 2 μ = Real.sqrt (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow, one_div]

def reflectedSquareContinuousMap {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) : C(Torus, ℝ) :=
  ⟨fun z ↦ u (squareReflection z), continuous_reflectedSquare hu⟩

theorem ae_torusLiftGradient_reflectedSquare {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) :
    torusLiftGradient (reflectedSquareContinuousMap hu) =ᵐ[torusMeasure]
      reflectedSquareGradient u := by
  have hd := ae_hasFDerivAt_torusLiftGradient (reflectedSquareContinuousMap hu)
    (lipschitzWith_reflectedSquare_lift hu)
  filter_upwards [hd] with z hz
  have he := (hz (centeredLift z) (torusQuotient_centeredLift z)).fderiv
  apply (InnerProductSpace.toDual ℝ PlanarSpace).injective
  change innerSL ℝ (torusLiftGradient (reflectedSquareContinuousMap hu) z) = _
  change _ = (InnerProductSpace.toDual ℝ PlanarSpace)
    ((InnerProductSpace.toDual ℝ PlanarSpace).symm
      (fderiv ℝ (fun y ↦ u (squareReflection (torusQuotient y))) (centeredLift z)))
  rw [(InnerProductSpace.toDual ℝ PlanarSpace).apply_symm_apply]
  exact he.symm

theorem lpNorm_torusLiftGradient_reflectedSquare {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) :
    lpNorm (torusLiftGradient (reflectedSquareContinuousMap hu)) 2 torusMeasure =
      2 * lpNorm (rectangleOrdinaryGradient u) 2 squareLebesgue := by
  rw [lpNorm_two_eq_sqrt_integral_sq (measurable_torusLiftGradient _).aestronglyMeasurable,
    lpNorm_two_eq_sqrt_integral_sq (measurable_rectangleOrdinaryGradient u).aestronglyMeasurable]
  have he : (∫ z, ‖torusLiftGradient (reflectedSquareContinuousMap hu) z‖ ^ 2 ∂torusMeasure) =
      ∫ z, ‖reflectedSquareGradient u z‖ ^ 2 ∂torusMeasure := by
    apply integral_congr_ae
    exact (ae_torusLiftGradient_reflectedSquare hu).mono fun z hz ↦ congrArg (fun v ↦ ‖v‖ ^ 2) hz
  rw [he, sqrt_integral_sq_norm_reflectedSquareGradient hu]

theorem lpNorm_rectanglePullback_le {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedDoubleRectangle) :
    lpNorm (rectangleOrdinaryGradient (fun y ↦ u (rectangleStretch y))) 2 squareLebesgue ≤
      2 * lpNorm (rectangleOrdinaryGradient u) 2 rectangleLebesgue := by
  rw [lpNorm_two_eq_sqrt_integral_sq
      (measurable_rectangleOrdinaryGradient _).aestronglyMeasurable,
    lpNorm_two_eq_sqrt_integral_sq (measurable_rectangleOrdinaryGradient _).aestronglyMeasurable]
  exact sqrt_integral_sq_norm_rectanglePullback_le hu

def squareSobolevConstant (r : ℝ) : ℝ := 2 * torusSobolevConstant r
def rectangleSobolevConstant (r : ℝ) : ℝ := 4 * torusSobolevConstant r

theorem squareSobolevConstant_nonneg (r : ℝ) : 0 ≤ squareSobolevConstant r :=
  mul_nonneg (by norm_num) (torusSobolevConstant_nonneg r)

theorem rectangleSobolevConstant_nonneg (r : ℝ) : 0 ≤ rectangleSobolevConstant r :=
  mul_nonneg (by norm_num) (torusSobolevConstant_nonneg r)

/-- Exact square assertion of source Lemma 3.1, for every finite real r≥2. -/
theorem square_lipschitz_sobolev {r : ℝ} (hr : 2 ≤ r) {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedUnitSquare) :
    lpNorm (fun x ↦ u x - ∫ y, u y ∂squareLebesgue) (ENNReal.ofReal r) squareLebesgue ≤
      squareSobolevConstant r * lpNorm (rectangleOrdinaryGradient u) 2 squareLebesgue := by
  have h := torus_lipschitz_sobolev hr (reflectedSquareContinuousMap hu)
    (lipschitzWith_reflectedSquare_lift hu)
  rw [lpNorm_torusLiftGradient_reflectedSquare hu] at h
  have hm := integral_squareReflection ((memLp_square hu 1).integrable le_rfl)
  have hn := eLpNorm_comp_measurePreserving
    (g := fun x ↦ u x - ∫ y, u y ∂squareLebesgue)
    ((aestronglyMeasurable_square hu).sub aestronglyMeasurable_const)
    measurePreserving_squareReflection (p := ENNReal.ofReal r)
  have hn' := congrArg ENNReal.toReal hn
  change lpNorm (fun z ↦ u (squareReflection z) - ∫ y, u y ∂squareLebesgue)
      (ENNReal.ofReal r) torusMeasure =
    lpNorm (fun x ↦ u x - ∫ y, u y ∂squareLebesgue) (ENNReal.ofReal r) squareLebesgue at hn'
  change lpNorm (fun z ↦ u (squareReflection z) - ∫ w, u (squareReflection w) ∂torusMeasure)
      (ENNReal.ofReal r) torusMeasure ≤ _ at h
  rw [hm, hn'] at h
  exact h.trans_eq (by unfold squareSobolevConstant; ring)

/-- Exact double-rectangle assertion of source Lemma 3.1, on its closure. -/
theorem rectangle_lipschitz_sobolev {r : ℝ} (hr : 2 ≤ r) {u : PlanarSpace → ℝ} {K : ℝ≥0}
    (hu : LipschitzOnWith K u closedDoubleRectangle) :
    lpNorm (fun x ↦ u x - ∫ y, u y ∂rectangleLebesgue) (ENNReal.ofReal r) rectangleLebesgue ≤
      rectangleSobolevConstant r * lpNorm (rectangleOrdinaryGradient u) 2 rectangleLebesgue := by
  have h := square_lipschitz_sobolev hr (lipschitzOnWith_rectanglePullback hu)
  have hm := integral_rectangleStretch ((memLp_rectangle hu 1).integrable le_rfl)
  have hn := eLpNorm_comp_measurePreserving
    (g := fun x ↦ u x - ∫ y, u y ∂rectangleLebesgue)
    ((aestronglyMeasurable_rectangle hu).sub aestronglyMeasurable_const)
    measurePreserving_rectangleStretch (p := ENNReal.ofReal r)
  have hn' := congrArg ENNReal.toReal hn
  change lpNorm (fun z ↦ u (rectangleStretch z) - ∫ y, u y ∂rectangleLebesgue)
      (ENNReal.ofReal r) squareLebesgue =
    lpNorm (fun x ↦ u x - ∫ y, u y ∂rectangleLebesgue) (ENNReal.ofReal r) rectangleLebesgue at hn'
  rw [hm, hn'] at h
  calc
    _ ≤ _ := h
    _ ≤ squareSobolevConstant r *
        (2 * lpNorm (rectangleOrdinaryGradient u) 2 rectangleLebesgue) :=
      mul_le_mul_of_nonneg_left (lpNorm_rectanglePullback_le hu) (squareSobolevConstant_nonneg r)
    _ = _ := by unfold squareSobolevConstant rectangleSobolevConstant; ring

end PeriodicAttractiveLogGas
