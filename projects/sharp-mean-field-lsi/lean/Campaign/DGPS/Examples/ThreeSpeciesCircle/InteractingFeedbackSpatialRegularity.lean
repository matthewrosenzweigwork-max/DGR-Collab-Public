import DGPS.Examples.ThreeSpeciesCircle.InteractingHolderFeedback

/-! Genuine spatial regularity of the actual fixed feedback basis. A Holder
norm bound does not imply a derivative bound; these derivative bounds follow
instead from the explicit smooth native basis and its true periodicity. -/

noncomputable section
open Filter Topology Function
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

private def fs (h : ℝ) : Fin 3 → Torus 1 → ℝ := ![featureC h, featureS h, featureB h]

private theorem fs_smooth (h : ℝ) (i : Fin 3) : IsSmoothPeriodic (fs h i) := by
  fin_cases i
  · exact isSmooth_featureC h
  · exact isSmooth_featureS h
  · exact isSmooth_featureB h

private theorem generator_smooth (h : ℝ) {f : Torus 1 → ℝ} (hf : IsSmoothPeriodic f) :
    IsSmoothPeriodic (elementaryFeatureGenerator h f) := by
  have hd := hf.isSmoothPeriodic_coordPartial 0
  exact (hd.isSmoothPeriodic_coordPartial 0).neg.sub
    (((isSmoothPeriodic_ellT h).isSmoothPeriodic_coordPartial 0).mul hd)

private theorem angular_point (t : ℝ) :
    DGPS.Circle.AngularNormalization.angEquiv.symm
      (t : DGPS.Circle.AngularNormalization.AngCircle) = pt (t / (2 * Real.pi)) := by
  rw [MeasurableEquiv.symm_apply_eq, angEquiv_apply]
  change (t : DGPS.Circle.AngularNormalization.AngCircle) =
    DGPS.Circle.AngularNormalization.angRescale ((t / (2 * Real.pi) : ℝ) : UnitAddCircle)
  rw [DGPS.Circle.AngularNormalization.angRescale_mk]
  congr 1
  field_simp

private theorem smooth_native {F : PeriodicHolder_STR02968} {f : Torus 1 → ℝ}
    (hf : IsSmoothPeriodic f)
    (he : ∀ t, F.val t = f (DGPS.Circle.AngularNormalization.angEquiv.symm
      (t : DGPS.Circle.AngularNormalization.AngCircle))) : ContDiff ℝ ∞ F.val := by
  have heq : F.val = fun t : ℝ => f (pt (t / (2 * Real.pi))) := by
    funext t
    rw [he, angular_point]
  rw [heq]
  exact (circ_smooth_pt hf).comp (contDiff_id.div_const (2 * Real.pi))

/-- The three actual spatial bases are smooth, retaining all physical scaling
and true generator harmonics. This uses no feature eigenfunction replacement. -/
theorem interactingHolderBasis_smooth {h : ℝ} (hh : 0 < h) (i : Fin 3) :
    ContDiff ℝ ∞ (interactingHolderFeature h i).val ∧
      ContDiff ℝ ∞ (interactingHolderDerivative h i).val ∧
        ContDiff ℝ ∞ (interactingHolderGenerator h i).val := by
  refine ⟨smooth_native (fs_smooth h i) (fun t => (interactingHolderFeature_native hh i t).1),
    smooth_native ((fs_smooth h i).isSmoothPeriodic_coordPartial 0)
      (fun t => (interactingHolderFeature_native hh i t).2.1),
    smooth_native (generator_smooth h (fs_smooth h i))
      (fun t => (interactingHolderFeature_native hh i t).2.2)⟩

private theorem derivative_bound (F : Fin 3 → PeriodicHolder_STR02968)
    (hF : ∀ i, ContDiff ℝ ∞ (F i).val) :
    ∃ B : ℝ, 0 < B ∧ ∀ i t, |deriv (F i).val t| ≤ B := by
  have hex (i : Fin 3) : ∃ M : ℝ, ∀ t, |deriv (F i).val t| ≤ M :=
    bdd_of_periodic_STR02968 (periodic_deriv_STR02901 (F i).isPerHolder.1)
      ((contDiff_infty_iff_deriv.mp (hF i)).2).continuous
  choose M hM using hex
  have hM0 (i : Fin 3) : 0 ≤ M i := (abs_nonneg _).trans (hM i 0)
  have hsum : 0 ≤ ∑ i : Fin 3, M i := Finset.sum_nonneg (fun i _ => hM0 i)
  refine ⟨1 + ∑ i : Fin 3, M i, by linarith, fun i t => ?_⟩
  have hi : M i ≤ ∑ j : Fin 3, M j :=
    Finset.single_le_sum (fun j _ => hM0 j) (Finset.mem_univ i)
  linarith [hM i t]

/-- First angular derivatives have one genuine bound chosen before every law,
rate and coupling. Such control is not inferred from the C0 Holder norm. -/
theorem interactingHolderBasis_derivative_bounds {h : ℝ} (hh : 0 < h) :
    ∃ B : ℝ, 0 < B ∧ ∀ i : Fin 3, ∀ t : ℝ,
      |deriv (interactingHolderFeature h i).val t| ≤ B ∧
        |deriv (interactingHolderDerivative h i).val t| ≤ B ∧
          |deriv (interactingHolderGenerator h i).val t| ≤ B := by
  obtain ⟨BF, hBF, hf⟩ := derivative_bound (interactingHolderFeature h)
    (fun i => (interactingHolderBasis_smooth hh i).1)
  obtain ⟨BD, hBD, hd⟩ := derivative_bound (interactingHolderDerivative h)
    (fun i => (interactingHolderBasis_smooth hh i).2.1)
  obtain ⟨BA, hBA, ha⟩ := derivative_bound (interactingHolderGenerator h)
    (fun i => (interactingHolderBasis_smooth hh i).2.2)
  refine ⟨BF + BD + BA, by positivity, fun i t =>
    ⟨by linarith [hf i t], by linarith [hd i t], by linarith [ha i t]⟩⟩

end DGPS.Examples.ThreeSpeciesCircle
