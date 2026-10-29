import LeanResearch.PeriodicAttractiveLogGas.GreenMollifierGradient
import LeanResearch.PeriodicAttractiveLogGas.RectangleDilation

/-! Ordinary local torus gradients for functions unrestricted off a closed
patch. The section is used only to define a measurable representative. Fiber
invariance identifies that representative at every Euclidean lift, without
assuming continuity or differentiability of the original function.

SOURCE_ONLY candidate: central elaboration and axiom inspection are pending.
-/

noncomputable section
open MeasureTheory Set Filter InnerProductSpace
open scoped Topology ENNReal NNReal

namespace PeriodicAttractiveLogGas

def torusOrdinaryGradient (f : Torus → ℝ) (z : Torus) : PlanarSpace :=
  rectangleOrdinaryGradient (fun x ↦ f (torusQuotient x)) (centeredLift z)

theorem torusOrdinaryGradient_lift (f : Torus → ℝ) (x : PlanarSpace) :
    torusOrdinaryGradient f (torusQuotient x) =
      rectangleOrdinaryGradient (fun y ↦ f (torusQuotient y)) x := by
  unfold torusOrdinaryGradient rectangleOrdinaryGradient
  rw [fderiv_torusLift_eq_of_torusQuotient_eq f (torusQuotient_centeredLift _)]

theorem measurable_torusOrdinaryGradient (f : Torus → ℝ) :
    Measurable (torusOrdinaryGradient f) :=
  (measurable_rectangleOrdinaryGradient (fun x ↦ f (torusQuotient x))).comp
    measurable_centeredLift

theorem norm_torusOrdinaryGradient_lift (f : Torus → ℝ) (x : PlanarSpace) :
    ‖torusOrdinaryGradient f (torusQuotient x)‖ =
      ‖fderiv ℝ (fun y ↦ f (torusQuotient y)) x‖ := by
  rw [torusOrdinaryGradient_lift, norm_rectangleOrdinaryGradient]

theorem differentiableAt_torusLift_add_frequencyVector (f : Torus → ℝ)
    (x : PlanarSpace) (k : Frequency) :
    DifferentiableAt ℝ (fun y ↦ f (torusQuotient y)) (x + frequencyVector k) ↔
      DifferentiableAt ℝ (fun y ↦ f (torusQuotient y)) x := by
  simpa only [torusQuotient_add_frequencyVector] using
    (differentiableAt_comp_add_right (𝕜 := ℝ)
      (f := fun y : PlanarSpace ↦ f (torusQuotient y))
      (x := x) (frequencyVector k)).symm

theorem differentiableAt_torusLift_iff_of_quotient_eq (f : Torus → ℝ)
    {x y : PlanarSpace} (hxy : torusQuotient x = torusQuotient y) :
    DifferentiableAt ℝ (fun w ↦ f (torusQuotient w)) x ↔
      DifferentiableAt ℝ (fun w ↦ f (torusQuotient w)) y := by
  obtain ⟨k, rfl⟩ := exists_frequencyVector_of_torusQuotient_eq hxy
  exact (differentiableAt_torusLift_add_frequencyVector f x k).symm

/-- The metric in this condition is the actual Euclidean quotient metric.
There is no condition on f outside D. -/
def PhysicalLipschitzOn (L : ℝ≥0) (f : Torus → ℝ) (D : Set Torus) : Prop :=
  ∀ x ∈ D, ∀ y ∈ D, |f x - f y| ≤ (L : ℝ) * torusEuclideanDist x y

theorem PhysicalLipschitzOn.continuousOn {L : ℝ≥0} {f : Torus → ℝ} {D : Set Torus}
    (hf : PhysicalLipschitzOn L f D) : ContinuousOn f D := by
  let F : PiLp 2 (fun _ : Fin 2 ↦ UnitAddCircle) → ℝ := fun z ↦ f (WithLp.ofLp z)
  have hF : LipschitzOnWith L F (WithLp.ofLp ⁻¹' D) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [F, Real.dist_eq, torusEuclideanDist_eq_piLp_dist,
      WithLp.toLp_ofLp] using hf (WithLp.ofLp x) hx (WithLp.ofLp y) hy
  simpa only [F, Function.comp_def, WithLp.ofLp_toLp] using!
    hF.continuousOn.comp (PiLp.continuous_toLp 2 (fun _ : Fin 2 ↦ UnitAddCircle)).continuousOn
      (fun z hz ↦ hz)

theorem PhysicalLipschitzOn.lift {L : ℝ≥0} {f : Torus → ℝ} {D : Set Torus}
    (hf : PhysicalLipschitzOn L f D) {S : Set PlanarSpace}
    (hS : MapsTo torusQuotient S D) :
    LipschitzOnWith L (fun x ↦ f (torusQuotient x)) S := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  rw [Real.dist_eq]
  exact (hf _ (hS hx) _ (hS hy)).trans
    (mul_le_mul_of_nonneg_left (torusEuclideanDist_quotient_le x y) L.coe_nonneg)

theorem PhysicalLipschitzOn.aestronglyMeasurable {L : ℝ≥0} {f : Torus → ℝ}
    {D : Set Torus} (hf : PhysicalLipschitzOn L f D) (hD : MeasurableSet D)
    {μ : Measure Torus} (hμ : ∀ᵐ z ∂μ, z ∈ D) : AEStronglyMeasurable f μ := by
  have h := hf.continuousOn.aestronglyMeasurable (μ := μ) hD
  simpa only [Measure.restrict_eq_self_of_ae_mem hμ] using h

theorem PhysicalLipschitzOn.memLp {L : ℝ≥0} {f : Torus → ℝ} {D : Set Torus}
    (hf : PhysicalLipschitzOn L f D) (hD : IsCompact D)
    {μ : Measure Torus} [IsFiniteMeasure μ] (hμ : ∀ᵐ z ∂μ, z ∈ D)
    (r : ℝ≥0∞) : MemLp f r μ := by
  obtain ⟨C, hC⟩ := hD.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound (hf.aestronglyMeasurable hD.isClosed.measurableSet hμ) C
    (hμ.mono fun z hz ↦ hC z hz)

theorem PhysicalLipschitzOn.integrable_continuous_comp {L : ℝ≥0}
    {f : Torus → ℝ} {D : Set Torus} (hf : PhysicalLipschitzOn L f D) (hD : IsCompact D)
    {μ : Measure Torus} [IsFiniteMeasure μ] (hμ : ∀ᵐ z ∂μ, z ∈ D)
    {Φ : ℝ → ℝ} (hΦ : Continuous Φ) : Integrable (fun z ↦ Φ (f z)) μ := by
  have hc : ContinuousOn (fun z ↦ Φ (f z)) D := hΦ.comp_continuousOn hf.continuousOn
  obtain ⟨C, hC⟩ := hD.exists_bound_of_continuousOn hc
  have hm : AEStronglyMeasurable (fun z ↦ Φ (f z)) μ := by
    have h := hc.aestronglyMeasurable (μ := μ) hD.isClosed.measurableSet
    simpa only [Measure.restrict_eq_self_of_ae_mem hμ] using h
  exact (MemLp.of_bound (p := 1) hm C (hμ.mono fun z hz ↦ hC z hz)).integrable le_rfl

/-- Affine precomposition of the total ordinary derivative. This identity
also holds at nondifferentiability points, by Mathlib's exact affine rules. -/
theorem fderiv_oriented_affine (f : PlanarSpace → ℝ)
    (O : PlanarSpace ≃ₗᵢ[ℝ] PlanarSpace) (a : PlanarSpace) (J : ℝ) (Z : PlanarSpace) :
    fderiv ℝ (fun W ↦ f (RectangleDilation.affine a J (O W))) Z =
      (J⁻¹ • fderiv ℝ f (RectangleDilation.affine a J (O Z))).comp
        O.toContinuousLinearEquiv.toContinuousLinearMap := by
  have ha (x : PlanarSpace) :
      fderiv ℝ (fun W ↦ f (RectangleDilation.affine a J W)) x =
        J⁻¹ • fderiv ℝ f (RectangleDilation.affine a J x) := by
    unfold RectangleDilation.affine
    rw [fderiv_comp_smul (f := fun W ↦ f (a + W)) J⁻¹, fderiv_comp_add_left]
  have he := O.toContinuousLinearEquiv.comp_right_fderiv
    (f := fun W ↦ f (RectangleDilation.affine a J W)) (x := Z)
  simpa only [Function.comp_def, ha] using! he

theorem norm_gradient_torus_oriented_affine (f : Torus → ℝ)
    (O : PlanarSpace ≃ₗᵢ[ℝ] PlanarSpace) (a : PlanarSpace)
    {J : ℝ} (hJ : 0 < J) (Z : PlanarSpace) :
    ‖rectangleOrdinaryGradient
      (fun W ↦ f (torusQuotient (RectangleDilation.affine a J (O W)))) Z‖ =
      J⁻¹ * ‖torusOrdinaryGradient f (torusQuotient (RectangleDilation.affine a J (O Z)))‖ := by
  rw [norm_rectangleOrdinaryGradient, fderiv_oriented_affine (fun x ↦ f (torusQuotient x)) O a J Z,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hJ), norm_torusOrdinaryGradient_lift]

theorem differentiableAt_of_oriented_affine_comp {f : PlanarSpace → ℝ}
    (O : PlanarSpace ≃ₗᵢ[ℝ] PlanarSpace) (a : PlanarSpace) {J : ℝ} (hJ : J ≠ 0)
    {Z : PlanarSpace}
    (hf : DifferentiableAt ℝ (fun W ↦ f (RectangleDilation.affine a J (O W))) Z) :
    DifferentiableAt ℝ f (RectangleDilation.affine a J (O Z)) := by
  let A := RectangleDilation.affine a J
  let B := fun x ↦ O.symm (RectangleDilation.inverseAffine a J x)
  have hB : Differentiable ℝ B := by
    intro x
    exact O.symm.toContinuousLinearEquiv.differentiableAt.comp x
      (((hasFDerivAt_id x).sub_const a).const_smul J).differentiableAt
  have hBA : B (A (O Z)) = Z := by
    simp [B, A, RectangleDilation.inverseAffine_affine a hJ]
  have hf' : DifferentiableAt ℝ (fun W ↦ f (A (O W))) (B (A (O Z))) := by
    simpa only [hBA, A] using hf
  have hcomp := hf'.comp (A (O Z)) (hB _)
  have he : (fun x ↦ f (A (O (B x)))) = f := by
    funext x
    simp [A, B, RectangleDilation.affine_inverseAffine a hJ]
  change DifferentiableAt ℝ (fun x ↦ f (A (O (B x)))) (A (O Z)) at hcomp
  rw [he] at hcomp
  exact hcomp

end PeriodicAttractiveLogGas
