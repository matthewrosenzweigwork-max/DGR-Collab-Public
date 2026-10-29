import LeanResearch.PeriodicAttractiveLogGas.AmbientProduct
import LeanResearch.PeriodicAttractiveLogGas.ConditionalSourceCharts
import LeanResearch.PeriodicAttractiveLogGas.BoundaryEdgeSummation

/-! The source smooth observable class satisfies the concrete interfaces used
in the conditional calculations. The ordinary coordinate gradients are exactly
the blocks of the genuine smooth gradient, and their unscaled energy is the
energy of the existing ambient form. Source: Proposition 3.11, Proposition 3.12,
and the smooth-core passage in Proposition 2.6. -/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff BigOperators NNReal ENNReal

namespace PeriodicAttractiveLogGas

open MovingPoleNumerators MovingPoleDerivativeIdentification
open ConditionalSourceCharts OneCoordinateConditionals MeshCells GreenPointWeights
open LabelOccupations

theorem SmoothPair.configurationEuclideanLipschitz {N : ℕ} (f : SmoothPair N) :
    ConfigurationEuclideanLipschitzWith ‖f.gradient‖₊ f.value :=
  configurationEuclideanLipschitzWith_iff_lift.mpr f.lipschitz_configurationLift

theorem configurationQuotient_sourceVariation {N : ℕ} (i : Fin N)
    (y : Gradient N) (z : PlanarSpace) :
    configurationQuotient N (sourceVariation i y z) =
      Function.update (configurationQuotient N y) i (torusQuotient z) := by
  classical
  funext k j
  change ((sourceVariation i y z (k, j) : ℝ) : UnitAddCircle) = _
  rw [sourceVariation_apply]
  by_cases h : k = i
  · subst k
    simp only [ite_true, Function.update_self]
    rfl
  · simp only [ite_eq_right h, Function.update_of_ne h]
    rfl

/-- True ordinary derivative of the coordinate section, at every lift. -/
theorem SmoothPair.hasFDerivAt_coordinateSection {N : ℕ} (f : SmoothPair N)
    (i : Fin N) (y : Gradient N) :
    HasFDerivAt (fun z : PlanarSpace ↦
      f.value (Function.update (configurationQuotient N y) i (torusQuotient z)))
      (InnerProductSpace.toDual ℝ PlanarSpace
        (sourceProjection i (f.gradient (configurationQuotient N y))))
      (sourceProjection i y) := by
  have hd := hasFDerivAt_sourceBlock (f.differential y) i
  simpa only [configurationQuotient_sourceVariation] using hd

/-- The total ordinary-gradient representative agrees everywhere for smooth
observables. No almost-everywhere or differentiability hypothesis is hidden. -/
theorem SmoothPair.coordinateOrdinaryGradient_eq {N : ℕ} (f : SmoothPair N)
    (i : Fin N) (X : Configuration N) :
    coordinateOrdinaryGradient f.value i X = sourceProjection i (f.gradient X) := by
  obtain ⟨y, rfl⟩ := configurationQuotient_surjective N X
  have hd := f.hasFDerivAt_coordinateSection i y
  change torusOrdinaryGradient
    (fun z ↦ f.value (Function.update (configurationQuotient N y) i z))
    (torusQuotient (sourceProjection i y)) = _
  rw [torusOrdinaryGradient_lift, rectangleOrdinaryGradient, hd.fderiv]
  exact (InnerProductSpace.toDual ℝ PlanarSpace).symm_apply_apply _

theorem SmoothPair.sum_coordinateOrdinaryGradient_sq {N : ℕ} (f : SmoothPair N)
    (X : Configuration N) :
    (∑ i : Fin N, ‖coordinateOrdinaryGradient f.value i X‖ ^ 2) =
      ‖f.gradient X‖ ^ 2 := by
  rw [gradient_norm_sq]
  apply Finset.sum_congr rfl
  intro i hi
  rw [f.coordinateOrdinaryGradient_eq, EuclideanSpace.real_norm_sq_eq]
  rfl

theorem SmoothPair.totalEnergyDensity_eq {N : ℕ} (f : SmoothPair N)
    (X : Configuration N) :
    BoundaryEdgeSummation.totalEnergyDensity f.value X = ‖f.gradient X‖ ^ 2 :=
  f.sum_coordinateOrdinaryGradient_sq X

theorem SmoothPair.ambientEnergy_eq_coordinate_integral {N : ℕ} (f : SmoothPair N)
    (μ : Measure (Configuration N)) [IsFiniteMeasure μ] :
    ambientEnergy (f.toAmbient μ) =
      ∫ X, ∑ i : Fin N, ‖coordinateOrdinaryGradient f.value i X‖ ^ 2 ∂μ := by
  change graphEnergy (ContinuousMap.toLp 2 μ ℝ f.value,
    ContinuousMap.toLp 2 μ ℝ f.gradient) = _
  rw [graphEnergy_toLp]
  apply integral_congr_ae
  exact Eventually.of_forall fun X ↦ by
    change (∑ i : Fin N, ∑ k : Fin 2, (f.gradient X (i, k)) ^ 2) =
      ∑ i : Fin N, ‖coordinateOrdinaryGradient f.value i X‖ ^ 2
    rw [f.sum_coordinateOrdinaryGradient_sq, gradient_norm_sq]

namespace SmoothObservableInterfaces

variable {n : ℕ}

/-- Actual insertion on the Euclidean cover. The inserted planar variable
and the retained physical sources are assembled without any scaling. -/
def insertedCover (i : Fin (n + 1))
    (p : SourceSpace (otherParticles i) × PlanarSpace) : Gradient (n + 1) :=
  (EuclideanSpace.equiv (Fin (n + 1) × Fin 2) ℝ).symm
    (fun q ↦ if h : q.1 = i then p.2 q.2 else
      p.1 (⟨q.1, (mem_otherParticles i q.1).mpr h⟩, q.2))

theorem insertedCover_contDiff (i : Fin (n + 1)) :
    ContDiff ℝ ∞ (insertedCover i) := by
  apply (EuclideanSpace.equiv (Fin (n + 1) × Fin 2) ℝ).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro q
  by_cases h : q.1 = i
  · simp only [dite_eq_left h]
    exact (EuclideanSpace.proj (𝕜 := ℝ) q.2).contDiff.comp contDiff_snd
  · simp only [dite_eq_right h]
    exact (EuclideanSpace.proj (𝕜 := ℝ)
      ((⟨q.1, (mem_otherParticles i q.1).mpr h⟩ : otherParticles i), q.2)).contDiff.comp
      contDiff_fst

theorem configurationQuotient_insertedCover (i : Fin (n + 1))
    (p : SourceSpace (otherParticles i) × PlanarSpace) :
    configurationQuotient (n + 1) (insertedCover i p) =
      insertedConfiguration i p.1 (torusQuotient p.2) := by
  classical
  funext k j
  by_cases h : k = i
  · subst k
    rw [insertedConfiguration_self]
    change ((if h : i = i then p.2 j else
      p.1 (⟨i, (mem_otherParticles i i).mpr h⟩, j) : ℝ) : UnitAddCircle) = _
    rw [dite_eq_left rfl]
    rfl
  · let k' : otherParticles i := ⟨k, (mem_otherParticles i k).mpr h⟩
    have he := congrFun (insertedConfiguration_retained i p.1 (torusQuotient p.2) k') j
    change configurationQuotient (n + 1) (insertedCover i p) k j = _
    rw [he]
    change ((if h : k = i then p.2 j else
      p.1 (⟨k, (mem_otherParticles i k).mpr h⟩, j) : ℝ) : UnitAddCircle) = _
    rw [dite_eq_right h]
    rfl

/-- Pulling any ambient smooth observable to any cell/edge source chart
produces an actual globally smooth function. No separation from collisions,
cell faces, or the periodic seam is required. -/
theorem contDiff_configurationFactor (i : Fin (n + 1)) (f : SmoothPair (n + 1))
    (J : ℕ) (a : MeshIndex J) :
    ContDiff ℝ ∞ (torusFactor (configurationFactor i f.value) J a) := by
  have hm : ContDiff ℝ ∞ (fun p : SourceSpace (otherParticles i) × PlanarSpace ↦
      (p.1, meshAffine J a p.2)) :=
    contDiff_fst.prodMk ((contDiff_const.add contDiff_snd).const_smul (J : ℝ)⁻¹)
  have h := f.smooth.comp ((insertedCover_contDiff i).comp hm)
  change ContDiff ℝ ∞ (fun p : SourceSpace (otherParticles i) × PlanarSpace ↦
    f.value (insertedConfiguration i p.1 (torusQuotient (meshAffine J a p.2))))
  simpa only [Function.comp_def, configurationQuotient_insertedCover] using! h

theorem smoothOnChart_configurationFactor (i : Fin (n + 1)) (f : SmoothPair (n + 1))
    (J : ℕ) (a : MeshIndex J) (S : Set (SourceSpace (otherParticles i)))
    (B : Set PlanarSpace) :
    SmoothOnChart S B (torusFactor (configurationFactor i f.value) J a) :=
  smoothOnChart_of_contDiff ((contDiff_configurationFactor i f J a).of_le (by simp))

end SmoothObservableInterfaces
end PeriodicAttractiveLogGas
