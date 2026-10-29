import LeanResearch.PeriodicAttractiveLogGas.ConditionalVarianceAssembly
import LeanResearch.PeriodicAttractiveLogGas.SmoothObservableInterfaces

/-! Actual Proposition 3.12, including its ambient form-domain extension.

The complete label boundary energy uses the unconditioned Green Gibbs
weights. Both capped endpoints, all periodic orientations, and the original
particle count are retained. The smooth theorem is assembled from the
proved conditional variance bounds and actual four-edge summation. Fixed
label restrictions define continuous linear functionals on the original
Gibbs L2 space; genuine smooth form approximation then gives the full
ambient statement, without a symmetry or regularity assumption on f.

SOURCE_ONLY candidate. No Lean execution, transitive axiom inspection,
independent semantic review, or protected acceptance is claimed. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology RealInnerProductSpace

namespace PeriodicAttractiveLogGas.BoundaryComparison

open MeshCells MeshAdjacentCells LabelOccupations CellRestrictions
open ConditionalLawEstimates CollectiveGradientBounds CollectiveCovarianceBounds
open ConditionalVarianceAssembly BoundaryEdgeSummation DiscreteOccupationIdentities

/-- Exactly the source C_BT, independent of particle count, mesh, actual
coupling, labels, orientation, and observable. -/
def boundaryComparisonConstant (β₀ δ : ℝ) : ℝ :=
  4 * (finePoincareConstant β₀ + finePoincareConstant β₀ ^ 2 *
    crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant *
      (1 + averageConstant β₀ δ))

theorem boundaryComparisonConstant_nonneg (β₀ : ℝ) {δ : ℝ} (hδ : 0 ≤ δ) :
    0 ≤ boundaryComparisonConstant β₀ δ := by
  have hA := finePoincareConstant_nonneg β₀
  have hB := crossingConstantSquared_nonneg β₀ hδ GreenCovarianceBounds.hessianConstant
  have hC := averageConstant_nonneg β₀ hδ
  unfold boundaryComparisonConstant
  positivity

theorem retainedEnergy_eq_outsideEnergy {n : ℕ} (f : Configuration (n + 1) → ℝ)
    (i : Fin (n + 1)) (X : Configuration (n + 1)) :
    retainedEnergy f i X = outsideEnergy f i X := by
  rw [outsideEnergy_eq_sub]
  have h := Fin.sum_univ_succAbove (fun k ↦ ‖coordinateOrdinaryGradient f k X‖ ^ 2) i
  change totalEnergyDensity f X = coordinateEnergy f i X + retainedEnergy f i X at h
  linarith

theorem singleEdgeDensity_eq {n : ℕ} (β₀ δ : ℝ) (f : Configuration (n + 1) → ℝ)
    (i : Fin (n + 1)) (X : Configuration (n + 1)) :
    singleEdgeDensity (finePoincareConstant β₀)
      (finePoincareConstant β₀ ^ 2 * crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant)
      (averageConstant β₀ δ) f i X =
        finePoincareConstant β₀ * ‖coordinateOrdinaryGradient f i X‖ ^ 2 +
          (finePoincareConstant β₀ ^ 2 *
            crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant) / (n + 1 : ℕ) *
            meanEnergy β₀ δ f i X := by
  rw [singleEdgeDensity, meanEnergy, retainedEnergy_eq_outsideEnergy]
  rfl

section SmoothComparison

variable {n J : ℕ} {β β₀ δ : ℝ}

/-- The positive periodic orientation of an actual capped graph edge.
Both completed labels are the actual graph vertices, and the local
smooth gate is discharged by the genuine smooth observable interface. -/
theorem positive_label_edge_bound
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (f : SmoothPair (n + 1)) (η ζ : LabelState J (n + 1) δ)
    (i : Fin (n + 1)) (r : Fin 2) (he : CoordinateStep (mesh_pos hmesh) i η ζ)
    (hr : ζ.val i = nextCell J (mesh_pos hmesh) (η.val i) r) :
    labelTerm (mesh_pos hmesh) β (labelMean (mesh_pos hmesh) β f.value) η ζ ≤
      (1 / (J : ℝ) ^ 2) * (labelWeight (mesh_pos hmesh) β η + labelWeight (mesh_pos hmesh) β ζ) *
        (∫ X, singleEdgeDensity (finePoincareConstant β₀)
          (finePoincareConstant β₀ ^ 2 *
            crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant)
          (averageConstant β₀ δ) f.value i X
          ∂twoCellGibbsMeasure (mesh_pos hmesh) η.val i (η.val i) (ζ.val i) β) := by
  classical
  let hJ := mesh_pos hmesh
  let P := twoCellGibbsMeasure hJ η.val i (η.val i) (ζ.val i) β
  let p := (twoCellMixingWeight hJ η.val i (η.val i) (ζ.val i) β).toReal
  let CA := finePoincareConstant β₀
  let CΛ := crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant
  let Cg := averageConstant β₀ δ
  have hu : Function.update η.val i (η.val i) = η.val := by funext k; simp
  have hadm : AdjacentAdmissible hJ δ η.val i (η.val i) r := by
    constructor
    · change OccupationCap δ (Function.update η.val i (η.val i))
      rw [hu]
      exact η.property
    · change OccupationCap δ (Function.update η.val i (nextCell J hJ (η.val i) r))
      rw [← hr, he.2]
      exact ζ.property
  have hs := twoCell_single_edge_estimate hN hβ hβ₀ hsub hδ₀ hδ hmesh η.val i (η.val i) r hadm
    f.value f.configurationEuclideanLipschitz
    (SmoothObservableInterfaces.smoothOnChart_configurationFactor i f J (η.val i) _ _)
  dsimp only at hs
  rw [← hr, hu, he.2] at hs
  let : IsProbabilityMeasure P := isProbabilityMeasure_twoCellGibbsMeasure hJ hN η.val i
    (he.1.ne (mesh_two_le hmesh)) hβ (hβ₀.trans_lt hsub)
  have hei := integrable_coordinate_energy f.configurationEuclideanLipschitz P i
  have hemi := integrable_meanEnergy f.configurationEuclideanLipschitz β₀ δ P i
  have hJ0 : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hN0 : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hint : (CA / (J : ℝ) ^ 2) * (∫ X, ‖coordinateOrdinaryGradient f.value i X‖ ^ 2 ∂P) +
      (CA ^ 2 * CΛ / ((n + 1 : ℕ) * (J : ℝ) ^ 2)) * (∫ X, meanEnergy β₀ δ f.value i X ∂P) =
        (1 / (J : ℝ) ^ 2) * (∫ X, singleEdgeDensity CA (CA ^ 2 * CΛ) Cg f.value i X ∂P) := by
    simp_rw [show ∀ X, singleEdgeDensity CA (CA ^ 2 * CΛ) Cg f.value i X =
      CA * ‖coordinateOrdinaryGradient f.value i X‖ ^ 2 +
        (CA ^ 2 * CΛ / (n + 1 : ℕ)) * meanEnergy β₀ δ f.value i X from
      singleEdgeDensity_eq β₀ δ f.value i]
    rw [integral_add (hei.const_mul _) (hemi.const_mul _), integral_const_mul, integral_const_mul]
    field_simp [hJ0, hN0]
  have hW : 0 ≤ labelWeight hJ β η + labelWeight hJ β ζ :=
    add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  rw [labelTerm_eq_mass_mixing hJ hN hβ (hβ₀.trans_lt hsub) _ η ζ i he]
  calc
    _ = (labelWeight hJ β η + labelWeight hJ β ζ) *
        (p * (1 - p) * (labelMean hJ β f.value η - labelMean hJ β f.value ζ) ^ 2) := by ring
    _ ≤ (labelWeight hJ β η + labelWeight hJ β ζ) *
        ((CA / (J : ℝ) ^ 2) * (∫ X, ‖coordinateOrdinaryGradient f.value i X‖ ^ 2 ∂P) +
          (CA ^ 2 * CΛ / ((n + 1 : ℕ) * (J : ℝ) ^ 2)) * ∫ X, meanEnergy β₀ δ f.value i X ∂P) :=
      mul_le_mul_of_nonneg_left hs hW
    _ = _ := by rw [hint]; ring

/-- Reversing a graph edge preserves the actual two-cell Gibbs law.
The equality is proved through its actual union of label events. -/
theorem twoCellGibbsMeasure_coordinateStep_symm {N J : ℕ} {t : ℝ} (hJ : 0 < J)
    (β : ℝ) (η ζ : LabelState J N t) (i : Fin N) (he : CoordinateStep hJ i η ζ) :
    twoCellGibbsMeasure hJ ζ.val i (ζ.val i) (η.val i) β =
      twoCellGibbsMeasure hJ η.val i (η.val i) (ζ.val i) β := by
  rw [twoCellGibbsMeasure, twoCellGibbsMeasure,
    ← edgeEvent_eq_twoCellFiber he.symm, ← edgeEvent_eq_twoCellFiber he, edgeEvent_symm hJ ζ η]

/-- Every unoriented actual graph edge receives the same derived bound. -/
theorem label_edge_bound
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (f : SmoothPair (n + 1)) (η ζ : LabelState J (n + 1) δ)
    (i : Fin (n + 1)) (he : CoordinateStep (mesh_pos hmesh) i η ζ) :
    labelTerm (mesh_pos hmesh) β (labelMean (mesh_pos hmesh) β f.value) η ζ ≤
      (1 / (J : ℝ) ^ 2) * (labelWeight (mesh_pos hmesh) β η + labelWeight (mesh_pos hmesh) β ζ) *
        (∫ X, singleEdgeDensity (finePoincareConstant β₀)
          (finePoincareConstant β₀ ^ 2 *
            crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant)
          (averageConstant β₀ δ) f.value i X
          ∂twoCellGibbsMeasure (mesh_pos hmesh) η.val i (η.val i) (ζ.val i) β) := by
  obtain ⟨r, hr | hr⟩ := he.1
  · exact positive_label_edge_bound hN hβ hβ₀ hsub hδ₀ hδ hmesh f η ζ i r he hr
  · have h := positive_label_edge_bound hN hβ hβ₀ hsub hδ₀ hδ hmesh f ζ η i r he.symm hr
    rw [labelTerm_symm (mesh_pos hmesh) β _ ζ η,
      twoCellGibbsMeasure_coordinateStep_symm (mesh_pos hmesh) β η ζ i he,
      add_comm (labelWeight (mesh_pos hmesh) β ζ) (labelWeight (mesh_pos hmesh) β η)] at h
    exact h

theorem smooth_boundary_comparison_succ
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (f : SmoothPair (n + 1)) :
    labelEnergy (t := δ) (mesh_pos hmesh) β (labelMean (mesh_pos hmesh) β f.value) ≤
      (boundaryComparisonConstant β₀ δ / (J : ℝ) ^ 2) *
        ambientEnergy (f.toAmbient (gibbsMeasure greenRealRepresentative (n + 1) β)) := by
  have h := source_boundary_energy_of_single_edge hN hβ hβ₀ hsub hmesh
    (finePoincareConstant_nonneg β₀)
    (mul_nonneg (sq_nonneg (finePoincareConstant β₀))
      (crossingConstantSquared_nonneg β₀ hδ₀.le GreenCovarianceBounds.hessianConstant))
    (averageConstant_nonneg β₀ hδ₀.le) f.configurationEuclideanLipschitz
    (label_edge_bound hN hβ hβ₀ hsub hδ₀ hδ hmesh f)
  rw [f.ambientEnergy_eq_coordinate_integral]
  exact h

end SmoothComparison

/-- Complete smooth Proposition 3.12, with arbitrary particle number N
in the source regime and no symmetry or auxiliary regularity gates. -/
theorem smooth_boundary_comparison {N J : ℕ} {β β₀ δ : ℝ}
    (hN : 2 ≤ N) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (f : SmoothPair N) :
    labelEnergy (t := δ) (mesh_pos hmesh) β (labelMean (mesh_pos hmesh) β f.value) ≤
      (boundaryComparisonConstant β₀ δ / (J : ℝ) ^ 2) *
        ambientEnergy (f.toAmbient (gibbsMeasure greenRealRepresentative N β)) := by
  cases N with
  | zero => omega
  | succ n => exact smooth_boundary_comparison_succ hN hβ hβ₀ hsub hδ₀ hδ hmesh f

section FixedLabelContinuity

variable {N J : ℕ} {t : ℝ}

/-- A fixed actual label mean is a continuous linear functional on the
original joint Gibbs L2 space. The indicator and its mass are fixed before
the observable varies; no smaller-particle marginal is introduced. -/
def labelMeanFunctional (hJ : 0 < J) (β : ℝ) (η : LabelVector J N) :
    Lp ℝ 2 (gibbsMeasure greenRealRepresentative N β) →L[ℝ] ℝ :=
  ((labelProbability hJ η β)⁻¹).toReal •
    innerSL ℝ (indicatorConstLp 2 (measurableSet_labelFiber hJ η)
      (measure_ne_top (gibbsMeasure greenRealRepresentative N β) (labelFiber hJ η)) (1 : ℝ))

theorem labelGibbsMeasure_absolutelyContinuous (hJ : 0 < J) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) (η : LabelVector J N) :
    labelGibbsMeasure hJ η β ≪ gibbsMeasure greenRealRepresentative N β := by
  rw [labelGibbsMeasure_eq_cond hJ hN η hβ hsub]
  exact Measure.absolutelyContinuous_restrict.smul_left _

/-- Every actual restricted mean is integrable for an ambient L2 value.
Positivity of the actual label mass discharges the inverse-scalar gate. -/
theorem integrable_labelMeanL2 (hJ : 0 < J) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) (η : LabelVector J N)
    (u : Lp ℝ 2 (gibbsMeasure greenRealRepresentative N β)) :
    Integrable u (labelGibbsMeasure hJ η β) := by
  have hi : Integrable u (gibbsMeasure greenRealRepresentative N β) :=
    (Lp.memLp u).integrable (by norm_num)
  rw [labelGibbsMeasure_eq_cond hJ hN η hβ hsub]
  exact hi.integrableOn.smul_measure
    (ENNReal.inv_ne_top.mpr (labelProbability_ne_zero hJ hN η hβ hsub))

/-- The functional is literally integration against the existing
normalized label Gibbs restriction, not a newly chosen conditional mean. -/
theorem labelMeanFunctional_apply (hJ : 0 < J) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) (η : LabelVector J N)
    (u : Lp ℝ 2 (gibbsMeasure greenRealRepresentative N β)) :
    labelMeanFunctional hJ β η u = ∫ X, u X ∂labelGibbsMeasure hJ η β := by
  rw [labelGibbsMeasure_eq_cond hJ hN η hβ hsub, ProbabilityTheory.cond, integral_smul_measure]
  change ((labelProbability hJ η β)⁻¹).toReal *
    ⟪indicatorConstLp 2 (measurableSet_labelFiber hJ η)
      (measure_ne_top (gibbsMeasure greenRealRepresentative N β) (labelFiber hJ η)) (1 : ℝ), u⟫ = _
  rw [L2.inner_indicatorConstLp_one]
  rfl

theorem continuous_labelMeanL2 (hJ : 0 < J) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) (η : LabelState J N t) :
    Continuous (fun u : Lp ℝ 2 (gibbsMeasure greenRealRepresentative N β) ↦
      labelMean hJ β u η) := by
  have he : (fun u : Lp ℝ 2 (gibbsMeasure greenRealRepresentative N β) ↦ labelMean hJ β u η) =
      (fun u ↦ labelMeanFunctional hJ β η.val u) := by
    funext u
    exact (labelMeanFunctional_apply hJ hN hβ hsub η.val u).symm
  rw [he]
  exact (labelMeanFunctional hJ β η.val).continuous

/-- All label means converge together on this fixed finite graph. This
is continuity of the actual conditional integrals in the original L2
norm, proved above from the fixed measurable restrictions. -/
theorem continuous_labelEnergyL2 (hJ : 0 < J) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    Continuous (fun u : Lp ℝ 2 (gibbsMeasure greenRealRepresentative N β) ↦
      labelEnergy (t := t) hJ β (labelMean hJ β u)) := by
  classical
  unfold labelEnergy labelTerm
  apply continuous_finsetSum
  intro η _
  apply continuous_finsetSum
  intro ζ _
  by_cases he : labelRank η < labelRank ζ
  · simp only [ite_eq_left he]
    exact continuous_const.mul
      (((continuous_labelMeanL2 hJ hN hβ hsub ζ).sub
        (continuous_labelMeanL2 hJ hN hβ hsub η)).pow 2)
  · simp only [ite_eq_right he]
    exact continuous_const

/-- The smooth L2 representative has the same actual label means, because
each label law is absolutely continuous with respect to the original law. -/
theorem labelMean_toLp (hJ : 0 < J) (hN : 2 ≤ N)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) (f : C(Configuration N, ℝ)) :
    labelMean (t := t) hJ β (ContinuousMap.toLp 2 (gibbsMeasure greenRealRepresentative N β) ℝ f) =
      labelMean hJ β f := by
  funext η
  apply integral_congr_ae
  exact (labelGibbsMeasure_absolutelyContinuous hJ hN hβ hsub η.val).ae_le
    (ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (gibbsMeasure greenRealRepresentative N β) f)

end FixedLabelContinuity

/-- Complete Proposition 3.12 on the actual full ambient closed form
domain. Genuine smooth form approximation gives strong scalar and vector
L2 convergence. Fixed finite label restrictions give convergence of the
actual boundary energy, while the ambient energy converges in form norm.
There is no approximation, convergence, regularity, or symmetry premise. -/
theorem green_ambient_boundary_comparison {N J : ℕ} {β β₀ δ : ℝ}
    (hN : 2 ≤ N) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 < δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (f : GreenAmbientFormDomain N β) :
    labelEnergy (t := δ) (mesh_pos hmesh) β (labelMean (mesh_pos hmesh) β (ambientValue f)) ≤
      (boundaryComparisonConstant β₀ δ / (J : ℝ) ^ 2) * ambientEnergy f := by
  let μ := gibbsMeasure greenRealRepresentative N β
  let hJ := mesh_pos hmesh
  let C := boundaryComparisonConstant β₀ δ / (J : ℝ) ^ 2
  obtain ⟨s, hs⟩ := exists_smooth_formNorm_approx f
  have hp : Tendsto (fun k ↦ (ContinuousMap.toLp 2 μ ℝ (s k).value,
      ContinuousMap.toLp 2 μ ℝ (s k).gradient)) atTop (𝓝 f.1) :=
    tendsto_iff_graphFormNorm_sub_tendsto_zero.mpr hs
  have hv : Tendsto (fun k ↦ ContinuousMap.toLp 2 μ ℝ (s k).value)
      atTop (𝓝 (ambientValue f)) := (continuous_fst.tendsto f.1).comp hp
  have hg : Tendsto (fun k ↦ ContinuousMap.toLp 2 μ ℝ (s k).gradient)
      atTop (𝓝 (ambientGradient f)) := (continuous_snd.tendsto f.1).comp hp
  have hleft : Tendsto (fun k ↦ labelEnergy (t := δ) hJ β
      (labelMean hJ β (ContinuousMap.toLp 2 μ ℝ (s k).value)))
      atTop (𝓝 (labelEnergy (t := δ) hJ β (labelMean hJ β (ambientValue f)))) :=
    ((continuous_labelEnergyL2 (t := δ) hJ hN hβ (hβ₀.trans_lt hsub)).tendsto (ambientValue f)).comp hv
  have hright : Tendsto (fun k ↦ C * ambientEnergy ((s k).toAmbient μ))
      atTop (𝓝 (C * ambientEnergy f)) := by
    change Tendsto (fun k ↦ C * ‖ContinuousMap.toLp 2 μ ℝ (s k).gradient‖ ^ 2)
      atTop (𝓝 (C * ‖ambientGradient f‖ ^ 2))
    exact (hg.norm.pow 2).const_mul C
  have hbound (k : ℕ) : labelEnergy (t := δ) hJ β
      (labelMean hJ β (ContinuousMap.toLp 2 μ ℝ (s k).value)) ≤ C * ambientEnergy ((s k).toAmbient μ) := by
    rw [labelMean_toLp hJ hN hβ (hβ₀.trans_lt hsub)]
    exact smooth_boundary_comparison hN hβ hβ₀ hsub hδ₀ hδ hmesh (s k)
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall hbound)

end PeriodicAttractiveLogGas.BoundaryComparison
