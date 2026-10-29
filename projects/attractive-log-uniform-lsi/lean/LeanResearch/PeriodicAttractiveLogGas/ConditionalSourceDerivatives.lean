import LeanResearch.PeriodicAttractiveLogGas.ConditionalSourceLipschitz
import LeanResearch.PeriodicAttractiveLogGas.BoundaryCovarianceSplitting

/-! Actual named-law derivative identifications for Proposition 3.11.

The logarithmic ratio, crossing probability, and conditional average use
the actual normalizers and conditional kernel. Genuine source derivatives
and neighborhood value identities give ordinary coordinate derivatives;
no differentiability is inferred from a totalized gradient equality.

SOURCE_ONLY. This file has not been elaborated or executed by its author.
Central checking, transitive axiom inspection, semantic review, and
protected replay remain separate statuses. -/

noncomputable section
open Set MeasureTheory Filter
open scoped BigOperators NNReal ENNReal Topology ContDiff RealInnerProductSpace

namespace PeriodicAttractiveLogGas.ConditionalSourceDerivatives

open MovingPoleNumerators hiding patchDomain
open MovingPoleCharts MovingPoleCalculus MovingPoleNormalized MovingPoleDerivativeIdentification
open GreenPointWeights
open ConditionalSourceCharts ConditionalSourceLipschitz
open MeshCells MeshAdjacentCells LabelOccupations OneCoordinateConditionals
open CellRestrictions LabelRatioTransport CollectiveGradientBounds CrossingLogistic
open CollectiveCovarianceBounds ConditionalLawEstimates

variable {n J : ℕ}

/-- A genuine ordinary derivative in the physical coordinate lift. -/
def HasCoordinateDerivative {N : ℕ} (g : Configuration N → ℝ)
    (k : Fin N) (X : Configuration N) (v : PlanarSpace) : Prop :=
  HasFDerivAt (fun z : PlanarSpace ↦ g (Function.update X k (torusQuotient z)))
    (InnerProductSpace.toDual ℝ PlanarSpace v) (centeredLift (X k))

theorem HasCoordinateDerivative.gradient {N : ℕ} {g : Configuration N → ℝ}
    {k : Fin N} {X : Configuration N} {v : PlanarSpace} (h : HasCoordinateDerivative g k X v) :
    coordinateOrdinaryGradient g k X = v := by
  unfold HasCoordinateDerivative at h
  rw [coordinateOrdinaryGradient, torusOrdinaryGradient, rectangleOrdinaryGradient, h.fderiv]
  exact (InnerProductSpace.toDual ℝ PlanarSpace).symm_apply_apply v

theorem hasFDerivAt_torusLift_of_quotient_eq (g : Torus → ℝ)
    {x y : PlanarSpace} {L : PlanarSpace →L[ℝ] ℝ}
    (hxy : torusQuotient x = torusQuotient y)
    (hx : HasFDerivAt (fun z ↦ g (torusQuotient z)) L x) :
    HasFDerivAt (fun z ↦ g (torusQuotient z)) L y := by
  have hd : DifferentiableAt ℝ (fun z ↦ g (torusQuotient z)) y :=
    (differentiableAt_torusLift_iff_of_quotient_eq g hxy).mp hx.differentiableAt
  have he : fderiv ℝ (fun z ↦ g (torusQuotient z)) y = L :=
    (fderiv_torusLift_eq_of_torusQuotient_eq g hxy.symm).trans hx.fderiv
  simpa only [he] using hd.hasFDerivAt

/-- The full genuine source derivative yields the genuine derivative at
the canonical physical lift, not just its total gradient representative. -/
theorem hasCoordinateDerivative_of_source (i : Fin (n + 1)) (g : Configuration n → ℝ)
    (X G : SourceSpace (otherParticles i))
    (hg : HasFDerivAt (fun Z ↦ g (outsideCoordinates i Z))
      (InnerProductSpace.toDual ℝ (SourceSpace (otherParticles i)) G) X) (j : Fin n) :
    HasCoordinateDerivative g j (outsideCoordinates i X) (sourceProjection (otherIndexEquiv i j) G) := by
  have hb := hasFDerivAt_sourceBlock hg (otherIndexEquiv i j)
  simp_rw [outsideCoordinates_variation] at hb
  apply hasFDerivAt_torusLift_of_quotient_eq
    (fun z ↦ g (Function.update (outsideCoordinates i X) j z)) ?_ hb
  rw [torusQuotient_centeredLift]
  rfl

theorem HasCoordinateDerivative.removeSite (i : Fin (n + 1)) {g : Configuration n → ℝ}
    (X : Configuration (n + 1)) {j : Fin n} {v : PlanarSpace}
    (h : HasCoordinateDerivative g j (removeSite i X) v) :
    HasCoordinateDerivative (fun Y ↦ g (removeSite i Y)) (i.succAbove j) X v := by
  simpa only [HasCoordinateDerivative, removeSite_update_retained,
    OneCoordinateConditionals.removeSite] using h

def jointLogRatio (hJ : 0 < J) (β : ℝ) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2) (X : Configuration (n + 1)) : ℝ :=
  logNormalizerRatio hJ β a r (removeSite i X)

def jointCrossing (hJ : 0 < J) (β : ℝ) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2) (X : Configuration (n + 1)) : ℝ :=
  normalizerRatio hJ β a r (removeSite i X)

def jointAverage (hJ : 0 < J) (β : ℝ) (i : Fin (n + 1)) (a : MeshIndex J)
    (r : Fin 2) (f : Configuration (n + 1) → ℝ) (X : Configuration (n + 1)) : ℝ :=
  outsideMean hJ i β a (.edge r) f (removeSite i X)

def outsideCrossingProbability (hJ : 0 < J) (β : ℝ) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2) (Y : Configuration n) : ℝ :=
  (conditionalKernel (edgeCellMeasure J hJ a r) i β Y).real (meshCell J hJ a)

theorem jointAverage_eq_conditionalAverage (hJ : 0 < J) (β : ℝ) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2) (f : Configuration (n + 1) → ℝ) :
    jointAverage hJ β i a r f = BoundaryCovarianceSplitting.conditionalAverage hJ i a r β f := rfl

theorem outsideCrossingProbability_joint (hJ : 0 < J) (β : ℝ) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2) :
    (fun X ↦ outsideCrossingProbability hJ β i a r (removeSite i X)) =
      BoundaryCovarianceSplitting.crossingProbability hJ i a r β := rfl

theorem jointAverage_eq (hJ : 0 < J) (β : ℝ) (i : Fin (n + 1)) (a : MeshIndex J)
    (r : Fin 2) (f : Configuration (n + 1) → ℝ) (X : Configuration (n + 1)) :
    jointAverage hJ β i a r f X =
      ∫ z, f (Function.update X i z)
        ∂conditionalKernel (edgeCellMeasure J hJ a r) i β (removeSite i X) := by
  simp only [jointAverage, outsideMean, patchMeasure,
    CoordinateConditionalKernels.insertSite_eq_update]

theorem logNormalizerRatio_eq_outsideLog (hJ : 0 < J) (i : Fin (n + 1))
    (β : ℝ) (a : MeshIndex J) (r : Fin 2) (Y : Configuration n)
    (ha : 0 < outsideNormalizer hJ i β a .cell Y)
    (hb : 0 < outsideNormalizer hJ i β (nextCell J hJ a r) .cell Y) :
    logNormalizerRatio hJ β a r Y = outsideLog hJ i β a .cell Y -
      outsideLog hJ i β (nextCell J hJ a r) .cell Y := by
  have he (c : MeshIndex J) : cellNormalizer hJ c β Y =
      (J : ℝ) ^ 2 * outsideNormalizer hJ i β c .cell Y := cellNormalizer_eq_haar hJ c β Y
  have hj : (J : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 (by exact_mod_cast hJ.ne')
  rw [logNormalizerRatio, he a, he (nextCell J hJ a r),
    Real.log_mul hj ha.ne', Real.log_mul hj hb.ne', outsideLog, outsideLog]
  ring

theorem source_logBlock_eq_actual (hJ : 0 < J) (hJ2 : 2 ≤ J) (i : Fin (n + 1))
    (β : ℝ) (a : MeshIndex J) (S : Set (SourceSpace (otherParticles i)))
    (hc : MovingPoleDerivativeIdentification.SourceCalculus
      (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a .cell S (fun _ _ ↦ 1))
    (X : SourceSpace (otherParticles i)) (hX : X ∈ S) (j : Fin n) :
    sourceProjection (otherIndexEquiv i j)
      (rawLogGradient (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a .cell X) =
      (-(β / (n + 1 : ℕ))) • ∫ z, greenGradient (z - outsideCoordinates i X j)
        ∂conditionalKernel (meshCellMeasure J hJ a) i β (outsideCoordinates i X) := by
  have hc' : MovingPoleDerivativeIdentification.SourceCalculus
      (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a .cell S
      (configurationFactor i (fun _ ↦ 1)) := hc
  have hk := ConditionalSourceCharts.SourceCalculus.conditionalKernel_eq_source hc' hJ2 X hX
  simp only [patchMeasure] at hk
  rw [(hc.blocks X hX (otherIndexEquiv i j)).1, logBlock, source_patchDomain, hk]
  rfl

structure OutsideDerivatives (hJ : 0 < J) (β : ℝ) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (f : Configuration (n + 1) → ℝ) (Y : Configuration n) : Prop where
  prescribed : PrescribedOutside hJ η i Y
  log_derivative : ∀ j, HasCoordinateDerivative (logNormalizerRatio hJ β a r) j Y
    (logRatioField hJ β i a r Y j)
  crossing_derivative : ∀ j, HasCoordinateDerivative (normalizerRatio hJ β a r) j Y
    (crossingField hJ β i a r Y j)
  mean_derivative : ∀ j, HasCoordinateDerivative (outsideMean hJ i β a (.edge r) f) j Y
    (conditionalMeanField (conditionalKernel (edgeCellMeasure J hJ a r) i β Y) β f i Y j)
  probability_eq : outsideCrossingProbability hJ β i a r Y = normalizerRatio hJ β a r Y
  probability_derivative : ∀ j, HasCoordinateDerivative (outsideCrossingProbability hJ β i a r) j Y
    (crossingField hJ β i a r Y j)

/-- A genuine chain-rule assembly at a source-chart interior point. The
identities of actual observables hold on a neighborhood supplied by the
closed chart; equality merely at the point is never used for derivatives. -/
theorem outsideDerivatives_of_source (hJ : 0 < J) (hJ2 : 2 ≤ J)
    (β : ℝ) (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (f : Configuration (n + 1) → ℝ)
    (ha : MovingPoleDerivativeIdentification.SourceCalculus
      (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a .cell
      (cellChart (otherParticles i) η) (fun _ _ ↦ 1))
    (hb : MovingPoleDerivativeIdentification.SourceCalculus
      (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ (nextCell J hJ a r) .cell
      (cellChart (otherParticles i) η) (fun _ _ ↦ 1))
    (hm : MovingPoleDerivativeIdentification.SourceCalculus
      (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ a (.edge r)
      (cellChart (otherParticles i) η) (configurationFactor i f))
    (hf : SmoothOnChart (cellChart (otherParticles i) η) (patchClosed (.edge r))
      (torusFactor (configurationFactor i f) J a))
    (hQ : ∀ Y, PrescribedOutside hJ η i Y →
      outsideCrossingProbability hJ β i a r Y = normalizerRatio hJ β a r Y) :
    ∀ᵐ X ∂(volume : Measure (SourceSpace (otherParticles i))).restrict (cellChart (otherParticles i) η),
      OutsideDerivatives hJ β η i a r f (outsideCoordinates i X) := by
  let S := cellChart (otherParticles i) η
  let w : otherParticles i → ℝ := fun _ ↦ β / (n + 1 : ℕ)
  have hpres (Z : SourceSpace (otherParticles i)) (hZ : Z ∈ S) :
      PrescribedOutside hJ η i (outsideCoordinates i Z) := by
    intro j
    exact source_mem_closure_patch hJ _ _ hZ (otherIndexEquiv i j)
  have hpos (Z : SourceSpace (otherParticles i)) (hZ : Z ∈ S) :
      0 < outsideNormalizer hJ i β a .cell (outsideCoordinates i Z) ∧
      0 < outsideNormalizer hJ i β (nextCell J hJ a r) .cell (outsideCoordinates i Z) := by
    simp only [outsideNormalizer_comp]
    exact ⟨ha.normalization.normalizer_pos Z hZ, hb.normalization.normalizer_pos Z hZ⟩
  have hlog (Z : SourceSpace (otherParticles i)) (hZ : Z ∈ S) :
      logNormalizerRatio hJ β a r (outsideCoordinates i Z) =
        rawLog w J hJ a .cell Z - rawLog w J hJ (nextCell J hJ a r) .cell Z := by
    rw [logNormalizerRatio_eq_outsideLog hJ i β a r _ (hpos Z hZ).1 (hpos Z hZ).2,
      outsideLog_comp, outsideLog_comp]
  have hq (Z : SourceSpace (otherParticles i)) (hZ : Z ∈ S) :
      normalizerRatio hJ β a r (outsideCoordinates i Z) =
        Real.sigmoid (logNormalizerRatio hJ β a r (outsideCoordinates i Z)) := by
    rw [normalizerRatio_eq_sigmoid_outsideLog hJ i β a r _ (hpos Z hZ).1 (hpos Z hZ).2,
      logNormalizerRatio_eq_outsideLog hJ i β a r _ (hpos Z hZ).1 (hpos Z hZ).2]
  filter_upwards [ha.ordinary, hb.ordinary, hm.ordinary,
    ae_closedChart_mem_nhds J (fun k : otherParticles i ↦ η k) (fun _ ↦ Patch.cell),
    ae_restrict_mem (isCompact_closedChart J (fun k : otherParticles i ↦ η k)
      (fun _ ↦ Patch.cell)).measurableSet] with X hda hdb hdm hn hX
  let G := rawLogGradient w J hJ a .cell X - rawLogGradient w J hJ (nextCell J hJ a r) .cell X
  let GM := rawMeanGradient w J hJ a (.edge r) (configurationFactor i f) X
  have hle : (fun Z ↦ logNormalizerRatio hJ β a r (outsideCoordinates i Z)) =ᶠ[𝓝 X]
      (fun Z ↦ rawLog w J hJ a .cell Z - rawLog w J hJ (nextCell J hJ a r) .cell Z) :=
    Filter.mem_of_superset hn fun Z hZ ↦ hlog Z hZ
  have hdlog : HasFDerivAt (fun Z ↦ logNormalizerRatio hJ β a r (outsideCoordinates i Z))
      (InnerProductSpace.toDual ℝ (SourceSpace (otherParticles i)) G) X :=
    hle.hasFDerivAt_iff.mpr (by simpa only [G, w, map_sub, Pi.sub_apply] using! hda.1.sub hdb.1)
  have hqe : (fun Z ↦ normalizerRatio hJ β a r (outsideCoordinates i Z)) =ᶠ[𝓝 X]
      (fun Z ↦ Real.sigmoid (logNormalizerRatio hJ β a r (outsideCoordinates i Z))) :=
    Filter.mem_of_superset hn fun Z hZ ↦ hq Z hZ
  have hdq : HasFDerivAt (fun Z ↦ normalizerRatio hJ β a r (outsideCoordinates i Z))
      (InnerProductSpace.toDual ℝ (SourceSpace (otherParticles i))
        ((normalizerRatio hJ β a r (outsideCoordinates i X) *
          (1 - normalizerRatio hJ β a r (outsideCoordinates i X))) • G)) X := by
    apply hqe.hasFDerivAt_iff.mpr
    simpa only [map_smul, hq X hX] using CrossingLogistic.hasFDerivAt_sigmoid hdlog
  have hpe : (fun Z ↦ outsideCrossingProbability hJ β i a r (outsideCoordinates i Z)) =ᶠ[𝓝 X]
      (fun Z ↦ normalizerRatio hJ β a r (outsideCoordinates i Z)) :=
    Filter.mem_of_superset hn fun Z hZ ↦ hQ _ (hpres Z hZ)
  have hdprob := hpe.hasFDerivAt_iff.mpr hdq
  have hme : (fun Z ↦ outsideMean hJ i β a (.edge r) f (outsideCoordinates i Z)) =ᶠ[𝓝 X]
      conditionalMean w J hJ a (.edge r) (configurationFactor i f) :=
    Filter.mem_of_superset hn fun Z hZ ↦
      ConditionalSourceCharts.SourceCalculus.outsideMean_comp hm hJ2 Z hZ
  have hdmean : HasFDerivAt (fun Z ↦ outsideMean hJ i β a (.edge r) f (outsideCoordinates i Z))
      (InnerProductSpace.toDual ℝ (SourceSpace (otherParticles i)) GM) X :=
    hme.hasFDerivAt_iff.mpr hdm.2
  have hG (j : Fin n) : sourceProjection (otherIndexEquiv i j) G =
      logRatioField hJ β i a r (outsideCoordinates i X) j := by
    rw [show G = rawLogGradient w J hJ a .cell X -
      rawLogGradient w J hJ (nextCell J hJ a r) .cell X from rfl, map_sub,
      source_logBlock_eq_actual hJ hJ2 i β a S ha X hX j,
      source_logBlock_eq_actual hJ hJ2 i β (nextCell J hJ a r) S hb X hX j,
      logRatioField, gradientExpectationDifference, smul_sub, neg_div]
  have hGM (j : Fin n) : sourceProjection (otherIndexEquiv i j) GM =
      conditionalMeanField (conditionalKernel (edgeCellMeasure J hJ a r) i β
        (outsideCoordinates i X)) β f i (outsideCoordinates i X) j := by
    rw [show GM = rawMeanGradient w J hJ a (.edge r) (configurationFactor i f) X from rfl,
      (hm.blocks X hX (otherIndexEquiv i j)).2,
      ConditionalSourceCharts.SourceCalculus.meanBlock_eq_physical hm hJ2 hf X hX j]
    rfl
  refine ⟨hpres X hX, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, hQ _ (hpres X hX), fun j ↦ ?_⟩
  · simpa only [hG j] using hasCoordinateDerivative_of_source i _ X G hdlog j
  · simpa only [map_smul, hG j, crossingField] using hasCoordinateDerivative_of_source i _ X _ hdq j
  · simpa only [hGM j] using hasCoordinateDerivative_of_source i _ X GM hdmean j
  · simpa only [map_smul, hG j, crossingField] using hasCoordinateDerivative_of_source i _ X _ hdprob j

theorem twoCell_sourceChart (η : LabelVector J (n + 1)) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2) :
    closedChart J (fun k : otherParticles i ↦ Function.update η i a k)
      (fun k ↦ OneCoordinateConditionals.adjacentShapes i r k) = cellChart (otherParticles i) η := by
  have hA : (fun k : otherParticles i ↦ Function.update η i a k) =
      (fun k : otherParticles i ↦ η k) := by
    funext k
    exact Function.update_of_ne ((mem_otherParticles i k).mp k.property) _ _
  rw [hA, integrated_adjacent_closedChart]

theorem jointLaw_adjacent_eq_twoCell (hJ : 0 < J) (hJ2 : 2 ≤ J) (hN : 2 ≤ n + 1)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    {β : ℝ} (hβ : 0 ≤ β) (hsub : β < 4) :
    DeletedPairConditionals.jointLaw hJ (Function.update η i a)
      (OneCoordinateConditionals.adjacentShapes i r) none β =
        twoCellGibbsMeasure hJ η i a (nextCell J hJ a r) β := by
  rw [DeletedPairConditionals.jointLaw_none, productGibbs_patch_eq_cond hJ hJ2 hN _ _ hβ hsub,
    patchProductEvent_adjacent]
  rfl

structure JointDerivatives (hJ : 0 < J) (β : ℝ) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (f : Configuration (n + 1) → ℝ) (X : Configuration (n + 1)) : Prop where
  prescribed : PrescribedOutside hJ η i (removeSite i X)
  log_derivative : ∀ j, HasCoordinateDerivative (jointLogRatio hJ β i a r) (i.succAbove j) X
    (logRatioField hJ β i a r (removeSite i X) j)
  crossing_derivative : ∀ j, HasCoordinateDerivative (jointCrossing hJ β i a r) (i.succAbove j) X
    (crossingField hJ β i a r (removeSite i X) j)
  mean_derivative : ∀ j, HasCoordinateDerivative (jointAverage hJ β i a r f) (i.succAbove j) X
    (conditionalMeanField (conditionalKernel (edgeCellMeasure J hJ a r) i β (removeSite i X))
      β f i (removeSite i X) j)
  probability_eq : BoundaryCovarianceSplitting.crossingProbability hJ i a r β X =
    jointCrossing hJ β i a r X
  probability_derivative : ∀ j, HasCoordinateDerivative
    (BoundaryCovarianceSplitting.crossingProbability hJ i a r β) (i.succAbove j) X
    (crossingField hJ β i a r (removeSite i X) j)

theorem OutsideDerivatives.joint (hJ : 0 < J) (β : ℝ) (η : LabelVector J (n + 1))
    (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (f : Configuration (n + 1) → ℝ) (X : Configuration (n + 1))
    (h : OutsideDerivatives hJ β η i a r f (removeSite i X)) :
    JointDerivatives hJ β η i a r f X :=
  ⟨h.prescribed, fun j ↦ HasCoordinateDerivative.removeSite i X (h.log_derivative j),
    fun j ↦ HasCoordinateDerivative.removeSite i X (h.crossing_derivative j),
    fun j ↦ HasCoordinateDerivative.removeSite i X (h.mean_derivative j), h.probability_eq,
    fun j ↦ HasCoordinateDerivative.removeSite i X (h.probability_derivative j)⟩

theorem integrated_coordinate_zero (hJ : 0 < J) (β : ℝ) (i : Fin (n + 1))
    (a : MeshIndex J) (r : Fin 2) (f : Configuration (n + 1) → ℝ) (X : Configuration (n + 1)) :
    coordinateOrdinaryGradient (jointLogRatio hJ β i a r) i X = 0 ∧
    coordinateOrdinaryGradient (jointCrossing hJ β i a r) i X = 0 ∧
    coordinateOrdinaryGradient (jointAverage hJ β i a r f) i X = 0 :=
  ⟨coordinateOrdinaryGradient_removeSite_self i _ X,
    coordinateOrdinaryGradient_removeSite_self i _ X,
    coordinateOrdinaryGradient_removeSite_self i _ X⟩

theorem sum_coordinateGradient_removeSite (i : Fin (n + 1)) (g : Configuration n → ℝ)
    (X : Configuration (n + 1)) (V : Fin n → PlanarSpace)
    (hV : ∀ j, coordinateOrdinaryGradient (fun Y ↦ g (removeSite i Y)) (i.succAbove j) X = V j) :
    (∑ k : Fin (n + 1), ‖coordinateOrdinaryGradient (fun Y ↦ g (removeSite i Y)) k X‖ ^ 2) =
      ∑ j : Fin n, ‖V j‖ ^ 2 := by
  rw [Fin.sum_univ_succAbove _ i, coordinateOrdinaryGradient_removeSite_self,
    norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
  exact Finset.sum_congr rfl fun j _ ↦ congrArg (fun v : PlanarSpace ↦ ‖v‖ ^ 2) (hV j)

theorem JointDerivatives.sum_fields {hJ : 0 < J} {β : ℝ} {η : LabelVector J (n + 1)}
    {i : Fin (n + 1)} {a : MeshIndex J} {r : Fin 2} {f : Configuration (n + 1) → ℝ}
    {X : Configuration (n + 1)} (h : JointDerivatives hJ β η i a r f X) :
    (∑ k, ‖coordinateOrdinaryGradient (jointLogRatio hJ β i a r) k X‖ ^ 2) =
      (∑ j, ‖logRatioField hJ β i a r (removeSite i X) j‖ ^ 2) ∧
    (∑ k, ‖coordinateOrdinaryGradient (jointCrossing hJ β i a r) k X‖ ^ 2) =
      (∑ j, ‖crossingField hJ β i a r (removeSite i X) j‖ ^ 2) ∧
    (∑ k, ‖coordinateOrdinaryGradient (jointAverage hJ β i a r f) k X‖ ^ 2) =
      (∑ j, ‖conditionalMeanField
        (conditionalKernel (edgeCellMeasure J hJ a r) i β (removeSite i X))
        β f i (removeSite i X) j‖ ^ 2) :=
  ⟨sum_coordinateGradient_removeSite i _ X _ (fun j ↦ (h.log_derivative j).gradient),
    sum_coordinateGradient_removeSite i _ X _ (fun j ↦ (h.crossing_derivative j).gradient),
    sum_coordinateGradient_removeSite i _ X _ (fun j ↦ (h.mean_derivative j).gradient)⟩

theorem JointDerivatives.sum_probabilityField {hJ : 0 < J} {β : ℝ} {η : LabelVector J (n + 1)}
    {i : Fin (n + 1)} {a : MeshIndex J} {r : Fin 2} {f : Configuration (n + 1) → ℝ}
    {X : Configuration (n + 1)} (h : JointDerivatives hJ β η i a r f X) :
    (∑ k, ‖coordinateOrdinaryGradient
      (BoundaryCovarianceSplitting.crossingProbability hJ i a r β) k X‖ ^ 2) =
      ∑ j, ‖crossingField hJ β i a r (removeSite i X) j‖ ^ 2 :=
  sum_coordinateGradient_removeSite i (outsideCrossingProbability hJ β i a r) X _
    (fun j ↦ (h.probability_derivative j).gradient)

theorem crossingProbability_integrated_coordinate_zero (hJ : 0 < J) (β : ℝ)
    (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2) (X : Configuration (n + 1)) :
    coordinateOrdinaryGradient (BoundaryCovarianceSplitting.crossingProbability hJ i a r β) i X = 0 :=
  coordinateOrdinaryGradient_removeSite_self i (outsideCrossingProbability hJ β i a r) X

/-- Actual named-law endpoint. Every source-calculus premise is built
from the real Green bounds, the capped completed labels, and local smoothness.
The supplied caps are the source's two adjacent completed-label caps. -/
theorem twoCell_ordinary_derivatives {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    (f : Configuration (n + 1) → ℝ)
    (hf : SmoothOnChart (cellChart (otherParticles i) η) (patchClosed (.edge r))
      (torusFactor (configurationFactor i f) J a)) :
    IsProbabilityMeasure (twoCellGibbsMeasure (mesh_pos hmesh) η i a
      (nextCell J (mesh_pos hmesh) a r) β) ∧
      ∀ᵐ X ∂twoCellGibbsMeasure (mesh_pos hmesh) η i a (nextCell J (mesh_pos hmesh) a r) β,
        JointDerivatives (mesh_pos hmesh) β η i a r f X := by
  let hJ := mesh_pos hmesh
  let S := cellChart (otherParticles i) η
  let ζ := Function.update η i a
  have hcap : OccupationCap (ConditionalParameters.fixedDelta β₀ kernelConstant kernelConstant) ζ :=
    hadm.1.mono hδ
  have hplace : ∀ X ∈ S, ∀ k ∈ otherParticles i,
      extendedSources (otherParticles i) X k ∈ closure (meshCell J hJ (ζ k)) := by
    intro X hX k hk
    have hki := (mem_otherParticles i k).mp hk
    simpa only [ζ, Function.update_of_ne hki] using cellChart_placement hJ (otherParticles i) η hX k hk
  have hc (c : MeshIndex J) (b : Patch) (F : SourceSpace (otherParticles i) → Torus → ℝ)
      (hF : SmoothOnChart S (patchClosed b) (torusFactor F J c)) :
      MovingPoleDerivativeIdentification.SourceCalculus
        (fun _ : otherParticles i ↦ β / (n + 1 : ℕ)) J hJ c b S F :=
    capped_sourceCalculus MovingPoleIntegrability.fixedKernelBounds hJ (Nat.succ_pos n)
      hβ hβ₀ kernelConstant_pos.le kernelConstant_pos.le kernel_log_bound kernel_gradient_bound hmesh
      (otherParticles i) S (isCompact_closedChart J _ _) (convex_closedChart J _ _)
      (fun _ ↦ ζ) (fun _ _ ↦ hcap) hplace (fun _ ↦ β / (n + 1 : ℕ))
      (fun _ _ ↦ div_nonneg hβ (Nat.cast_nonneg _)) (fun _ _ ↦ le_rfl) c b hF
  have ha := hc a .cell (fun _ _ ↦ 1) (smoothOnChart_of_contDiff contDiff_const)
  have hb := hc (nextCell J hJ a r) .cell (fun _ _ ↦ 1) (smoothOnChart_of_contDiff contDiff_const)
  have hm := hc a (.edge r) (configurationFactor i f) hf
  have hQ (Y : Configuration n) (hY : PrescribedOutside hJ η i Y) :
      outsideCrossingProbability hJ β i a r Y = normalizerRatio hJ β a r Y := by
    exact (adjacent_ratio_eq_probability hβ hβ₀ hδ hmesh η i a r hadm Y hY).symm
  have hsrc := outsideDerivatives_of_source hJ (mesh_two_le hmesh) β η i a r f ha hb hm hf hQ
  have hout : ∀ᵐ Y ∂outsideReference
      (fun k ↦ patchMeasure J hJ (ζ k) (OneCoordinateConditionals.adjacentShapes i r k)) i,
      OutsideDerivatives hJ β η i a r f Y := by
    apply ae_outsideReference_of_chart hJ (mesh_three_le hmesh) i ζ
      (OneCoordinateConditionals.adjacentShapes i r)
    simpa only [ζ, twoCell_sourceChart] using hsrc
  have hjoint := ae_jointLaw_of_outsideReference hJ ζ (OneCoordinateConditionals.adjacentShapes i r)
    none β i hout
  have he := jointLaw_adjacent_eq_twoCell hJ (mesh_two_le hmesh) hN η i a r hβ (hβ₀.trans_lt hsub)
  have hp := DeletedPairConditionals.jointLaw_probability hJ (mesh_two_le hmesh) hN ζ
    (OneCoordinateConditionals.adjacentShapes i r) none hβ (hβ₀.trans_lt hsub)
  rw [he] at hjoint hp
  exact ⟨hp, hjoint.mono fun X hX ↦ OutsideDerivatives.joint hJ β η i a r f X hX⟩

/-- Both source collective bounds now control the literal ordinary
gradients of the actual named observables under the actual named law. -/
theorem twoCell_log_crossing_gradient_bounds {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r) :
    ∀ᵐ X ∂twoCellGibbsMeasure (mesh_pos hmesh) η i a (nextCell J (mesh_pos hmesh) a r) β,
      (∑ k, ‖coordinateOrdinaryGradient (jointLogRatio (mesh_pos hmesh) β i a r) k X‖ ^ 2) ≤
        crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant * J ^ 2 / (n + 1 : ℕ) ∧
      (∑ k, ‖coordinateOrdinaryGradient
        (BoundaryCovarianceSplitting.crossingProbability (mesh_pos hmesh) i a r β) k X‖ ^ 2) ≤
        crossingConstantSquared β₀ δ GreenCovarianceBounds.hessianConstant * J ^ 2 /
          (4 * (n + 1 : ℕ)) *
          (BoundaryCovarianceSplitting.crossingProbability (mesh_pos hmesh) i a r β X *
            (1 - BoundaryCovarianceSplitting.crossingProbability (mesh_pos hmesh) i a r β X)) := by
  have hf : SmoothOnChart (cellChart (otherParticles i) η) (patchClosed (.edge r))
      (torusFactor (configurationFactor i (fun _ ↦ 1)) J a) :=
    smoothOnChart_of_contDiff contDiff_const
  have hd := (twoCell_ordinary_derivatives hN hβ hβ₀ hsub hδ hmesh η i a r hadm (fun _ ↦ 1) hf).2
  filter_upwards [hd] with X hX
  constructor
  · rw [hX.sum_fields.1]
    exact collective_logRatioField hβ hβ₀ hδ₀ hδ GreenCovarianceBounds.hessianConstant_pos.le
      GreenCovarianceBounds.kernel_hessian_bound hmesh η i a r hadm (removeSite i X) hX.prescribed
  · rw [hX.sum_probabilityField, hX.probability_eq]
    exact adjacent_crossingField_squared hβ hβ₀ hδ₀ hδ hmesh η i a r hadm
      (removeSite i X) hX.prescribed

/-- Actual mean energy bound with the exact average constant. The global
physical Lipschitz hypothesis concerns the original observable f, as in
the imported field-energy theorem; local smoothness supplies the actual
derivative identification of its conditional average. -/
theorem twoCell_average_gradient_bound {β β₀ δ : ℝ}
    (hN : 2 ≤ n + 1) (hβ : 0 ≤ β) (hβ₀ : β ≤ β₀) (hsub : β₀ < 4)
    (hδ₀ : 0 ≤ δ) (hδ : δ ≤ occupationBound β₀) (hmesh : 8 * (radius β₀ + 4) ≤ J)
    (η : LabelVector J (n + 1)) (i : Fin (n + 1)) (a : MeshIndex J) (r : Fin 2)
    (hadm : AdjacentAdmissible (mesh_pos hmesh) δ η i a r)
    (f : Configuration (n + 1) → ℝ) {L : ℝ≥0}
    (hfLip : ConfigurationEuclideanLipschitzWith L f)
    (hf : SmoothOnChart (cellChart (otherParticles i) η) (patchClosed (.edge r))
      (torusFactor (configurationFactor i f) J a)) :
    ∀ᵐ X ∂twoCellGibbsMeasure (mesh_pos hmesh) η i a (nextCell J (mesh_pos hmesh) a r) β,
      (∑ k, ‖coordinateOrdinaryGradient
        (BoundaryCovarianceSplitting.conditionalAverage (mesh_pos hmesh) i a r β f) k X‖ ^ 2) ≤
        2 * (∫ z, ∑ j : Fin n, ‖coordinateOrdinaryGradient f (i.succAbove j) (Function.update X i z)‖ ^ 2
          ∂conditionalKernel (edgeCellMeasure J (mesh_pos hmesh) a r) i β (removeSite i X)) +
        2 * averageConstant β₀ δ / (n + 1 : ℕ) *
          ∫ z, ‖coordinateOrdinaryGradient f i (Function.update X i z)‖ ^ 2
            ∂conditionalKernel (edgeCellMeasure J (mesh_pos hmesh) a r) i β (removeSite i X) := by
  have hd := (twoCell_ordinary_derivatives hN hβ hβ₀ hsub hδ hmesh η i a r hadm f hf).2
  filter_upwards [hd] with X hX
  rw [← jointAverage_eq_conditionalAverage, hX.sum_fields.2.2]
  simpa only [patchMeasure, CoordinateConditionalKernels.insertSite_eq_update] using
    adjacent_meanField_energy hN hβ hβ₀ hsub hδ₀ hδ hmesh η i a r hadm
      (removeSite i X) hX.prescribed hfLip

end PeriodicAttractiveLogGas.ConditionalSourceDerivatives
