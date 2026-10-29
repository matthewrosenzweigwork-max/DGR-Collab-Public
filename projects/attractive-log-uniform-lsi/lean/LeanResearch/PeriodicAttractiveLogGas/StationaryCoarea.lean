import LeanResearch.PeriodicAttractiveLogGas.StationaryLevelGeometry
import LeanResearch.Imported.ProbabilityApproximation.ScalarCoarea
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
Coarea for the actual physical Euclidean torus. The old product metric on
`Torus` is not changed: physical Hausdorff measure is transported from its
explicit L2 product metric. The imported Euclidean theorem is the attributed
Apache-2.0 scalar coarea proof in `Imported/ProbabilityApproximation`; see its
`ORIGIN.md` and the separate development note for exact checking status.
-/

noncomputable section

open Set Filter MeasureTheory MeasureTheory.Measure Metric
open scoped Topology ENNReal NNReal ContDiff

namespace PeriodicAttractiveLogGas.StationaryCoarea

open StationaryLevelGeometry StationaryDistribution

private theorem continuous_integrable {f : Torus → ℝ} (hf : Continuous f) :
    Integrable f torusMeasure :=
  memLp_one_iff_integrable.mp
    (ContinuousMap.memLp (μ := torusMeasure) (p := 1) ℝ ⟨f, hf⟩)

/-- The same two circles equipped with the physical Euclidean product metric. -/
abbrev PhysicalTorus := PiLp 2 (fun _ : Fin 2 ↦ UnitAddCircle)

/-- Only the metric changes; this measurable equivalence retains the original
torus topology and Borel sets. -/
def physicalEquiv : Torus ≃ᵐ PhysicalTorus :=
  MeasurableEquiv.toLp 2 Torus

def physicalQuotient (x : PlanarSpace) : PhysicalTorus := physicalEquiv (torusQuotient x)

/-- The source curve-length measure on the original torus measurable space,
using the normalized one-dimensional Euclidean Hausdorff measure. -/
def physicalCurveMeasure : Measure Torus :=
  (Measure.euclideanHausdorffMeasure 1 : Measure PhysicalTorus).map physicalEquiv.symm

theorem physicalQuotient_lipschitz : LipschitzWith 1 physicalQuotient := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change dist (WithLp.toLp 2 (torusQuotient x) : PhysicalTorus)
    (WithLp.toLp 2 (torusQuotient y)) ≤ (1 : ℝ) * dist x y
  rw [← torusEuclideanDist_eq_piLp_dist, one_mul]
  exact torusEuclideanDist_quotient_le x y

/-- On each ball of radius one eighth the actual quotient is an isometry.
The strict diameter bound avoids every periodic seam ambiguity. -/
theorem physicalQuotient_isometry_ball (a : PlanarSpace) :
    Isometry (fun x : ball a (1 / 8 : ℝ) ↦ physicalQuotient x) := by
  apply Isometry.of_dist_eq
  intro x y
  change dist (WithLp.toLp 2 (torusQuotient x) : PhysicalTorus)
    (WithLp.toLp 2 (torusQuotient y)) = dist (x : PlanarSpace) (y : PlanarSpace)
  rw [← torusEuclideanDist_eq_piLp_dist]
  apply torusEuclideanDist_quotient_eq_of_dist_lt_half
  calc
    dist (x : PlanarSpace) (y : PlanarSpace) ≤ dist (x : PlanarSpace) a + dist a y :=
      dist_triangle _ _ _
    _ < (1 / 8 : ℝ) + 1 / 8 :=
      add_lt_add x.property (by simpa only [Metric.mem_ball, dist_comm] using y.property)
    _ < 1 / 2 := by norm_num

/-- Actual physical Hausdorff measure is preserved on every subset of a
small quotient chart, including nonclosed or half-open subsets. -/
theorem physicalQuotient_curve_image {a : PlanarSpace} {s : Set PlanarSpace}
    (hs : s ⊆ ball a (1 / 8 : ℝ)) :
    (Measure.euclideanHausdorffMeasure 1 : Measure PhysicalTorus)
        (physicalQuotient '' s) =
      (Measure.euclideanHausdorffMeasure 1 : Measure PlanarSpace) s := by
  let T : Set (ball a (1 / 8 : ℝ)) := Subtype.val ⁻¹' s
  have hval : (Subtype.val : ball a (1 / 8 : ℝ) → PlanarSpace) '' T = s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hs hx⟩, hx, rfl⟩
  have hq : physicalQuotient '' s =
      (fun x : ball a (1 / 8 : ℝ) ↦ physicalQuotient x) '' T := by
    rw [← hval, image_image]
  rw [hq, (physicalQuotient_isometry_ball a).euclideanHausdorffMeasure_image]
  have he := (isometry_subtype_coe :
    Isometry (Subtype.val : ball a (1 / 8 : ℝ) → PlanarSpace)).euclideanHausdorffMeasure_image
      (d := 1) T
  rw [hval] at he
  exact he.symm

def fundamentalBox : Set PlanarSpace := euclideanFundamentalBox (centeredBoxAnchor 0)

theorem measurableSet_fundamentalBox : MeasurableSet fundamentalBox :=
  measurableSet_euclideanFundamentalBox _

theorem physicalQuotient_injOn_fundamentalBox :
    InjOn physicalQuotient fundamentalBox := by
  intro x hx y hy hxy
  exact injOn_torusQuotient_box (centeredBoxAnchor 0) hx hy (physicalEquiv.injective hxy)

private def chartPiece (n : ℕ) : Set PlanarSpace :=
  disjointed (fun k ↦ ball (TopologicalSpace.denseSeq PlanarSpace k) (1 / 8 : ℝ)) n

private theorem chartPiece_measurable (n : ℕ) : MeasurableSet (chartPiece n) :=
  MeasurableSet.disjointed (fun _ ↦ isOpen_ball.measurableSet) n

private theorem chartPiece_disjoint : Pairwise (fun i j ↦ Disjoint (chartPiece i) (chartPiece j)) :=
  disjoint_disjointed _

private theorem chartPiece_subset (n : ℕ) :
    chartPiece n ⊆ ball (TopologicalSpace.denseSeq PlanarSpace n) (1 / 8 : ℝ) :=
  disjointed_subset _ n

private theorem chartPiece_cover : (⋃ n, chartPiece n) = univ := by
  change (⋃ n, disjointed
    (fun k ↦ ball (TopologicalSpace.denseSeq PlanarSpace k) (1 / 8 : ℝ)) n) = univ
  rw [iUnion_disjointed]
  have hc := (Metric.dense_iff_iUnion_ball
    (range (TopologicalSpace.denseSeq PlanarSpace))).1
      (TopologicalSpace.denseRange_denseSeq PlanarSpace) (1 / 8 : ℝ) (by norm_num)
  apply eq_univ_of_forall
  intro x
  have hx : x ∈ ⋃ c ∈ range (TopologicalSpace.denseSeq PlanarSpace),
      ball c (1 / 8 : ℝ) := by rw [hc]; trivial
  obtain ⟨c, hx⟩ := mem_iUnion.mp hx
  obtain ⟨hc, hx⟩ := mem_iUnion.mp hx
  obtain ⟨n, rfl⟩ := hc
  exact mem_iUnion.mpr ⟨n, hx⟩

/-- Countable disjoint local isometries preserve the actual curve measure
on every measurable subset of the half-open fundamental box. The seams
are retained in precisely one chart, with no Hausdorff-nullity assumption. -/
theorem physicalQuotient_curve_image_fundamentalBox {s : Set PlanarSpace}
    (hs : MeasurableSet s) (hbox : s ⊆ fundamentalBox) :
    (Measure.euclideanHausdorffMeasure 1 : Measure PhysicalTorus)
        (physicalQuotient '' s) =
      (Measure.euclideanHausdorffMeasure 1 : Measure PlanarSpace) s := by
  have hcover : s = ⋃ n, s ∩ chartPiece n := by
    rw [← inter_iUnion, chartPiece_cover, inter_univ]
  have hdis : Pairwise (fun i j ↦ Disjoint (s ∩ chartPiece i) (s ∩ chartPiece j)) :=
    pairwise_disjoint_mono chartPiece_disjoint fun _ ↦ inter_subset_right
  have hm (n : ℕ) : MeasurableSet (s ∩ chartPiece n) :=
    hs.inter (chartPiece_measurable n)
  have him (n : ℕ) : MeasurableSet (physicalQuotient '' (s ∩ chartPiece n)) := by
    apply (hm n).image_of_continuousOn_injOn
    · exact physicalQuotient_lipschitz.continuous.continuousOn
    · exact physicalQuotient_injOn_fundamentalBox.mono (inter_subset_left.trans hbox)
  have hid : Pairwise (fun i j ↦ Disjoint (physicalQuotient '' (s ∩ chartPiece i))
      (physicalQuotient '' (s ∩ chartPiece j))) := by
    intro i j hij
    apply Disjoint.image _ physicalQuotient_injOn_fundamentalBox
      (inter_subset_left.trans hbox) (inter_subset_left.trans hbox)
    exact hdis hij
  calc
    (Measure.euclideanHausdorffMeasure 1 : Measure PhysicalTorus)
        (physicalQuotient '' s) =
      ∑' n, (Measure.euclideanHausdorffMeasure 1 : Measure PhysicalTorus)
        (physicalQuotient '' (s ∩ chartPiece n)) := by
      conv_lhs => rw [hcover, image_iUnion]
      exact measure_iUnion hid him
    _ = ∑' n, (Measure.euclideanHausdorffMeasure 1 : Measure PlanarSpace)
        (s ∩ chartPiece n) := by
      apply tsum_congr
      intro n
      exact physicalQuotient_curve_image (inter_subset_right.trans (chartPiece_subset n))
    _ = (Measure.euclideanHausdorffMeasure 1 : Measure PlanarSpace) s := by
      conv_rhs => rw [hcover]
      exact (measure_iUnion hdis hm).symm

/-- Actual Hausdorff measure transport by the quotient. This is a measure
identity, not a new definition of the torus curve measure. -/
theorem map_physicalQuotient_curveMeasure :
    ((Measure.euclideanHausdorffMeasure 1 : Measure PlanarSpace).restrict fundamentalBox).map
        physicalQuotient =
      (Measure.euclideanHausdorffMeasure 1 : Measure PhysicalTorus) := by
  ext1 s hs
  rw [Measure.map_apply physicalQuotient_lipschitz.continuous.measurable hs,
    Measure.restrict_apply (physicalQuotient_lipschitz.continuous.measurable hs)]
  have himage : physicalQuotient '' (physicalQuotient ⁻¹' s ∩ fundamentalBox) = s := by
    apply Subset.antisymm
    · rintro z ⟨x, hx, rfl⟩
      exact hx.1
    · intro z hz
      refine ⟨centeredLift (physicalEquiv.symm z), ⟨?_, ?_⟩, ?_⟩
      · change physicalQuotient (centeredLift (physicalEquiv.symm z)) ∈ s
        simpa only [physicalQuotient, torusQuotient_centeredLift,
          MeasurableEquiv.apply_symm_apply] using hz
      · exact centeredLift_mem_fundamentalBox _
      · simp only [physicalQuotient, torusQuotient_centeredLift,
          MeasurableEquiv.apply_symm_apply]
  rw [← physicalQuotient_curve_image_fundamentalBox
    ((physicalQuotient_lipschitz.continuous.measurable hs).inter measurableSet_fundamentalBox)
    inter_subset_right, himage]

theorem map_torusQuotient_curveMeasure :
    ((Measure.euclideanHausdorffMeasure 1 : Measure PlanarSpace).restrict fundamentalBox).map
      torusQuotient = physicalCurveMeasure := by
  unfold physicalCurveMeasure
  rw [← map_physicalQuotient_curveMeasure,
    Measure.map_map physicalEquiv.symm.measurable
      physicalQuotient_lipschitz.continuous.measurable]
  congr 1

/-- Literal lifted fibre content on a half-open fundamental box. This is
an intermediate expression, not a definition of torus Hausdorff measure. -/
def liftedFiberIntegral (v : Torus → ℝ) (w : Torus → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x in fundamentalBox ∩ {x | v (torusQuotient x) = t},
    w (torusQuotient x) ∂(Measure.euclideanHausdorffMeasure 1 : Measure PlanarSpace)

theorem scalarCoareaFiber_fundamentalBox (v : Torus → ℝ) (w : Torus → ℝ≥0∞)
    (t : ℝ) :
    ProbabilityTheory.scalarCoareaFiber (fun x : PlanarSpace ↦ v (torusQuotient x))
      (fundamentalBox.indicator (fun x ↦ w (torusQuotient x))) t =
        liftedFiberIntegral v w t := by
  change (∫⁻ x in {x | v (torusQuotient x) = t},
    fundamentalBox.indicator (fun x ↦ w (torusQuotient x)) x
      ∂(Measure.euclideanHausdorffMeasure 1 : Measure PlanarSpace)) = _
  rw [lintegral_indicator measurableSet_fundamentalBox,
    Measure.restrict_restrict measurableSet_fundamentalBox]
  rfl

theorem aemeasurable_liftedFiberIntegral {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (w : Torus → ℝ≥0∞) (hw : Measurable w) :
    AEMeasurable (liftedFiberIntegral v w) volume := by
  obtain ⟨L, hL⟩ := exists_lipschitz_lift hv
  have hW : Measurable (fun x : PlanarSpace ↦ w (torusQuotient x)) :=
    hw.comp isOpenQuotientMap_torusQuotient.continuous.measurable
  have hm := ProbabilityTheory.LipschitzWith.aemeasurable_scalarCoareaFiber hL
    (fundamentalBox.indicator (fun x ↦ w (torusQuotient x)))
    (hW.indicator measurableSet_fundamentalBox)
  exact hm.congr (Filter.Eventually.of_forall (scalarCoareaFiber_fundamentalBox v w))

/-- Euclidean coarea on the actual periodic fundamental box. The scalar
Jacobian equals the physical gradient norm, and the left measure is exactly
the original probability Haar measure. -/
theorem lifted_coarea {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (w : Torus → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ z, ENNReal.ofReal ‖torusOrdinaryGradient v z‖ * w z ∂torusMeasure) =
      ∫⁻ t : ℝ, liftedFiberIntegral v w t := by
  let f : PlanarSpace → ℝ := fun x ↦ v (torusQuotient x)
  let W : PlanarSpace → ℝ≥0∞ := fun x ↦ w (torusQuotient x)
  have hW : Measurable W := hw.comp isOpenQuotientMap_torusQuotient.continuous.measurable
  obtain ⟨L, hL⟩ := exists_lipschitz_lift hv
  have hco := ProbabilityTheory.LipschitzWith.scalarCoareaFormula hL
    (fundamentalBox.indicator W) (hW.indicator measurableSet_fundamentalBox)
  change (∫⁻ x, ProbabilityTheory.scalarJacobian f x * fundamentalBox.indicator W x) = _ at hco
  rw [← ProbabilityTheory.setLIntegral_scalarJacobian_mul_eq_lintegral_indicator f W
    measurableSet_fundamentalBox] at hco
  have hm : Measurable (fun z ↦ ENNReal.ofReal ‖torusOrdinaryGradient v z‖ * w z) :=
    ((measurable_torusOrdinaryGradient v).norm.ennreal_ofReal).mul hw
  calc
    (∫⁻ z, ENNReal.ofReal ‖torusOrdinaryGradient v z‖ * w z ∂torusMeasure) =
        ∫⁻ x in fundamentalBox,
          ENNReal.ofReal ‖torusOrdinaryGradient v (torusQuotient x)‖ * W x :=
      ((measurePreserving_torusQuotient_box (centeredBoxAnchor 0)).lintegral_comp hm).symm
    _ = ∫⁻ x in fundamentalBox, ProbabilityTheory.scalarJacobian f x * W x := by
      apply lintegral_congr
      intro x
      rw [norm_torusOrdinaryGradient_lift]
      rfl
    _ = ∫⁻ t : ℝ, ProbabilityTheory.scalarCoareaFiber f
        (fundamentalBox.indicator W) t := hco
    _ = _ := lintegral_congr (scalarCoareaFiber_fundamentalBox v w)

/-- The actual weighted fibre integral for physical torus Hausdorff length. -/
def fiberIntegral (v : Torus → ℝ) (w : Torus → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ :=
  ∫⁻ z in {z | v z = t}, w z ∂physicalCurveMeasure

theorem liftedFiberIntegral_eq_fiberIntegral {v : Torus → ℝ} (hv : Measurable v)
    (w : Torus → ℝ≥0∞) (hw : Measurable w) (t : ℝ) :
    liftedFiberIntegral v w t = fiberIntegral v w t := by
  have hp : MeasurePreserving torusQuotient
      ((Measure.euclideanHausdorffMeasure 1 : Measure PlanarSpace).restrict fundamentalBox)
      physicalCurveMeasure :=
    ⟨isOpenQuotientMap_torusQuotient.continuous.measurable, map_torusQuotient_curveMeasure⟩
  have hs : MeasurableSet {z | v z = t} := hv (measurableSet_singleton t)
  have he := (hp.restrict_preimage hs).lintegral_comp hw
  rw [Measure.restrict_restrict (hp.measurable hs)] at he
  simpa only [liftedFiberIntegral, fiberIntegral, preimage_ofPred_eq, inter_comm] using he

theorem aemeasurable_fiberIntegral {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (w : Torus → ℝ≥0∞) (hw : Measurable w) :
    AEMeasurable (fiberIntegral v w) volume := by
  exact (aemeasurable_liftedFiberIntegral hv w hw).congr
    (Eventually.of_forall (liftedFiberIntegral_eq_fiberIntegral
      (continuous_of_contDiff_lift hv).measurable w hw))

/-- Scalar coarea for the original Haar probability and the physical
Euclidean Hausdorff length, with their actual normalizations. -/
theorem coarea {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (w : Torus → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ z, ENNReal.ofReal ‖torusOrdinaryGradient v z‖ * w z ∂torusMeasure) =
      ∫⁻ t : ℝ, fiberIntegral v w t := by
  rw [lifted_coarea hv w hw]
  exact lintegral_congr (liftedFiberIntegral_eq_fiberIntegral
    (continuous_of_contDiff_lift hv).measurable w hw)

theorem fiberIntegral_indicator {v : Torus → ℝ} (hv : Measurable v)
    (w : Torus → ℝ≥0∞) (s : Set ℝ) (t : ℝ) :
    fiberIntegral v ((v ⁻¹' s).indicator w) t = s.indicator (fiberIntegral v w) t := by
  classical
  by_cases ht : t ∈ s
  · rw [Set.indicator_of_mem ht]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (hv (measurableSet_singleton t))] with z hz
    apply Set.indicator_of_mem
    change v z ∈ s
    rwa [show v z = t from hz]
  · rw [Set.indicator_of_notMem ht]
    change (∫⁻ z in {z | v z = t}, (v ⁻¹' s).indicator w z ∂physicalCurveMeasure) = 0
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [ae_restrict_mem (hv (measurableSet_singleton t))] with z hz
    apply Set.indicator_of_notMem
    change v z ∉ s
    rwa [show v z = t from hz]

theorem coarea_preimage {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (w : Torus → ℝ≥0∞) (hw : Measurable w) {s : Set ℝ} (hs : MeasurableSet s) :
    (∫⁻ z in v ⁻¹' s, ENNReal.ofReal ‖torusOrdinaryGradient v z‖ * w z ∂torusMeasure) =
      ∫⁻ t in s, fiberIntegral v w t := by
  have hvm := (continuous_of_contDiff_lift hv).measurable
  calc
    (∫⁻ z in v ⁻¹' s, ENNReal.ofReal ‖torusOrdinaryGradient v z‖ * w z ∂torusMeasure) =
      ∫⁻ z, ENNReal.ofReal ‖torusOrdinaryGradient v z‖ * (v ⁻¹' s).indicator w z
        ∂torusMeasure := by
      rw [← lintegral_indicator (hvm hs)]
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ v ⁻¹' s <;> simp [hz]
    _ = ∫⁻ t, fiberIntegral v ((v ⁻¹' s).indicator w) t :=
      coarea hv _ (hw.indicator (hvm hs))
    _ = ∫⁻ t in s, fiberIntegral v w t := by
      rw [← lintegral_indicator hs]
      exact lintegral_congr (fiberIntegral_indicator hvm w s)

def inverseGradientFiber (v : Torus → ℝ) : ℝ → ℝ≥0∞ :=
  fiberIntegral v (fun z ↦ ENNReal.ofReal (‖torusOrdinaryGradient v z‖⁻¹))

def gradientFluxFiber (v : Torus → ℝ) : ℝ → ℝ≥0∞ :=
  fiberIntegral v (fun z ↦ ENNReal.ofReal ‖torusOrdinaryGradient v z‖)

theorem aemeasurable_inverseGradientFiber {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    AEMeasurable (inverseGradientFiber v) volume :=
  aemeasurable_fiberIntegral hv _ (measurable_torusOrdinaryGradient v).norm.inv.ennreal_ofReal

theorem aemeasurable_gradientFluxFiber {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    AEMeasurable (gradientFluxFiber v) volume :=
  aemeasurable_fiberIntegral hv _ (measurable_torusOrdinaryGradient v).norm.ennreal_ofReal

/-- The inverse-gradient profile is integrable across values even when
critical levels have positive area. Its total mass counts only points
where the gradient is nonzero, and is at most the original Haar mass. -/
theorem lintegral_inverseGradientFiber_le_one {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    (∫⁻ t : ℝ, inverseGradientFiber v t) ≤ 1 := by
  have hw : Measurable (fun z ↦ ENNReal.ofReal (‖torusOrdinaryGradient v z‖⁻¹)) := by
    simpa only [Pi.inv_apply] using
      (measurable_torusOrdinaryGradient v).norm.inv.ennreal_ofReal
  rw [inverseGradientFiber, ← coarea hv _ hw]
  calc
    (∫⁻ z, ENNReal.ofReal ‖torusOrdinaryGradient v z‖ *
      ENNReal.ofReal (‖torusOrdinaryGradient v z‖⁻¹) ∂torusMeasure) ≤
      ∫⁻ _z : Torus, (1 : ℝ≥0∞) ∂torusMeasure := by
      apply lintegral_mono
      intro z
      change ENNReal.ofReal ‖torusOrdinaryGradient v z‖ *
        ENNReal.ofReal (‖torusOrdinaryGradient v z‖⁻¹) ≤ 1
      rw [← ENNReal.ofReal_mul (norm_nonneg _)]
      by_cases hz : ‖torusOrdinaryGradient v z‖ = 0
      · simp [hz]
      · simp [mul_inv_cancel₀ hz]
    _ = 1 := by simp

/-- The actual distribution has the inverse-gradient coarea density on
every measurable set of regular values. No conclusion about critical
atoms is needed or imposed. -/
theorem measure_preimage_regular {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {s : Set ℝ} (hs : MeasurableSet s)
    (hreg : ∀ t ∈ s, t ∉ StationarySard.torusCriticalValues v) :
    torusMeasure (v ⁻¹' s) = ∫⁻ t in s, inverseGradientFiber v t := by
  have hw : Measurable (fun z ↦ ENNReal.ofReal (‖torusOrdinaryGradient v z‖⁻¹)) := by
    simpa only [Pi.inv_apply] using
      (measurable_torusOrdinaryGradient v).norm.inv.ennreal_ofReal
  calc
    torusMeasure (v ⁻¹' s) = ∫⁻ _z in v ⁻¹' s, (1 : ℝ≥0∞) ∂torusMeasure := by simp
    _ = ∫⁻ z in v ⁻¹' s, ENNReal.ofReal ‖torusOrdinaryGradient v z‖ *
        ENNReal.ofReal (‖torusOrdinaryGradient v z‖⁻¹) ∂torusMeasure := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem ((continuous_of_contDiff_lift hv).measurable hs)] with z hz
      have hn : ‖torusOrdinaryGradient v z‖ ≠ 0 := by
        intro hzero
        exact hreg (v z) hz ⟨z, norm_eq_zero.mp hzero, rfl⟩
      rw [← ENNReal.ofReal_mul (norm_nonneg _), mul_inv_cancel₀ hn]
      simp
    _ = _ := coarea_preimage hv _ hw hs

theorem lintegral_gradientFluxFiber {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    (∫⁻ t : ℝ, gradientFluxFiber v t) =
      ∫⁻ z, ENNReal.ofReal (‖torusOrdinaryGradient v z‖ ^ 2) ∂torusMeasure := by
  rw [gradientFluxFiber, ← coarea hv _
    (measurable_torusOrdinaryGradient v).norm.ennreal_ofReal]
  apply lintegral_congr
  intro z
  rw [← ENNReal.ofReal_mul (norm_nonneg _), pow_two]

theorem lintegral_gradientFluxFiber_lt_top {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    (∫⁻ t : ℝ, gradientFluxFiber v t) < (∞ : ℝ≥0∞) := by
  rw [lintegral_gradientFluxFiber hv]
  have hi : Integrable (fun z ↦ ‖torusOrdinaryGradient v z‖ ^ 2) torusMeasure :=
    memLp_one_iff_integrable.mp (ContinuousMap.memLp (μ := torusMeasure) (p := 1) ℝ
      ⟨_, (continuous_norm_gradient hv).pow 2⟩)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun z ↦ sq_nonneg _)]
  exact ENNReal.ofReal_lt_top

private theorem ae_finite_of_lintegral_lt_top {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} (hm : AEMeasurable f μ)
    (hf : (∫⁻ x, f x ∂μ) < (∞ : ℝ≥0∞)) : ∀ᵐ x ∂μ, f x < (∞ : ℝ≥0∞) := by
  have hg : (∫⁻ x, hm.mk f x ∂μ) < (∞ : ℝ≥0∞) := by
    rw [← lintegral_congr_ae hm.ae_eq_mk]
    exact hf
  filter_upwards [ae_lt_top hm.measurable_mk hg.ne, hm.ae_eq_mk] with x hx he
  rwa [he]

private theorem integrable_real_of_lintegral_lt_top {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} (hm : AEMeasurable f μ)
    (hf : (∫⁻ x, f x ∂μ) < (∞ : ℝ≥0∞)) : Integrable (fun x ↦ (f x).toReal) μ := by
  refine ⟨hm.ennreal_toReal.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)).mpr
  calc
    (∫⁻ x, ENNReal.ofReal (f x).toReal ∂μ) = ∫⁻ x, f x ∂μ :=
      lintegral_congr_ae ((ae_finite_of_lintegral_lt_top hm hf).mono
        fun _ hx ↦ ENNReal.ofReal_toReal hx.ne)
    _ < (∞ : ℝ≥0∞) := hf

def inverseGradientDensity (v : Torus → ℝ) (t : ℝ) : ℝ :=
  (inverseGradientFiber v t).toReal

def gradientFluxDensity (v : Torus → ℝ) (t : ℝ) : ℝ :=
  (gradientFluxFiber v t).toReal

theorem integrable_inverseGradientDensity {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    Integrable (inverseGradientDensity v) volume :=
  integrable_real_of_lintegral_lt_top (aemeasurable_inverseGradientFiber hv)
    ((lintegral_inverseGradientFiber_le_one hv).trans_lt (by simp))

theorem integrable_gradientFluxDensity {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    Integrable (gradientFluxDensity v) volume :=
  integrable_real_of_lintegral_lt_top (aemeasurable_gradientFluxFiber hv)
    (lintegral_gradientFluxFiber_lt_top hv)

theorem inverseGradientDensity_eq_integral (v : Torus → ℝ) (t : ℝ) :
    inverseGradientDensity v t =
      ∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖⁻¹ ∂physicalCurveMeasure := by
  symm
  exact integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall fun _ ↦ inv_nonneg.mpr (norm_nonneg _))
    ((measurable_torusOrdinaryGradient v).norm.inv.aestronglyMeasurable)

theorem gradientFluxDensity_eq_integral (v : Torus → ℝ) (t : ℝ) :
    gradientFluxDensity v t =
      ∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖ ∂physicalCurveMeasure := by
  symm
  exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ((measurable_torusOrdinaryGradient v).norm.aestronglyMeasurable)

/-- These are genuine integrable fibre functions at almost every value,
not identities obtained solely from the totalized real integral. -/
theorem ae_integrable_level_weights {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    ∀ᵐ t : ℝ, IntegrableOn (fun z ↦ ‖torusOrdinaryGradient v z‖⁻¹)
        {z | v z = t} physicalCurveMeasure ∧
      IntegrableOn (fun z ↦ ‖torusOrdinaryGradient v z‖)
        {z | v z = t} physicalCurveMeasure := by
  have hi := ae_finite_of_lintegral_lt_top (aemeasurable_inverseGradientFiber hv)
    ((lintegral_inverseGradientFiber_le_one hv).trans_lt (by simp))
  have hg := ae_finite_of_lintegral_lt_top (aemeasurable_gradientFluxFiber hv)
    (lintegral_gradientFluxFiber_lt_top hv)
  filter_upwards [hi, hg] with t ht hk
  constructor
  · refine ⟨(measurable_torusOrdinaryGradient v).norm.inv.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun _ ↦ inv_nonneg.mpr (norm_nonneg _))).mpr ht
  · refine ⟨(measurable_torusOrdinaryGradient v).norm.aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun _ ↦ norm_nonneg _)).mpr hk

theorem rank_sub_eq_integral {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {a b : ℝ} (hab : a ≤ b)
    (hreg : ∀ t ∈ Ioc a b, t ∉ StationarySard.torusCriticalValues v) :
    rank v a - rank v b = ∫ t in Ioc a b, inverseGradientDensity v t := by
  have hvm := (continuous_of_contDiff_lift hv).measurable
  have hsub : {z | b < v z} ⊆ {z | a < v z} := fun _ hz ↦ hab.trans_lt hz
  have he : v ⁻¹' Ioc a b = {z | a < v z} \ {z | b < v z} := by
    ext z
    simp only [mem_preimage, mem_Ioc, Set.mem_sdiff, mem_ofPred_eq, not_lt]
  have hmass : torusMeasure.real (v ⁻¹' Ioc a b) = rank v a - rank v b := by
    rw [he, measureReal_sdiff hsub (measurableSet_lt measurable_const hvm)]
    rfl
  have hf := ae_finite_of_lintegral_lt_top (aemeasurable_inverseGradientFiber hv)
    ((lintegral_inverseGradientFiber_le_one hv).trans_lt (by simp))
  calc
    rank v a - rank v b = (torusMeasure (v ⁻¹' Ioc a b)).toReal := hmass.symm
    _ = (∫⁻ t in Ioc a b, inverseGradientFiber v t).toReal :=
      congrArg ENNReal.toReal (measure_preimage_regular hv measurableSet_Ioc hreg)
    _ = ∫ t in Ioc a b, inverseGradientDensity v t :=
      (integral_toReal (aemeasurable_inverseGradientFiber hv).restrict
        (ae_restrict_of_ae hf)).symm

theorem rank_eq_primitive_on_regular_interval {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {a b x : ℝ} (hx : x ∈ Icc a b)
    (hreg : ∀ t ∈ Icc a b, t ∉ StationarySard.torusCriticalValues v) :
    rank v x = rank v a - ∫ t in a..x, inverseGradientDensity v t := by
  have hh := rank_sub_eq_integral hv hx.1
    (fun t ht ↦ hreg t ⟨ht.1.le, ht.2.trans hx.2⟩)
  rw [intervalIntegral.integral_of_le hx.1]
  linarith

/-- The actual rank is absolutely continuous on every closed interval
of regular values. This follows from the proved coarea density identity;
absolute continuity of the global rank (which may have atoms) is not used. -/
theorem rank_absolutelyContinuous_regular_interval {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {a b : ℝ} (hab : a ≤ b)
    (hreg : ∀ t ∈ Icc a b, t ∉ StationarySard.torusCriticalValues v) :
    AbsolutelyContinuousOnInterval (rank v) a b := by
  have hi : IntervalIntegrable (inverseGradientDensity v) volume a b :=
    (integrable_inverseGradientDensity hv).intervalIntegrable
  have hI : AbsolutelyContinuousOnInterval
      (fun x ↦ ∫ t in a..x, inverseGradientDensity v t) a b :=
    hi.absolutelyContinuousOnInterval_intervalIntegral (c := a) (by simp)
  have hC : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ rank v a) a b :=
    contDiff_const.contDiffOn.absolutelyContinuousOnInterval
  have hP : AbsolutelyContinuousOnInterval
      (fun x ↦ rank v a - ∫ t in a..x, inverseGradientDensity v t) a b := by
    simpa only [Pi.sub_apply] using! hC.sub hI
  apply hP.congr
  intro x hx
  have hx' : x ∈ Icc a b := by simpa only [uIcc_of_le hab] using hx
  exact (rank_eq_primitive_on_regular_interval hv hx' hreg).symm

theorem ae_hasDerivAt_rank_regular_interval {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {a b : ℝ} (hreg : ∀ t ∈ Icc a b, t ∉ StationarySard.torusCriticalValues v) :
    ∀ᵐ t : ℝ, t ∈ Ioo a b → HasDerivAt (rank v) (-inverseGradientDensity v t) t := by
  filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral
      (integrable_inverseGradientDensity hv).locallyIntegrable]
    with t ht hi
  have hp : HasDerivAt
      (fun x ↦ rank v a - ∫ r in a..x, inverseGradientDensity v r)
      (-inverseGradientDensity v t) t := by
    simpa only [Pi.sub_apply, zero_sub] using! (hasDerivAt_const t (rank v a)).sub (ht a)
  apply hp.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds hi.1 hi.2] with x hx
  exact rank_eq_primitive_on_regular_interval hv hx hreg

/-- The additional differentiation exceptional set is proved null by a
countable local-to-global argument. This is explicitly an AE statement;
it does not assert continuity of the fibre density at every regular value. -/
theorem ae_hasDerivAt_rank_regular {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    ∀ᵐ t : ℝ, t ∉ StationarySard.torusCriticalValues v →
      HasDerivAt (rank v) (-inverseGradientDensity v t) t := by
  let E : Set ℝ := {t | t ∉ StationarySard.torusCriticalValues v ∧
    ¬HasDerivAt (rank v) (-inverseGradientDensity v t) t}
  have hlocal : ∀ t ∈ E, ∃ u ∈ 𝓝[E] t, volume (id '' u) = 0 := by
    intro t ht
    obtain ⟨ε, hε, hg⟩ := exists_regular_band_gradient_lower hv ht.1
    have hreg : ∀ r ∈ Icc (t - ε) (t + ε), r ∉ StationarySard.torusCriticalValues v := by
      intro r hr ⟨z, hz, hzr⟩
      have hn := hg z (by rw [hzr]; exact abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩)
      rw [hz, norm_zero] at hn
      exact (not_le_of_gt hε) hn
    refine ⟨E ∩ Ioo (t - ε) (t + ε), ?_, ?_⟩
    · exact inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds
        (Ioo_mem_nhds (by linarith) (by linarith)))
    · rw [image_id]
      apply measure_mono_null _ (ae_iff.mp (ae_hasDerivAt_rank_regular_interval hv hreg))
      intro r hr
      change ¬(r ∈ Ioo (t - ε) (t + ε) →
        HasDerivAt (rank v) (-inverseGradientDensity v r) r)
      intro hh
      exact hr.1.2 (hh hr.2)
  have hn : volume E = 0 := by
    simpa only [image_id] using (StationarySard.measure_image_null_of_locally_null hlocal)
  have he : {t | ¬(t ∉ StationarySard.torusCriticalValues v →
      HasDerivAt (rank v) (-inverseGradientDensity v t) t)} = E := by
    ext t
    simp only [E, mem_ofPred_eq, not_imp]
  rw [ae_iff, he]
  exact hn

theorem ae_rank_deriv_eq_level_integral {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    ∀ᵐ t : ℝ, t ∉ StationarySard.torusCriticalValues v →
      -deriv (rank v) t =
        ∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖⁻¹ ∂physicalCurveMeasure := by
  filter_upwards [ae_hasDerivAt_rank_regular hv] with t ht hr
  rw [(ht hr).deriv, neg_neg, inverseGradientDensity_eq_integral]

/-- The pushforward of physical Dirichlet energy has the actual
gradient-flux fibre density. This measure identity also justifies signed
test-function transport without an implicit Fubini or finiteness premise. -/
theorem map_gradientEnergy {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    (torusMeasure.withDensity (fun z ↦ ENNReal.ofReal (‖torusOrdinaryGradient v z‖ ^ 2))).map v =
      volume.withDensity (gradientFluxFiber v) := by
  ext1 s hs
  have hvm := (continuous_of_contDiff_lift hv).measurable
  rw [Measure.map_apply hvm hs, withDensity_apply _ (hvm hs), withDensity_apply _ hs]
  calc
    (∫⁻ z in v ⁻¹' s, ENNReal.ofReal (‖torusOrdinaryGradient v z‖ ^ 2) ∂torusMeasure) =
      ∫⁻ z in v ⁻¹' s, ENNReal.ofReal ‖torusOrdinaryGradient v z‖ *
        ENNReal.ofReal ‖torusOrdinaryGradient v z‖ ∂torusMeasure := by
      apply lintegral_congr
      intro z
      rw [pow_two, ENNReal.ofReal_mul (norm_nonneg _)]
    _ = _ := coarea_preimage hv _
      (measurable_torusOrdinaryGradient v).norm.ennreal_ofReal hs

theorem integral_gradientEnergy {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    (∫ z, φ (v z) * ‖torusOrdinaryGradient v z‖ ^ 2 ∂torusMeasure) =
      ∫ t : ℝ, φ t * gradientFluxDensity v t := by
  have hvm := (continuous_of_contDiff_lift hv).measurable
  have hgm : Measurable (fun z ↦ ENNReal.ofReal (‖torusOrdinaryGradient v z‖ ^ 2)) :=
    ((measurable_torusOrdinaryGradient v).norm.pow_const 2).ennreal_ofReal
  have hfin := ae_finite_of_lintegral_lt_top (aemeasurable_gradientFluxFiber hv)
    (lintegral_gradientFluxFiber_lt_top hv)
  calc
    (∫ z, φ (v z) * ‖torusOrdinaryGradient v z‖ ^ 2 ∂torusMeasure) =
      ∫ z, φ (v z) ∂torusMeasure.withDensity
        (fun z ↦ ENNReal.ofReal (‖torusOrdinaryGradient v z‖ ^ 2)) := by
      rw [integral_withDensity_eq_integral_toReal_smul hgm
        (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
      simp only [ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, mul_comm]
    _ = ∫ t, φ t ∂(torusMeasure.withDensity
        (fun z ↦ ENNReal.ofReal (‖torusOrdinaryGradient v z‖ ^ 2))).map v :=
      (integral_map_of_stronglyMeasurable hvm hφ.stronglyMeasurable).symm
    _ = ∫ t, φ t ∂volume.withDensity (gradientFluxFiber v) := by rw [map_gradientEnergy hv]
    _ = ∫ t, φ t * gradientFluxDensity v t := by
      rw [integral_withDensity_eq_integral_toReal_smul₀
        (aemeasurable_gradientFluxFiber hv) hfin]
      simp only [gradientFluxDensity, smul_eq_mul, mul_comm]

def lowerPrimitive (φ : ℝ → ℝ) (r : ℝ) : ℝ := ∫ t in Iio r, φ t

theorem lowerPrimitive_eq (φ : ℝ → ℝ) (hφ : Integrable φ) (r : ℝ) :
    lowerPrimitive φ r = lowerPrimitive φ 0 + ∫ t in (0 : ℝ)..r, φ t := by
  have he := intervalIntegral.integral_Iic_sub_Iic
    (a := (0 : ℝ)) (b := r) hφ.restrict hφ.restrict
  simp only [integral_Iic_eq_integral_Iio] at he
  change lowerPrimitive φ r - lowerPrimitive φ 0 = ∫ t in (0 : ℝ)..r, φ t at he
  linarith

theorem lowerPrimitive_hasDerivAt {φ : ℝ → ℝ} (hc : Continuous φ)
    (hi : Integrable φ) (r : ℝ) : HasDerivAt (lowerPrimitive φ) (φ r) r := by
  have he : lowerPrimitive φ = fun x ↦ lowerPrimitive φ 0 + ∫ t in (0 : ℝ)..x, φ t :=
    funext (lowerPrimitive_eq φ hi)
  rw [he]
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 r)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simpa only [Pi.add_apply, zero_add] using! (hasDerivAt_const r (lowerPrimitive φ 0)).add hd

theorem lowerPrimitive_contDiff {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hi : Integrable φ) : ContDiff ℝ ∞ (lowerPrimitive φ) := by
  apply contDiff_infty_iff_deriv.mpr
  refine ⟨fun r ↦ (lowerPrimitive_hasDerivAt hφ.continuous hi r).differentiableAt, ?_⟩
  have he : deriv (lowerPrimitive φ) = φ :=
    funext fun r ↦ (lowerPrimitive_hasDerivAt hφ.continuous hi r).deriv
  rw [he]
  exact hφ

/-- Actual Fubini for the lower primitive. Joint integrability follows
from the integrable product of the two absolute values before restricting
to the strict subgraph; no unsigned or formal interchange is used. -/
theorem lowerPrimitive_pair_integral {v w : Torus → ℝ} {φ : ℝ → ℝ}
    (hvm : Measurable v) (hwm : Measurable w) (hwi : Integrable w torusMeasure)
    (hφm : Measurable φ) (hφi : Integrable φ) :
    (∫ z, lowerPrimitive φ (v z) * w z ∂torusMeasure) =
      ∫ t : ℝ, φ t * ∫ z in {z | t < v z}, w z ∂torusMeasure := by
  let H : ℝ × Torus → ℝ := {p | p.1 < v p.2}.indicator (fun p ↦ φ p.1 * w p.2)
  have hS : MeasurableSet {p : ℝ × Torus | p.1 < v p.2} :=
    measurableSet_lt measurable_fst (hvm.comp measurable_snd)
  have hm : Measurable (fun p : ℝ × Torus ↦ φ p.1 * w p.2) :=
    (hφm.comp measurable_fst).mul (hwm.comp measurable_snd)
  have hb : Integrable (fun p : ℝ × Torus ↦ φ p.1 * w p.2)
      (volume.prod torusMeasure) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨Eventually.of_forall (fun t ↦ hwi.const_mul (φ t)), ?_⟩
    have he : (fun t ↦ ∫ z, ‖φ t * w z‖ ∂torusMeasure) =
        fun t ↦ ‖φ t‖ * ∫ z, ‖w z‖ ∂torusMeasure := by
      funext t
      simp only [norm_mul, integral_const_mul]
    rw [he]
    exact hφi.norm.mul_const _
  have hH : Integrable H (volume.prod torusMeasure) := hb.indicator hS
  have hleft (t : ℝ) : (∫ z, H (t, z) ∂torusMeasure) =
      φ t * ∫ z in {z | t < v z}, w z ∂torusMeasure := by
    rw [← integral_const_mul, ← integral_indicator (measurableSet_lt measurable_const hvm)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ by
      by_cases hz : t < v z <;> simp [H, hz]
  have hright (z : Torus) : (∫ t : ℝ, H (t, z)) = lowerPrimitive φ (v z) * w z := by
    rw [lowerPrimitive, ← integral_mul_const, ← integral_indicator measurableSet_Iio]
    apply integral_congr_ae
    exact Eventually.of_forall fun t ↦ by
      by_cases ht : t < v z <;> simp [H, ht]
  calc
    (∫ z, lowerPrimitive φ (v z) * w z ∂torusMeasure) =
      ∫ z, (∫ t : ℝ, H (t, z)) ∂torusMeasure :=
      integral_congr_ae (Eventually.of_forall fun z ↦ (hright z).symm)
    _ = ∫ t : ℝ, ∫ z, H (t, z) ∂torusMeasure :=
      (integral_integral_swap (f := fun t z ↦ H (t, z))
        (μ := volume) (ν := torusMeasure) hH).symm
    _ = _ := integral_congr_ae (Eventually.of_forall hleft)

/-- Measurability of the literal signed superlevel integral follows from
the jointly measurable strict-subgraph indicator. -/
theorem measurable_superlevel_integral {v w : Torus → ℝ}
    (hv : Measurable v) (hw : Measurable w) :
    Measurable (fun t : ℝ ↦ ∫ z in {z | t < v z}, w z ∂torusMeasure) := by
  let H : ℝ × Torus → ℝ := {p | p.1 < v p.2}.indicator (fun p ↦ w p.2)
  have hS : MeasurableSet {p : ℝ × Torus | p.1 < v p.2} :=
    measurableSet_lt measurable_fst (hv.comp measurable_snd)
  have hm : Measurable H := (hw.comp measurable_snd).indicator hS
  have he (t : ℝ) : (∫ z, H (t, z) ∂torusMeasure) =
      ∫ z in {z | t < v z}, w z ∂torusMeasure := by
    rw [← integral_indicator (measurableSet_lt measurable_const hv)]
    apply integral_congr_ae
    exact Eventually.of_forall fun z ↦ by
      by_cases hz : t < v z <;> simp [H, hz]
  have hM : Measurable (fun t : ℝ ↦ ∫ z, H (t, z) ∂torusMeasure) :=
    (show StronglyMeasurable (Function.uncurry (fun t z ↦ H (t, z))) from
      hm.stronglyMeasurable).integral_prod_right.measurable
  simpa only [he] using hM

theorem norm_superlevel_integral_le {v w : Torus → ℝ}
    (hv : Measurable v) (hw : Integrable w torusMeasure) (t : ℝ) :
    ‖∫ z in {z | t < v z}, w z ∂torusMeasure‖ ≤ ∫ z, ‖w z‖ ∂torusMeasure := by
  have hS : MeasurableSet {z | t < v z} := measurableSet_lt measurable_const hv
  rw [← integral_indicator hS]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_ae (hw.indicator hS).norm hw.norm
  filter_upwards with z
  by_cases hz : t < v z
  · simp only [Set.indicator_of_mem (show z ∈ {z | t < v z} from hz)]
    exact le_rfl
  · simp only [Set.indicator_of_notMem (show z ∉ {z | t < v z} from hz), norm_zero]
    exact norm_nonneg _

theorem locallyIntegrable_superlevel_integral {v w : Torus → ℝ}
    (hv : Measurable v) (hwm : Measurable w) (hwi : Integrable w torusMeasure) :
    LocallyIntegrable (fun t : ℝ ↦ ∫ z in {z | t < v z}, w z ∂torusMeasure) := by
  apply (locallyIntegrable_const (μ := volume) (∫ z, ‖w z‖ ∂torusMeasure)).mono
    (measurable_superlevel_integral hv hwm).aestronglyMeasurable
  filter_upwards with t
  rw [Real.norm_of_nonneg (integral_nonneg fun z ↦ norm_nonneg (w z))]
  exact norm_superlevel_integral_le hv hwi t

theorem locallyIntegrable_superlevel_source {v : Torus → ℝ} (hv : Continuous v) :
    LocallyIntegrable (fun t : ℝ ↦ superlevelMass v t - rank v t) := by
  have hc : Continuous (fun z ↦ Real.exp (v z) - 1) :=
    (Real.continuous_exp.comp hv).sub continuous_const
  simpa only [superlevel_source_integral hv] using
    locallyIntegrable_superlevel_integral hv.measurable hc.measurable
      (continuous_integrable hc)

/-- Compact smooth tests identify the actual physical level flux with
the PDE superlevel expression. The primitive is constructed explicitly;
the signed interchange uses the proved product-integrability lemma. -/
theorem stationary_flux_test {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ t : ℝ, φ t * gradientFluxDensity v t) =
      ∫ t : ℝ, φ t * (ρ * (superlevelMass v t - rank v t)) := by
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  have hvc := continuous_of_contDiff_lift hv1
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hc
  have hwc : Continuous (fun z ↦ Real.exp (v z) - 1) :=
    (Real.continuous_exp.comp hvc).sub continuous_const
  calc
    (∫ t : ℝ, φ t * gradientFluxDensity v t) =
        ∫ z, φ (v z) * ‖torusOrdinaryGradient v z‖ ^ 2 ∂torusMeasure :=
      (integral_gradientEnergy hv1 φ hφ.continuous.measurable).symm
    _ = ∫ z, deriv (lowerPrimitive φ) (v z) *
        ‖torusOrdinaryGradient v z‖ ^ 2 ∂torusMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z ↦ by
        change φ (v z) * ‖torusOrdinaryGradient v z‖ ^ 2 =
          deriv (lowerPrimitive φ) (v z) * ‖torusOrdinaryGradient v z‖ ^ 2
        rw [(lowerPrimitive_hasDerivAt hφ.continuous hφi (v z)).deriv]
    _ = ρ * ∫ z, lowerPrimitive φ (v z) * (Real.exp (v z) - 1) ∂torusMeasure :=
      stationary_weak_flux hv hpde (lowerPrimitive_contDiff hφ hφi)
    _ = ρ * ∫ t : ℝ, φ t *
        ∫ z in {z | t < v z}, Real.exp (v z) - 1 ∂torusMeasure := by
      rw [lowerPrimitive_pair_integral hvc.measurable hwc.measurable
        (continuous_integrable hwc) hφ.continuous.measurable hφi]
    _ = ∫ t : ℝ, φ t * (ρ * (superlevelMass v t - rank v t)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall fun t ↦ by
        change ρ * (φ t * ∫ z in {z | t < v z}, Real.exp (v z) - 1 ∂torusMeasure) =
          φ t * (ρ * (superlevelMass v t - rank v t))
        rw [superlevel_source_integral hvc t]
        ring

/-- Actual Hausdorff boundary flux for almost every value, derived from
the PDE and coarea. This theorem does not assert the additional continuity
of the fibre profile needed to upgrade the identity to every regular value. -/
theorem ae_stationary_level_flux {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1)) :
    ∀ᵐ t : ℝ, (∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖ ∂physicalCurveMeasure) =
      ρ * (superlevelMass v t - rank v t) := by
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  have hl : LocallyIntegrable (gradientFluxDensity v) :=
    (integrable_gradientFluxDensity hv1).locallyIntegrable
  have hr : LocallyIntegrable (fun t : ℝ ↦ ρ * (superlevelMass v t - rank v t)) := by
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      (locallyIntegrable_superlevel_source (continuous_of_contDiff_lift hv1)).smul ρ
  have he := ae_eq_of_integral_contDiff_smul_eq hl hr (fun φ hφ hc ↦ by
    simpa only [smul_eq_mul] using stationary_flux_test hv hpde hφ hc)
  simpa only [gradientFluxDensity_eq_integral] using he

/-- Both literal level identities and their true integrability hold off
one null set of values. Sard removes the actual critical values; the
additional exceptional values arise from one-dimensional differentiation
and equality of locally integrable functions as distributions. -/
theorem ae_stationary_level_identities {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1)) :
    ∀ᵐ t : ℝ, t ∉ StationarySard.torusCriticalValues v ∧
      IntegrableOn (fun z ↦ ‖torusOrdinaryGradient v z‖⁻¹) {z | v z = t} physicalCurveMeasure ∧
      IntegrableOn (fun z ↦ ‖torusOrdinaryGradient v z‖) {z | v z = t} physicalCurveMeasure ∧
      HasDerivAt (rank v)
        (-(∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖⁻¹ ∂physicalCurveMeasure)) t ∧
      (∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖ ∂physicalCurveMeasure) =
        ρ * (superlevelMass v t - rank v t) := by
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  have hcrit : ∀ᵐ t : ℝ, t ∉ StationarySard.torusCriticalValues v := by
    rw [ae_iff, show {t | ¬t ∉ StationarySard.torusCriticalValues v} =
      StationarySard.torusCriticalValues v by ext t; simp]
    exact StationarySard.volume_torusCriticalValues_eq_zero hv
  filter_upwards [hcrit, ae_integrable_level_weights hv1,
    ae_hasDerivAt_rank_regular hv1, ae_stationary_level_flux hv hpde] with t ht hi hd hf
  refine ⟨ht, hi.1, hi.2, ?_, hf⟩
  simpa only [inverseGradientDensity_eq_integral] using hd ht

/-- A measurable exceptional set is constructed from the proved AE
identities. It contains the literal critical-value set, but is not claimed
to consist only of critical values. This is the explicit exceptional-value
adaptation, not a pointwise regular-level theorem. -/
theorem exists_null_exceptional_values {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1)) :
    ∃ C : Set ℝ, MeasurableSet C ∧ volume C = 0 ∧
      StationarySard.torusCriticalValues v ⊆ C ∧
      ∀ t ∉ C,
        IntegrableOn (fun z ↦ ‖torusOrdinaryGradient v z‖⁻¹) {z | v z = t} physicalCurveMeasure ∧
        IntegrableOn (fun z ↦ ‖torusOrdinaryGradient v z‖) {z | v z = t} physicalCurveMeasure ∧
        HasDerivAt (rank v)
          (-(∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖⁻¹ ∂physicalCurveMeasure)) t ∧
        (∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖ ∂physicalCurveMeasure) =
          ρ * (superlevelMass v t - rank v t) := by
  let P : ℝ → Prop := fun t ↦ t ∉ StationarySard.torusCriticalValues v ∧
    IntegrableOn (fun z ↦ ‖torusOrdinaryGradient v z‖⁻¹) {z | v z = t} physicalCurveMeasure ∧
    IntegrableOn (fun z ↦ ‖torusOrdinaryGradient v z‖) {z | v z = t} physicalCurveMeasure ∧
    HasDerivAt (rank v)
      (-(∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖⁻¹ ∂physicalCurveMeasure)) t ∧
    (∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖ ∂physicalCurveMeasure) =
      ρ * (superlevelMass v t - rank v t)
  have hP : ∀ᵐ t : ℝ, P t := ae_stationary_level_identities hv hpde
  have hn : volume {t | ¬P t} = 0 := ae_iff.mp hP
  refine ⟨toMeasurable volume {t | ¬P t}, measurableSet_toMeasurable _ _, ?_, ?_, ?_⟩
  · exact (measure_toMeasurable (μ := volume) _).trans hn
  · intro t ht
    apply subset_toMeasurable
    exact fun hp ↦ hp.1 ht
  · intro t ht
    have hp : P t := by
      by_contra hn
      exact ht (subset_toMeasurable volume {t | ¬P t} hn)
    exact hp.2

/-- The already proved physical boundary-layer limit is identified with
the actual H1 level integral at almost every value, with the exceptional
set arising from the two preceding proved identities. -/
theorem ae_boundaryLayer_tendsto_level_flux {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1)) :
    ∀ᵐ t : ℝ, Tendsto (fun n : ℕ ↦ ∫ z,
      ((n : ℝ) * superlevelCutoff t n (v z) * (1 - superlevelCutoff t n (v z))) *
        ‖torusOrdinaryGradient v z‖ ^ 2 ∂torusMeasure) atTop
      (𝓝 (∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖ ∂physicalCurveMeasure)) := by
  filter_upwards [ae_stationary_level_identities hv hpde] with t ht
  rw [ht.2.2.2.2]
  exact stationary_superlevel_flux_limit hv hpde ht.1

/-- Cauchy--Schwarz with reciprocal weights also proves finiteness of the
underlying measure. No finite-measure assumption is used to manufacture an
integrable constant in this argument. -/
theorem measure_sq_le_integral_mul_integral_inv {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : α → ℝ} (hm : Measurable g) (hp : ∀ᵐ x ∂μ, 0 < g x)
    (hg : Integrable g μ) (hi : Integrable (fun x ↦ (g x)⁻¹) μ) :
    μ univ < (∞ : ℝ≥0∞) ∧
      (μ.real univ) ^ 2 ≤ (∫ x, g x ∂μ) * ∫ x, (g x)⁻¹ ∂μ := by
  have hsq : (fun x ↦ Real.sqrt (g x) ^ 2) =ᵐ[μ] g := by
    filter_upwards [hp] with x hx
    exact Real.sq_sqrt hx.le
  have hisq : (fun x ↦ Real.sqrt ((g x)⁻¹) ^ 2) =ᵐ[μ] fun x ↦ (g x)⁻¹ := by
    filter_upwards [hp] with x hx
    exact Real.sq_sqrt (inv_nonneg.mpr hx.le)
  have hL : MemLp (fun x ↦ Real.sqrt (g x)) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.measurable.comp hm).aestronglyMeasurable).mpr
        (hg.congr hsq.symm)
  have hR : MemLp (fun x ↦ Real.sqrt ((g x)⁻¹)) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.measurable.comp hm.inv).aestronglyMeasurable).mpr
        (hi.congr hisq.symm)
  have hprod : (fun x ↦ Real.sqrt (g x) * Real.sqrt ((g x)⁻¹)) =ᵐ[μ]
      fun _ ↦ (1 : ℝ) := by
    filter_upwards [hp] with x hx
    rw [← Real.sqrt_mul hx.le, mul_inv_cancel₀ hx.ne', Real.sqrt_one]
  have hmul : Integrable (fun x ↦ Real.sqrt (g x) * Real.sqrt ((g x)⁻¹)) μ := by
    simpa only [Pi.mul_apply] using! hL.integrable_mul hR
  have hone : Integrable (fun _ : α ↦ (1 : ℝ)) μ := hmul.congr hprod
  have hfin : μ univ < (∞ : ℝ≥0∞) := by
    have hh := (hasFiniteIntegral_iff_ofReal
      (Eventually.of_forall fun _ : α ↦ (by norm_num : (0 : ℝ) ≤ 1))).mp hone.hasFiniteIntegral
    simpa using hh
  refine ⟨hfin, ?_⟩
  have hconj : (2 : ℝ).HolderConjugate 2 := by constructor <;> norm_num
  have hL' : MemLp (fun x ↦ Real.sqrt (g x)) (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hL
  have hR' : MemLp (fun x ↦ Real.sqrt ((g x)⁻¹)) (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hR
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (Eventually.of_forall fun x ↦ Real.sqrt_nonneg (g x))
    (Eventually.of_forall fun x ↦ Real.sqrt_nonneg ((g x)⁻¹)) hL' hR'
  simp only [Real.rpow_two] at hh
  rw [integral_congr_ae hprod, integral_congr_ae hsq, integral_congr_ae hisq] at hh
  simp only [integral_const, smul_eq_mul, mul_one, ← Real.sqrt_eq_rpow] at hh
  have hn : 0 ≤ ∫ x, g x ∂μ := integral_nonneg_of_ae (hp.mono fun _ hx ↦ hx.le)
  have hni : 0 ≤ ∫ x, (g x)⁻¹ ∂μ :=
    integral_nonneg_of_ae (hp.mono fun _ hx ↦ inv_nonneg.mpr hx.le)
  have hpow := pow_le_pow_left₀ (ENNReal.toReal_nonneg : 0 ≤ μ.real univ) hh 2
  simpa only [mul_pow, Real.sq_sqrt hn, Real.sq_sqrt hni] using! hpow

/-- Actual physical level-length Cauchy--Schwarz. The positivity follows
from the literal regular-value condition, and both integrability hypotheses
are supplied almost everywhere by the proved coarea theorem. -/
theorem level_cauchy_schwarz {v : Torus → ℝ} {t : ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (ht : t ∉ StationarySard.torusCriticalValues v)
    (hi : IntegrableOn (fun z ↦ ‖torusOrdinaryGradient v z‖⁻¹)
      {z | v z = t} physicalCurveMeasure)
    (hg : IntegrableOn (fun z ↦ ‖torusOrdinaryGradient v z‖)
      {z | v z = t} physicalCurveMeasure) :
    physicalCurveMeasure {z | v z = t} < (∞ : ℝ≥0∞) ∧
      (physicalCurveMeasure.real {z | v z = t}) ^ 2 ≤
        (∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖ ∂physicalCurveMeasure) *
          ∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖⁻¹ ∂physicalCurveMeasure := by
  have hS : MeasurableSet {z | v z = t} :=
    (measurableSet_singleton t).preimage (continuous_of_contDiff_lift hv).measurable
  have hp : ∀ᵐ z ∂physicalCurveMeasure.restrict {z | v z = t},
      0 < ‖torusOrdinaryGradient v z‖ := by
    filter_upwards [ae_restrict_mem hS] with z hz
    apply norm_pos_iff.mpr
    exact fun hzero ↦ ht ⟨z, hzero, hz⟩
  have hh := measure_sq_le_integral_mul_integral_inv
    (measurable_torusOrdinaryGradient v).norm hp hg hi
  simpa only [Measure.real, Measure.restrict_apply_univ] using hh

/-- The source Cauchy--Schwarz bound, before the separate physical torus
isoperimetric inequality. It is derived for the actual rank and actual H1
length at almost every value, without a geometric bound as a premise. -/
theorem ae_level_length_squared_le_flux_rank {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1)) :
    ∀ᵐ t : ℝ, physicalCurveMeasure {z | v z = t} < (∞ : ℝ≥0∞) ∧
      (physicalCurveMeasure.real {z | v z = t}) ^ 2 ≤
        ρ * (superlevelMass v t - rank v t) * (-deriv (rank v) t) := by
  filter_upwards [ae_stationary_level_identities hv hpde] with t ht
  have hh := level_cauchy_schwarz (hv.of_le (by simp)) ht.1 ht.2.1 ht.2.2.1
  refine ⟨hh.1, ?_⟩
  rw [ht.2.2.2.1.deriv, neg_neg]
  simpa only [ht.2.2.2.2] using hh.2

end PeriodicAttractiveLogGas.StationaryCoarea
