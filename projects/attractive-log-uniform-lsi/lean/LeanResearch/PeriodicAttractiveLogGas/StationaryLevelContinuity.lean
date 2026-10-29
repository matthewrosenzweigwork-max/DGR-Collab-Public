import LeanResearch.PeriodicAttractiveLogGas.StationaryLevelBoundary
import Mathlib.Topology.PartitionOfUnity
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Continuity of actual regular-level integrals

This unit develops the pointwise regular-value upgrade needed in the
stationary argument.  The curve measure is the physical Euclidean
Hausdorff measure from `StationaryCoarea`, not the default product metric.
The local area formula is deduced from the genuine injective chart
sections and the attributed lower-dimensional area theorem in
`Imported.ProbabilityApproximation.ScalarCoarea`.

Development checks and the precise remaining scope are recorded in
`research/reviews/stationary-level-continuity-development.md`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ENNReal ContDiff

namespace PeriodicAttractiveLogGas.StationaryLevelContinuity

open StationarySard StationaryDistribution StationaryLevelGeometry StationaryCoarea
  StationaryLevelBoundary

/-- The actual torus curve measure agrees with planar curve measure on
every subset of a physical quotient-isometry ball. -/
theorem torusQuotient_curve_image {a : PlanarSpace} {s : Set PlanarSpace}
    (hs : s ⊆ Metric.ball a (1 / 8 : ℝ)) :
    physicalCurveMeasure (torusQuotient '' s) =
      (Measure.euclideanHausdorffMeasure 1 : Measure PlanarSpace) s := by
  unfold physicalCurveMeasure
  rw [physicalEquiv.symm.measurableEmbedding.map_apply]
  have he : physicalEquiv.symm ⁻¹' (torusQuotient '' s) = physicalQuotient '' s := by
    ext z
    constructor
    · rintro ⟨x, hx, he⟩
      refine ⟨x, hx, ?_⟩
      change physicalEquiv (torusQuotient x) = z
      rw [he, MeasurableEquiv.apply_symm_apply]
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, by simp only [physicalQuotient, MeasurableEquiv.symm_apply_apply]⟩
  rw [he]
  exact physicalQuotient_curve_image hs

/-- Local measure transport, including arbitrary measurable pieces of a
level fibre. No new definition of the torus curve measure is introduced. -/
theorem map_torusQuotient_curveMeasure_small {a : PlanarSpace} {s : Set PlanarSpace}
    (hs : s ⊆ Metric.ball a (1 / 8 : ℝ)) :
    ((Measure.euclideanHausdorffMeasure 1 : Measure PlanarSpace).restrict s).map
        torusQuotient = physicalCurveMeasure.restrict (torusQuotient '' s) := by
  ext1 t ht
  have hq := isOpenQuotientMap_torusQuotient.continuous.measurable
  rw [Measure.map_apply hq ht, Measure.restrict_apply (hq ht), Measure.restrict_apply ht]
  rw [← torusQuotient_curve_image (inter_subset_right.trans hs), image_preimage_inter]

section ChartArea

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [FiniteDimensional ℝ K] [MeasurableSpace K] [BorelSpace K]

/-- The actual weighted physical H1 formula for any injective immersed
one-dimensional chart section lying in a quotient-isometry ball. The
derivative and injectivity data are supplied below by constructed regular
charts, not postulated as a final source hypothesis. -/
theorem chart_lintegral {θ : K → PlanarSpace} {Dθ : K → K →L[ℝ] PlanarSpace}
    {s : Set K} {a : PlanarSpace}
    (hdim : Module.finrank ℝ K = 1) (hs : MeasurableSet s)
    (hθ : ∀ y ∈ s, HasFDerivWithinAt θ (Dθ y) s y)
    (hDθ : ∀ y ∈ s, Function.Injective (Dθ y)) (hinj : InjOn θ s)
    (hsmall : ∀ y ∈ s, θ y ∈ Metric.ball a (1 / 8 : ℝ))
    (w : Torus → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ z in (fun y ↦ torusQuotient (θ y)) '' s, w z ∂physicalCurveMeasure) =
      ∫⁻ y in s, ENNReal.ofReal (Dθ y).toLinearMap.normDet *
        w (torusQuotient (θ y)) := by
  have himage : (fun y ↦ torusQuotient (θ y)) '' s = torusQuotient '' (θ '' s) := by
    rw [image_image]
  have hb : θ '' s ⊆ Metric.ball a (1 / 8 : ℝ) := by
    rintro x ⟨y, hy, rfl⟩
    exact hsmall y hy
  rw [himage, ← map_torusQuotient_curveMeasure_small hb]
  rw [lintegral_map' hw.aemeasurable
    isOpenQuotientMap_torusQuotient.continuous.measurable.aemeasurable]
  have harea :=
    ProbabilityTheory.lintegral_image_eq_lintegral_normDet_fderivWithin_mul
      hs hθ hDθ hinj (fun x ↦ w (torusQuotient x))
      (hw.comp isOpenQuotientMap_torusQuotient.continuous.measurable)
  rw [hdim] at harea
  exact harea

/-- Specialization to the actual value-coordinate chart. Its full-rank
area data follow by differentiating the kernel-coordinate identity. -/
theorem regular_chart_lintegral {P : PlanarSpace →L[ℝ] K} {a : PlanarSpace}
    {e : OpenPartialHomeomorph PlanarSpace (ℝ × K)} {U : Set (ℝ × K)}
    (hdim : Module.finrank ℝ K = 1) (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 (e.symm : (ℝ × K) → PlanarSpace) U)
    (hcoord : ∀ p ∈ U, P (e.symm p - a) = p.2)
    (hsmall : ∀ p ∈ U, e.symm p ∈ Metric.ball a (1 / 8 : ℝ))
    (r : ℝ) (w : Torus → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ z in (fun y ↦ torusQuotient (e.symm (r, y))) '' {y | (r, y) ∈ U},
      w z ∂physicalCurveMeasure) =
      ∫⁻ y in {y | (r, y) ∈ U},
        ENNReal.ofReal (fderiv ℝ (fun z ↦ e.symm (r, z)) y).toLinearMap.normDet *
          w (torusQuotient (e.symm (r, y))) := by
  have hsection := chartSection_immersion hU hG hcoord r
  have hS : IsOpen {y : K | (r, y) ∈ U} :=
    hU.preimage (continuous_const.prodMk continuous_id)
  apply chart_lintegral hdim hS.measurableSet _ hsection.2.2 hsection.2.1
    (fun y hy ↦ hsmall (r, y) hy) w hw
  intro y hy
  exact ((hsection.1.contDiffAt (hS.mem_nhds hy)).differentiableAt
    (by norm_num)).hasFDerivAt.hasFDerivWithinAt

end ChartArea

/-- A compactly supported local expression extends continuously by zero
across the boundary of its open domain. This is used for actual chart
weights after their support has been proved to lie in a compact subchart. -/
theorem continuous_zero_extension {X : Type*} [TopologicalSpace X] [T2Space X]
    {U C : Set X} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U)
    {g : X → ℝ} (hg : ContinuousOn g U)
    (hzero : ∀ x ∈ U, x ∉ C → g x = 0) :
    Continuous (U.indicator g) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x ∈ U
  · apply (hg.continuousAt (hU.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hx] with y hy
    exact Set.indicator_of_mem hy g
  · have hxC : x ∉ C := fun h ↦ hx (hCU h)
    apply (continuousAt_const : ContinuousAt (fun _ : X ↦ (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [hC.isClosed.isOpen_compl.mem_nhds hxC] with y hy
    by_cases hyU : y ∈ U
    · rw [Set.indicator_of_mem hyU]
      exact hzero y hyU hy
    · exact Set.indicator_of_notMem hyU g

/-- The same zero extension has genuine compact support. -/
theorem compactSupport_zero_extension {X : Type*} [TopologicalSpace X] [T2Space X]
    {U C : Set X} (hC : IsCompact C) {g : X → ℝ}
    (hzero : ∀ x ∈ U, x ∉ C → g x = 0) :
    HasCompactSupport (U.indicator g) := by
  classical
  have hs : Function.support (U.indicator g) ⊆ C := by
    intro x hx
    by_contra hxC
    apply hx
    by_cases hxU : x ∈ U
    · rw [Set.indicator_of_mem hxU]
      exact hzero x hxU hxC
    · exact Set.indicator_of_notMem hxU g
  exact hC.of_isClosed_subset isClosed_closure (closure_minimal hs hC.isClosed)

section CompactParameter

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [FiniteDimensional ℝ K] [MeasurableSpace K] [BorelSpace K]

/-- A jointly continuous compactly supported chart integrand is
integrable on every section, with continuous real parameter integral. -/
theorem compact_parameter_integral {H : ℝ × K → ℝ} {C : Set (ℝ × K)}
    (hH : Continuous H) (hC : IsCompact C) (hs : Function.support H ⊆ C) :
    (∀ r : ℝ, Integrable (fun y : K ↦ H (r, y)) volume) ∧
      Continuous (fun r : ℝ ↦ ∫ y : K, H (r, y)) := by
  let D : Set K := Prod.snd '' C
  have hD : IsCompact D := hC.image continuous_snd
  have hzero (r : ℝ) (y : K) (hy : y ∉ D) : H (r, y) = 0 := by
    by_contra hn
    exact hy ⟨(r, y), hs hn, rfl⟩
  have hsection (r : ℝ) : Continuous (fun y : K ↦ H (r, y)) :=
    hH.comp (continuous_const.prodMk continuous_id)
  have hc (r : ℝ) : HasCompactSupport (fun y : K ↦ H (r, y)) := by
    apply hD.of_isClosed_subset isClosed_closure
    apply closure_minimal _ hD.isClosed
    intro y hy
    by_contra hyD
    exact hy (hzero r y hyD)
  refine ⟨fun r ↦ (hsection r).integrable_of_hasCompactSupport (hc r), ?_⟩
  apply continuousOn_univ.mp
  apply continuousOn_integral_of_compact_support
    (f := fun r y ↦ H (r, y)) (s := univ) hD hH.continuousOn
  intro r y _ hy
  exact hzero r y hy

end CompactParameter

section CompactChart

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [FiniteDimensional ℝ K] [MeasurableSpace K] [BorelSpace K]

/-- The derivative in the kernel variable, expressed using a fixed linear
inclusion so that its dependence on both coordinates is explicit. -/
def sectionDerivative (G : ℝ × K → PlanarSpace) (p : ℝ × K) : K →L[ℝ] PlanarSpace :=
  (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ ℝ K)

def sectionJacobian (G : ℝ × K → PlanarSpace) (p : ℝ × K) : ℝ :=
  (sectionDerivative G p).toLinearMap.normDet

omit [FiniteDimensional ℝ K] [MeasurableSpace K] [BorelSpace K] in
theorem sectionDerivative_eq {G : ℝ × K → PlanarSpace} {U : Set (ℝ × K)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U) {p : ℝ × K} (hp : p ∈ U) :
    sectionDerivative G p = fderiv ℝ (fun y : K ↦ G (p.1, y)) p.2 := by
  have hinc : HasFDerivAt (fun y : K ↦ (p.1, y))
      (ContinuousLinearMap.inr ℝ ℝ K) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have hd : HasFDerivAt (fun y : K ↦ G (p.1, y)) (sectionDerivative G p) p.2 := by
    simpa only [sectionDerivative, Function.comp_def] using!
      ((hG.contDiffAt (hU.mem_nhds hp)).differentiableAt (by norm_num)).hasFDerivAt.comp
        p.2 hinc
  exact hd.fderiv.symm

omit [MeasurableSpace K] [BorelSpace K] in
theorem continuousOn_sectionJacobian {G : ℝ × K → PlanarSpace} {U : Set (ℝ × K)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U) :
    ContinuousOn (sectionJacobian G) U := by
  intro p hp
  have hD : ContinuousAt (fderiv ℝ G) p :=
    (hG.contDiffAt (hU.mem_nhds hp)).continuousAt_fderiv one_ne_zero
  have hS : ContinuousAt (sectionDerivative G) p := hD.clm_comp continuousAt_const
  exact (ProbabilityTheory.continuous_normDet.continuousAt.comp hS).continuousWithinAt

omit [MeasurableSpace K] [BorelSpace K] in
theorem sectionJacobian_nonneg (G : ℝ × K → PlanarSpace) (p : ℝ × K) :
    0 ≤ sectionJacobian G p := (sectionDerivative G p).toLinearMap.normDet_nonneg

omit [InnerProductSpace ℝ K] [FiniteDimensional ℝ K] [MeasurableSpace K] [BorelSpace K] in
/-- A torus weight supported in the compact subchart pulls back to zero
off that same compact target set. Both quotient and chart injectivity are
used explicitly; no compact-preimage assertion is assumed. -/
theorem chart_weight_vanishes {a : PlanarSpace}
    {e : OpenPartialHomeomorph PlanarSpace (ℝ × K)} {U C : Set (ℝ × K)}
    (hCU : C ⊆ U) (hUt : U ⊆ e.target)
    (hsmall : ∀ p ∈ U, e.symm p ∈ Metric.ball a (1 / 8 : ℝ))
    {w : Torus → ℝ} (hws : Function.support w ⊆ torusQuotient '' (e.symm '' C))
    {p : ℝ × K} (hp : p ∈ U) (hpC : p ∉ C) :
    w (torusQuotient (e.symm p)) = 0 := by
  by_contra hn
  obtain ⟨x, ⟨q, hq, rfl⟩, heq⟩ := hws hn
  have hphys : physicalQuotient (e.symm q) = physicalQuotient (e.symm p) :=
    congrArg physicalEquiv heq
  have hsub : (⟨e.symm q, hsmall q (hCU hq)⟩ : Metric.ball a (1 / 8 : ℝ)) =
      ⟨e.symm p, hsmall p hp⟩ := (physicalQuotient_isometry_ball a).injective hphys
  have he := congrArg e (congrArg Subtype.val hsub)
  rw [e.right_inv (hUt (hCU hq)), e.right_inv (hUt hp)] at he
  exact hpC (he ▸ hq)

/-- The genuine chart Jacobian times a spatial weight, extended by zero
outside the open coordinate domain. -/
def chartIntegrand (e : OpenPartialHomeomorph PlanarSpace (ℝ × K))
    (U : Set (ℝ × K)) (w : Torus → ℝ) : ℝ × K → ℝ :=
  U.indicator (fun p ↦ sectionJacobian e.symm p * w (torusQuotient (e.symm p)))

omit [MeasurableSpace K] [BorelSpace K] in
theorem chartIntegrand_support {a : PlanarSpace}
    {e : OpenPartialHomeomorph PlanarSpace (ℝ × K)} {U C : Set (ℝ × K)}
    (hCU : C ⊆ U) (hUt : U ⊆ e.target)
    (hsmall : ∀ p ∈ U, e.symm p ∈ Metric.ball a (1 / 8 : ℝ))
    {w : Torus → ℝ} (hws : Function.support w ⊆ torusQuotient '' (e.symm '' C)) :
    Function.support (chartIntegrand e U w) ⊆ C := by
  classical
  intro p hp
  by_contra hpC
  apply hp
  by_cases hpU : p ∈ U
  · rw [chartIntegrand, Set.indicator_of_mem hpU,
      chart_weight_vanishes hCU hUt hsmall hws hpU hpC, mul_zero]
  · exact Set.indicator_of_notMem hpU _

omit [MeasurableSpace K] [BorelSpace K] in
theorem continuous_chartIntegrand {a : PlanarSpace}
    {e : OpenPartialHomeomorph PlanarSpace (ℝ × K)} {U C : Set (ℝ × K)}
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U) (hUt : U ⊆ e.target)
    (hG : ContDiffOn ℝ 1 (e.symm : (ℝ × K) → PlanarSpace) U)
    (hsmall : ∀ p ∈ U, e.symm p ∈ Metric.ball a (1 / 8 : ℝ))
    {w : Torus → ℝ} (hw : Continuous w)
    (hws : Function.support w ⊆ torusQuotient '' (e.symm '' C)) :
    Continuous (chartIntegrand e U w) := by
  apply continuous_zero_extension hU hC hCU
  · exact (continuousOn_sectionJacobian hU hG).mul
      (hw.comp_continuousOn
        (isOpenQuotientMap_torusQuotient.continuous.comp_continuousOn hG.continuousOn))
  · intro p hp hpC
    rw [chart_weight_vanishes hCU hUt hsmall hws hp hpC, mul_zero]

omit [MeasurableSpace K] [BorelSpace K] in
theorem chartIntegrand_nonneg (e : OpenPartialHomeomorph PlanarSpace (ℝ × K))
    (U : Set (ℝ × K)) {w : Torus → ℝ} (hw : ∀ z, 0 ≤ w z) (p : ℝ × K) :
    0 ≤ chartIntegrand e U w p := by
  classical
  by_cases hp : p ∈ U
  · rw [chartIntegrand, Set.indicator_of_mem hp]
    exact mul_nonneg (sectionJacobian_nonneg _ _) (hw _)
  · rw [chartIntegrand, Set.indicator_of_notMem hp]

/-- The continuity and integrability of the parameter integral are proved
for the actual geometric Jacobian and actual pulled-back spatial weight. -/
theorem chart_parameter_integral {a : PlanarSpace}
    {e : OpenPartialHomeomorph PlanarSpace (ℝ × K)} {U C : Set (ℝ × K)}
    (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U) (hUt : U ⊆ e.target)
    (hG : ContDiffOn ℝ 1 (e.symm : (ℝ × K) → PlanarSpace) U)
    (hsmall : ∀ p ∈ U, e.symm p ∈ Metric.ball a (1 / 8 : ℝ))
    {w : Torus → ℝ} (hw : Continuous w)
    (hws : Function.support w ⊆ torusQuotient '' (e.symm '' C)) :
    (∀ r : ℝ, Integrable (fun y : K ↦ chartIntegrand e U w (r, y)) volume) ∧
      Continuous (fun r : ℝ ↦ ∫ y : K, chartIntegrand e U w (r, y)) :=
  compact_parameter_integral (continuous_chartIntegrand hU hC hCU hUt hG hsmall hw hws)
    hC (chartIntegrand_support hCU hUt hsmall hws)

/-- Identification of the actual weighted chart fibre with the proved
continuous parameter integrand. -/
theorem chart_lintegral_eq_parameter {P : PlanarSpace →L[ℝ] K} {a : PlanarSpace}
    {e : OpenPartialHomeomorph PlanarSpace (ℝ × K)} {U : Set (ℝ × K)}
    (hdim : Module.finrank ℝ K = 1) (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 (e.symm : (ℝ × K) → PlanarSpace) U)
    (hcoord : ∀ p ∈ U, P (e.symm p - a) = p.2)
    (hsmall : ∀ p ∈ U, e.symm p ∈ Metric.ball a (1 / 8 : ℝ))
    (r : ℝ) {w : Torus → ℝ} (hw : Measurable w) :
    (∫⁻ z in (fun y ↦ torusQuotient (e.symm (r, y))) '' {y | (r, y) ∈ U},
      ENNReal.ofReal (w z) ∂physicalCurveMeasure) =
      ∫⁻ y : K, ENNReal.ofReal (chartIntegrand e U w (r, y)) := by
  classical
  rw [regular_chart_lintegral hdim hU hG hcoord hsmall r _ hw.ennreal_ofReal]
  have hS : MeasurableSet {y : K | (r, y) ∈ U} :=
    (hU.preimage (continuous_const.prodMk continuous_id)).measurableSet
  rw [← lintegral_indicator hS]
  apply lintegral_congr
  intro y
  by_cases hy : (r, y) ∈ U
  · have hyS : y ∈ {y : K | (r, y) ∈ U} := hy
    rw [Set.indicator_of_mem hyS, chartIntegrand, Set.indicator_of_mem hy,
      sectionJacobian, sectionDerivative_eq hU hG hy]
    rw [ENNReal.ofReal_mul (LinearMap.normDet_nonneg _)]
  · have hyS : y ∉ {y : K | (r, y) ∈ U} := hy
    rw [Set.indicator_of_notMem hyS, chartIntegrand, Set.indicator_of_notMem hy,
      ENNReal.ofReal_zero]

/-- Localization in a chart is an exact identity for the full literal
level integral when the spatial weight is supported in a subchart. -/
theorem localized_level_lintegral {v : Torus → ℝ} (hv : Continuous v)
    {P : PlanarSpace →L[ℝ] K} {a : PlanarSpace}
    {e : OpenPartialHomeomorph PlanarSpace (ℝ × K)} {U C : Set (ℝ × K)}
    (hdim : Module.finrank ℝ K = 1) (hU : IsOpen U)
    (hCU : C ⊆ U) (hUt : U ⊆ e.target)
    (hG : ContDiffOn ℝ 1 (e.symm : (ℝ × K) → PlanarSpace) U)
    (hvalue : ∀ p ∈ U, v (torusQuotient (e.symm p)) = p.1)
    (hcoord : ∀ p ∈ U, P (e.symm p - a) = p.2)
    (hsmall : ∀ p ∈ U, e.symm p ∈ Metric.ball a (1 / 8 : ℝ))
    {w : Torus → ℝ} (hw : Measurable w)
    (hws : Function.support w ⊆ torusQuotient '' (e.symm '' C)) (r : ℝ) :
    (∫⁻ z in {z | v z = r}, ENNReal.ofReal (w z) ∂physicalCurveMeasure) =
      ∫⁻ y : K, ENNReal.ofReal (chartIntegrand e U w (r, y)) := by
  classical
  let V : Set Torus := torusQuotient '' (e.symm '' U)
  have hV : IsOpen V := isOpenQuotientMap_torusQuotient.isOpenMap _
    (e.isOpen_image_symm_of_subset_target hU hUt)
  have hWV : Function.support w ⊆ V := hws.trans (image_mono (image_mono hCU))
  have hwzero (z : Torus) (hz : z ∉ V) : w z = 0 := by
    by_contra hn
    exact hz (hWV hn)
  have hlevel : V ∩ {z | v z = r} =
      (fun y ↦ torusQuotient (e.symm (r, y))) '' {y | (r, y) ∈ U} := by
    ext z
    constructor
    · rintro ⟨⟨x, ⟨⟨p, y⟩, hp, rfl⟩, rfl⟩, hz⟩
      have hpr : p = r := (hvalue (p, y) hp).symm.trans hz
      subst p
      exact ⟨y, hp, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨e.symm (r, y), ⟨(r, y), hy, rfl⟩, rfl⟩, hvalue (r, y) hy⟩
  have hL : MeasurableSet {z | v z = r} := (isClosed_eq hv continuous_const).measurableSet
  have he : ({z | v z = r}.indicator (fun z ↦ ENNReal.ofReal (w z))) =
      (V ∩ {z | v z = r}).indicator (fun z ↦ ENNReal.ofReal (w z)) := by
    funext z
    by_cases hzL : z ∈ {z | v z = r}
    · by_cases hzV : z ∈ V
      · have hzVL : z ∈ V ∩ {z | v z = r} := ⟨hzV, hzL⟩
        rw [Set.indicator_of_mem hzL, Set.indicator_of_mem hzVL]
      · rw [Set.indicator_of_mem hzL,
          Set.indicator_of_notMem (fun h : z ∈ V ∩ {z | v z = r} ↦ hzV h.1),
          hwzero z hzV, ENNReal.ofReal_zero]
    · rw [Set.indicator_of_notMem hzL,
        Set.indicator_of_notMem (fun h : z ∈ V ∩ {z | v z = r} ↦ hzL h.2)]
  rw [← lintegral_indicator hL, he, lintegral_indicator (hV.measurableSet.inter hL), hlevel]
  exact chart_lintegral_eq_parameter hdim hU hG hcoord hsmall r hw

/-- The localized physical level integral is genuinely finite and
continuous for every real parameter. Compact support, the H1 formula and
all integrability are derived in the proof. -/
theorem localized_level_integral {v : Torus → ℝ} (hv : Continuous v)
    {P : PlanarSpace →L[ℝ] K} {a : PlanarSpace}
    {e : OpenPartialHomeomorph PlanarSpace (ℝ × K)} {U C : Set (ℝ × K)}
    (hdim : Module.finrank ℝ K = 1) (hU : IsOpen U) (hC : IsCompact C)
    (hCU : C ⊆ U) (hUt : U ⊆ e.target)
    (hG : ContDiffOn ℝ 1 (e.symm : (ℝ × K) → PlanarSpace) U)
    (hvalue : ∀ p ∈ U, v (torusQuotient (e.symm p)) = p.1)
    (hcoord : ∀ p ∈ U, P (e.symm p - a) = p.2)
    (hsmall : ∀ p ∈ U, e.symm p ∈ Metric.ball a (1 / 8 : ℝ))
    {w : Torus → ℝ} (hw : Continuous w) (hwn : ∀ z, 0 ≤ w z)
    (hws : Function.support w ⊆ torusQuotient '' (e.symm '' C)) :
    (∀ r : ℝ, IntegrableOn w {z | v z = r} physicalCurveMeasure ∧
      (∫ z in {z | v z = r}, w z ∂physicalCurveMeasure) =
        ∫ y : K, chartIntegrand e U w (r, y)) ∧
      Continuous (fun r : ℝ ↦ ∫ z in {z | v z = r}, w z ∂physicalCurveMeasure) := by
  have hp := chart_parameter_integral hU hC hCU hUt hG hsmall hw hws
  have he (r : ℝ) := localized_level_lintegral hv hdim hU hCU hUt hG
    hvalue hcoord hsmall hw.measurable hws r
  have hHn (r : ℝ) : ∀ᵐ y : K, 0 ≤ chartIntegrand e U w (r, y) :=
    Eventually.of_forall fun y ↦ chartIntegrand_nonneg e U hwn (r, y)
  have hreal (r : ℝ) : IntegrableOn w {z | v z = r} physicalCurveMeasure ∧
      (∫ z in {z | v z = r}, w z ∂physicalCurveMeasure) =
        ∫ y : K, chartIntegrand e U w (r, y) := by
    have hfinite := (hasFiniteIntegral_iff_ofReal (hHn r)).mp (hp.1 r).hasFiniteIntegral
    have hwi : IntegrableOn w {z | v z = r} physicalCurveMeasure := by
      refine ⟨hw.measurable.aestronglyMeasurable, ?_⟩
      apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hwn)).mpr
      rw [he r]
      exact hfinite
    refine ⟨hwi, ?_⟩
    calc
      (∫ z in {z | v z = r}, w z ∂physicalCurveMeasure) =
          (∫⁻ z in {z | v z = r}, ENNReal.ofReal (w z) ∂physicalCurveMeasure).toReal :=
        integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hwn)
          hw.measurable.aestronglyMeasurable
      _ = (∫⁻ y : K, ENNReal.ofReal (chartIntegrand e U w (r, y))).toReal :=
        congrArg ENNReal.toReal (he r)
      _ = ∫ y : K, chartIntegrand e U w (r, y) :=
        (integral_eq_lintegral_of_nonneg_ae (hHn r) (hp.1 r).aestronglyMeasurable).symm
  refine ⟨hreal, ?_⟩
  have heq : (fun r : ℝ ↦ ∫ z in {z | v z = r}, w z ∂physicalCurveMeasure) =
      (fun r : ℝ ↦ ∫ y : K, chartIntegrand e U w (r, y)) :=
    funext fun r ↦ (hreal r).2
  rw [heq]
  exact hp.2

end CompactChart

/-- Every actual regular point has a smaller open chart on which all
nonnegative continuous spatial weights yield finite, continuous actual
physical level integrals. The compact target support is constructed here. -/
theorem exists_local_level_integral_continuity {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {z : Torus} (hz : torusOrdinaryGradient v z ≠ 0) :
    ∃ V : Set Torus, IsOpen V ∧ z ∈ V ∧
      ∀ w : Torus → ℝ, Continuous w → (∀ x, 0 ≤ w x) → Function.support w ⊆ V →
        (∀ r : ℝ, IntegrableOn w {x | v x = r} physicalCurveMeasure) ∧
        Continuous (fun r : ℝ ↦ ∫ x in {x | v x = r}, w x ∂physicalCurveMeasure) := by
  obtain ⟨a, rfl⟩ := torusQuotient_surjective z
  have ha : fderiv ℝ (fun x : PlanarSpace ↦ v (torusQuotient x)) a ≠ 0 := by
    intro hzero
    exact hz ((mem_torusCriticalPoints_lift_iff v a).mpr hzero)
  obtain ⟨P, e, U, -, -, -, hinverse, hU, hUa, hUt, hsmall, hG, hdim, hcoord⟩ :=
    exists_planar_regular_chart hv ha
  obtain ⟨C, hC, -, hcenter, hCU⟩ := exists_compact_closed_between
    (isCompact_singleton : IsCompact ({(v (torusQuotient a), 0)} :
      Set (ℝ × ↥(fderiv ℝ (fun x : PlanarSpace ↦ v (torusQuotient x)) a).ker)))
    hU (singleton_subset_iff.mpr hUa)
  let V : Set Torus := torusQuotient '' (e.symm '' interior C)
  have hV : IsOpen V := isOpenQuotientMap_torusQuotient.isOpenMap _
    (e.isOpen_image_symm_of_subset_target isOpen_interior
      (interior_subset.trans (hCU.trans hUt)))
  have haV : torusQuotient a ∈ V :=
    ⟨a, ⟨(v (torusQuotient a), 0), hcenter (mem_singleton _), hinverse⟩, rfl⟩
  refine ⟨V, hV, haV, ?_⟩
  intro w hw hwn hws
  have hwsC : Function.support w ⊆ torusQuotient '' (e.symm '' C) :=
    hws.trans (image_mono (image_mono interior_subset))
  have hh := localized_level_integral (continuous_of_contDiff_lift hv) hdim hU hC hCU hUt
    hG (fun p hp ↦ (hcoord p hp).1) (fun p hp ↦ (hcoord p hp).2) hsmall hw hwn hwsC
  exact ⟨fun r ↦ (hh.1 r).1, hh.2⟩

/-- Compact spatial support disjoint from one literal level is disjoint
from every level in an actual neighborhood of that value. -/
theorem weight_vanishes_near_level {v w : Torus → ℝ} (hv : Continuous v)
    {C : Set Torus} (hC : IsCompact C) (hws : Function.support w ⊆ C)
    {t : ℝ} (havoid : ∀ z ∈ C, v z ≠ t) :
    ∀ᶠ r in 𝓝 t, ∀ z, v z = r → w z = 0 := by
  have ht : t ∉ v '' C := by
    rintro ⟨z, hz, he⟩
    exact havoid z hz he
  filter_upwards [(hC.image hv).isClosed.isOpen_compl.mem_nhds ht] with r hr z hz
  by_contra hn
  exact hr ⟨z, hws hn, hz⟩

/-- The part of a finite partition supported away from the chosen level
has genuinely zero fibre integral nearby; no integrability at distant
critical fibres is assumed. -/
theorem level_integral_away_support {v w : Torus → ℝ} (hv : Continuous v)
    {C : Set Torus} (hC : IsCompact C) (hws : Function.support w ⊆ C)
    {t : ℝ} (havoid : ∀ z ∈ C, v z ≠ t) :
    (∀ᶠ r in 𝓝 t, IntegrableOn w {z | v z = r} physicalCurveMeasure) ∧
      ContinuousAt (fun r : ℝ ↦ ∫ z in {z | v z = r}, w z ∂physicalCurveMeasure) t := by
  have hz := weight_vanishes_near_level hv hC hws havoid
  have hboth : ∀ᶠ r in 𝓝 t, IntegrableOn w {z | v z = r} physicalCurveMeasure ∧
      (∫ z in {z | v z = r}, w z ∂physicalCurveMeasure) = 0 := by
    filter_upwards [hz] with r hr
    have hL : MeasurableSet {z | v z = r} := (isClosed_eq hv continuous_const).measurableSet
    have he : w =ᵐ[physicalCurveMeasure.restrict {z | v z = r}] (fun _ ↦ 0) := by
      filter_upwards [ae_restrict_mem hL] with z hz
      exact hr z hz
    refine ⟨(integrable_zero Torus ℝ
      (physicalCurveMeasure.restrict {z | v z = r})).congr he.symm, ?_⟩
    rw [integral_congr_ae he, integral_zero]
  exact ⟨hboth.mono fun _ h ↦ h.1,
    continuousAt_const.congr_of_eventuallyEq (hboth.mono fun _ h ↦ h.2)⟩

/-- Finite partition assembly of the actual physical level integral.
Every regular chart is constructed from the source function. The
complementary partition weights vanish on an actual value neighborhood,
so no integrability at distant critical fibres is used. -/
theorem level_integral_continuousAt_regular {v w : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hw : Continuous w) (hwn : ∀ z, 0 ≤ w z) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    IntegrableOn w {z | v z = t} physicalCurveMeasure ∧
      ContinuousAt (fun r : ℝ ↦ ∫ z in {z | v z = r}, w z ∂physicalCurveMeasure) t := by
  classical
  have hvc := continuous_of_contDiff_lift hv
  have hlocal (z : {z : Torus | v z = t}) :=
    exists_local_level_integral_continuity hv
      (show torusOrdinaryGradient v z ≠ 0 from fun hz ↦ ht ⟨z, hz, z.property⟩)
  choose V hVo hVz hVP using hlocal
  let U : Option {z : Torus | v z = t} → Set Torus
    | none => {z | v z ≠ t}
    | some z => V z
  have hUo (i : Option {z : Torus | v z = t}) : IsOpen (U i) := by
    cases i with
    | none => exact (isClosed_eq hvc continuous_const).isOpen_compl
    | some z => exact hVo z
  have hcover : (univ : Set Torus) ⊆ ⋃ i, U i := by
    intro z _
    by_cases hz : v z = t
    · exact mem_iUnion.mpr ⟨some ⟨z, hz⟩, hVz ⟨z, hz⟩⟩
    · exact mem_iUnion.mpr ⟨none, hz⟩
  obtain ⟨S, hS⟩ := (isCompact_univ : IsCompact (univ : Set Torus)).elim_finite_subcover
    U hUo hcover
  let j : Fin S.card → Option {z : Torus | v z = t} := fun i ↦ (S.equivFin.symm i).val
  have hcoverFin : (univ : Set Torus) ⊆ ⋃ i : Fin S.card, U (j i) := by
    intro z hz
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hS hz)
    obtain ⟨hiS, hzi⟩ := mem_iUnion.mp hi
    refine mem_iUnion.mpr ⟨S.equivFin ⟨i, hiS⟩, ?_⟩
    simpa only [j, Equiv.symm_apply_apply] using hzi
  obtain ⟨χ, hχs, hχsum, hχrange, hχcompact⟩ :=
    exists_continuous_sum_one_of_isOpen_isCompact (fun i : Fin S.card ↦ hUo (j i))
      (isCompact_univ : IsCompact (univ : Set Torus)) hcoverFin
  let g : Fin S.card → Torus → ℝ := fun i z ↦ χ i z * w z
  have hgc (i : Fin S.card) : Continuous (g i) := (χ i).continuous.mul hw
  have hgn (i : Fin S.card) (z : Torus) : 0 ≤ g i z :=
    mul_nonneg (hχrange i z).1 (hwn z)
  have hgs (i : Fin S.card) : Function.support (g i) ⊆ tsupport (χ i) := by
    intro z hz
    apply subset_tsupport (χ i)
    intro hzero
    apply hz
    simp only [g, hzero, zero_mul]
  have hsum (z : Torus) : ∑ i, g i z = w z := by
    have hχz : (∑ i, χ i z) = 1 := by simpa using hχsum (mem_univ z)
    change (∑ i, χ i z * w z) = w z
    rw [← Finset.sum_mul, hχz, one_mul]
  have hi (i : Fin S.card) :
      (∀ᶠ r in 𝓝 t, IntegrableOn (g i) {z | v z = r} physicalCurveMeasure) ∧
        ContinuousAt (fun r : ℝ ↦ ∫ z in {z | v z = r}, g i z ∂physicalCurveMeasure) t := by
    cases hji : j i with
    | none =>
        apply level_integral_away_support hvc (hχcompact i) (hgs i)
        intro z hz
        have hh := hχs i hz
        change z ∈ U (j i) at hh
        rw [hji] at hh
        change v z ≠ t at hh
        exact hh
    | some z =>
        have hs : Function.support (g i) ⊆ V z := by
          simpa only [hji, U] using (hgs i).trans (hχs i)
        have hh := hVP z (g i) (hgc i) (hgn i) hs
        exact ⟨Eventually.of_forall hh.1, hh.2.continuousAt⟩
  have hiall : ∀ᶠ r in 𝓝 t, ∀ i : Fin S.card,
      IntegrableOn (g i) {z | v z = r} physicalCurveMeasure :=
    eventually_all.mpr fun i ↦ (hi i).1
  have hevent : ∀ᶠ r in 𝓝 t,
      IntegrableOn w {z | v z = r} physicalCurveMeasure ∧
        (∫ z in {z | v z = r}, w z ∂physicalCurveMeasure) =
          ∑ i, ∫ z in {z | v z = r}, g i z ∂physicalCurveMeasure := by
    filter_upwards [hiall] with r hr
    have hsumI : Integrable (fun z ↦ ∑ i, g i z)
        (physicalCurveMeasure.restrict {z | v z = r}) :=
      integrable_finsetSum Finset.univ fun i _ ↦ hr i
    refine ⟨hsumI.congr (Eventually.of_forall hsum), ?_⟩
    calc
      (∫ z in {z | v z = r}, w z ∂physicalCurveMeasure) =
          ∫ z in {z | v z = r}, ∑ i, g i z ∂physicalCurveMeasure :=
        integral_congr_ae (Eventually.of_forall fun z ↦ (hsum z).symm)
      _ = ∑ i, ∫ z in {z | v z = r}, g i z ∂physicalCurveMeasure :=
        integral_finsetSum Finset.univ fun i _ ↦ hr i
  have hcs : ContinuousAt
      (fun r : ℝ ↦ ∑ i, ∫ z in {z | v z = r}, g i z ∂physicalCurveMeasure) t := by
    have hci := fun i ↦ (hi i).2
    fun_prop
  exact ⟨(mem_of_mem_nhds hevent).1,
    hcs.congr_of_eventuallyEq (hevent.mono fun _ h ↦ h.2)⟩

/-- The inverse physical-gradient weight is integrable on every regular
level and its actual level integral is continuous there. A globally
continuous truncated inverse is used only outside the proved regular band;
on all relevant fibres it is exactly the source inverse gradient. -/
theorem inverseGradient_integrable_continuousAt_regular {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    IntegrableOn (fun z ↦ ‖torusOrdinaryGradient v z‖⁻¹)
        {z | v z = t} physicalCurveMeasure ∧
      ContinuousAt (inverseGradientDensity v) t := by
  obtain ⟨ε, hε, hgrad⟩ := exists_regular_band_gradient_lower hv ht
  let w : Torus → ℝ := fun z ↦ (max ε ‖torusOrdinaryGradient v z‖)⁻¹
  have hw : Continuous w :=
    (continuous_const.max (continuous_norm_gradient hv)).inv₀
      (fun z ↦ (hε.trans_le (le_max_left ε ‖torusOrdinaryGradient v z‖)).ne')
  have hwn (z : Torus) : 0 ≤ w z :=
    inv_nonneg.mpr (hε.le.trans (le_max_left _ _))
  have hp := level_integral_continuousAt_regular hv hw hwn ht
  have he (r : ℝ) (hr : |r - t| ≤ ε) :
      w =ᵐ[physicalCurveMeasure.restrict {z | v z = r}]
        (fun z ↦ ‖torusOrdinaryGradient v z‖⁻¹) := by
    have hL : MeasurableSet {z | v z = r} :=
      (isClosed_eq (continuous_of_contDiff_lift hv) continuous_const).measurableSet
    filter_upwards [ae_restrict_mem hL] with z hz
    change (max ε ‖torusOrdinaryGradient v z‖)⁻¹ = ‖torusOrdinaryGradient v z‖⁻¹
    rw [max_eq_right (hgrad z (by rw [hz]; exact hr))]
  refine ⟨hp.1.congr (he t (by simpa only [sub_self, abs_zero] using hε.le)), ?_⟩
  apply hp.2.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (show t - ε < t by linarith)
    (show t < t + ε by linarith)] with r hr
  rw [inverseGradientDensity_eq_integral]
  exact integral_congr_ae (he r (abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩)).symm

theorem gradientFlux_integrable_continuousAt_regular {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    IntegrableOn (fun z ↦ ‖torusOrdinaryGradient v z‖)
        {z | v z = t} physicalCurveMeasure ∧
      ContinuousAt (gradientFluxDensity v) t := by
  have hh := level_integral_continuousAt_regular hv (continuous_norm_gradient hv)
    (fun z ↦ norm_nonneg (torusOrdinaryGradient v z)) ht
  refine ⟨hh.1, ?_⟩
  have he : gradientFluxDensity v =
      (fun r ↦ ∫ z in {z | v z = r}, ‖torusOrdinaryGradient v z‖ ∂physicalCurveMeasure) :=
    funext (gradientFluxDensity_eq_integral v)
  rw [he]
  exact hh.2

/-- The manuscript's rank derivative now holds at every literal regular
value. The proof differentiates the exact coarea primitive using the
proved continuity of the actual inverse-gradient fibre integral. -/
theorem hasDerivAt_rank_regular {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    HasDerivAt (rank v)
      (-(∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖⁻¹ ∂physicalCurveMeasure)) t := by
  obtain ⟨ε, hε, hgrad⟩ := exists_regular_band_gradient_lower hv ht
  have hreg : ∀ r ∈ Icc (t - ε) (t + ε), r ∉ torusCriticalValues v := by
    intro r hr ⟨z, hz, hzr⟩
    have hbound := hgrad z (by
      rw [hzr]
      exact abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩)
    rw [hz, norm_zero] at hbound
    linarith
  have hi := integrable_inverseGradientDensity hv
  have hd : HasDerivAt (fun r : ℝ ↦ ∫ x in (t - ε)..r, inverseGradientDensity v x)
      (inverseGradientDensity v t) t :=
    intervalIntegral.integral_hasDerivAt_right hi.intervalIntegrable
      hi.aestronglyMeasurable.stronglyMeasurableAtFilter
      (inverseGradient_integrable_continuousAt_regular hv ht).2
  have hp : HasDerivAt
      (fun r ↦ rank v (t - ε) - ∫ x in (t - ε)..r, inverseGradientDensity v x)
      (-inverseGradientDensity v t) t := by
    simpa only [Pi.sub_apply, zero_sub] using!
      (hasDerivAt_const t (rank v (t - ε))).sub hd
  have hactual : HasDerivAt (rank v) (-inverseGradientDensity v t) t := by
    apply hp.congr_of_eventuallyEq
    filter_upwards [Icc_mem_nhds (show t - ε < t by linarith)
      (show t < t + ε by linarith)] with r hr
    exact rank_eq_primitive_on_regular_interval hv hr hreg
  simpa only [inverseGradientDensity_eq_integral] using hactual

/-- Actual H1 boundary flux at every regular value. The already proved AE
identity is upgraded on the open regular-value set using the genuine fibre
continuity above and continuity of the original superlevel quantities. -/
theorem stationary_level_flux_regular {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    {t : ℝ} (ht : t ∉ torusCriticalValues v) :
    (∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖ ∂physicalCurveMeasure) =
      ρ * (superlevelMass v t - rank v t) := by
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  let R : Set ℝ := (torusCriticalValues v)ᶜ
  have hR : IsOpen R := (isCompact_torusCriticalValues hv1).isClosed.isOpen_compl
  have hleft : ContinuousOn
      (fun r ↦ ∫ z in {z | v z = r}, ‖torusOrdinaryGradient v z‖ ∂physicalCurveMeasure) R := by
    intro r hr
    exact (level_integral_continuousAt_regular hv1 (continuous_norm_gradient hv1)
      (fun z ↦ norm_nonneg (torusOrdinaryGradient v z)) hr).2.continuousWithinAt
  have hright : ContinuousOn (fun r ↦ ρ * (superlevelMass v r - rank v r)) R := by
    intro r hr
    exact (continuousAt_const.mul ((superlevelMass_continuousAt_regular hv1 hr).sub
      (rank_continuousAt_regular hv1 hr))).continuousWithinAt
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae (ae_stationary_level_flux hv hpde))
    hR hleft hright ht

/-- The two source level identities, true integrability, and physical H1
finiteness now hold at every regular value, with no added exceptional set. -/
theorem stationary_level_identities_regular {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    {t : ℝ} (ht : t ∉ torusCriticalValues v) :
    IntegrableOn (fun z ↦ ‖torusOrdinaryGradient v z‖⁻¹) {z | v z = t} physicalCurveMeasure ∧
      IntegrableOn (fun z ↦ ‖torusOrdinaryGradient v z‖) {z | v z = t} physicalCurveMeasure ∧
      physicalCurveMeasure {z | v z = t} < (∞ : ℝ≥0∞) ∧
      HasDerivAt (rank v)
        (-(∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖⁻¹ ∂physicalCurveMeasure)) t ∧
      (∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖ ∂physicalCurveMeasure) =
        ρ * (superlevelMass v t - rank v t) := by
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  have hi := (inverseGradient_integrable_continuousAt_regular hv1 ht).1
  have hg := (gradientFlux_integrable_continuousAt_regular hv1 ht).1
  exact ⟨hi, hg, (level_cauchy_schwarz hv1 ht hi hg).1,
    hasDerivAt_rank_regular hv1 ht, stationary_level_flux_regular hv hpde ht⟩

/-- Source level Cauchy--Schwarz with the actual pointwise regular-value
rank and flux identities. The separate isoperimetric step is not assumed. -/
theorem level_length_squared_le_flux_rank_regular {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    {t : ℝ} (ht : t ∉ torusCriticalValues v) :
    (physicalCurveMeasure.real {z | v z = t}) ^ 2 ≤
      ρ * (superlevelMass v t - rank v t) * (-deriv (rank v) t) := by
  have hh := stationary_level_identities_regular hv hpde ht
  have hcs := (level_cauchy_schwarz (hv.of_le (by simp)) ht hh.1 hh.2.1).2
  rw [hh.2.2.2.1.deriv, neg_neg]
  simpa only [hh.2.2.2.2] using hcs

/-- The literal strict-superlevel frontier carries the same physical flux
as the regular level. No smooth-boundary or divergence premise is added. -/
theorem stationary_frontier_flux_regular {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    {t : ℝ} (ht : t ∉ torusCriticalValues v) :
    (∫ z in frontier {z | t < v z}, ‖torusOrdinaryGradient v z‖ ∂physicalCurveMeasure) =
      ρ * (superlevelMass v t - rank v t) := by
  rw [frontier_strict_superlevel_eq (hv.of_le (by simp)) ht]
  exact stationary_level_flux_regular hv hpde ht

/-- The actual sigmoid boundary layers converge to the physical H1 level
flux at every regular value, closing the earlier geometric identification. -/
theorem boundaryLayer_tendsto_level_flux_regular {v : Torus → ℝ} {ρ t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    (ht : t ∉ torusCriticalValues v) :
    Tendsto (fun n : ℕ ↦ ∫ z,
      ((n : ℝ) * superlevelCutoff t n (v z) * (1 - superlevelCutoff t n (v z))) *
        ‖torusOrdinaryGradient v z‖ ^ 2 ∂torusMeasure) atTop
      (𝓝 (∫ z in {z | v z = t}, ‖torusOrdinaryGradient v z‖ ∂physicalCurveMeasure)) := by
  rw [stationary_level_flux_regular hv hpde ht]
  exact stationary_superlevel_flux_limit hv hpde ht

end PeriodicAttractiveLogGas.StationaryLevelContinuity
