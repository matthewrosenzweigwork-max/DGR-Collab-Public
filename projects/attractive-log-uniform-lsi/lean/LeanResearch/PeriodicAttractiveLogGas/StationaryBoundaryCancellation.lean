import LeanResearch.PeriodicAttractiveLogGas.StationarySignedCoarea

/-! Cancellation of the oriented boundary integrals of a regular torus
superlevel. Periodic integration by parts and signed coarea prove the
cancellation; no homology or divergence identity is assumed. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators RealInnerProductSpace
namespace PeriodicAttractiveLogGas.StationaryBoundaryCancellation
open StationaryCoarea StationarySard StationaryLevelGeometry
  StationaryLevelCircles StationaryPeriodDisplacement StationarySignedCoarea

theorem torusGradient_eq_ordinary (f : SmoothPair 1) (z : Torus) :
    f.torusGradient z = torusOrdinaryGradient f.torusValue z := by
  symm
  obtain ⟨x, rfl⟩ := torusQuotient_surjective z
  rw [torusOrdinaryGradient_lift, rectangleOrdinaryGradient, (f.torus_differential x).fderiv]
  exact (InnerProductSpace.toDual ℝ PlanarSpace).symm_apply_apply _

theorem integral_torusGradient_inner_zero (f : SmoothPair 1) (e : PlanarSpace) :
    (∫ z, inner ℝ (f.torusGradient z) e ∂torusMeasure) = 0 := by
  have hh := f.integral_gradient_inner_eq_zero (singleParticleCoordinates e)
  have hs : Continuous (singleConfiguration : Torus → Configuration 1) := by
    unfold singleConfiguration
    exact continuous_pi fun _ ↦ continuous_id
  have hm : AEStronglyMeasurable
      (fun z ↦ inner ℝ (f.gradient (singleConfiguration z)) (singleParticleCoordinates e)) torusMeasure :=
    ((f.gradient.continuous.comp hs).inner continuous_const).aestronglyMeasurable
  rw [integral_reference_one_eq_torus _ hm] at hh
  simpa only [SmoothPair.torusGradient, ContinuousMap.coe_mk, inner_firstParticleCoordinates] using hh

theorem integral_gradient_test_zero {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {T : ℝ → ℝ} (hT : ContDiff ℝ ∞ T) (j : Fin 2) :
    (∫ z, deriv T (v z) * torusOrdinaryGradient v z j ∂torusMeasure) = 0 := by
  let V : C(Torus, ℝ) := ⟨v, continuous_of_contDiff_lift (hv.of_le (by simp))⟩
  let f := SmoothPair.ofTorusContDiffLift V hv
  have hvalue : f.torusValue = v := rfl
  have hh := integral_torusGradient_inner_zero (f.compSmooth T hT) (EuclideanSpace.single j 1)
  simp only [torusGradient_compSmooth, inner_smul_left, conj_trivial,
    EuclideanSpace.inner_single_right, one_mul] at hh
  simp_rw [torusGradient_eq_ordinary, hvalue] at hh
  exact hh

theorem integral_rotated_gradient_test_zero {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {T : ℝ → ℝ} (hT : ContDiff ℝ ∞ T) (j : Fin 2) :
    (∫ z, deriv T (v z) * quarterTurn (torusOrdinaryGradient v z) j ∂torusMeasure) = 0 := by
  fin_cases j
  · change (∫ z, deriv T (v z) * quarterTurn (torusOrdinaryGradient v z) 0 ∂torusMeasure) = 0
    simp only [quarterTurn_apply_zero, mul_neg, integral_neg,
      integral_gradient_test_zero hv hT 1, neg_zero]
  · change (∫ z, deriv T (v z) * quarterTurn (torusOrdinaryGradient v z) 1 ∂torusMeasure) = 0
    simp only [quarterTurn_apply_one, integral_gradient_test_zero hv hT 0]

theorem gradientNorm_mul_unitTangent (v : Torus → ℝ) (z : Torus) (j : Fin 2) :
    ‖torusOrdinaryGradient v z‖ * unitTangent v z j = quarterTurn (torusOrdinaryGradient v z) j := by
  by_cases hz : torusOrdinaryGradient v z = 0
  · simp [unitTangent, hz]
  · change ‖torusOrdinaryGradient v z‖ *
      (‖torusOrdinaryGradient v z‖⁻¹ * quarterTurn (torusOrdinaryGradient v z) j) = _
    rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz), one_mul]

theorem measurable_unitTangent_coordinate {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) (j : Fin 2) :
    Measurable (fun z ↦ unitTangent v z j) :=
  (EuclideanSpace.proj j).continuous.measurable.comp (measurable_unitTangent hv)

theorem unitTangent_coordinate_bound (v : Torus → ℝ) (j : Fin 2) (z : Torus) :
    |unitTangent v z j| ≤ 1 := by
  exact (show |unitTangent v z j| ≤ ‖unitTangent v z‖ by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (unitTangent v z) j).trans
      (norm_unitTangent_le v z)

private theorem compact_support_bound {φ : ℝ → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) : ∃ B : ℝ, ∀ t, |φ t| ≤ B := by
  obtain ⟨B, hB⟩ := (show IsCompact (tsupport φ) from hc).exists_bound_of_continuousOn hφ.continuousOn
  refine ⟨max B 0, fun t ↦ ?_⟩
  by_cases ht : t ∈ tsupport φ
  · exact (show |φ t| ≤ B by simpa only [Real.norm_eq_abs] using hB t ht).trans (le_max_left _ _)
  · have hz : φ t = 0 := by
      by_contra hn
      exact ht (subset_tsupport φ hn)
    rw [hz, abs_zero]
    exact le_max_right _ _

theorem unitTangent_level_test_zero {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (j : Fin 2) {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ t : ℝ, φ t * levelIntegral v (fun z ↦ unitTangent v z j) t) = 0 := by
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  obtain ⟨B, hB⟩ := compact_support_bound hφ.continuous hc
  have hφi : Integrable φ := hφ.continuous.integrable_of_hasCompactSupport hc
  have hco := (bounded_signed_coarea hv1 (measurable_unitTangent_coordinate hv1 j)
    (unitTangent_coordinate_bound v j)).2.2 φ hφ.continuous.measurable B hB
  rw [← hco]
  simp_rw [gradientNorm_mul_unitTangent]
  have hh := integral_rotated_gradient_test_zero hv (lowerPrimitive_contDiff hφ hφi) j
  have hd (r : ℝ) : deriv (lowerPrimitive φ) r = φ r :=
    (lowerPrimitive_hasDerivAt hφ.continuous hφi r).deriv
  simpa only [hd] using hh

theorem ae_unitTangent_level_integral_zero {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x))) (j : Fin 2) :
    ∀ᵐ t : ℝ, levelIntegral v (fun z ↦ unitTangent v z j) t = 0 := by
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  have hl := (bounded_signed_coarea hv1 (measurable_unitTangent_coordinate hv1 j)
    (unitTangent_coordinate_bound v j)).1.locallyIntegrable
  have hr := (integrable_zero ℝ ℝ volume : Integrable (fun _ : ℝ ↦ (0 : ℝ)) volume).locallyIntegrable
  have he := ae_eq_of_integral_contDiff_smul_eq hl hr (fun φ hφ hc ↦ by
    simpa only [smul_eq_mul, Pi.zero_apply, mul_zero, integral_zero] using unitTangent_level_test_zero hv j hφ hc)
  exact he


/-- The normalized tangent has a continuous representative throughout a
band around each regular level. Its actual level integral is continuous. -/
theorem unitTangent_coordinate_integrable_continuousAt {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} (ht : t ∉ torusCriticalValues v) (j : Fin 2) :
    IntegrableOn (fun z ↦ unitTangent v z j) {z | v z = t} physicalCurveMeasure ∧
      ContinuousAt (levelIntegral v (fun z ↦ unitTangent v z j)) t := by
  obtain ⟨ε, hε, hgrad⟩ := exists_regular_band_gradient_lower hv ht
  let w : Torus → ℝ := fun z ↦ (max ε ‖torusOrdinaryGradient v z‖)⁻¹ *
    quarterTurn (torusOrdinaryGradient v z) j
  have hnum : Continuous (fun z ↦ quarterTurn (torusOrdinaryGradient v z) j) :=
    (EuclideanSpace.proj j).continuous.comp (quarterTurn.continuous.comp (continuous_ordinaryGradient hv))
  have hw : Continuous w :=
    ((continuous_const.max (continuous_norm_gradient hv)).inv₀
      (fun z ↦ (hε.trans_le (le_max_left ε ‖torusOrdinaryGradient v z‖)).ne')).mul hnum
  have hp := levelIntegral_continuousAt_regular hv hw ht
  have he (r : ℝ) (hr : |r - t| ≤ ε) :
      w =ᵐ[physicalCurveMeasure.restrict {z | v z = r}]
        (fun z ↦ unitTangent v z j) := by
    have hL : MeasurableSet {z | v z = r} :=
      (isClosed_eq (continuous_of_contDiff_lift hv) continuous_const).measurableSet
    filter_upwards [ae_restrict_mem hL] with z hz
    change (max ε ‖torusOrdinaryGradient v z‖)⁻¹ * quarterTurn (torusOrdinaryGradient v z) j =
      ‖torusOrdinaryGradient v z‖⁻¹ * quarterTurn (torusOrdinaryGradient v z) j
    rw [max_eq_right (hgrad z (by rw [hz]; exact hr))]
  refine ⟨hp.1.congr (he t (by simpa only [sub_self, abs_zero] using hε.le)), ?_⟩
  apply hp.2.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (show t - ε < t by linarith)
    (show t < t + ε by linarith)] with r hr
  exact (integral_congr_ae (he r (abs_le.mpr ⟨by linarith [hr.1], by linarith [hr.2]⟩))).symm

theorem unitTangent_coordinate_level_integral_zero {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} (ht : t ∉ torusCriticalValues v) (j : Fin 2) :
    levelIntegral v (fun z ↦ unitTangent v z j) t = 0 := by
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  let R : Set ℝ := (torusCriticalValues v)ᶜ
  have hR : IsOpen R := (isCompact_torusCriticalValues hv1).isClosed.isOpen_compl
  have hleft : ContinuousOn (levelIntegral v (fun z ↦ unitTangent v z j)) R := by
    intro r hr
    exact (unitTangent_coordinate_integrable_continuousAt hv1 hr j).2.continuousWithinAt
  exact Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae (ae_unitTangent_level_integral_zero hv j))
    hR hleft continuousOn_const ht

theorem integrable_unitTangent_level {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} (ht : t ∉ torusCriticalValues v) :
    IntegrableOn (unitTangent v) {z | v z = t} physicalCurveMeasure := by
  let : IsFiniteMeasure (physicalCurveMeasure.restrict {z | v z = t}) := ⟨by
    simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      physicalCurveMeasure_level_lt_top hv ht⟩
  exact Integrable.of_bound (measurable_unitTangent hv).stronglyMeasurable.aestronglyMeasurable
    1 (Eventually.of_forall (norm_unitTangent_le v))

/-- The actual oriented vector boundary integral vanishes at every regular
value, not merely almost everywhere in the value parameter. -/
theorem unitTangent_level_integral_zero {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} (ht : t ∉ torusCriticalValues v) :
    (∫ z in {z | v z = t}, unitTangent v z ∂physicalCurveMeasure) = 0 := by
  have hi := integrable_unitTangent_level (hv.of_le (by simp)) ht
  apply PiLp.ext
  intro j
  have hh := (EuclideanSpace.proj j).integral_comp_comm hi
  have hz := unitTangent_coordinate_level_integral_zero hv ht j
  change (∫ z in {z | v z = t}, unitTangent v z j ∂physicalCurveMeasure) =
    (∫ z in {z | v z = t}, unitTangent v z ∂physicalCurveMeasure) j at hh
  change (∫ z in {z | v z = t}, unitTangent v z ∂physicalCurveMeasure) j = 0
  exact hh.symm.trans hz

/-- Additivity over the proved finite family of actual connected components.
Each component carries the same original rotated-gradient orientation. -/
theorem sum_component_unitTangent_integrals_zero {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} (ht : t ∉ torusCriticalValues v) :
    let := (finite_levelComponents (hv.of_le (by simp)) ht).fintype
    (∑ C : levelComponents v t, ∫ z in (C : Set Torus), unitTangent v z ∂physicalCurveMeasure) = 0 := by
  let := (finite_levelComponents (hv.of_le (by simp)) ht).fintype
  change (∑ C : levelComponents v t, ∫ z in (C : Set Torus), unitTangent v z ∂physicalCurveMeasure) = 0
  have hi := integrable_unitTangent_level (hv.of_le (by simp)) ht
  have hs (C : levelComponents v t) : IntegrableOn (unitTangent v) (C : Set Torus) physicalCurveMeasure :=
    hi.mono_set (levelComponent_subset C.property)
  rw [← integral_iUnion_fintype
    (fun C : levelComponents v t ↦ (levelComponent_isCompact (hv.of_le (by simp)) C.property).isClosed.measurableSet)
    (fun C D hne ↦ levelComponents_disjoint C.property D.property (Subtype.coe_ne_coe.mpr hne)) hs,
    iUnion_levelComponents]
  exact unitTangent_level_integral_zero hv ht

end PeriodicAttractiveLogGas.StationaryBoundaryCancellation
