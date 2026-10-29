import LeanResearch.PeriodicAttractiveLogGas.StationaryPeriodDisplacement

/-! Signed coarea for the original probability Haar measure and physical
one-dimensional Hausdorff measure. Integrability of the level integrals
is proved before subtracting the positive and negative parts. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal
namespace PeriodicAttractiveLogGas.StationarySignedCoarea
open StationaryCoarea StationaryLevelGeometry

def levelIntegral (v w : Torus → ℝ) (t : ℝ) : ℝ :=
  ∫ z in {z | v z = t}, w z ∂physicalCurveMeasure

private theorem ae_finite {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} (hm : AEMeasurable f μ)
    (hf : (∫⁻ x, f x ∂μ) < (∞ : ℝ≥0∞)) : ∀ᵐ x ∂μ, f x < (∞ : ℝ≥0∞) := by
  have hg : (∫⁻ x, hm.mk f x ∂μ) < (∞ : ℝ≥0∞) := by
    rw [← lintegral_congr_ae hm.ae_eq_mk]
    exact hf
  filter_upwards [ae_lt_top hm.measurable_mk hg.ne, hm.ae_eq_mk] with x hx he
  rwa [he]

private theorem integrable_toReal {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ≥0∞} (hm : AEMeasurable f μ)
    (hf : (∫⁻ x, f x ∂μ) < (∞ : ℝ≥0∞)) : Integrable (fun x ↦ (f x).toReal) μ := by
  refine ⟨hm.ennreal_toReal.aestronglyMeasurable, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.toReal_nonneg)).mpr
  calc
    (∫⁻ x, ENNReal.ofReal (f x).toReal ∂μ) = ∫⁻ x, f x ∂μ :=
      lintegral_congr_ae ((ae_finite hm hf).mono fun _ hx ↦ ENNReal.ofReal_toReal hx.ne)
    _ < (∞ : ℝ≥0∞) := hf

theorem levelIntegral_eq_fiber_toReal {v w : Torus → ℝ}
    (hw : Measurable w) (hn : ∀ z, 0 ≤ w z) (t : ℝ) :
    levelIntegral v w t = (fiberIntegral v (fun z ↦ ENNReal.ofReal (w z)) t).toReal := by
  exact integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hn) hw.aestronglyMeasurable

theorem fiber_lintegral_lt_top {v w : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hw : Measurable w) (hn : ∀ z, 0 ≤ w z)
    (hi : Integrable (fun z ↦ ‖torusOrdinaryGradient v z‖ * w z) torusMeasure) :
    (∫⁻ t : ℝ, fiberIntegral v (fun z ↦ ENNReal.ofReal (w z)) t) < (∞ : ℝ≥0∞) := by
  rw [← coarea hv _ hw.ennreal_ofReal]
  simp_rw [← ENNReal.ofReal_mul (norm_nonneg _)]
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun z ↦ mul_nonneg (norm_nonneg _) (hn z))]
  exact ENNReal.ofReal_lt_top

theorem nonnegative_level_integrability {v w : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hw : Measurable w) (hn : ∀ z, 0 ≤ w z)
    (hi : Integrable (fun z ↦ ‖torusOrdinaryGradient v z‖ * w z) torusMeasure) :
    Integrable (levelIntegral v w) volume ∧
      ∀ᵐ t : ℝ, IntegrableOn w {z | v z = t} physicalCurveMeasure := by
  have hm := aemeasurable_fiberIntegral hv _ hw.ennreal_ofReal
  have hf := fiber_lintegral_lt_top hv hw hn hi
  constructor
  · have hr := integrable_toReal hm hf
    exact hr.congr (Eventually.of_forall fun t ↦ (levelIntegral_eq_fiber_toReal hw hn t).symm)
  · filter_upwards [ae_finite hm hf] with t ht
    exact ⟨hw.aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).mpr ht⟩

theorem map_nonnegative_weight {v w : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hw : Measurable w) :
    (torusMeasure.withDensity (fun z ↦ ENNReal.ofReal (‖torusOrdinaryGradient v z‖ * w z))).map v =
      volume.withDensity (fiberIntegral v (fun z ↦ ENNReal.ofReal (w z))) := by
  ext1 s hs
  have hvm := (continuous_of_contDiff_lift hv).measurable
  rw [Measure.map_apply hvm hs, withDensity_apply _ (hvm hs), withDensity_apply _ hs]
  simp_rw [ENNReal.ofReal_mul (norm_nonneg _)]
  exact coarea_preimage hv _ hw.ennreal_ofReal hs

theorem nonnegative_coarea_test {v w : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hw : Measurable w) (hn : ∀ z, 0 ≤ w z)
    (hi : Integrable (fun z ↦ ‖torusOrdinaryGradient v z‖ * w z) torusMeasure)
    (φ : ℝ → ℝ) (hφ : Measurable φ) :
    (∫ z, φ (v z) * (‖torusOrdinaryGradient v z‖ * w z) ∂torusMeasure) =
      ∫ t : ℝ, φ t * levelIntegral v w t := by
  have hvm := (continuous_of_contDiff_lift hv).measurable
  have hgm : Measurable (fun z ↦ ENNReal.ofReal (‖torusOrdinaryGradient v z‖ * w z)) :=
    ((measurable_torusOrdinaryGradient v).norm.mul hw).ennreal_ofReal
  have hfin := ae_finite (aemeasurable_fiberIntegral hv _ hw.ennreal_ofReal)
    (fiber_lintegral_lt_top hv hw hn hi)
  calc
    (∫ z, φ (v z) * (‖torusOrdinaryGradient v z‖ * w z) ∂torusMeasure) =
        ∫ z, φ (v z) ∂torusMeasure.withDensity
          (fun z ↦ ENNReal.ofReal (‖torusOrdinaryGradient v z‖ * w z)) := by
      rw [integral_withDensity_eq_integral_toReal_smul hgm
        (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [] with z
      change φ (v z) * (‖torusOrdinaryGradient v z‖ * w z) =
        (ENNReal.ofReal (‖torusOrdinaryGradient v z‖ * w z)).toReal • φ (v z)
      rw [ENNReal.toReal_ofReal (mul_nonneg (norm_nonneg _) (hn z)), smul_eq_mul, mul_comm]
    _ = ∫ t, φ t ∂(torusMeasure.withDensity
          (fun z ↦ ENNReal.ofReal (‖torusOrdinaryGradient v z‖ * w z))).map v :=
      (integral_map_of_stronglyMeasurable hvm hφ.stronglyMeasurable).symm
    _ = ∫ t, φ t ∂volume.withDensity (fiberIntegral v (fun z ↦ ENNReal.ofReal (w z))) := by
      rw [map_nonnegative_weight hv hw]
    _ = ∫ t : ℝ, φ t * levelIntegral v w t := by
      rw [integral_withDensity_eq_integral_toReal_smul₀
        (aemeasurable_fiberIntegral hv _ hw.ennreal_ofReal) hfin]
      simp only [levelIntegral_eq_fiber_toReal hw hn, smul_eq_mul, mul_comm]


/-- Signed coarea with bounded measurable weights and bounded measurable
value tests. The two integrability assertions are part of the conclusion. -/
theorem bounded_signed_coarea {v w : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hw : Measurable w) {C : ℝ} (hb : ∀ z, |w z| ≤ C) :
    Integrable (levelIntegral v w) volume ∧
      (∀ᵐ t : ℝ, IntegrableOn w {z | v z = t} physicalCurveMeasure) ∧
      ∀ (φ : ℝ → ℝ), Measurable φ → ∀ B : ℝ, (∀ t, |φ t| ≤ B) →
        (∫ z, φ (v z) * (‖torusOrdinaryGradient v z‖ * w z) ∂torusMeasure) =
          ∫ t : ℝ, φ t * levelIntegral v w t := by
  let wp : Torus → ℝ := fun z ↦ max (w z) 0
  let wm : Torus → ℝ := fun z ↦ max (-w z) 0
  have hp : Measurable wp := hw.max measurable_const
  have hm : Measurable wm := hw.neg.max measurable_const
  have hpn (z : Torus) : 0 ≤ wp z := le_max_right _ _
  have hmn (z : Torus) : 0 ≤ wm z := le_max_right _ _
  have hpbound (z : Torus) : ‖wp z‖ ≤ |C| := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hpn z)]
    exact max_le ((le_abs_self _).trans ((hb z).trans (le_abs_self _))) (abs_nonneg _)
  have hmbound (z : Torus) : ‖wm z‖ ≤ |C| := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hmn z)]
    exact max_le ((neg_le_abs _).trans ((hb z).trans (le_abs_self _))) (abs_nonneg _)
  have hg : Integrable (fun z ↦ ‖torusOrdinaryGradient v z‖) torusMeasure :=
    memLp_one_iff_integrable.mp (ContinuousMap.memLp (μ := torusMeasure) (p := 1) ℝ
      ⟨_, continuous_norm_gradient hv⟩)
  have hip : Integrable (fun z ↦ ‖torusOrdinaryGradient v z‖ * wp z) torusMeasure := by
    simpa only [mul_comm] using hg.bdd_mul hp.aestronglyMeasurable (Eventually.of_forall hpbound)
  have him : Integrable (fun z ↦ ‖torusOrdinaryGradient v z‖ * wm z) torusMeasure := by
    simpa only [mul_comm] using hg.bdd_mul hm.aestronglyMeasurable (Eventually.of_forall hmbound)
  obtain ⟨hlp, haep⟩ := nonnegative_level_integrability hv hp hpn hip
  obtain ⟨hlm, haem⟩ := nonnegative_level_integrability hv hm hmn him
  have he (z : Torus) : w z = wp z - wm z := by
    dsimp only [wp, wm]
    by_cases hz : 0 ≤ w z
    · rw [max_eq_left hz, max_eq_right (neg_nonpos.mpr hz), sub_zero]
    · have hz' : w z ≤ 0 := le_of_not_ge hz
      rw [max_eq_right hz', max_eq_left (neg_nonneg.mpr hz')]
      ring
  have hfi : ∀ᵐ t : ℝ, IntegrableOn w {z | v z = t} physicalCurveMeasure := by
    filter_upwards [haep, haem] with t hp' hm'
    exact (hp'.sub hm').congr (Eventually.of_forall fun z ↦ (he z).symm)
  have hle : levelIntegral v w =ᵐ[volume]
      (fun t ↦ levelIntegral v wp t - levelIntegral v wm t) := by
    filter_upwards [haep, haem] with t hp' hm'
    unfold levelIntegral
    rw [← integral_sub hp' hm']
    exact integral_congr_ae (Eventually.of_forall he)
  refine ⟨(hlp.sub hlm).congr hle.symm, hfi, ?_⟩
  intro φ hφ B hB
  have hvm := (continuous_of_contDiff_lift hv).measurable
  have hipφ : Integrable (fun z ↦ φ (v z) * (‖torusOrdinaryGradient v z‖ * wp z)) torusMeasure :=
    hip.bdd_mul (hφ.comp hvm).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ by simpa only [Real.norm_eq_abs] using (hB (v z)).trans (le_abs_self B))
  have himφ : Integrable (fun z ↦ φ (v z) * (‖torusOrdinaryGradient v z‖ * wm z)) torusMeasure :=
    him.bdd_mul (hφ.comp hvm).aestronglyMeasurable
      (Eventually.of_forall fun z ↦ by simpa only [Real.norm_eq_abs] using (hB (v z)).trans (le_abs_self B))
  have hlpφ : Integrable (fun t ↦ φ t * levelIntegral v wp t) volume :=
    hlp.bdd_mul hφ.aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by simpa only [Real.norm_eq_abs] using (hB t).trans (le_abs_self B))
  have hlmφ : Integrable (fun t ↦ φ t * levelIntegral v wm t) volume :=
    hlm.bdd_mul hφ.aestronglyMeasurable
      (Eventually.of_forall fun t ↦ by simpa only [Real.norm_eq_abs] using (hB t).trans (le_abs_self B))
  calc
    (∫ z, φ (v z) * (‖torusOrdinaryGradient v z‖ * w z) ∂torusMeasure) =
        ∫ z, φ (v z) * (‖torusOrdinaryGradient v z‖ * wp z) -
          φ (v z) * (‖torusOrdinaryGradient v z‖ * wm z) ∂torusMeasure := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [he z]
      ring
    _ = (∫ z, φ (v z) * (‖torusOrdinaryGradient v z‖ * wp z) ∂torusMeasure) -
        ∫ z, φ (v z) * (‖torusOrdinaryGradient v z‖ * wm z) ∂torusMeasure :=
      integral_sub hipφ himφ
    _ = (∫ t : ℝ, φ t * levelIntegral v wp t) -
        ∫ t : ℝ, φ t * levelIntegral v wm t := by
      rw [nonnegative_coarea_test hv hp hpn hip φ hφ, nonnegative_coarea_test hv hm hmn him φ hφ]
    _ = ∫ t : ℝ, φ t * levelIntegral v w t := by
      rw [← integral_sub hlpφ hlmφ]
      apply integral_congr_ae
      filter_upwards [hle] with t ht
      change φ t * levelIntegral v wp t - φ t * levelIntegral v wm t = φ t * levelIntegral v w t
      rw [ht]
      ring


/-- Signed continuous weights have continuous physical level integrals at
regular values. The neighboring regular-value set is used explicitly. -/
theorem levelIntegral_continuousAt_regular {v w : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hw : Continuous w) {t : ℝ} (ht : t ∉ StationarySard.torusCriticalValues v) :
    IntegrableOn w {z | v z = t} physicalCurveMeasure ∧
      ContinuousAt (levelIntegral v w) t := by
  let wp : Torus → ℝ := fun z ↦ max (w z) 0
  let wm : Torus → ℝ := fun z ↦ max (-w z) 0
  have hp : Continuous wp := hw.max continuous_const
  have hm : Continuous wm := hw.neg.max continuous_const
  have hpn (z : Torus) : 0 ≤ wp z := le_max_right _ _
  have hmn (z : Torus) : 0 ≤ wm z := le_max_right _ _
  have he (z : Torus) : w z = wp z - wm z := by
    dsimp only [wp, wm]
    by_cases hz : 0 ≤ w z
    · rw [max_eq_left hz, max_eq_right (neg_nonpos.mpr hz), sub_zero]
    · have hz' : w z ≤ 0 := le_of_not_ge hz
      rw [max_eq_right hz', max_eq_left (neg_nonneg.mpr hz')]
      ring
  have hip := StationaryLevelContinuity.level_integral_continuousAt_regular hv hp hpn ht
  have him := StationaryLevelContinuity.level_integral_continuousAt_regular hv hm hmn ht
  have heq (r : ℝ) (hr : r ∉ StationarySard.torusCriticalValues v) :
      levelIntegral v w r = levelIntegral v wp r - levelIntegral v wm r := by
    have hrp := (StationaryLevelContinuity.level_integral_continuousAt_regular hv hp hpn hr).1
    have hrm := (StationaryLevelContinuity.level_integral_continuousAt_regular hv hm hmn hr).1
    unfold levelIntegral
    rw [← integral_sub hrp hrm]
    exact integral_congr_ae (Eventually.of_forall he)
  refine ⟨(hip.1.sub him.1).congr (Eventually.of_forall fun z ↦ (he z).symm), ?_⟩
  apply (hip.2.sub him.2).congr_of_eventuallyEq
  have hR : (StationarySard.torusCriticalValues v)ᶜ ∈ 𝓝 t :=
    (StationarySard.isCompact_torusCriticalValues hv).isClosed.isOpen_compl.mem_nhds ht
  filter_upwards [hR] with r hr
  exact heq r hr

end PeriodicAttractiveLogGas.StationarySignedCoarea
