import LeanResearch.PeriodicAttractiveLogGas.StationaryComponentCircles

/-! Weighted curve integration for the actual physical torus measure.
This extends the checked local area formula to one injective traversal.
It is used to compare a lifted boundary displacement with its length. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace PeriodicAttractiveLogGas.StationaryCurveIntegrals
open StationaryCoarea StationaryLevelContinuity StationaryCurveLength

theorem lintegral_small {γ : ℝ → PlanarSpace}
    {D : ℝ → ℝ →L[ℝ] PlanarSpace} {s : Set ℝ} {a : PlanarSpace}
    (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt γ (D x) s x)
    (hDi : ∀ x ∈ s, Function.Injective (D x))
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) s)
    (hb : ∀ x ∈ s, γ x ∈ Metric.ball a (1 / 8 : ℝ))
    (w : Torus → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ z in (fun x ↦ torusQuotient (γ x)) '' s, w z ∂physicalCurveMeasure) =
      ∫⁻ x in s, ENNReal.ofReal (D x).toLinearMap.normDet * w (torusQuotient (γ x)) := by
  exact chart_lintegral (K := ℝ) (by simp) hs hD hDi
    (fun x hx y hy h ↦ hi hx hy (congrArg torusQuotient h)) hb w hw

theorem lintegral_finite_cover {γ : ℝ → PlanarSpace}
    (hγ : Measurable γ) {D : ℝ → ℝ →L[ℝ] PlanarSpace}
    (centers : Finset PlanarSpace) {s : Set ℝ} (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt γ (D x) s x)
    (hDi : ∀ x ∈ s, Function.Injective (D x))
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) s)
    (hc : ∀ x ∈ s, ∃ a ∈ centers, γ x ∈ Metric.ball a (1 / 8 : ℝ))
    (w : Torus → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ z in (fun x ↦ torusQuotient (γ x)) '' s, w z ∂physicalCurveMeasure) =
      ∫⁻ x in s, ENNReal.ofReal (D x).toLinearMap.normDet * w (torusQuotient (γ x)) := by
  classical
  induction centers using Finset.induction_on generalizing s with
  | empty =>
      have he : s = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        obtain ⟨a, ha, _⟩ := hc x hx
        simp at ha
      simp [he]
  | @insert a centers ha ih =>
      let B : Set ℝ := s ∩ γ ⁻¹' Metric.ball a (1 / 8 : ℝ)
      let C : Set ℝ := s \ γ ⁻¹' Metric.ball a (1 / 8 : ℝ)
      have hB : MeasurableSet B := hs.inter (hγ Metric.isOpen_ball.measurableSet)
      have hC : MeasurableSet C := hs.diff (hγ Metric.isOpen_ball.measurableSet)
      have hBs : B ⊆ s := inter_subset_left
      have hCs : C ⊆ s := sdiff_subset
      have hBC : Disjoint B C := by
        rw [Set.disjoint_left]
        intro x hx hy
        exact hy.2 hx.2
      have hcover : B ∪ C = s := by
        ext x
        simp only [B, C, mem_union, mem_inter_iff, Set.mem_sdiff, mem_preimage]
        tauto
      have hDB : ∀ x ∈ B, HasFDerivWithinAt γ (D x) B x :=
        fun x hx ↦ (hD x hx.1).mono hBs
      have hDC : ∀ x ∈ C, HasFDerivWithinAt γ (D x) C x :=
        fun x hx ↦ (hD x hx.1).mono hCs
      have hsmall := lintegral_small hB hDB (fun x hx ↦ hDi x hx.1)
        (hi.mono hBs) (fun x hx ↦ hx.2) w hw
      have hrest := ih hC hDC (fun x hx ↦ hDi x hx.1) (hi.mono hCs) (by
        intro x hx
        obtain ⟨b, hb, hxb⟩ := hc x hx.1
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact False.elim (hx.2 hxb)
        · exact ⟨b, hb, hxb⟩)
      have hqcont : ContinuousOn (fun x ↦ torusQuotient (γ x)) C :=
        isOpenQuotientMap_torusQuotient.continuous.comp_continuousOn
          (fun x hx ↦ (hDC x hx).continuousWithinAt)
      have hqm : MeasurableSet ((fun x ↦ torusQuotient (γ x)) '' C) :=
        hC.image_of_continuousOn_injOn hqcont (hi.mono hCs)
      have hqd : Disjoint ((fun x ↦ torusQuotient (γ x)) '' B)
          ((fun x ↦ torusQuotient (γ x)) '' C) := by
        rw [Set.disjoint_left]
        rintro z ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
        have he := hi (hCs hy) (hBs hx) hxy
        subst y
        exact hy.2 hx.2
      calc
        (∫⁻ z in (fun x ↦ torusQuotient (γ x)) '' s, w z ∂physicalCurveMeasure) =
            (∫⁻ z in (fun x ↦ torusQuotient (γ x)) '' B, w z ∂physicalCurveMeasure) +
              ∫⁻ z in (fun x ↦ torusQuotient (γ x)) '' C, w z ∂physicalCurveMeasure := by
          rw [← hcover, image_union, lintegral_union hqm hqd]
        _ = (∫⁻ x in B, ENNReal.ofReal (D x).toLinearMap.normDet * w (torusQuotient (γ x))) +
            ∫⁻ x in C, ENNReal.ofReal (D x).toLinearMap.normDet * w (torusQuotient (γ x)) := by
          rw [hsmall, hrest]
        _ = ∫⁻ x in s, ENNReal.ofReal (D x).toLinearMap.normDet * w (torusQuotient (γ x)) := by
          rw [← lintegral_union hC hBC, hcover]

theorem lintegral_Ico {γ γ' : ℝ → PlanarSpace} {a b : ℝ}
    (hγ : ∀ x, HasDerivAt γ (γ' x) x)
    (hn : ∀ x ∈ Ico a b, γ' x ≠ 0)
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) (Ico a b))
    (w : Torus → ℝ≥0∞) (hw : Measurable w) :
    (∫⁻ z in (fun x ↦ torusQuotient (γ x)) '' Ico a b, w z ∂physicalCurveMeasure) =
      ∫⁻ x in Ico a b, ENNReal.ofReal ‖γ' x‖ * w (torusQuotient (γ x)) := by
  classical
  have hcont : Continuous γ := continuous_iff_continuousAt.mpr fun x ↦ (hγ x).continuousAt
  obtain ⟨A, _, hA, hcover⟩ := (isCompact_Icc.image hcont).finite_cover_balls
    (by norm_num : (0 : ℝ) < 1 / 8)
  have hh := lintegral_finite_cover hcont.measurable hA.toFinset measurableSet_Ico
    (fun x _ ↦ (hγ x).hasDerivWithinAt.hasFDerivWithinAt)
    (fun x hx ↦ velocity_injective (hn x hx)) hi (by
      intro x hx
      obtain ⟨c, hc, hxc⟩ := mem_iUnion₂.mp (hcover (mem_image_of_mem γ (Ico_subset_Icc_self hx)))
      exact ⟨c, by simpa using hc, hxc⟩) w hw
  simpa only [normDet_velocity] using hh

theorem length_Ico {γ γ' : ℝ → PlanarSpace} {a b : ℝ}
    (hγ : ∀ x, HasDerivAt γ (γ' x) x)
    (hn : ∀ x ∈ Ico a b, γ' x ≠ 0)
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) (Ico a b)) :
    physicalCurveMeasure ((fun x ↦ torusQuotient (γ x)) '' Ico a b) =
      ∫⁻ x in Ico a b, ENNReal.ofReal ‖γ' x‖ := by
  simpa using lintegral_Ico hγ hn hi (fun _ ↦ 1) measurable_const


/-- The curve measure is the push-forward of the actual speed density. -/
theorem map_speed_Ico {γ γ' : ℝ → PlanarSpace} {a b : ℝ}
    (hγ : ∀ x, HasDerivAt γ (γ' x) x) (hγ' : Measurable γ')
    (hn : ∀ x ∈ Ico a b, γ' x ≠ 0)
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) (Ico a b)) :
    Measure.map (fun x ↦ torusQuotient (γ x))
      ((volume.restrict (Ico a b)).withDensity (fun x ↦ ENNReal.ofReal ‖γ' x‖)) =
        physicalCurveMeasure.restrict ((fun x ↦ torusQuotient (γ x)) '' Ico a b) := by
  have hq : Measurable (fun x ↦ torusQuotient (γ x)) :=
    (isOpenQuotientMap_torusQuotient.continuous.comp
      (continuous_iff_continuousAt.mpr fun x ↦ (hγ x).continuousAt)).measurable
  apply Measure.ext_of_lintegral
  intro w hw
  rw [lintegral_map' hw.aemeasurable hq.aemeasurable]
  have hm := lintegral_withDensity_eq_lintegral_mul (volume.restrict (Ico a b))
    hγ'.norm.ennreal_ofReal (hw.comp hq)
  simp only [Function.comp_def, Pi.mul_apply] at hm
  rw [hm]
  exact (lintegral_Ico hγ hn hi w hw).symm

/-- Signed and vector-valued curve integration, with no absolute-value
replacement of the integrand. -/
theorem integral_Ico {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ γ' : ℝ → PlanarSpace} {a b : ℝ}
    (hγ : ∀ x, HasDerivAt γ (γ' x) x) (hγ' : Measurable γ')
    (hn : ∀ x ∈ Ico a b, γ' x ≠ 0)
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) (Ico a b))
    (w : Torus → E) (hw : StronglyMeasurable w) :
    (∫ z in (fun x ↦ torusQuotient (γ x)) '' Ico a b, w z ∂physicalCurveMeasure) =
      ∫ x in Ico a b, ‖γ' x‖ • w (torusQuotient (γ x)) := by
  have hq : Measurable (fun x ↦ torusQuotient (γ x)) :=
    (isOpenQuotientMap_torusQuotient.continuous.comp
      (continuous_iff_continuousAt.mpr fun x ↦ (hγ x).continuousAt)).measurable
  rw [← map_speed_Ico hγ hγ' hn hi, integral_map_of_stronglyMeasurable hq hw,
    integral_withDensity_eq_integral_toReal_smul hγ'.norm.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (norm_nonneg _)]

theorem length_Ico_real {γ γ' : ℝ → PlanarSpace} {a b : ℝ}
    (hγ : ∀ x, HasDerivAt γ (γ' x) x) (hγ' : Measurable γ')
    (hn : ∀ x ∈ Ico a b, γ' x ≠ 0)
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) (Ico a b)) :
    physicalCurveMeasure.real ((fun x ↦ torusQuotient (γ x)) '' Ico a b) =
      ∫ x in Ico a b, ‖γ' x‖ := by
  change (physicalCurveMeasure _).toReal = _
  rw [length_Ico hγ hn hi, ← integral_toReal hγ'.norm.ennreal_ofReal.aemeasurable
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (norm_nonneg _)]

theorem periodic_range_eq_image {A : Type*} {φ : ℝ → A} {P : ℝ}
    (hP : 0 < P) (hp : Function.Periodic φ P) :
    Set.range φ = φ '' Ico 0 P := by
  let : Fact (0 < P) := ⟨hP⟩
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨r, hr, he⟩ := AddCircle.eq_coe_Ico (s : AddCircle P)
    refine ⟨r, hr, ?_⟩
    simpa only [Function.Periodic.lift_coe] using congrArg hp.lift he
  · rintro ⟨s, _, rfl⟩
    exact ⟨s, rfl⟩

theorem periodic_length_real {γ γ' : ℝ → PlanarSpace} {P : ℝ}
    (hP : 0 < P) (hγ : ∀ x, HasDerivAt γ (γ' x) x) (hγ' : Measurable γ')
    (hn : ∀ x ∈ Ico 0 P, γ' x ≠ 0)
    (hp : Function.Periodic (fun x ↦ torusQuotient (γ x)) P)
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) (Ico 0 P)) :
    physicalCurveMeasure.real (Set.range (fun x ↦ torusQuotient (γ x))) =
      ∫ x in (0 : ℝ)..P, ‖γ' x‖ := by
  rw [periodic_range_eq_image hP hp, length_Ico_real hγ hγ' hn hi,
    integral_Ico_eq_integral_Ioc, intervalIntegral.integral_of_le hP.le]

theorem displacement_le_length {γ γ' : ℝ → PlanarSpace} {P : ℝ}
    (hP : 0 < P) (hγ : ∀ x, HasDerivAt γ (γ' x) x) (hγ' : Continuous γ')
    (hn : ∀ x ∈ Ico 0 P, γ' x ≠ 0)
    (hp : Function.Periodic (fun x ↦ torusQuotient (γ x)) P)
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) (Ico 0 P)) :
    ‖γ P - γ 0‖ ≤ physicalCurveMeasure.real (Set.range (fun x ↦ torusQuotient (γ x))) := by
  rw [periodic_length_real hP hγ hγ'.measurable hn hp hi,
    ← intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hγ x) (hγ'.intervalIntegrable 0 P)]
  exact intervalIntegral.norm_integral_le_integral_norm hP.le

end PeriodicAttractiveLogGas.StationaryCurveIntegrals
