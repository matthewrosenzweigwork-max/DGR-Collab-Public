import LeanResearch.PeriodicAttractiveLogGas.StationaryLevelContinuity

/-!
Physical length of a genuinely injective torus curve. The local formula
is the proved lower-dimensional area formula. Finite small-ball covers
and disjoint measurable pieces globalize it without assuming a length
identity. This supports the regular-boundary construction in source
lemma `lem:iso`; it does not assert the sharp torus inequality.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal Topology

namespace PeriodicAttractiveLogGas.StationaryCurveLength

open StationaryCoarea StationaryLevelContinuity

theorem area_small {γ : ℝ → PlanarSpace}
    {D : ℝ → ℝ →L[ℝ] PlanarSpace} {s : Set ℝ} {a : PlanarSpace}
    (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt γ (D x) s x)
    (hDi : ∀ x ∈ s, Function.Injective (D x))
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) s)
    (hb : ∀ x ∈ s, γ x ∈ Metric.ball a (1 / 8 : ℝ)) :
    physicalCurveMeasure ((fun x ↦ torusQuotient (γ x)) '' s) =
      ∫⁻ x in s, ENNReal.ofReal (D x).toLinearMap.normDet := by
  have hgi : InjOn γ s := fun x hx y hy h ↦ hi hx hy (congrArg torusQuotient h)
  simpa using chart_lintegral (K := ℝ) (by simp) hs hD hDi hgi hb
    (fun _ ↦ 1) measurable_const

theorem area_finite_cover {γ : ℝ → PlanarSpace}
    (hγ : Measurable γ) {D : ℝ → ℝ →L[ℝ] PlanarSpace}
    (centers : Finset PlanarSpace) {s : Set ℝ} (hs : MeasurableSet s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt γ (D x) s x)
    (hDi : ∀ x ∈ s, Function.Injective (D x))
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) s)
    (hc : ∀ x ∈ s, ∃ a ∈ centers, γ x ∈ Metric.ball a (1 / 8 : ℝ)) :
    physicalCurveMeasure ((fun x ↦ torusQuotient (γ x)) '' s) =
      ∫⁻ x in s, ENNReal.ofReal (D x).toLinearMap.normDet := by
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
        simp only [B, C, mem_union, mem_inter_iff, mem_sdiff, mem_preimage]
        tauto
      have hDB : ∀ x ∈ B, HasFDerivWithinAt γ (D x) B x :=
        fun x hx ↦ (hD x hx.1).mono hBs
      have hDC : ∀ x ∈ C, HasFDerivWithinAt γ (D x) C x :=
        fun x hx ↦ (hD x hx.1).mono hCs
      have hsmall := area_small hB hDB (fun x hx ↦ hDi x hx.1)
        (hi.mono hBs) (fun x hx ↦ hx.2)
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
        physicalCurveMeasure ((fun x ↦ torusQuotient (γ x)) '' s) =
            physicalCurveMeasure ((fun x ↦ torusQuotient (γ x)) '' B) +
              physicalCurveMeasure ((fun x ↦ torusQuotient (γ x)) '' C) := by
          rw [← hcover, image_union, measure_union hqd hqm]
        _ = (∫⁻ x in B, ENNReal.ofReal (D x).toLinearMap.normDet) +
            ∫⁻ x in C, ENNReal.ofReal (D x).toLinearMap.normDet := by rw [hsmall, hrest]
        _ = ∫⁻ x in s, ENNReal.ofReal (D x).toLinearMap.normDet := by
          rw [← lintegral_union hC hBC, hcover]

theorem area_compact_of_measurable {γ : ℝ → PlanarSpace}
    (hγ : Measurable γ) {D : ℝ → ℝ →L[ℝ] PlanarSpace} {s : Set ℝ}
    (hs : IsCompact s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt γ (D x) s x)
    (hDi : ∀ x ∈ s, Function.Injective (D x))
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) s) :
    physicalCurveMeasure ((fun x ↦ torusQuotient (γ x)) '' s) =
      ∫⁻ x in s, ENNReal.ofReal (D x).toLinearMap.normDet := by
  classical
  have hc : ContinuousOn γ s := fun x hx ↦ (hD x hx).continuousWithinAt
  obtain ⟨A, _, hA, hcover⟩ := (hs.image_of_continuousOn hc).finite_cover_balls
    (by norm_num : (0 : ℝ) < 1 / 8)
  apply area_finite_cover hγ hA.toFinset hs.measurableSet hD hDi hi
  intro x hx
  have hh := hcover (mem_image_of_mem γ hx)
  obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp hh
  exact ⟨a, by simpa using ha, hxa⟩

theorem area_compact {γ : ℝ → PlanarSpace}
    {D : ℝ → ℝ →L[ℝ] PlanarSpace} {s : Set ℝ}
    (hs : IsCompact s)
    (hD : ∀ x ∈ s, HasFDerivWithinAt γ (D x) s x)
    (hDi : ∀ x ∈ s, Function.Injective (D x))
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) s) :
    physicalCurveMeasure ((fun x ↦ torusQuotient (γ x)) '' s) =
      ∫⁻ x in s, ENNReal.ofReal (D x).toLinearMap.normDet := by
  classical
  let φ : ℝ → PlanarSpace := s.piecewise γ (fun _ ↦ 0)
  have hφ : Measurable φ := ContinuousOn.measurable_piecewise
    (fun x hx ↦ (hD x hx).continuousWithinAt) continuous_const.continuousOn hs.measurableSet
  have he : ∀ x ∈ s, φ x = γ x := by
    intro x hx
    simp [φ, hx]
  have hφD : ∀ x ∈ s, HasFDerivWithinAt φ (D x) s x :=
    fun x hx ↦ (hD x hx).congr (fun y hy ↦ he y hy) (he x hx)
  have hφi : InjOn (fun x ↦ torusQuotient (φ x)) s := by
    intro x hx y hy h
    apply hi hx hy
    simpa only [he x hx, he y hy] using h
  have hh := area_compact_of_measurable hφ hs hφD hDi hφi
  have him : (fun x ↦ torusQuotient (φ x)) '' s =
      (fun x ↦ torusQuotient (γ x)) '' s := by
    apply Set.image_congr
    intro x hx
    rw [he x hx]
  rwa [him] at hh

theorem normDet_velocity (v : PlanarSpace) :
    (ContinuousLinearMap.toSpanSingleton ℝ v).toLinearMap.normDet = ‖v‖ := by
  by_cases hv : v = 0
  · subst v
    simp
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hu : ‖‖v‖⁻¹ • v‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
  let e := LinearIsometry.toSpanSingleton ℝ PlanarSpace hu
  have he : (ContinuousLinearMap.toSpanSingleton ℝ v).toLinearMap =
      ‖v‖ • e.toLinearMap := by
    apply LinearMap.ext
    intro x
    change x • v = ‖v‖ • (x • (‖v‖⁻¹ • v))
    rw [smul_smul, smul_smul]
    congr 1
    field_simp
  rw [he, LinearMap.normDet_smul, e.normDet_eq_one]
  simp

theorem velocity_injective {v : PlanarSpace} (hv : v ≠ 0) :
    Function.Injective (ContinuousLinearMap.toSpanSingleton ℝ v) := by
  intro a b hab
  have hh : (a - b) • v = 0 := by
    change a • v = b • v at hab
    rw [sub_smul, hab, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hh).resolve_right hv)

theorem length_compact {γ γ' : ℝ → PlanarSpace} {s : Set ℝ}
    (hs : IsCompact s)
    (hγ : ∀ x ∈ s, HasDerivWithinAt γ (γ' x) s x)
    (hn : ∀ x ∈ s, γ' x ≠ 0)
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) s) :
    physicalCurveMeasure ((fun x ↦ torusQuotient (γ x)) '' s) =
      ∫⁻ x in s, ENNReal.ofReal ‖γ' x‖ := by
  have h := area_compact hs (fun x hx ↦ (hγ x hx).hasFDerivWithinAt)
    (fun x hx ↦ velocity_injective (hn x hx)) hi
  simpa only [normDet_velocity] using h

theorem length_Icc {γ γ' : ℝ → PlanarSpace} {a b : ℝ}
    (hγ : ∀ x ∈ Icc a b, HasDerivWithinAt γ (γ' x) (Icc a b) x)
    (hn : ∀ x ∈ Icc a b, γ' x ≠ 0)
    (hi : InjOn (fun x ↦ torusQuotient (γ x)) (Icc a b)) :
    physicalCurveMeasure ((fun x ↦ torusQuotient (γ x)) '' Icc a b) =
      ∫⁻ x in Icc a b, ENNReal.ofReal ‖γ' x‖ :=
  length_compact isCompact_Icc hγ hn hi

end PeriodicAttractiveLogGas.StationaryCurveLength
