import LeanResearch.PeriodicAttractiveLogGas.ClosedLoopWidths

/-! A coordinate cut missing a regular boundary of perimeter below two.
All coordinate projection measures are computed in the actual unit circle.
The closed-loop width estimate retains the decisive factor one half. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace PeriodicAttractiveLogGas.StationaryCoordinateCuts
open StationaryCoarea StationarySard StationaryLevelGeometry StationaryLevelCircles
  StationaryEssentialBoundary StationaryCurveIntegrals ClosedLoopWidths

theorem circle_dist_coe_le (x y : ℝ) :
    dist (x : UnitAddCircle) (y : UnitAddCircle) ≤ |x - y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub]
  exact QuotientAddGroup.norm_mk_le_norm

theorem circle_image_interval_volume_le {a b : ℝ} :
    volume (((↑) : ℝ → UnitAddCircle) '' Icc a b) ≤ ENNReal.ofReal (b - a) := by
  have hsub : ((↑) : ℝ → UnitAddCircle) '' Icc a b ⊆
      Metric.closedBall (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2) := by
    rintro z ⟨x, hx, rfl⟩
    exact (circle_dist_coe_le x ((a + b) / 2)).trans
      (abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  calc
    volume (((↑) : ℝ → UnitAddCircle) '' Icc a b) ≤
        volume (Metric.closedBall (((a + b) / 2 : ℝ) : UnitAddCircle) ((b - a) / 2)) := measure_mono hsub
    _ = ENNReal.ofReal (min 1 (b - a)) := by rw [AddCircle.volume_closedBall]; congr 2; ring
    _ ≤ ENNReal.ofReal (b - a) := ENNReal.ofReal_le_ofReal (min_le_right _ _)

theorem component_projection_volume_le {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} (ht : t ∉ torusCriticalValues v)
    (hper : physicalCurveMeasure.real (frontier {z | t < v z}) < 2)
    {C : Set Torus} (hC : C ∈ levelComponents v t) (j : Fin 2) :
    volume ((fun z : Torus ↦ z j) '' C) ≤ ENNReal.ofReal (physicalCurveMeasure.real C / 2) := by
  obtain ⟨γ, hγ, _hlevel, P, hP, hp, hi, hr⟩ := closed_component_lift_of_perimeter_lt_two hv ht hper hC
  have hcont : Continuous γ := continuous_iff_continuousAt.mpr fun s ↦ (hγ s).continuousAt
  have hspeed : Continuous (fun s ↦ tangentField v (γ s)) :=
    (contDiff_tangentField (hv.of_le (by simp))).continuous.comp hcont
  have hn (s : ℝ) : tangentField v (γ s) ≠ 0 := by
    intro hz
    have hg : torusOrdinaryGradient v (torusQuotient (γ s)) = 0 := by
      apply norm_eq_zero.mp
      rw [← norm_tangentField, hz, norm_zero]
    exact ht ⟨torusQuotient (γ s), hg, _hlevel s⟩
  have hpq : Function.Periodic (fun s ↦ torusQuotient (γ s)) P :=
    fun s ↦ congrArg torusQuotient (hp s)
  obtain ⟨a, b, hab, hbounds, hwidth⟩ := exists_coordinate_interval hP hγ hspeed hp j
  have hlen := periodic_length_real hP hγ hspeed.measurable (fun s _ ↦ hn s) hpq hi
  rw [hr] at hlen
  have hsub : (fun z : Torus ↦ z j) '' C ⊆ ((↑) : ℝ → UnitAddCircle) '' Icc a b := by
    rintro z ⟨x, hx, rfl⟩
    rw [← hr] at hx
    obtain ⟨s, rfl⟩ := hx
    exact ⟨γ s j, hbounds s, rfl⟩
  refine (measure_mono hsub).trans (circle_image_interval_volume_le.trans ?_)
  apply ENNReal.ofReal_le_ofReal
  rw [hlen]
  linarith only [hwidth]

theorem level_projection_volume_lt_one {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} (ht : t ∉ torusCriticalValues v)
    (hper : physicalCurveMeasure.real (frontier {z | t < v z}) < 2) (j : Fin 2) :
    volume ((fun z : Torus ↦ z j) '' {z | v z = t}) < 1 := by
  classical
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  let := (finite_levelComponents hv1 ht).fintype
  have hsub : (fun z : Torus ↦ z j) '' {z | v z = t} =
      ⋃ C : levelComponents v t, (fun z : Torus ↦ z j) '' (C : Set Torus) := by
    rw [← iUnion_levelComponents v t, image_iUnion]
  rw [hsub]
  calc
    volume (⋃ C : levelComponents v t, (fun z : Torus ↦ z j) '' (C : Set Torus)) ≤
        ∑ C : levelComponents v t, volume ((fun z : Torus ↦ z j) '' (C : Set Torus)) := by
      simpa only [tsum_fintype] using measure_iUnion_le
        (fun C : levelComponents v t ↦ (fun z : Torus ↦ z j) '' (C : Set Torus))
    _ ≤ ∑ C : levelComponents v t, ENNReal.ofReal (physicalCurveMeasure.real (C : Set Torus) / 2) :=
      Finset.sum_le_sum fun C _ ↦ component_projection_volume_le hv ht hper C.property j
    _ = ENNReal.ofReal (physicalCurveMeasure.real (frontier {z | t < v z}) / 2) := by
      have hn (C : levelComponents v t) : 0 ≤ physicalCurveMeasure.real (C : Set Torus) / 2 :=
        div_nonneg ENNReal.toReal_nonneg (by norm_num)
      have hh : ENNReal.ofReal (∑ C : levelComponents v t, physicalCurveMeasure.real (C : Set Torus) / 2) =
          ∑ C : levelComponents v t, ENNReal.ofReal (physicalCurveMeasure.real (C : Set Torus) / 2) :=
        ENNReal.ofReal_sum_of_nonneg (fun C _ ↦ hn C)
      rw [← hh, ← Finset.sum_div]
      have hp := physicalPerimeter_real_eq_sum_components hv1 ht
      change physicalCurveMeasure.real (frontier {z | t < v z}) =
        ∑ C : levelComponents v t, physicalCurveMeasure.real (C : Set Torus) at hp
      rw [hp]
    _ < 1 := by
      rw [← ENNReal.ofReal_one]
      exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num : (0 : ℝ) < 1)).mpr (by linarith only [hper])

/-- Both coordinates are selected at once, independently of a component
parametrization. No boundary point lies on either coordinate cut. -/
theorem exists_coordinate_cuts {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} (ht : t ∉ torusCriticalValues v)
    (hper : physicalCurveMeasure.real (frontier {z | t < v z}) < 2) :
    ∃ p : Torus, ∀ z : Torus, v z = t → ∀ j : Fin 2, z j ≠ p j := by
  have hex (j : Fin 2) : ∃ a : UnitAddCircle, a ∉ (fun z : Torus ↦ z j) '' {z | v z = t} := by
    by_contra hh
    have hs : (fun z : Torus ↦ z j) '' {z | v z = t} = univ := by
      apply eq_univ_of_forall
      intro a
      by_contra ha
      exact hh ⟨a, ha⟩
    have hm := level_projection_volume_lt_one hv ht hper j
    rw [hs] at hm
    simp only [AddCircle.measure_univ, ENNReal.ofReal_one, lt_self_iff_false] at hm
  choose p hp using hex
  refine ⟨p, fun z hz j hj ↦ hp j ?_⟩
  exact ⟨z, hz, hj⟩

end PeriodicAttractiveLogGas.StationaryCoordinateCuts
