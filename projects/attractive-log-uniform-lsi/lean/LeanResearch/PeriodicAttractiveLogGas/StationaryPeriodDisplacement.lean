import LeanResearch.PeriodicAttractiveLogGas.StationaryCurveIntegrals

/-! The period displacement of an actual regular boundary circle.
The vector is a genuine integer lattice vector, and its boundary integral
and physical length are obtained from the proved curve measure formula. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace PeriodicAttractiveLogGas.StationaryPeriodDisplacement
open StationaryCoarea StationarySard StationaryLevelGeometry StationaryLevelCircles
  StationaryCurveIntegrals

theorem continuous_ordinaryGradient {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    Continuous (torusOrdinaryGradient v) := by
  apply isOpenQuotientMap_torusQuotient.isQuotientMap.continuous_iff.mpr
  let R : (PlanarSpace →L[ℝ] ℝ) →L[ℝ] PlanarSpace :=
    (InnerProductSpace.toDual ℝ PlanarSpace).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hc := R.continuous.comp (hv.fderiv_right (m := 0) (by norm_num)).continuous
  simpa only [Function.comp_def, torusOrdinaryGradient_lift, rectangleOrdinaryGradient, R] using! hc

def unitTangent (v : Torus → ℝ) (z : Torus) : PlanarSpace :=
  ‖torusOrdinaryGradient v z‖⁻¹ • quarterTurn (torusOrdinaryGradient v z)

theorem measurable_unitTangent {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    Measurable (unitTangent v) := by
  unfold unitTangent
  exact (continuous_norm_gradient hv).measurable.inv.smul
    (quarterTurn.continuous.comp (continuous_ordinaryGradient hv)).measurable

theorem norm_unitTangent_le (v : Torus → ℝ) (z : Torus) :
    ‖unitTangent v z‖ ≤ 1 := by
  unfold unitTangent
  rw [norm_smul, norm_inv, norm_norm, quarterTurn.norm_map]
  by_cases hz : ‖torusOrdinaryGradient v z‖ = 0
  · simp [hz]
  · rw [inv_mul_cancel₀ hz]

theorem unitTangent_lift (v : Torus → ℝ) (x : PlanarSpace) :
    unitTangent v (torusQuotient x) = ‖tangentField v x‖⁻¹ • tangentField v x := by
  rw [unitTangent, norm_tangentField, torusOrdinaryGradient_lift]
  rfl

theorem period_displacement_integer {γ : ℝ → PlanarSpace} {P : ℝ}
    (hp : Function.Periodic (fun x ↦ torusQuotient (γ x)) P) :
    ∃ k : Frequency, γ P - γ 0 = frequencyVector k := by
  obtain ⟨k, hk⟩ := exists_frequencyVector_of_torusQuotient_eq hp.eq.symm
  exact ⟨k, by rw [hk]; abel⟩

theorem norm_frequencyVector_ge_one {k : Frequency} (hk : k ≠ 0) :
    1 ≤ ‖frequencyVector k‖ := by
  have hex : ∃ j : Fin 2, k j ≠ 0 := by
    by_contra hh
    apply hk
    funext j
    by_contra hj
    exact hh ⟨j, hj⟩
  obtain ⟨j, hj⟩ := hex
  have hpos : (1 : ℤ) ≤ |k j| := by
    have := abs_pos.mpr hj
    omega
  have hc : (1 : ℝ) ≤ |(k j : ℝ)| := by exact_mod_cast hpos
  have hn := PiLp.norm_apply_le (frequencyVector k) j
  exact hc.trans (by simpa only [Real.norm_eq_abs, frequencyVector_apply] using hn)

theorem nonzero_displacement_length {γ γ' : ℝ → PlanarSpace} {P : ℝ}
    (hP : 0 < P) (hγ : ∀ s, HasDerivAt γ (γ' s) s) (hγ' : Continuous γ')
    (hn : ∀ s ∈ Ico 0 P, γ' s ≠ 0)
    (hp : Function.Periodic (fun s ↦ torusQuotient (γ s)) P)
    (hi : InjOn (fun s ↦ torusQuotient (γ s)) (Ico 0 P))
    (hd : γ P ≠ γ 0) :
    1 ≤ physicalCurveMeasure.real (Set.range (fun s ↦ torusQuotient (γ s))) := by
  obtain ⟨k, hk⟩ := period_displacement_integer hp
  have hkn : k ≠ 0 := by
    intro hz
    rw [hz, frequencyVector_zero] at hk
    exact hd (sub_eq_zero.mp hk)
  have hh := norm_frequencyVector_ge_one hkn
  rw [← hk] at hh
  exact hh.trans (displacement_le_length hP hγ hγ' hn hp hi)

/-- The orientation is the original rotated-gradient orientation. No
homology value or oriented boundary integral is supplied as a premise. -/
theorem integral_unitTangent_eq_displacement {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {γ : ℝ → PlanarSpace} {P : ℝ} (hP : 0 < P)
    (hγ : ∀ s, HasDerivAt γ (tangentField v (γ s)) s)
    (hn : ∀ s ∈ Ico 0 P, tangentField v (γ s) ≠ 0)
    (hp : Function.Periodic (fun s ↦ torusQuotient (γ s)) P)
    (hi : InjOn (fun s ↦ torusQuotient (γ s)) (Ico 0 P)) :
    (∫ z in Set.range (fun s ↦ torusQuotient (γ s)), unitTangent v z ∂physicalCurveMeasure) =
      γ P - γ 0 := by
  have hcont : Continuous γ := continuous_iff_continuousAt.mpr fun s ↦ (hγ s).continuousAt
  have hspeed : Continuous (fun s ↦ tangentField v (γ s)) :=
    (contDiff_tangentField hv).continuous.comp hcont
  rw [periodic_range_eq_image hP hp,
    integral_Ico hγ hspeed.measurable hn hi _ (measurable_unitTangent (hv.of_le (by norm_num))).stronglyMeasurable]
  have he : (∫ s in Ico 0 P, ‖tangentField v (γ s)‖ • unitTangent v (torusQuotient (γ s))) =
      ∫ s in Ico 0 P, tangentField v (γ s) := by
    apply setIntegral_congr_fun measurableSet_Ico
    intro s hs
    change ‖tangentField v (γ s)‖ • unitTangent v (torusQuotient (γ s)) = tangentField v (γ s)
    rw [unitTangent_lift, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr (hn s hs)), one_smul]
  rw [he, integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hP.le]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ ↦ hγ s) (hspeed.intervalIntegrable 0 P)

end PeriodicAttractiveLogGas.StationaryPeriodDisplacement
