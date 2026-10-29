import LeanResearch.PeriodicAttractiveLogGas.StationaryBoundaryCancellation

/-! The essential-boundary alternative in the square-torus isoperimetric
argument. Nonzero integer displacements must occur at least twice because
the actual oriented boundary integral is zero. If the perimeter is below
two, every component instead has a genuinely closed periodic planar lift. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace PeriodicAttractiveLogGas.StationaryEssentialBoundary
open StationaryCoarea StationarySard StationaryLevelGeometry StationaryLevelCircles
  StationaryComponentCircles StationaryPeriodDisplacement StationaryBoundaryCancellation

theorem parametrization_with_lift_image {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} (ht : t ∉ torusCriticalValues v) {C : Set Torus} (hC : C ∈ levelComponents v t) :
    ∃ γ : ℝ → PlanarSpace,
      (∀ s, HasDerivAt γ (tangentField v (γ s)) s) ∧
      (∀ s, v (torusQuotient (γ s)) = t) ∧
      ∃ P : ℝ, 0 < P ∧ Function.Periodic (fun s ↦ torusQuotient (γ s)) P ∧
        InjOn (fun s ↦ torusQuotient (γ s)) (Ico 0 P) ∧
        Set.range (fun s ↦ torusQuotient (γ s)) = C := by
  obtain ⟨γ, hγ, hlevel, P, hP, hp, hi, c, _hc, he, hr⟩ := levelComponent_parametrization hv ht hC
  let : Fact (0 < P) := ⟨hP⟩
  refine ⟨γ, hγ, hlevel, P, hP, hp, hi, ?_⟩
  rw [← hr]
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨(s : AddCircle P), he s⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨r, _hr, rfl⟩ := AddCircle.eq_coe_Ico s
    exact ⟨r, (he r).symm⟩

theorem nonzero_component_integral_length {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} (ht : t ∉ torusCriticalValues v) {C : Set Torus} (hC : C ∈ levelComponents v t)
    (hn : (∫ z in C, unitTangent v z ∂physicalCurveMeasure) ≠ 0) :
    1 ≤ physicalCurveMeasure.real C := by
  obtain ⟨γ, hγ, hlevel, P, hP, hp, hi, hr⟩ := parametrization_with_lift_image hv ht hC
  have hspeed (s : ℝ) : tangentField v (γ s) ≠ 0 := by
    intro hz
    have hnorm : ‖torusOrdinaryGradient v (torusQuotient (γ s))‖ = 0 := by
      rw [← norm_tangentField, hz, norm_zero]
    exact ht ⟨torusQuotient (γ s), norm_eq_zero.mp hnorm, hlevel s⟩
  have hd := integral_unitTangent_eq_displacement hv hP hγ (fun s _ ↦ hspeed s) hp hi
  rw [hr] at hd
  have hne : γ P ≠ γ 0 := by
    intro he
    rw [he, sub_self] at hd
    exact hn hd
  rw [← hr]
  exact nonzero_displacement_length hP hγ
    ((contDiff_tangentField hv).continuous.comp (continuous_iff_continuousAt.mpr fun s ↦ (hγ s).continuousAt))
    (fun s _ ↦ hspeed s) hp hi hne

theorem perimeter_ge_two_of_nonzero_component {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} (ht : t ∉ torusCriticalValues v) {C : Set Torus} (hC : C ∈ levelComponents v t)
    (hn : (∫ z in C, unitTangent v z ∂physicalCurveMeasure) ≠ 0) :
    2 ≤ physicalCurveMeasure.real (frontier {z | t < v z}) := by
  classical
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  have hv2 : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  let := (finite_levelComponents hv1 ht).fintype
  let c : levelComponents v t := ⟨C, hC⟩
  let D : levelComponents v t → PlanarSpace := fun A ↦ ∫ z in (A : Set Torus), unitTangent v z ∂physicalCurveMeasure
  let L : levelComponents v t → ℝ := fun A ↦ physicalCurveMeasure.real (A : Set Torus)
  have hsum : (∑ A, D A) = 0 := sum_component_unitTangent_integrals_zero hv ht
  have hnonzero : D c ≠ 0 := hn
  have hex : ∃ A : levelComponents v t, A ≠ c ∧ D A ≠ 0 := by
    by_contra h
    have hz (A : levelComponents v t) (hA : A ≠ c) : D A = 0 := by
      by_contra hD
      exact h ⟨A, hA, hD⟩
    have hs : (∑ A, D A) = D c :=
      Finset.sum_eq_single c (fun A _ hA ↦ hz A hA) (by simp)
    exact hnonzero (hs.symm.trans hsum)
  obtain ⟨a, hac, ha⟩ := hex
  have hc1 : 1 ≤ L c := nonzero_component_integral_length hv2 ht hC hn
  have ha1 : 1 ≤ L a := nonzero_component_integral_length hv2 ht a.property ha
  have hln (A : levelComponents v t) : 0 ≤ L A := ENNReal.toReal_nonneg
  have hpair : L c + L a ≤ ∑ A, L A := by
    have hs := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ ({c, a} : Finset (levelComponents v t)))
      (fun A _ _ ↦ hln A)
    simpa only [Finset.sum_pair hac.symm] using hs
  have hp := physicalPerimeter_real_eq_sum_components hv1 ht
  change physicalCurveMeasure.real (frontier {z | t < v z}) = ∑ A, L A at hp
  rw [hp]
  linarith only [hc1, ha1, hpair]

theorem lift_periodic_of_closed {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {γ : ℝ → PlanarSpace} {P : ℝ}
    (hγ : ∀ s, HasDerivAt γ (tangentField v (γ s)) s) (hclosed : γ P = γ 0) :
    Function.Periodic γ P := by
  obtain ⟨K, hK⟩ := exists_lipschitz_tangentField hv
  have hs (s : ℝ) : HasDerivAt (fun r ↦ γ (r + P)) (tangentField v (γ (s + P))) s := by
    have ha : HasDerivAt (fun r : ℝ ↦ r + P) (1 : ℝ) s := by
      simpa only [id_eq] using (hasDerivAt_id s).add_const P
    simpa only [Function.comp_def, one_smul] using! (hγ (s + P)).scomp s ha
  have he : (fun r : ℝ ↦ γ (r + P)) = γ :=
    ODE_solution_unique_univ (v := fun _ : ℝ ↦ tangentField v)
      (s := fun _ : ℝ ↦ univ) (t₀ := 0)
      (fun _ ↦ hK.lipschitzOnWith) (fun s ↦ ⟨hs s, mem_univ _⟩)
      (fun s ↦ ⟨hγ s, mem_univ _⟩) (by simpa only [zero_add] using hclosed)
  exact fun s ↦ congrFun he s

/-- Below perimeter two, every actual component has a closed planar lift.
The conclusion is stronger than a bare assertion of contractibility: it
retains the source tangent equation, the injective period, and exact image. -/
theorem closed_component_lift_of_perimeter_lt_two {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} (ht : t ∉ torusCriticalValues v)
    (hper : physicalCurveMeasure.real (frontier {z | t < v z}) < 2)
    {C : Set Torus} (hC : C ∈ levelComponents v t) :
    ∃ γ : ℝ → PlanarSpace,
      (∀ s, HasDerivAt γ (tangentField v (γ s)) s) ∧
      (∀ s, v (torusQuotient (γ s)) = t) ∧
      ∃ P : ℝ, 0 < P ∧ Function.Periodic γ P ∧
        InjOn (fun s ↦ torusQuotient (γ s)) (Ico 0 P) ∧
        Set.range (fun s ↦ torusQuotient (γ s)) = C := by
  have hv2 : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  obtain ⟨γ, hγ, hlevel, P, hP, hp, hi, hr⟩ := parametrization_with_lift_image hv2 ht hC
  have hzero : (∫ z in C, unitTangent v z ∂physicalCurveMeasure) = 0 := by
    by_contra hn
    exact (not_le_of_gt hper) (perimeter_ge_two_of_nonzero_component hv ht hC hn)
  have hn (s : ℝ) : tangentField v (γ s) ≠ 0 := by
    intro hz
    have hnorm : ‖torusOrdinaryGradient v (torusQuotient (γ s))‖ = 0 := by
      rw [← norm_tangentField, hz, norm_zero]
    exact ht ⟨torusQuotient (γ s), norm_eq_zero.mp hnorm, hlevel s⟩
  have hd := integral_unitTangent_eq_displacement hv2 hP hγ (fun s _ ↦ hn s) hp hi
  rw [hr, hzero] at hd
  exact ⟨γ, hγ, hlevel, P, hP, lift_periodic_of_closed hv2 hγ (sub_eq_zero.mp hd.symm), hi, hr⟩

end PeriodicAttractiveLogGas.StationaryEssentialBoundary
