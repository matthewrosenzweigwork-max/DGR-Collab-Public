import LeanResearch.PeriodicAttractiveLogGas.StationaryOrbitLength

/-! The actual connected components of a regular level are embedded circles.
ODE uniqueness makes distinct trajectory images disjoint. The uniform
positive physical length and finite total level length make their number
finite; compactness then identifies each orbit with one connected component. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal NNReal
namespace PeriodicAttractiveLogGas.StationaryComponentCircles
open StationaryLevelCircles StationaryClosedCurves StationaryOrbitLength
  StationaryCoarea StationarySard

theorem trajectory_ranges_eq_of_eq {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x)))
    {γ η : ℝ → PlanarSpace}
    (hγ : ∀ s, HasDerivAt γ (tangentField v (γ s)) s)
    (hη : ∀ s, HasDerivAt η (tangentField v (η s)) s)
    {a b : ℝ} (hab : torusQuotient (γ a) = torusQuotient (η b)) :
    Set.range (fun s => torusQuotient (γ s)) = Set.range (fun s => torusQuotient (η s)) := by
  obtain ⟨K, hK⟩ := exists_lipschitz_tangentField hv
  let d : PlanarSpace := η b - γ a
  have hd : torusQuotient d = 0 := by
    simp only [d, torusQuotient_sub, hab, sub_self]
  have hf (s : ℝ) : HasDerivAt (fun r => γ (r + a)) (tangentField v (γ (s + a))) s := by
    have hs : HasDerivAt (fun r : ℝ => r + a) (1 : ℝ) s := by
      simpa only [id_eq] using (hasDerivAt_id s).add_const a
    simpa only [Function.comp_def, one_smul] using! (hγ (s + a)).scomp s hs
  have hg (s : ℝ) : HasDerivAt (fun r => η (r + b) - d)
      (tangentField v (η (s + b) - d)) s := by
    have he : torusQuotient (η (s + b) - d) = torusQuotient (η (s + b)) := by
      rw [torusQuotient_sub, hd, sub_zero]
    rw [tangentField_eq_of_quotient_eq v he]
    have hs : HasDerivAt (fun r : ℝ => r + b) (1 : ℝ) s := by
      simpa only [id_eq] using (hasDerivAt_id s).add_const b
    have hh : HasDerivAt (fun r => η (r + b)) (tangentField v (η (s + b))) s := by
      simpa only [Function.comp_def, one_smul] using! (hη (s + b)).scomp s hs
    exact hh.sub_const d
  have hbase : γ (0 + a) = η (0 + b) - d := by
    dsimp only [d]
    simp only [zero_add]
    abel
  have he : (fun r : ℝ => γ (r + a)) = fun r => η (r + b) - d :=
    ODE_solution_unique_univ (v := fun _ : ℝ => tangentField v)
      (s := fun _ : ℝ => univ) (t₀ := 0)
      (fun _ => hK.lipschitzOnWith) (fun s => ⟨hf s, mem_univ _⟩)
      (fun s => ⟨hg s, mem_univ _⟩) hbase
  have hq (r : ℝ) : torusQuotient (γ (r + a)) = torusQuotient (η (r + b)) := by
    have hh := congrArg torusQuotient (congrFun he r)
    simpa only [torusQuotient_sub, hd, sub_zero] using hh
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s - a + b, by simpa only [sub_add_cancel] using (hq (s - a)).symm⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s - b + a, by simpa only [sub_add_cancel] using hq (s - b)⟩

/-- Images of actual global tangent trajectories on the specified level.
This definition contains no connectedness, circle, or perimeter assertion. -/
def orbits (v : Torus → ℝ) (t : ℝ) : Set (Set Torus) :=
  {C | ∃ γ : ℝ → PlanarSpace,
    (∀ s, HasDerivAt γ (tangentField v (γ s)) s) ∧
    (∀ s, v (torusQuotient (γ s)) = t) ∧
    C = Set.range (fun s => torusQuotient (γ s))}

theorem orbit_subset_level {v : Torus → ℝ} {t : ℝ} {C : Set Torus}
    (hC : C ∈ orbits v t) : C ⊆ {z | v z = t} := by
  obtain ⟨γ, _, hlevel, rfl⟩ := hC
  rintro z ⟨s, rfl⟩
  exact hlevel s

theorem orbit_isConnected {v : Torus → ℝ} {t : ℝ} {C : Set Torus}
    (hC : C ∈ orbits v t) : IsConnected C := by
  obtain ⟨γ, hγ, _, rfl⟩ := hC
  have hc := isOpenQuotientMap_torusQuotient.continuous.comp
    (continuous_iff_continuousAt.mpr fun s => (hγ s).continuousAt)
  simpa only [image_univ, Function.comp_def] using (isConnected_univ : IsConnected (univ : Set ℝ)).image _ hc.continuousOn

theorem orbit_circle {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {C : Set Torus} (hC : C ∈ orbits v t) :
    ∃ P : ℝ, 0 < P ∧ ∃ c : C(AddCircle P, Torus), Topology.IsClosedEmbedding c ∧ Set.range c = C := by
  obtain ⟨γ, hγ, hlevel, rfl⟩ := hC
  obtain ⟨P, hP, _, _, c, hc, _, he⟩ := regular_trajectory_circle hv ht hγ hlevel
  exact ⟨P, hP, c, hc, he⟩

theorem orbit_isCompact {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {C : Set Torus} (hC : C ∈ orbits v t) : IsCompact C := by
  obtain ⟨P, hP, c, _, he⟩ := orbit_circle hv ht hC
  let : Fact (0 < P) := ⟨hP⟩
  rw [← he]
  exact isCompact_range c.continuous

theorem orbits_disjoint {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    {C D : Set Torus} (hC : C ∈ orbits v t) (hD : D ∈ orbits v t) (hne : C ≠ D) :
    Disjoint C D := by
  obtain ⟨γ, hγ, _, rfl⟩ := hC
  obtain ⟨η, hη, _, rfl⟩ := hD
  apply Set.disjoint_left.mpr
  rintro z ⟨a, ha⟩ ⟨b, hb⟩
  exact hne (trajectory_ranges_eq_of_eq hv hγ hη (ha.trans hb.symm))

theorem exists_orbit_containing {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {z : Torus} (hz : v z = t) :
    ∃ C : Set Torus, C ∈ orbits v t ∧ z ∈ C := by
  obtain ⟨γ, hγ0, hγ, hlevel, _⟩ := exists_global_regular_tangent_trajectory hv ht
    (a := centeredLift z) (by rw [torusQuotient_centeredLift]; exact hz)
  refine ⟨Set.range (fun s => torusQuotient (γ s)), ⟨γ, hγ, hlevel, rfl⟩, ⟨0, ?_⟩⟩
  change torusQuotient (γ 0) = z
  rw [hγ0, torusQuotient_centeredLift]

theorem iUnion_orbits {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    (⋃ C : orbits v t, (C : Set Torus)) = {z | v z = t} := by
  ext z
  constructor
  · intro hz
    obtain ⟨C, hzC⟩ := mem_iUnion.mp hz
    exact orbit_subset_level C.property hzC
  · intro hz
    obtain ⟨C, hC, hzC⟩ := exists_orbit_containing hv ht hz
    exact mem_iUnion.mpr ⟨⟨C, hC⟩, hzC⟩

/-- Finiteness follows from a proved uniform physical length lower bound,
not from a pre-assumed classification of one-dimensional manifolds. -/
theorem finite_orbits {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) : (orbits v t).Finite := by
  obtain ⟨c, hc, hlower⟩ := exists_uniform_orbit_length_lower hv ht
  have hm (C : orbits v t) : ENNReal.ofReal c ≤ physicalCurveMeasure (C : Set Torus) := by
    obtain ⟨γ, hγ, hlevel, he⟩ := C.property
    rw [he]
    exact hlower γ hγ hlevel
  have hh := Measure.finite_const_le_meas_of_disjoint_iUnion physicalCurveMeasure
    (ENNReal.ofReal_pos.mpr hc) (As := fun C : orbits v t => (C : Set Torus))
    (fun C => (orbit_isCompact hv ht C.property).isClosed.measurableSet)
    (fun C D hne => orbits_disjoint hv C.property D.property (Subtype.coe_ne_coe.mpr hne))
    (by rw [iUnion_orbits hv ht]; exact (physicalCurveMeasure_level_lt_top (hv.of_le (by norm_num)) ht).ne)
  have he : {C : orbits v t | ENNReal.ofReal c ≤ physicalCurveMeasure (C : Set Torus)} = univ :=
    eq_univ_iff_forall.mpr hm
  rw [he] at hh
  exact Set.finite_coe_iff.mp (Finite.of_finite_univ hh)


/-- Each actual orbit is relatively open in the level: its complement
there is the finite union of all the other compact orbits. -/
theorem exists_open_isolating_orbit {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {C : Set Torus} (hC : C ∈ orbits v t) :
    ∃ O : Set Torus, IsOpen O ∧ C = O ∩ {z | v z = t} := by
  classical
  let := (finite_orbits hv ht).fintype
  let E : Set Torus := ⋃ D : orbits v t, if (D : Set Torus) = C then ∅ else D
  have hE : IsClosed E := by
    apply isClosed_iUnion_of_finite
    intro D
    split_ifs
    · exact isClosed_empty
    · exact (orbit_isCompact hv ht D.property).isClosed
  refine ⟨Eᶜ, hE.isOpen_compl, ?_⟩
  ext z
  constructor
  · intro hzC
    refine ⟨?_, orbit_subset_level hC hzC⟩
    intro hzE
    obtain ⟨D, hzD⟩ := mem_iUnion.mp hzE
    by_cases he : (D : Set Torus) = C
    · simp only [he, ite_true, mem_empty_iff_false] at hzD
    · have hzD' : z ∈ (D : Set Torus) := by simpa only [he, ite_false] using hzD
      exact Set.disjoint_left.mp (orbits_disjoint hv D.property hC he) hzD' hzC
  · rintro ⟨hzE, hzL⟩
    obtain ⟨D, hD, hzD⟩ := exists_orbit_containing hv ht hzL
    by_cases he : D = C
    · exact he ▸ hzD
    · exact False.elim (hzE (mem_iUnion.mpr ⟨⟨D, hD⟩,
        by simpa only [he, ite_false] using hzD⟩))

/-- An orbit is exactly the connected component through any of its points.
The proof uses its actual relative openness and closedness just established. -/
theorem orbit_eq_component {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {C : Set Torus} (hC : C ∈ orbits v t)
    {z : Torus} (hz : z ∈ C) : C = connectedComponentIn {w | v w = t} z := by
  have hsub := orbit_subset_level hC
  have hzL := hsub hz
  obtain ⟨O, hO, hCO⟩ := exists_open_isolating_orbit hv ht hC
  let S : Set Torus := {w | v w = t}
  let D : Set S := Subtype.val ⁻¹' C
  have hclosed : IsClosed D := (orbit_isCompact hv ht hC).isClosed.preimage continuous_subtype_val
  have hopen : IsOpen D := by
    have he : D = Subtype.val ⁻¹' O := by
      ext y
      change (y : Torus) ∈ C ↔ (y : Torus) ∈ O
      rw [hCO]
      exact ⟨fun h => h.1, fun h => ⟨h, y.property⟩⟩
    rw [he]
    exact hO.preimage continuous_subtype_val
  have hclopen : IsClopen D := by constructor <;> assumption
  apply Set.Subset.antisymm
  · exact (orbit_isConnected hC).isPreconnected.subset_connectedComponentIn hz hsub
  · rw [connectedComponentIn_eq_image hzL]
    rintro w ⟨y, hy, rfl⟩
    exact hclopen.connectedComponent_subset (show (⟨z, hzL⟩ : S) ∈ D from hz) hy

theorem orbits_eq_levelComponents {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) : orbits v t = levelComponents v t := by
  ext C
  constructor
  · intro hC
    obtain ⟨z, hz⟩ := (orbit_isConnected hC).nonempty
    exact ⟨⟨z, orbit_subset_level hC hz⟩, (orbit_eq_component hv ht hC hz).symm⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨C, hC, hzC⟩ := exists_orbit_containing hv ht z.property
    change connectedComponentIn {w | v w = t} (z : Torus) ∈ orbits v t
    rw [← orbit_eq_component hv ht hC hzC]
    exact hC

/-- Source Lemma `lem:iso`, the regular-boundary circle decomposition.
Together with `finite_levelComponents`, `iUnion_levelComponents`, and
`levelComponents_disjoint`, this gives a finite disjoint union of actual
embedded circles. The physical perimeter sum was proved separately.

The parametrization retains its actual tangent equation and physical
quotient lift, which are needed for the remaining length and topology
arguments; an abstract homeomorphism type is not substituted for them. -/
theorem levelComponent_parametrization {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {C : Set Torus} (hC : C ∈ levelComponents v t) :
    ∃ γ : ℝ → PlanarSpace,
      (∀ s, HasDerivAt γ (tangentField v (γ s)) s) ∧
      (∀ s, v (torusQuotient (γ s)) = t) ∧
      ∃ P : ℝ, 0 < P ∧ Function.Periodic (fun s => torusQuotient (γ s)) P ∧
        InjOn (fun s => torusQuotient (γ s)) (Ico 0 P) ∧
        ∃ c : C(AddCircle P, Torus), Topology.IsClosedEmbedding c ∧
          (∀ s : ℝ, c (s : AddCircle P) = torusQuotient (γ s)) ∧ Set.range c = C := by
  have ho : C ∈ orbits v t := by rw [orbits_eq_levelComponents hv ht]; exact hC
  obtain ⟨γ, hγ, hlevel, hCeq⟩ := ho
  obtain ⟨P, hP, hp, hi, c, hc, he, hr⟩ := regular_trajectory_circle hv ht hγ hlevel
  exact ⟨γ, hγ, hlevel, P, hP, hp, hi, c, hc, he, hr.trans hCeq.symm⟩

end PeriodicAttractiveLogGas.StationaryComponentCircles
