import LeanResearch.PeriodicAttractiveLogGas.StationaryLevelContinuity
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Analysis.ODE.ExistUnique

/-!
The compact regular boundary in the supplied square-torus isoperimetric
argument. All local level geometry comes from the actual physical IFT
charts. The development record separates finite-component and perimeter
results from the further global circle-parametrization obligation.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal NNReal BigOperators

namespace PeriodicAttractiveLogGas.StationaryLevelCircles

open StationarySard StationaryLevelGeometry StationaryLevelBoundary
  StationaryCoarea StationaryLevelContinuity

theorem isCompact_level {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) (t : ℝ) :
    IsCompact {z : Torus | v z = t} :=
  (isClosed_eq (continuous_of_contDiff_lift hv) continuous_const).isCompact

/-- Finiteness is for the actual physical one-dimensional Hausdorff measure.
It follows from the constructed chart integral theorem at every regular
value, including empty fibres. -/
theorem physicalCurveMeasure_level_lt_top {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    physicalCurveMeasure {z : Torus | v z = t} < (∞ : ℝ≥0∞) := by
  have hi : IntegrableOn (fun _ : Torus ↦ (1 : ℝ)) {z | v z = t} physicalCurveMeasure :=
    (level_integral_continuousAt_regular hv continuous_const (fun _ ↦ zero_le_one) ht).1
  have hh := hi.hasFiniteIntegral
  simpa only [HasFiniteIntegral, enorm_one, lintegral_const, one_mul,
    Measure.restrict_apply MeasurableSet.univ, univ_inter] using hh

theorem physicalCurveMeasure_frontier_lt_top {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    physicalCurveMeasure (frontier {z : Torus | t < v z}) < (∞ : ℝ≥0∞) := by
  rw [frontier_strict_superlevel_eq hv ht]
  exact physicalCurveMeasure_level_lt_top hv ht

/-- The actual IFT chart can be shrunk inside any given torus neighborhood
so that its literal level section is connected. The fixed-value section
of the target ball is a ball in the one-dimensional derivative kernel. -/
theorem exists_connected_level_neighborhood {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {z : Torus} (hz : torusOrdinaryGradient v z ≠ 0)
    {O : Set Torus} (hO : O ∈ 𝓝 z) :
    ∃ V : Set Torus, IsOpen V ∧ z ∈ V ∧ V ⊆ O ∧
      IsConnected (V ∩ {w | v w = v z}) := by
  obtain ⟨a, rfl⟩ := torusQuotient_surjective z
  have ha : fderiv ℝ (fun x : PlanarSpace ↦ v (torusQuotient x)) a ≠ 0 := by
    intro hzero
    exact hz ((mem_torusCriticalPoints_lift_iff v a).mpr hzero)
  obtain ⟨P, e, U, -, -, -, hinverse, hU, hUa, hUt, -, hG, -, hcoord⟩ :=
    exists_planar_regular_chart hv ha
  let K := ↥(fderiv ℝ (fun x : PlanarSpace ↦ v (torusQuotient x)) a).ker
  let b : ℝ × K := (v (torusQuotient a), 0)
  have hcont : ContinuousAt (fun p : ℝ × K ↦ torusQuotient (e.symm p)) b :=
    isOpenQuotientMap_torusQuotient.continuous.continuousAt.comp
      (hG.contDiffAt (hU.mem_nhds hUa)).continuousAt
  have hpre : {p : ℝ × K | torusQuotient (e.symm p) ∈ O} ∈ 𝓝 b := by
    apply hcont.eventually_mem
    simpa only [b, hinverse] using hO
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hU.mem_nhds hUa) hpre)
  let W : Set (ℝ × K) := Metric.ball b r
  have hWU : W ⊆ U := fun p hp ↦ (hball hp).1
  let V : Set Torus := torusQuotient '' (e.symm '' W)
  have hV : IsOpen V := isOpenQuotientMap_torusQuotient.isOpenMap _
    (e.isOpen_image_symm_of_subset_target Metric.isOpen_ball (hWU.trans hUt))
  have hzV : torusQuotient a ∈ V :=
    ⟨a, ⟨b, Metric.mem_ball_self hr, hinverse⟩, rfl⟩
  have hVO : V ⊆ O := by
    rintro w ⟨x, ⟨p, hp, rfl⟩, rfl⟩
    exact (hball hp).2
  have hsection (y : K) :
      (v (torusQuotient a), y) ∈ W ↔ y ∈ Metric.ball (0 : K) r := by
    simp only [W, b, Metric.mem_ball, dist_prod_same_left]
  have he : V ∩ {w | v w = v (torusQuotient a)} =
      (fun y : K ↦ torusQuotient (e.symm (v (torusQuotient a), y))) ''
        Metric.ball (0 : K) r := by
    ext w
    constructor
    · rintro ⟨⟨x, ⟨⟨p, y⟩, hp, rfl⟩, rfl⟩, hw⟩
      have hpval : v (torusQuotient (e.symm (p, y))) = p :=
        (hcoord (p, y) (hWU hp)).1
      have hpt : p = v (torusQuotient a) := hpval.symm.trans hw
      subst p
      exact ⟨y, (hsection y).mp hp, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      have hp := (hsection y).mpr hy
      exact ⟨⟨e.symm (v (torusQuotient a), y),
        ⟨(v (torusQuotient a), y), hp, rfl⟩, rfl⟩,
        (hcoord _ (hWU hp)).1⟩
  have hc : ContinuousOn
      (fun y : K ↦ torusQuotient (e.symm (v (torusQuotient a), y)))
      (Metric.ball (0 : K) r) :=
    isOpenQuotientMap_torusQuotient.continuous.comp_continuousOn
      ((chartSection_immersion hU hG (fun p hp ↦ (hcoord p hp).2)
        (v (torusQuotient a))).1.continuousOn.mono
          (fun y hy ↦ hWU ((hsection y).mpr hy)))
  refine ⟨V, hV, hzV, hVO, ?_⟩
  rw [he]
  exact (Metric.isConnected_ball hr).image _ hc

/-- Actual connected components of the literal level, with no duplicate
representatives and no empty component when the level is empty. -/
def levelComponents (v : Torus → ℝ) (t : ℝ) : Set (Set Torus) :=
  Set.range (fun z : {z : Torus | v z = t} ↦ connectedComponentIn {w | v w = t} z)

/-- The actual level has only finitely many connected components. Compactness
is applied to the open neighborhoods constructed above, each of whose level
sections is contained in one actual connected component. -/
theorem finite_levelComponents {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) : (levelComponents v t).Finite := by
  classical
  have hlocal (z : {z : Torus | v z = t}) :
      ∃ V : Set Torus, IsOpen V ∧ (z : Torus) ∈ V ∧ IsConnected (V ∩ {w | v w = t}) := by
    obtain ⟨V, hV, hzV, -, hc⟩ := exists_connected_level_neighborhood hv
      (show torusOrdinaryGradient v z ≠ 0 from fun hz ↦ ht ⟨z, hz, z.property⟩)
      (O := univ) univ_mem
    have hzval : v (z : Torus) = t := z.property
    exact ⟨V, hV, hzV, by simpa only [hzval] using hc⟩
  choose V hVo hVz hVc using hlocal
  have hcover : {z : Torus | v z = t} ⊆ ⋃ z : {z : Torus | v z = t}, V z := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z, hz⟩, hVz ⟨z, hz⟩⟩
  obtain ⟨I, hI⟩ := (isCompact_level hv t).elim_finite_subcover V hVo hcover
  apply (I.finite_toSet.image
    (fun z : {z : Torus | v z = t} ↦ connectedComponentIn {w | v w = t} z)).subset
  rintro C ⟨z, rfl⟩
  obtain ⟨y, hy, hzy⟩ := mem_iUnion₂.mp (hI z.property)
  have hsub : V y ∩ {w | v w = t} ⊆ connectedComponentIn {w | v w = t} y :=
    (hVc y).isPreconnected.subset_connectedComponentIn ⟨hVz y, y.property⟩ inter_subset_right
  exact ⟨y, hy, connectedComponentIn_eq (hsub ⟨hzy, z.property⟩)⟩

theorem levelComponent_subset {v : Torus → ℝ} {t : ℝ} {C : Set Torus}
    (hC : C ∈ levelComponents v t) : C ⊆ {z | v z = t} := by
  obtain ⟨z, rfl⟩ := hC
  exact connectedComponentIn_subset _ _

theorem levelComponent_isConnected {v : Torus → ℝ} {t : ℝ} {C : Set Torus}
    (hC : C ∈ levelComponents v t) : IsConnected C := by
  obtain ⟨z, rfl⟩ := hC
  exact isConnected_connectedComponentIn_iff.mpr z.property

theorem levelComponent_isCompact {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} {C : Set Torus} (hC : C ∈ levelComponents v t) : IsCompact C := by
  obtain ⟨z, rfl⟩ := hC
  let : CompactSpace {z : Torus | v z = t} :=
    isCompact_iff_compactSpace.mp (isCompact_level hv t)
  change IsCompact (connectedComponentIn {w : Torus | v w = t} (z : Torus))
  rw [connectedComponentIn_eq_image z.property]
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

theorem levelComponents_disjoint {v : Torus → ℝ} {t : ℝ} {C D : Set Torus}
    (hC : C ∈ levelComponents v t) (hD : D ∈ levelComponents v t) (hne : C ≠ D) :
    Disjoint C D := by
  obtain ⟨x, rfl⟩ := hC
  obtain ⟨y, rfl⟩ := hD
  apply Set.disjoint_left.mpr
  intro z hx hy
  exact hne ((connectedComponentIn_eq hx).trans (connectedComponentIn_eq hy).symm)

theorem iUnion_levelComponents (v : Torus → ℝ) (t : ℝ) :
    (⋃ C : levelComponents v t, (C : Set Torus)) = {z | v z = t} := by
  ext z
  constructor
  · intro hz
    obtain ⟨C, hzC⟩ := mem_iUnion.mp hz
    exact levelComponent_subset C.property hzC
  · intro hz
    refine mem_iUnion.mpr ⟨⟨connectedComponentIn {w | v w = t} z, ?_⟩, ?_⟩
    · exact ⟨⟨z, hz⟩, rfl⟩
    · exact mem_connectedComponentIn hz

theorem physicalCurveMeasure_component_lt_top {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {C : Set Torus} (hC : C ∈ levelComponents v t) :
    physicalCurveMeasure C < (∞ : ℝ≥0∞) :=
  (measure_mono (levelComponent_subset hC)).trans_lt (physicalCurveMeasure_level_lt_top hv ht)

/-- Countable additivity, with the now-proved finite component index, gives
the literal physical H1 decomposition. The summands are actual connected
components; no parametrization or length formula is assumed here. -/
theorem physicalCurveMeasure_level_eq_sum {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    let := (finite_levelComponents hv ht).fintype
    physicalCurveMeasure {z : Torus | v z = t} =
      ∑ C : levelComponents v t, physicalCurveMeasure (C : Set Torus) := by
  let := (finite_levelComponents hv ht).fintype
  rw [← iUnion_levelComponents v t]
  rw [measure_iUnion]
  · exact tsum_fintype _
  · intro C D hne
    exact levelComponents_disjoint C.property D.property (Subtype.coe_ne_coe.mpr hne)
  · intro C
    exact (levelComponent_isCompact hv C.property).isClosed.measurableSet

theorem physicalPerimeter_eq_sum_components {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    let := (finite_levelComponents hv ht).fintype
    physicalCurveMeasure (frontier {z : Torus | t < v z}) =
      ∑ C : levelComponents v t, physicalCurveMeasure (C : Set Torus) := by
  let := (finite_levelComponents hv ht).fintype
  rw [frontier_strict_superlevel_eq hv ht]
  exact physicalCurveMeasure_level_eq_sum hv ht

theorem physicalPerimeter_real_eq_sum_components {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    let := (finite_levelComponents hv ht).fintype
    physicalCurveMeasure.real (frontier {z : Torus | t < v z}) =
      ∑ C : levelComponents v t, physicalCurveMeasure.real (C : Set Torus) := by
  let := (finite_levelComponents hv ht).fintype
  have hh := congrArg ENNReal.toReal (physicalPerimeter_eq_sum_components hv ht)
  rw [ENNReal.toReal_sum (fun C _ ↦
    (physicalCurveMeasure_component_lt_top hv ht C.property).ne)] at hh
  exact hh

/-- Each actual component is relatively open in the level. The ambient
open isolating set is the complement of the finite union of all the other
compact components. -/
theorem exists_open_isolating_component {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {C : Set Torus} (hC : C ∈ levelComponents v t) :
    ∃ O : Set Torus, IsOpen O ∧ C = O ∩ {z | v z = t} := by
  classical
  let := (finite_levelComponents hv ht).fintype
  let E : Set Torus := ⋃ D : levelComponents v t, if (D : Set Torus) = C then ∅ else D
  have hE : IsClosed E := by
    apply isClosed_iUnion_of_finite
    intro D
    split_ifs
    · exact isClosed_empty
    · exact (levelComponent_isCompact hv D.property).isClosed
  refine ⟨Eᶜ, hE.isOpen_compl, ?_⟩
  ext z
  constructor
  · intro hzC
    refine ⟨?_, levelComponent_subset hC hzC⟩
    intro hzE
    obtain ⟨D, hzD⟩ := mem_iUnion.mp hzE
    by_cases he : (D : Set Torus) = C
    · simp only [he, ite_true, mem_empty_iff_false] at hzD
    · have hzD' : z ∈ (D : Set Torus) := by simpa only [he, ite_false] using hzD
      exact Set.disjoint_left.mp (levelComponents_disjoint D.property hC he) hzD' hzC
  · rintro ⟨hzE, hzL⟩
    let D : levelComponents v t :=
      ⟨connectedComponentIn {w | v w = t} z, ⟨⟨z, hzL⟩, rfl⟩⟩
    have hzD : z ∈ (D : Set Torus) := mem_connectedComponentIn hzL
    by_cases he : (D : Set Torus) = C
    · exact he ▸ hzD
    · exact False.elim (hzE (mem_iUnion.mpr ⟨D, by simpa only [he, ite_false] using hzD⟩))

/-- Counterclockwise quarter-turn in the actual Euclidean plane. -/
def quarterTurn : PlanarSpace ≃ₗᵢ[ℝ] PlanarSpace :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Equiv.swap (0 : Fin 2) 1)).trans
    (LinearIsometryEquiv.piLpCongrRight 2 fun j : Fin 2 ↦
      if j = 0 then (LinearIsometryEquiv.neg ℝ : ℝ ≃ₗᵢ[ℝ] ℝ)
      else LinearIsometryEquiv.refl ℝ ℝ)

@[simp] theorem quarterTurn_apply_zero (x : PlanarSpace) : quarterTurn x 0 = -x 1 := by
  simp [quarterTurn, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

@[simp] theorem quarterTurn_apply_one (x : PlanarSpace) : quarterTurn x 1 = x 0 := by
  simp [quarterTurn, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

theorem inner_quarterTurn (x : PlanarSpace) : inner ℝ x (quarterTurn x) = 0 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring

/-- The actual rotated ordinary gradient on the Euclidean periodic cover. -/
def tangentField (v : Torus → ℝ) (x : PlanarSpace) : PlanarSpace :=
  quarterTurn (rectangleOrdinaryGradient (fun y ↦ v (torusQuotient y)) x)

theorem norm_tangentField (v : Torus → ℝ) (x : PlanarSpace) :
    ‖tangentField v x‖ = ‖torusOrdinaryGradient v (torusQuotient x)‖ := by
  rw [tangentField, quarterTurn.norm_map, torusOrdinaryGradient_lift]

theorem fderiv_tangentField_zero (v : Torus → ℝ) (x : PlanarSpace) :
    fderiv ℝ (fun y : PlanarSpace ↦ v (torusQuotient y)) x (tangentField v x) = 0 := by
  have hh := inner_quarterTurn (rectangleOrdinaryGradient (fun y ↦ v (torusQuotient y)) x)
  simpa only [rectangleOrdinaryGradient, InnerProductSpace.toDual_symm_apply, tangentField]
    using hh

theorem contDiff_tangentField {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    ContDiff ℝ 1 (tangentField v) := by
  let R : (PlanarSpace →L[ℝ] ℝ) →L[ℝ] PlanarSpace :=
    (InnerProductSpace.toDual ℝ PlanarSpace).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hg : ContDiff ℝ 1
      (fun x : PlanarSpace ↦ rectangleOrdinaryGradient (fun y ↦ v (torusQuotient y)) x) := by
    change ContDiff ℝ 1 (R ∘ fderiv ℝ (fun y : PlanarSpace ↦ v (torusQuotient y)))
    exact R.contDiff.comp (hv.fderiv_right (m := 1) (by norm_num))
  exact quarterTurn.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp hg

theorem exists_tangentField_bound {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    ∃ L : ℝ≥0, ∀ x : PlanarSpace, ‖tangentField v x‖ ≤ L := by
  let G : C(Torus, ℝ) := ⟨fun z ↦ ‖torusOrdinaryGradient v z‖, continuous_norm_gradient hv⟩
  refine ⟨‖G‖₊, fun x ↦ ?_⟩
  change ‖tangentField v x‖ ≤ ‖G‖
  rw [norm_tangentField]
  simpa only [G, ContinuousMap.coe_mk, norm_norm] using G.norm_coe_le_norm (torusQuotient x)

/-- Arbitrarily long finite trajectories exist for the actual rotated
gradient. The radius grows with the prescribed time; boundedness comes from
the compact torus and the spatial Lipschitz estimate from C1 on that compact
Euclidean ball. No global-flow existence premise is introduced. -/
theorem exists_tangent_trajectory {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (a : PlanarSpace) (T : ℝ≥0) :
    ∃ γ : ℝ → PlanarSpace, γ 0 = a ∧
      ∀ s ∈ Icc (-(T : ℝ)) T,
        HasDerivWithinAt γ (tangentField v (γ s)) (Icc (-(T : ℝ)) T) s := by
  obtain ⟨L, hL⟩ := exists_tangentField_bound (hv.of_le (by norm_num))
  let R : ℝ≥0 := L * T
  obtain ⟨K, hK⟩ := (contDiff_tangentField hv).contDiffOn.exists_lipschitzOnWith
    (by norm_num) (convex_closedBall a (R : ℝ)) (isCompact_closedBall a (R : ℝ))
  have htime : (0 : ℝ) ∈ Icc (-(T : ℝ)) T := ⟨neg_nonpos.mpr T.coe_nonneg, T.coe_nonneg⟩
  have hp : IsPicardLindelof (fun _ : ℝ ↦ tangentField v) ⟨0, htime⟩ a R 0 L K :=
    IsPicardLindelof.of_time_independent (fun x _ ↦ hL x) hK (by simp [R])
  exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- The source value is constant along each actual tangent trajectory,
including the endpoints of its closed time interval. -/
theorem tangent_trajectory_preserves_level {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {γ : ℝ → PlanarSpace} {T : ℝ≥0}
    (hγ : ∀ s ∈ Icc (-(T : ℝ)) T,
      HasDerivWithinAt γ (tangentField v (γ s)) (Icc (-(T : ℝ)) T) s)
    {s : ℝ} (hs : s ∈ Icc (-(T : ℝ)) T) :
    v (torusQuotient (γ s)) = v (torusQuotient (γ 0)) := by
  have hd (r : ℝ) (hr : r ∈ Icc (-(T : ℝ)) T) :
      HasDerivWithinAt (fun u ↦ v (torusQuotient (γ u))) 0 (Icc (-(T : ℝ)) T) r := by
    have hh := ((hv.differentiable (by norm_num)) (γ r)).hasFDerivAt.comp_hasDerivWithinAt
      r (hγ r hr)
    simpa only [Function.comp_def, fderiv_tangentField_zero] using hh
  have h0 : (0 : ℝ) ∈ Icc (-(T : ℝ)) T := ⟨neg_nonpos.mpr T.coe_nonneg, T.coe_nonneg⟩
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (C := 0)
    hd (fun r hr ↦ by simp) (convex_Icc (-(T : ℝ)) T) h0 hs
  have hz : ‖v (torusQuotient (γ s)) - v (torusQuotient (γ 0))‖ ≤ 0 := by
    simpa only [zero_mul] using hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hz (norm_nonneg _)))

/-- On a regular level the actual trajectories have a uniform positive
speed lower bound, a uniform upper speed bound, and the corresponding
physical-lift Lipschitz estimate. The bounds are independent of time. -/
theorem exists_regular_tangent_trajectories {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {a : PlanarSpace} (ha : v (torusQuotient a) = t) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ L : ℝ≥0, ∀ T : ℝ≥0,
      ∃ γ : ℝ → PlanarSpace, γ 0 = a ∧
        (∀ s ∈ Icc (-(T : ℝ)) T,
          HasDerivWithinAt γ (tangentField v (γ s)) (Icc (-(T : ℝ)) T) s) ∧
        (∀ s ∈ Icc (-(T : ℝ)) T, v (torusQuotient (γ s)) = t) ∧
        (∀ s ∈ Icc (-(T : ℝ)) T, ε ≤ ‖tangentField v (γ s)‖) ∧
        LipschitzOnWith L γ (Icc (-(T : ℝ)) T) := by
  have hv1 := hv.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  obtain ⟨ε, hε, hlow⟩ := exists_regular_band_gradient_lower hv1 ht
  obtain ⟨L, hL⟩ := exists_tangentField_bound hv1
  refine ⟨ε, hε, L, fun T ↦ ?_⟩
  obtain ⟨γ, hγ0, hγ⟩ := exists_tangent_trajectory hv a T
  have hlevel (s : ℝ) (hs : s ∈ Icc (-(T : ℝ)) T) : v (torusQuotient (γ s)) = t := by
    rw [tangent_trajectory_preserves_level hv1 hγ hs, hγ0, ha]
  refine ⟨γ, hγ0, hγ, hlevel, ?_, ?_⟩
  · intro s hs
    rw [norm_tangentField]
    exact hlow _ (by rw [hlevel s hs, sub_self, abs_zero]; exact hε.le)
  · apply (convex_Icc (-(T : ℝ)) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le hγ
    intro s _
    exact_mod_cast hL (γ s)

theorem tangentField_eq_of_quotient_eq (v : Torus → ℝ) {x y : PlanarSpace}
    (hxy : torusQuotient x = torusQuotient y) : tangentField v x = tangentField v y := by
  unfold tangentField
  rw [← torusOrdinaryGradient_lift, ← torusOrdinaryGradient_lift, hxy]

private theorem fderiv_vectorLift_eq_of_quotient_eq (W : Torus → PlanarSpace)
    {x y : PlanarSpace} (hxy : torusQuotient x = torusQuotient y) :
    fderiv ℝ (fun z : PlanarSpace ↦ W (torusQuotient z)) x =
      fderiv ℝ (fun z : PlanarSpace ↦ W (torusQuotient z)) y := by
  obtain ⟨k, rfl⟩ := exists_frequencyVector_of_torusQuotient_eq hxy
  simpa only [torusQuotient_add_frequencyVector] using
    fderiv_comp_add_right (𝕜 := ℝ) (f := fun z : PlanarSpace ↦ W (torusQuotient z))
      (x := x) (frequencyVector k)

theorem fderiv_tangentField_eq_of_quotient_eq (v : Torus → ℝ) {x y : PlanarSpace}
    (hxy : torusQuotient x = torusQuotient y) :
    fderiv ℝ (tangentField v) x = fderiv ℝ (tangentField v) y := by
  have he : tangentField v = fun z : PlanarSpace ↦
      quarterTurn (torusOrdinaryGradient v (torusQuotient z)) := by
    funext z
    rw [torusOrdinaryGradient_lift]
    rfl
  rw [he]
  exact fderiv_vectorLift_eq_of_quotient_eq (fun z ↦ quarterTurn (torusOrdinaryGradient v z)) hxy

/-- Compactness of the original torus bounds the derivative of the actual
periodic tangent field. The resulting global Lipschitz property is proved,
not added to the ODE or circle interfaces as a premise. -/
theorem exists_lipschitz_tangentField {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    ∃ K : ℝ≥0, LipschitzWith K (tangentField v) := by
  let B : Torus → ℝ := fun z ↦ ‖fderiv ℝ (tangentField v) (centeredLift z)‖
  have hB (x : PlanarSpace) : B (torusQuotient x) = ‖fderiv ℝ (tangentField v) x‖ := by
    unfold B
    rw [fderiv_tangentField_eq_of_quotient_eq v (torusQuotient_centeredLift _)]
  have hBc : Continuous B := by
    apply isOpenQuotientMap_torusQuotient.isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, hB] using
      ((contDiff_tangentField hv).fderiv_right (m := 0) (by norm_num)).continuous.norm
  let G : C(Torus, ℝ) := ⟨B, hBc⟩
  refine ⟨‖G‖₊, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le ((contDiff_tangentField hv).differentiable (by norm_num))
  intro x
  have hnorm : ‖fderiv ℝ (tangentField v) x‖ ≤ ‖G‖ := by
    have hh := G.norm_coe_le_norm (torusQuotient x)
    simpa only [G, ContinuousMap.coe_mk, hB, norm_norm] using hh
  exact_mod_cast hnorm

/-- Compatible finite-time solutions glue to a literal global trajectory.
The arbitrary time-index choice disappears locally by ODE uniqueness. -/
theorem exists_global_tangent_trajectory {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x))) (a : PlanarSpace) :
    ∃ γ : ℝ → PlanarSpace, γ 0 = a ∧ ∀ s, HasDerivAt γ (tangentField v (γ s)) s := by
  classical
  obtain ⟨K, hK⟩ := exists_lipschitz_tangentField hv
  have hex (n : ℕ) : ∃ γ : ℝ → PlanarSpace, γ 0 = a ∧
      ∀ s ∈ Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1),
        HasDerivWithinAt γ (tangentField v (γ s)) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) s :=
    exists_tangent_trajectory hv a ⟨(n : ℝ) + 1, by positivity⟩
  choose γ hγ0 hγ using hex
  have hγc (n : ℕ) : ContinuousOn (γ n) (Icc (-((n : ℝ) + 1)) ((n : ℝ) + 1)) :=
    fun s hs ↦ (hγ n s hs).continuousWithinAt
  have hγd (n : ℕ) (s : ℝ) (hs : |s| < (n : ℝ) + 1) :
      HasDerivAt (γ n) (tangentField v (γ n s)) s := by
    have hh := abs_lt.mp hs
    exact (hγ n s ⟨hh.1.le, hh.2.le⟩).hasDerivAt (Icc_mem_nhds hh.1 hh.2)
  have heq (n m : ℕ) (s : ℝ) (hn : |s| ≤ (n : ℝ) + 1) (hm : |s| ≤ (m : ℝ) + 1) :
      γ n s = γ m s := by
    let A : ℝ := min ((n : ℝ) + 1) ((m : ℝ) + 1)
    have hA : 0 < A := lt_min (by positivity) (by positivity)
    have hnA : A ≤ (n : ℝ) + 1 := min_le_left _ _
    have hmA : A ≤ (m : ℝ) + 1 := min_le_right _ _
    have hcn := (hγc n).mono (Icc_subset_Icc (neg_le_neg hnA) hnA)
    have hcm := (hγc m).mono (Icc_subset_Icc (neg_le_neg hmA) hmA)
    have hh := ODE_solution_unique_of_mem_Icc
      (v := fun _ : ℝ ↦ tangentField v) (s := fun _ : ℝ ↦ univ)
      (fun _ _ ↦ hK.lipschitzOnWith) (show (0 : ℝ) ∈ Ioo (-A) A by constructor <;> linarith)
      hcn (fun r hr ↦ hγd n r ((abs_lt.mpr hr).trans_le hnA)) (fun _ _ ↦ mem_univ _)
      hcm (fun r hr ↦ hγd m r ((abs_lt.mpr hr).trans_le hmA)) (fun _ _ ↦ mem_univ _)
      ((hγ0 n).trans (hγ0 m).symm)
    exact hh (abs_le.mp (le_min hn hm))
  have hcover (s : ℝ) : ∃ n : ℕ, |s| < (n : ℝ) + 1 := by
    obtain ⟨n, hn⟩ := exists_nat_gt |s|
    exact ⟨n, by linarith⟩
  choose index hindex using hcover
  let Γ : ℝ → PlanarSpace := fun s ↦ γ (index s) s
  have hΓ (n : ℕ) (s : ℝ) (hs : |s| ≤ (n : ℝ) + 1) : Γ s = γ n s :=
    heq (index s) n s (hindex s).le hs
  refine ⟨Γ, ?_, fun s ↦ ?_⟩
  · rw [hΓ 0 0 (by norm_num), hγ0]
  · have ho : IsOpen {r : ℝ | |r| < (index s : ℝ) + 1} :=
      isOpen_lt continuous_id.abs continuous_const
    have he : Γ =ᶠ[𝓝 s] γ (index s) :=
      (show ∀ᶠ r in 𝓝 s, |r| < (index s : ℝ) + 1 from ho.mem_nhds (hindex s)).mono
        (fun r hr ↦ hΓ (index s) r hr.le)
    rw [hΓ (index s) s (hindex s).le]
    exact (hγd (index s) s (hindex s)).congr_of_eventuallyEq he

/-- Any repeated torus point of an actual global trajectory yields a period
of the entire projected trajectory. Translation invariance is inherited
from the ordinary periodic gradient, and equality comes from ODE uniqueness. -/
theorem tangent_trajectory_periodic_of_eq {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {γ : ℝ → PlanarSpace} (hγ : ∀ s, HasDerivAt γ (tangentField v (γ s)) s)
    {a b : ℝ} (hab : torusQuotient (γ a) = torusQuotient (γ b)) :
    Function.Periodic (fun s ↦ torusQuotient (γ s)) (b - a) := by
  obtain ⟨K, hK⟩ := exists_lipschitz_tangentField hv
  let d : PlanarSpace := γ b - γ a
  have hd : torusQuotient d = 0 := by
    simp only [d, torusQuotient_sub, hab, sub_self]
  have hf (s : ℝ) : HasDerivAt (fun r ↦ γ (r + a)) (tangentField v (γ (s + a))) s := by
    have hs : HasDerivAt (fun r : ℝ ↦ r + a) (1 : ℝ) s := by
      simpa only [id_eq] using (hasDerivAt_id s).add_const a
    simpa only [Function.comp_def, one_smul, mul_one] using!
      (hγ (s + a)).scomp s hs
  have hg (s : ℝ) : HasDerivAt (fun r ↦ γ (r + b) - d)
      (tangentField v (γ (s + b) - d)) s := by
    have he : torusQuotient (γ (s + b) - d) = torusQuotient (γ (s + b)) := by
      rw [torusQuotient_sub, hd, sub_zero]
    rw [tangentField_eq_of_quotient_eq v he]
    have hs : HasDerivAt (fun r : ℝ ↦ r + b) (1 : ℝ) s := by
      simpa only [id_eq] using (hasDerivAt_id s).add_const b
    have hh : HasDerivAt (fun r ↦ γ (r + b)) (tangentField v (γ (s + b))) s := by
      simpa only [Function.comp_def, one_smul, mul_one] using! (hγ (s + b)).scomp s hs
    exact hh.sub_const d
  have hbase : γ (0 + a) = γ (0 + b) - d := by
    dsimp only [d]
    simp only [zero_add]
    abel
  have he : (fun r : ℝ ↦ γ (r + a)) = fun r ↦ γ (r + b) - d :=
    ODE_solution_unique_univ (v := fun _ : ℝ ↦ tangentField v)
      (s := fun _ : ℝ ↦ univ) (t₀ := 0)
      (fun _ ↦ hK.lipschitzOnWith) (fun s ↦ ⟨hf s, mem_univ _⟩)
      (fun s ↦ ⟨hg s, mem_univ _⟩) hbase
  intro s
  have hh := congrArg torusQuotient (congrFun he (s - a))
  change torusQuotient (γ (s - a + a)) = torusQuotient (γ (s - a + b) - d) at hh
  rw [sub_add_cancel, torusQuotient_sub, hd, sub_zero] at hh
  rw [show s - a + b = s + (b - a) by ring] at hh
  exact hh.symm

/-- Actual global regular-level trajectories, with all analytic data and
uniform positive speed derived from the primitive smoothness/regularity
hypotheses. -/
theorem exists_global_regular_tangent_trajectory {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {a : PlanarSpace} (ha : v (torusQuotient a) = t) :
    ∃ γ : ℝ → PlanarSpace, γ 0 = a ∧
      (∀ s, HasDerivAt γ (tangentField v (γ s)) s) ∧
      (∀ s, v (torusQuotient (γ s)) = t) ∧
      ∃ ε : ℝ, 0 < ε ∧ (∀ s, ε ≤ ‖tangentField v (γ s)‖) ∧
        ∃ L : ℝ≥0, LipschitzWith L γ := by
  have hv1 := hv.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)
  obtain ⟨γ, hγ0, hγ⟩ := exists_global_tangent_trajectory hv a
  obtain ⟨ε, hε, hlow⟩ := exists_regular_band_gradient_lower hv1 ht
  obtain ⟨L, hL⟩ := exists_tangentField_bound hv1
  have hlevel (s : ℝ) : v (torusQuotient (γ s)) = t := by
    have hh := tangent_trajectory_preserves_level hv1 (T := ⟨|s|, abs_nonneg s⟩)
      (fun r _ ↦ (hγ r).hasDerivWithinAt) (show s ∈ Icc (-|s|) |s| from
        ⟨neg_abs_le s, le_abs_self s⟩)
    rw [hγ0, ha] at hh
    exact hh
  refine ⟨γ, hγ0, hγ, hlevel, ε, hε, ?_, L, ?_⟩
  · intro s
    rw [norm_tangentField]
    exact hlow _ (by rw [hlevel, sub_self, abs_zero]; exact hε.le)
  · apply lipschitzWith_of_nnnorm_deriv_le (fun s ↦ (hγ s).differentiableAt)
    intro s
    rw [(hγ s).deriv]
    exact_mod_cast hL (γ s)

end PeriodicAttractiveLogGas.StationaryLevelCircles
