import LeanResearch.PeriodicAttractiveLogGas.StationaryCoarea
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
The boundary of an actual regular strict superlevel set. Local two-sided
variation is proved from the nonzero physical derivative by Fermat's theorem;
it is not inferred from an almost-everywhere coarea identity. The torus
topology, Haar measure and physical Hausdorff measure remain the existing ones.
See the development note for the separate status of the pointwise fibre
continuity upgrade and for root-owned checking evidence.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace PeriodicAttractiveLogGas.StationaryLevelBoundary

open StationarySard StationaryLevelGeometry StationaryCoarea

/-- A noncritical point has a strictly larger value in every torus
neighborhood. A contrary neighborhood would give a local maximum of the
actual periodic lift and hence a zero physical derivative. -/
theorem exists_gt_mem_nhds {v : Torus → ℝ} {z : Torus}
    (hz : torusOrdinaryGradient v z ≠ 0) {s : Set Torus} (hs : s ∈ 𝓝 z) :
    ∃ w ∈ s, v z < v w := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective z
  by_contra hn
  have hle : ∀ w ∈ s, v w ≤ v (torusQuotient x) := by
    intro w hw
    exact le_of_not_gt fun hlt ↦ hn ⟨w, hw, hlt⟩
  have hq : ContinuousAt torusQuotient x :=
    isOpenQuotientMap_torusQuotient.continuous.continuousAt
  have hm : IsLocalMax (fun y : PlanarSpace ↦ v (torusQuotient y)) x := by
    filter_upwards [hq.eventually_mem hs] with y hy
    exact hle _ hy
  have hc : torusQuotient x ∈ torusCriticalPoints v :=
    (mem_torusCriticalPoints_lift_iff v x).mpr hm.fderiv_eq_zero
  exact hz hc

/-- A noncritical point also has a strictly smaller value in every torus
neighborhood. This uses the actual lift's local-minimum derivative theorem. -/
theorem exists_lt_mem_nhds {v : Torus → ℝ} {z : Torus}
    (hz : torusOrdinaryGradient v z ≠ 0) {s : Set Torus} (hs : s ∈ 𝓝 z) :
    ∃ w ∈ s, v w < v z := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective z
  by_contra hn
  have hle : ∀ w ∈ s, v (torusQuotient x) ≤ v w := by
    intro w hw
    exact le_of_not_gt fun hlt ↦ hn ⟨w, hw, hlt⟩
  have hq : ContinuousAt torusQuotient x :=
    isOpenQuotientMap_torusQuotient.continuous.continuousAt
  have hm : IsLocalMin (fun y : PlanarSpace ↦ v (torusQuotient y)) x := by
    filter_upwards [hq.eventually_mem hs] with y hy
    exact hle _ hy
  have hc : torusQuotient x ∈ torusCriticalPoints v :=
    (mem_torusCriticalPoints_lift_iff v x).mpr hm.fderiv_eq_zero
  exact hz hc

/-- Literal two-sided value variation at every point of every regular level.
No null exceptional set is introduced. -/
theorem regular_level_two_sided {v : Torus → ℝ} {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {z : Torus} (hz : v z = t)
    {s : Set Torus} (hs : s ∈ 𝓝 z) :
    (∃ w ∈ s, v w < t) ∧ (∃ w ∈ s, t < v w) := by
  have hg : torusOrdinaryGradient v z ≠ 0 := fun h ↦ ht ⟨z, h, hz⟩
  constructor
  · simpa only [hz] using exists_lt_mem_nhds hg hs
  · simpa only [hz] using exists_gt_mem_nhds hg hs

/-- The closure of the strict superlevel set is the closed superlevel set
at an actual regular value. The reverse inclusion uses local value variation. -/
theorem closure_strict_superlevel_eq {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    closure {z | t < v z} = {z | t ≤ v z} := by
  have hvc : Continuous v := continuous_of_contDiff_lift hv
  apply Subset.antisymm
  · apply closure_minimal ?_ (isClosed_le continuous_const hvc)
    intro z hz
    change t < v z at hz
    exact hz.le
  · intro z hz
    change t ≤ v z at hz
    rcases eq_or_lt_of_le hz with heq | hlt
    · by_contra hn
      have hs : (closure {w | t < v w})ᶜ ∈ 𝓝 z :=
        isClosed_closure.isOpen_compl.mem_nhds hn
      obtain ⟨w, hw, htw⟩ := (regular_level_two_sided ht heq.symm hs).2
      exact hw (subset_closure htw)
    · exact subset_closure hlt

/-- The manuscript's literal level set is the actual frontier of the strict
superlevel set at every regular value, including values outside the range. -/
theorem frontier_strict_superlevel_eq {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    frontier {z | t < v z} = {z | v z = t} := by
  have ho : IsOpen {z | t < v z} :=
    isOpen_lt continuous_const (continuous_of_contDiff_lift hv)
  change closure {z | t < v z} \ interior {z | t < v z} = _
  rw [ho.interior_eq, closure_strict_superlevel_eq hv ht]
  ext z
  change (t ≤ v z ∧ ¬t < v z) ↔ v z = t
  constructor
  · rintro ⟨hl, hu⟩
    exact le_antisymm (le_of_not_gt hu) hl
  · intro he
    simp only [he, le_refl, lt_irrefl, not_false_eq_true, and_self]

/-- The boundary/level identification retains the physical Euclidean
Hausdorff measure from `StationaryCoarea`, not the old product metric. -/
theorem physicalCurveMeasure_frontier_eq {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    physicalCurveMeasure (frontier {z | t < v z}) =
      physicalCurveMeasure {z | v z = t} := by
  rw [frontier_strict_superlevel_eq hv ht]

/-- The same actual boundary has zero original Haar area. This does not
assert that its physical one-dimensional Hausdorff measure is zero. -/
theorem torusMeasure_frontier_eq_zero {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    torusMeasure (frontier {z | t < v z}) = 0 := by
  rw [frontier_strict_superlevel_eq hv ht]
  exact torusMeasure_regular_level_eq_zero hv ht

/-- A genuine C1 value-coordinate chart, with inverse confined to a physical
quotient-isometry ball. The complemented-kernel construction follows the
Mathlib implicit-function argument used in `StationarySard`; that module
records attribution of its adapted TauCeti construction. All chart data and
identities below are constructed from the actual nonzero derivative. -/
theorem exists_planar_regular_chart {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ 1 f) {a : PlanarSpace} (ha : fderiv ℝ f a ≠ 0) :
    ∃ P : PlanarSpace →L[ℝ] ↥(fderiv ℝ f a).ker,
      ∃ e : OpenPartialHomeomorph PlanarSpace (ℝ × ↥(fderiv ℝ f a).ker),
        ∃ U : Set (ℝ × ↥(fderiv ℝ f a).ker),
          (∀ x, e x = (f x, P (x - a))) ∧
          a ∈ e.source ∧ e a = (f a, 0) ∧ e.symm (f a, 0) = a ∧
          IsOpen U ∧ (f a, 0) ∈ U ∧ U ⊆ e.target ∧
          (∀ p ∈ U, e.symm p ∈ Metric.ball a (1 / 8 : ℝ)) ∧
          ContDiffOn ℝ 1 (e.symm : (ℝ × ↥(fderiv ℝ f a).ker) → PlanarSpace) U ∧
          Module.finrank ℝ ↥(fderiv ℝ f a).ker = 1 ∧
          ∀ p ∈ U, f (e.symm p) = p.1 ∧ P (e.symm p - a) = p.2 := by
  let L : PlanarSpace →L[ℝ] ℝ := fderiv ℝ f a
  have hL : L.toLinearMap ≠ 0 := by
    intro hzero
    apply ha
    ext x
    exact LinearMap.congr_fun hzero x
  have hsurj : L.range = ⊤ := Module.Dual.range_eq_top_of_ne_zero hL
  let hker : L.ker.ClosedComplemented :=
    L.ker_closedComplemented_of_finiteDimensional_range
  let P : PlanarSpace →L[ℝ] ↥L.ker := Classical.choose hker
  have hfd : HasFDerivAt f L a :=
    (hf.contDiffAt.differentiableAt (by norm_num)).hasFDerivAt
  let phi : ImplicitFunctionData ℝ PlanarSpace ℝ ↥L.ker :=
    { leftFun := f
      leftDeriv := L
      rightFun x := P (x - a)
      rightDeriv := P
      pt := a
      hasStrictFDerivAt_leftFun :=
        hf.contDiffAt.hasStrictFDerivAt' hfd (by norm_num)
      hasStrictFDerivAt_rightFun :=
        P.hasStrictFDerivAt.comp a ((hasStrictFDerivAt_id a).sub_const a)
      range_leftDeriv := hsurj
      range_rightDeriv := LinearMap.range_eq_of_proj (Classical.choose_spec hker)
      isCompl_ker := LinearMap.isCompl_of_proj (Classical.choose_spec hker) }
  let e := phi.toOpenPartialHomeomorph
  have hsource : a ∈ e.source := phi.pt_mem_toOpenPartialHomeomorph_source
  have hcenter : e a = (f a, 0) := by
    change (f a, P (a - a)) = (f a, 0)
    simp only [sub_self, map_zero]
  have hinverse : e.symm (f a, 0) = a := by
    rw [← hcenter]
    exact e.left_inv hsource
  have htarget : (f a, (0 : ↥L.ker)) ∈ e.target := by
    rw [← hcenter]
    exact e.map_source hsource
  have hprod : phi.prodFun phi.pt = (f a, 0) := by
    change (f a, P (a - a)) = (f a, 0)
    simp only [sub_self, map_zero]
  have hright : ContDiffAt ℝ 1 phi.rightFun phi.pt := by
    change ContDiffAt ℝ 1 (fun x : PlanarSpace ↦ P (x - a)) a
    fun_prop
  have hG : ContDiffAt ℝ 1 (e.symm : (ℝ × ↥L.ker) → PlanarSpace) (f a, 0) := by
    have hh := phi.contDiffAt_implicitFunction hf.contDiffAt hright (by norm_num)
    rw [hprod] at hh
    exact hh
  obtain ⟨w, hw, hGw⟩ := hG.contDiffOn (m := (1 : ℕ∞ω)) le_rfl (by simp)
  have hsmall : ∀ᶠ p in 𝓝 (f a, (0 : ↥L.ker)),
      e.symm p ∈ Metric.ball a (1 / 8 : ℝ) := by
    apply hG.continuousAt.eventually_mem
    rw [hinverse]
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self (by norm_num))
  let W : Set (ℝ × ↥L.ker) :=
    (w ∩ e.target) ∩ {p | e.symm p ∈ Metric.ball a (1 / 8 : ℝ)}
  have hW : W ∈ 𝓝 (f a, (0 : ↥L.ker)) :=
    inter_mem (inter_mem hw (e.open_target.mem_nhds htarget)) hsmall
  let U : Set (ℝ × ↥L.ker) := interior W
  have hUW : U ⊆ W := interior_subset
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hL
  have hE : Module.finrank ℝ PlanarSpace = 2 := by simp [PlanarSpace]
  rw [hE] at hdim
  have hdim' : Module.finrank ℝ ↥L.ker = 1 := by
    change Module.finrank ℝ ↥L.ker + 1 = 2 at hdim
    omega
  refine ⟨P, e, U, fun _ ↦ rfl, hsource, hcenter, hinverse, isOpen_interior,
    mem_interior_iff_mem_nhds.mpr hW, fun p hp ↦ (hUW hp).1.2,
    fun p hp ↦ (hUW hp).2, hGw.mono (fun p hp ↦ (hUW hp).1.1), hdim', ?_⟩
  intro p hp
  have hmap := e.right_inv ((hUW hp).1.2)
  change (f (e.symm p), P (e.symm p - a)) = p at hmap
  exact ⟨congrArg Prod.fst hmap, congrArg Prod.snd hmap⟩

/-- The exact kernel-coordinate identity makes each fixed-value chart
section an injective immersion. Its injective derivative is proved by
differentiating that identity, rather than assumed as area-formula data. -/
theorem chartSection_immersion {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    {P : PlanarSpace →L[ℝ] K} {a : PlanarSpace}
    {e : OpenPartialHomeomorph PlanarSpace (ℝ × K)} {U : Set (ℝ × K)}
    (hU : IsOpen U) (hG : ContDiffOn ℝ 1 (e.symm : (ℝ × K) → PlanarSpace) U)
    (hcoord : ∀ p ∈ U, P (e.symm p - a) = p.2) (r : ℝ) :
    ContDiffOn ℝ 1 (fun y : K ↦ e.symm (r, y)) {y | (r, y) ∈ U} ∧
    InjOn (fun y : K ↦ e.symm (r, y)) {y | (r, y) ∈ U} ∧
    ∀ y ∈ {y : K | (r, y) ∈ U},
      Function.Injective (fderiv ℝ (fun z : K ↦ e.symm (r, z)) y) := by
  have hsection : ∀ y, (r, y) ∈ U →
      ContDiffAt ℝ 1 (fun z : K ↦ e.symm (r, z)) y := by
    intro y hy
    exact (hG.contDiffAt (hU.mem_nhds hy)).comp y (by fun_prop)
  refine ⟨fun y hy ↦ (hsection y hy).contDiffWithinAt, ?_, ?_⟩
  · intro y hy z hz he
    change e.symm (r, y) = e.symm (r, z) at he
    calc
      y = P (e.symm (r, y) - a) := (hcoord (r, y) hy).symm
      _ = P (e.symm (r, z) - a) := by rw [he]
      _ = z := hcoord (r, z) hz
  · intro y hy
    have hd : DifferentiableAt ℝ (fun z : K ↦ e.symm (r, z)) y :=
      (hsection y hy).differentiableAt (by norm_num)
    have hp : HasFDerivAt (fun z : K ↦ P (e.symm (r, z) - a))
        (P.comp (fderiv ℝ (fun z : K ↦ e.symm (r, z)) y)) y := by
      simpa only [Function.comp_def] using
        P.hasFDerivAt.comp y (hd.hasFDerivAt.sub_const a)
    have hm : ∀ᶠ z : K in 𝓝 y, (r, z) ∈ U :=
      (continuous_const.prodMk continuous_id).continuousAt.eventually_mem
        (hU.mem_nhds hy)
    have he : (fun z : K ↦ P (e.symm (r, z) - a)) =ᶠ[𝓝 y] (fun z : K ↦ z) :=
      hm.mono fun z hz ↦ hcoord (r, z) hz
    have hi : HasFDerivAt (fun z : K ↦ P (e.symm (r, z) - a))
        (ContinuousLinearMap.id ℝ K) y :=
      (hasFDerivAt_id y).congr_of_eventuallyEq he
    have hleft := hp.unique hi
    have hleft_apply (u : K) :
        P (fderiv ℝ (fun z : K ↦ e.symm (r, z)) y u) = u := by
      have hh := congrArg (fun A : K →L[ℝ] K ↦ A u) hleft
      exact hh
    intro u w huw
    calc
      u = P (fderiv ℝ (fun z : K ↦ e.symm (r, z)) y u) := (hleft_apply u).symm
      _ = P (fderiv ℝ (fun z : K ↦ e.symm (r, z)) y w) := congrArg P huw
      _ = w := hleft_apply w

/-- Actual periodic regular-level chart families. They cover an open torus
neighborhood, have literal value as first coordinate, and each section is
an injective physical parametrization with injective planar derivative.
The small-ball clause retains the Euclidean quotient metric exactly. -/
theorem exists_torus_regular_level_chart {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {z : Torus} (hz : torusOrdinaryGradient v z ≠ 0) :
    ∃ a : PlanarSpace, torusQuotient a = z ∧
      ∃ e : OpenPartialHomeomorph PlanarSpace
        (ℝ × ↥(fderiv ℝ (fun x : PlanarSpace ↦ v (torusQuotient x)) a).ker),
        ∃ U : Set (ℝ × ↥(fderiv ℝ (fun x : PlanarSpace ↦ v (torusQuotient x)) a).ker),
          ∃ V : Set Torus,
            Module.finrank ℝ
              ↥(fderiv ℝ (fun x : PlanarSpace ↦ v (torusQuotient x)) a).ker = 1 ∧
            IsOpen U ∧ (v z, 0) ∈ U ∧ U ⊆ e.target ∧
            e.symm (v z, 0) = a ∧ IsOpen V ∧ z ∈ V ∧
            (∀ p ∈ U, e.symm p ∈ Metric.ball a (1 / 8 : ℝ)) ∧
            (∀ p ∈ U, v (torusQuotient (e.symm p)) = p.1) ∧
            (∀ r : ℝ, V ∩ {w | v w = r} =
              (fun y ↦ torusQuotient (e.symm (r, y))) '' {y | (r, y) ∈ U}) ∧
            ∀ r : ℝ,
              ContDiffOn ℝ 1 (fun y ↦ e.symm (r, y)) {y | (r, y) ∈ U} ∧
              InjOn (fun y ↦ torusQuotient (e.symm (r, y))) {y | (r, y) ∈ U} ∧
              ∀ y ∈ {y | (r, y) ∈ U},
                Function.Injective (fderiv ℝ (fun w ↦ e.symm (r, w)) y) := by
  obtain ⟨a, rfl⟩ := torusQuotient_surjective z
  have ha : fderiv ℝ (fun x : PlanarSpace ↦ v (torusQuotient x)) a ≠ 0 := by
    intro hzero
    exact hz ((mem_torusCriticalPoints_lift_iff v a).mpr hzero)
  obtain ⟨P, e, U, -, -, -, hinverse, hU, hUa, hUt, hsmall, hG, hdim, hcoord⟩ :=
    exists_planar_regular_chart hv ha
  let V : Set Torus := torusQuotient '' (e.symm '' U)
  have hV : IsOpen V :=
    isOpenQuotientMap_torusQuotient.isOpenMap _
      (e.isOpen_image_symm_of_subset_target hU hUt)
  have haV : torusQuotient a ∈ V :=
    ⟨a, ⟨(v (torusQuotient a), 0), hUa, hinverse⟩, rfl⟩
  refine ⟨a, rfl, e, U, V, hdim, hU, hUa, hUt, hinverse, hV, haV, hsmall,
    fun p hp ↦ (hcoord p hp).1, ?_, ?_⟩
  · intro r
    ext w
    constructor
    · rintro ⟨⟨x, ⟨⟨p, y⟩, hp, rfl⟩, rfl⟩, hw⟩
      have hpval : v (torusQuotient (e.symm (p, y))) = p := (hcoord (p, y) hp).1
      have hpr : p = r := hpval.symm.trans hw
      subst p
      exact ⟨y, hp, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨e.symm (r, y), ⟨(r, y), hy, rfl⟩, rfl⟩, (hcoord (r, y) hy).1⟩
  · intro r
    have hs := chartSection_immersion hU hG (fun p hp ↦ (hcoord p hp).2) r
    refine ⟨hs.1, ?_, hs.2.2⟩
    intro y hy w hw hq
    have hphys : physicalQuotient (e.symm (r, y)) = physicalQuotient (e.symm (r, w)) :=
      congrArg physicalEquiv hq
    have hsub : (⟨e.symm (r, y), hsmall (r, y) hy⟩ : Metric.ball a (1 / 8 : ℝ)) =
        ⟨e.symm (r, w), hsmall (r, w) hw⟩ :=
      (physicalQuotient_isometry_ball a).injective hphys
    exact hs.2.1 hy hw (congrArg Subtype.val hsub)

end PeriodicAttractiveLogGas.StationaryLevelBoundary
