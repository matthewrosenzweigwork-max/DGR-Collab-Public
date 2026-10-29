/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; the unchanged license is retained in
research/discovery/references/TauCeti-Sard-d969ec21-20260928/LICENSE.

The stratification proof below is adapted from TauCeti's FlatStratum,
IntermediateStratum, VanishingDerivative, and Measure/LocallyNull modules at
Git tree d969ec21da00439b0479ee3923df9008da718365. Changes: repository namespace,
pinned-toolchain compatibility, removal of unrelated corollaries, and actual
planar/periodic scalar endpoints. No TauCeti package or unproved theorem is
imported. Exact source identities and checking status are in the development
record research/reviews/stationary-sard-development.md.
-/
import LeanResearch.PeriodicAttractiveLogGas.LogKernel
import LeanResearch.PeriodicAttractiveLogGas.TorusLocalGradient
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.MeasureTheory.OuterMeasure.Operations

/-!
The scalar Sard input at manuscript line 1622. The proof uses the actual image
of the zero-derivative locus. Flat strata have a proved higher-order Holder
bound; the other strata have a proved implicit parametrization in one lower
dimension. The sufficient finite regularity used in the induction is not
claimed to be sharp. It is implied by the manuscript's smooth hypothesis.
-/

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Module Set
open scoped ContDiff NNReal ENNReal Topology

namespace PeriodicAttractiveLogGas.StationarySard

def criticalPoints (f : PlanarSpace → ℝ) : Set PlanarSpace :=
  {x | fderiv ℝ f x = 0}

def criticalValues (f : PlanarSpace → ℝ) : Set ℝ :=
  f '' criticalPoints f

section FlatStratum

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : E → F} {k : ℕ} {s : Set E}

private theorem holderOnWith_of_dist_le {X Y : Type*}
    [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {C r : ℝ≥0} {g : X → Y} {t : Set X}
    (h : ∀ x ∈ t, ∀ y ∈ t, dist (g x) (g y) ≤ C * dist x y ^ (r : ℝ)) :
    HolderOnWith C r g t := by
  intro x hx y hy
  rw [edist_dist, edist_dist, ENNReal.ofReal_rpow_of_nonneg dist_nonneg r.coe_nonneg,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul C.coe_nonneg]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy)

/-- Descending mean-value induction; no Taylor remainder is supplied. -/
private theorem norm_iteratedFDeriv_sub_le {M : ℝ} {x : E}
    (hf : ∀ y ∈ s, ContDiffAt ℝ (k + 1 : ℕ) f y) (hs : Convex ℝ s) (hx : x ∈ s)
    (hM : ∀ y ∈ s, ‖iteratedFDeriv ℝ (k + 1) f y‖ ≤ M)
    (hzero : ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0) :
    ∀ j ≤ k, ∀ y ∈ s, ‖iteratedFDeriv ℝ (k - j) f y - iteratedFDeriv ℝ (k - j) f x‖
      ≤ M * ‖y - x‖ ^ (j + 1) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x hx)
  have hdiff : ∀ i ≤ k, ∀ y ∈ s, DifferentiableAt ℝ (iteratedFDeriv ℝ i f) y := fun i hi y hy ↦
    (hf y hy).differentiableAt_iteratedFDeriv (mod_cast Nat.lt_succ_of_le hi)
  intro j
  induction j with
  | zero =>
    intro _ y hy
    simpa using hs.norm_image_sub_le_of_norm_fderiv_le (fun z hz ↦ hdiff k le_rfl z hz)
      (fun z hz ↦ by rw [norm_fderiv_iteratedFDeriv]; exact hM z hz) hx hy
  | succ j ih =>
    intro hjk y hy
    have hj : j ≤ k := by omega
    have hstep : k - (j + 1) + 1 = k - j := by omega
    have hvanish : ∀ z ∈ s, ‖iteratedFDeriv ℝ (k - j) f z‖ ≤ M * ‖z - x‖ ^ (j + 1) := by
      intro z hz
      simpa [hzero (k - j) (by omega) (by omega)] using ih hj z hz
    have hseg : segment ℝ x y ⊆ s := hs.segment_subset hx hy
    have hbound : ∀ z ∈ segment ℝ x y,
        ‖fderiv ℝ (iteratedFDeriv ℝ (k - (j + 1)) f) z‖ ≤ M * ‖y - x‖ ^ (j + 1) := by
      intro z hz
      rw [norm_fderiv_iteratedFDeriv, hstep]
      refine (hvanish z (hseg hz)).trans ?_
      gcongr
      exact norm_sub_le_of_mem_segment hz
    have := (convex_segment x y).norm_image_sub_le_of_norm_fderiv_le
      (fun z hz ↦ hdiff _ (by omega) z (hseg hz)) hbound (left_mem_segment ℝ x y)
      (right_mem_segment ℝ x y)
    calc ‖iteratedFDeriv ℝ (k - (j + 1)) f y - iteratedFDeriv ℝ (k - (j + 1)) f x‖
        ≤ M * ‖y - x‖ ^ (j + 1) * ‖y - x‖ := this
      _ = M * ‖y - x‖ ^ (j + 1 + 1) := by rw [mul_assoc, ← pow_succ]

/-- The actual higher-order oscillation estimate on a flat stratum. -/
theorem norm_sub_le_pow_of_flat_jet {M : ℝ} {x y : E}
    (hf : ∀ z ∈ s, ContDiffAt ℝ (k + 1 : ℕ) f z) (hs : Convex ℝ s) (hx : x ∈ s) (hy : y ∈ s)
    (hM : ∀ z ∈ s, ‖iteratedFDeriv ℝ (k + 1) f z‖ ≤ M)
    (hzero : ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0) :
    ‖f y - f x‖ ≤ M * ‖y - x‖ ^ (k + 1) := by
  have key := norm_iteratedFDeriv_sub_le hf hs hx hM hzero k le_rfl y hy
  rw [Nat.sub_self] at key
  rwa [iteratedFDeriv_zero_eq_comp, comp_apply, comp_apply, ← LinearIsometryEquiv.map_sub,
    LinearIsometryEquiv.norm_map] at key

theorem holderOnWith_of_flat_jet {A V : Set E} {C : ℝ≥0}
    (hf : ∀ y ∈ V, ContDiffAt ℝ (k + 1 : ℕ) f y) (hV : Convex ℝ V)
    (hC : ∀ y ∈ V, ‖iteratedFDeriv ℝ (k + 1) f y‖ ≤ C) (hAV : A ⊆ V)
    (hzero : ∀ x ∈ A, ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0) :
    HolderOnWith C (k + 1) f A := by
  refine holderOnWith_of_dist_le fun x hx y hy ↦ ?_
  have hcast : (((k : ℝ≥0) + 1 : ℝ≥0) : ℝ) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [dist_eq_norm, dist_eq_norm, hcast, Real.rpow_natCast]
  exact norm_sub_le_pow_of_flat_jet hf hV (hAV hy) (hAV hx) hC (hzero y hy)

theorem dimH_image_flat [SecondCountableTopology E] {U : Set E} (hU : IsOpen U)
    (hf : ContDiffOn ℝ (k + 1 : ℕ) f U) (hsU : s ⊆ U)
    (hzero : ∀ x ∈ s, ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0) :
    dimH (f '' s) ≤ dimH s / (k + 1 : ℝ≥0∞) := by
  have hcont : ContinuousOn (iteratedFDeriv ℝ (k + 1) f) U :=
    (hf.continuousOn_iteratedFDerivWithin le_rfl hU.uniqueDiffOn).congr
      (iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := f) (k + 1) hU).symm
  have key : dimH (f '' s) ≤ dimH s / (((k : ℝ≥0) + 1 : ℝ≥0) : ℝ≥0∞) := by
    refine dimH_image_le_of_locally_holder_on (by positivity) fun a ha ↦ ?_
    have hM0 : (0 : ℝ) ≤ ‖iteratedFDeriv ℝ (k + 1) f a‖ + 1 := by positivity
    have hUa : U ∈ 𝓝 a := hU.mem_nhds (hsU ha)
    have hlt : ∀ᶠ y in 𝓝 a,
        ‖iteratedFDeriv ℝ (k + 1) f y‖ < ‖iteratedFDeriv ℝ (k + 1) f a‖ + 1 :=
      ((hcont.continuousAt hUa).norm).eventually_lt_const (lt_add_one _)
    have hnhds : {y | ‖iteratedFDeriv ℝ (k + 1) f y‖ ≤ ‖iteratedFDeriv ℝ (k + 1) f a‖ + 1} ∈ 𝓝 a :=
      hlt.mono fun y hy ↦ hy.le
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem hUa hnhds)
    refine ⟨(‖iteratedFDeriv ℝ (k + 1) f a‖ + 1).toNNReal, s ∩ Metric.ball a r,
      inter_mem_nhdsWithin s (Metric.ball_mem_nhds a hr), ?_⟩
    refine holderOnWith_of_flat_jet (V := Metric.ball a r)
      (fun y hy ↦ hf.contDiffAt (hU.mem_nhds (hball hy).1)) (convex_ball a r)
      (fun y hy ↦ ?_) inter_subset_right fun x hx ↦ hzero x hx.1
    rw [Real.coe_toNNReal _ hM0]
    exact (hball hy).2
  simpa using key

/-- Flat-stratum nullity follows from the proved Holder bound and actual
finite-dimensional Hausdorff measure, without assuming image nullity. -/
theorem addHaar_image_flat_eq_zero [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]
    (ν : Measure F) [IsAddHaarMeasure ν] {U : Set E}
    (hU : IsOpen U) (hf : ContDiffOn ℝ (k + 1 : ℕ) f U) (hsU : s ⊆ U)
    (hzero : ∀ x ∈ s, ∀ i, 1 ≤ i → i ≤ k → iteratedFDeriv ℝ i f x = 0)
    (hdim : finrank ℝ E < (k + 1) * finrank ℝ F) : ν (f '' s) = 0 := by
  have hν : ν ≪ (μH[(finrank ℝ F : ℝ)] : Measure F) := absolutelyContinuous_isAddHaarMeasure ν _
  refine measure_zero_of_dimH_lt (d := (finrank ℝ F : ℝ≥0)) hν ?_
  refine (dimH_image_flat hU hf hsU hzero).trans_lt ?_
  have hs : dimH s ≤ (finrank ℝ E : ℝ≥0∞) := by
    simpa only [Real.dimH_univ_eq_finrank] using dimH_mono (subset_univ s)
  refine lt_of_le_of_lt (ENNReal.div_le_div_right hs _) ?_
  rw [ENNReal.div_lt_iff (Or.inl (by simp)) (Or.inl (by simp)), ENNReal.coe_natCast, mul_comm]
  exact_mod_cast hdim

end FlatStratum

/-- Second countability supplies the countable local-to-global passage. -/
theorem measure_image_null_of_locally_null {E F G : Type*}
    [TopologicalSpace E] [SecondCountableTopology E]
    [FunLike G (Set F) ENNReal] [OuterMeasureClass G F] {ν : G}
    {f : E → F} {s : Set E}
    (h : ∀ x ∈ s, ∃ u ∈ 𝓝[s] x, ν (f '' u) = 0) : ν (f '' s) = 0 := by
  let ν' : OuterMeasure F :=
    { measureOf := ν
      empty := measure_empty
      mono := fun hst ↦ measure_mono hst
      iUnion_nat := fun t ht ↦ OuterMeasureClass.measure_iUnion_nat_le ν t ht }
  change ν' (f '' s) = 0
  simpa only [OuterMeasure.comap_apply] using
    measure_null_of_locally_null (μ := OuterMeasure.comap f ν') s h

section IntermediateStratum

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : E → F} {a : E} {i r : ℕ}

/-- The actual implicit parametrization of a stratum where derivative
vanishing stops. Its domain is the kernel of a constructed nonzero scalar
functional, and its local covering property is proved from the inverse map. -/
theorem exists_parametrization_flat_stratum
    (hf : ContDiffAt ℝ (r + i : ℕ) f a) (hr : r ≠ 0)
    (hi : iteratedFDeriv ℝ i f a = 0)
    (hnext : iteratedFDeriv ℝ (i + 1) f a ≠ 0) :
    ∃ (g : E → ℝ) (g' : E →L[ℝ] ℝ) (θ : ↥g'.ker → E),
      ContDiffAt ℝ r g a ∧
      HasFDerivAt g g' a ∧
      g'.range = ⊤ ∧
      (∀ x, iteratedFDeriv ℝ i f x = 0 → g x = 0) ∧
      θ 0 = a ∧
      ContDiffAt ℝ r θ 0 ∧
      (∀ᶠ z in 𝓝 0, g (θ z) = 0) ∧
      (∀ V ∈ 𝓝 (0 : ↥g'.ker), ∀ᶠ x in 𝓝 a, iteratedFDeriv ℝ i f x = 0 → x ∈ θ '' V) ∧
      finrank ℝ ↥g'.ker + 1 = finrank ℝ E := by
  let instCompleteE : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hr' : (r : ℕ∞ω) ≠ 0 := by exact_mod_cast hr
  let D : E →L[ℝ] E [×i]→L[ℝ] F := fderiv ℝ (iteratedFDeriv ℝ i f) a
  have hD : D ≠ 0 := by
    intro hDzero
    apply hnext
    rw [iteratedFDeriv_succ_eq_comp_left, comp_apply]
    change (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (i + 1) ↦ E) F).symm D = 0
    rw [← (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (i + 1) ↦ E) F).symm.map_zero]
    exact congrArg _ hDzero
  obtain ⟨v, hv⟩ : ∃ v : E, D v ≠ 0 := by
    by_contra h
    push Not at h
    exact hD (ContinuousLinearMap.ext h)
  obtain ⟨ell, _, hell⟩ := exists_dual_vector ℝ (D v) (norm_ne_zero_iff.mpr hv)
  let g : E → ℝ := fun x ↦ ell (iteratedFDeriv ℝ i f x)
  let g' : E →L[ℝ] ℝ := ell.comp D
  have hg' : g' ≠ 0 := by
    intro hg'zero
    have happly := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hg'zero
    simp only [g', ContinuousLinearMap.comp_apply, zero_apply] at happly
    exact (norm_ne_zero_iff.mpr hv) (hell.symm.trans happly)
  have hg'_linear : g'.toLinearMap ≠ 0 := by
    intro hzero
    apply hg'
    ext x
    exact LinearMap.congr_fun hzero x
  have hsurj : g'.range = ⊤ :=
    Module.Dual.range_eq_top_of_ne_zero hg'_linear
  have hiter : ContDiffAt ℝ r (iteratedFDeriv ℝ i f) a :=
    hf.iteratedFDeriv_right le_rfl
  have hg : ContDiffAt ℝ r g a := ell.contDiff.contDiffAt.comp a hiter
  have hgderiv : HasFDerivAt g g' a :=
    ell.hasFDerivAt.comp a (hiter.differentiableAt hr').hasFDerivAt
  have hga : g a = 0 := by simp [g, hi]
  have hstrict : HasStrictFDerivAt g g' a := hg.hasStrictFDerivAt' hgderiv hr'
  let hker : g'.ker.ClosedComplemented :=
    g'.ker_closedComplemented_of_finiteDimensional_range
  let projection : E →L[ℝ] ↥g'.ker := Classical.choose hker
  let phi : ImplicitFunctionData ℝ E ℝ ↥g'.ker :=
    { leftFun := g
      leftDeriv := g'
      rightFun x := projection (x - a)
      rightDeriv := projection
      pt := a
      hasStrictFDerivAt_leftFun := hstrict
      hasStrictFDerivAt_rightFun :=
        projection.hasStrictFDerivAt.comp a ((hasStrictFDerivAt_id a).sub_const a)
      range_leftDeriv := hsurj
      range_rightDeriv := LinearMap.range_eq_of_proj (Classical.choose_spec hker)
      isCompl_ker := LinearMap.isCompl_of_proj (Classical.choose_spec hker) }
  let theta : ↥g'.ker → E := phi.implicitFunction 0
  have hprod : phi.prodFun phi.pt = (0, (0 : ↥g'.ker)) := by
    ext <;> simp [phi, projection, hga]
  have htheta_zero : theta 0 = a := by
    have hleft : phi.leftFun phi.pt = 0 := by simp [phi, hga]
    have hright : phi.rightFun phi.pt = 0 := by simp [phi, projection]
    dsimp only [theta]
    rw [← hleft, ← hright, ImplicitFunctionData.implicitFunction_apply]
    rw [← ImplicitFunctionData.toOpenPartialHomeomorph_apply]
    simpa only [phi] using
      phi.toOpenPartialHomeomorph.left_inv phi.pt_mem_toOpenPartialHomeomorph_source
  have htheta_smooth : ContDiffAt ℝ r theta 0 := by
    have hright : ContDiffAt ℝ r phi.rightFun phi.pt := by
      simp only [phi]
      fun_prop
    have himplicit : ContDiffAt ℝ r phi.implicitFunction.uncurry (phi.prodFun phi.pt) :=
      phi.contDiffAt_implicitFunction (by simpa only [phi] using hg) hright hr'
    have hin : ContDiffAt ℝ r (fun z : ↥g'.ker ↦ ((0 : ℝ), z)) 0 := by fun_prop
    rw [hprod] at himplicit
    have hcomp := himplicit.comp 0 hin
    have heq : phi.implicitFunction.uncurry ∘ (fun z : ↥g'.ker ↦ ((0 : ℝ), z)) =
        phi.implicitFunction 0 := by
      funext z
      rfl
    rw [heq] at hcomp
    exact hcomp
  have htheta_level : ∀ᶠ z in 𝓝 0, g (theta z) = 0 := by
    have hmap := phi.leftFun_implicitFunction
    have htend : Tendsto (fun z : ↥g'.ker ↦ ((0 : ℝ), z)) (𝓝 0)
        (𝓝 (phi.prodFun phi.pt)) := by
      rw [hprod]
      exact continuousAt_const.prodMk continuousAt_id
    have hmap' := htend hmap
    rw [Filter.mem_map] at hmap'
    have hmap'' : ∀ᶠ z : ↥g'.ker in 𝓝 0,
        phi.leftFun (phi.implicitFunction 0 z) = 0 := hmap'
    simpa only [theta, phi] using hmap''
  have hzero : ∀ x, iteratedFDeriv ℝ i f x = 0 → g x = 0 := by
    intro x hx
    simp [g, hx]
  have hcover : ∀ V ∈ 𝓝 (0 : ↥g'.ker),
      ∀ᶠ x in 𝓝 a, iteratedFDeriv ℝ i f x = 0 → x ∈ theta '' V := by
    intro V hV
    have hright : ContinuousAt phi.rightFun a := by
      simp only [phi]
      fun_prop
    have hzeroright : phi.rightFun a = 0 := by simp [phi, projection]
    have hmem : ∀ᶠ x in 𝓝 a, phi.rightFun x ∈ V := hright.eventually_mem (by rwa [hzeroright])
    filter_upwards [phi.implicitFunction_apply_image, hmem] with x hx hxV hxi
    refine ⟨phi.rightFun x, hxV, ?_⟩
    dsimp only [theta]
    rw [← hzero x hxi]
    simpa only [phi] using hx
  have hfinrank : finrank ℝ ↥g'.ker + 1 = finrank ℝ E :=
    Module.Dual.finrank_ker_add_one_of_ne_zero hg'_linear
  exact ⟨g, g', theta, hg, hgderiv, hsurj, hzero, htheta_zero, htheta_smooth,
    htheta_level, hcover, hfinrank⟩

end IntermediateStratum

section DimensionInduction

universe u

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F] [Nontrivial F]
  (ν : Measure F) [IsAddHaarMeasure ν]

private theorem finite_order_ne_infty (m : ℕ) : (m : ℕ∞ω) ≠ (∞ : ℕ∞ω) := by simp

omit [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F] [Nontrivial F] in
private theorem critical_subset_strata {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → F) (s : Set E) (N : ℕ)
    (hs : ∀ x ∈ s, fderiv ℝ f x = 0) :
    s ⊆ {x ∈ s | ∀ i, 1 ≤ i → i ≤ N → iteratedFDeriv ℝ i f x = 0} ∪
      ⋃ i ∈ Set.Ico 1 N,
        {x ∈ s | iteratedFDeriv ℝ i f x = 0 ∧ iteratedFDeriv ℝ (i + 1) f x ≠ 0} := by
  classical
  intro x hx
  by_cases hflat : ∀ i, 1 ≤ i → i ≤ N → iteratedFDeriv ℝ i f x = 0
  · exact Or.inl ⟨hx, hflat⟩
  refine Or.inr ?_
  push Not at hflat
  obtain ⟨i, hi1, hiN, hine⟩ := hflat
  have h1 : iteratedFDeriv ℝ 1 f x = 0 := by
    rw [← norm_eq_zero, norm_iteratedFDeriv_one, hs x hx, norm_zero]
  let p : ℕ → Prop := fun j ↦ iteratedFDeriv ℝ (j + 1) f x ≠ 0
  have hp : ∃ j, p j := ⟨i - 1, by
    change iteratedFDeriv ℝ (i - 1 + 1) f x ≠ 0
    rwa [Nat.sub_add_cancel hi1]⟩
  have hjpos : 0 < Nat.find hp := (Nat.find_pos hp).2 (by simpa [p] using h1)
  have hjzero : iteratedFDeriv ℝ (Nat.find hp) f x = 0 := by
    have hmin := Nat.find_min hp
      (Nat.sub_lt hjpos (by omega) : Nat.find hp - 1 < Nat.find hp)
    simp only [p, not_ne_iff] at hmin
    rwa [Nat.sub_add_cancel hjpos] at hmin
  have hjN : Nat.find hp < N := by
    have hlast : p (i - 1) := by
      change iteratedFDeriv ℝ (i - 1 + 1) f x ≠ 0
      rwa [Nat.sub_add_cancel hi1]
    have hji : Nat.find hp ≤ i - 1 := Nat.find_le (h := hp) hlast
    omega
  exact mem_biUnion ⟨hjpos, hjN⟩ ⟨hx, hjzero, Nat.find_spec hp⟩

/-- Dimension induction on the actual zero-derivative image. The source space
is quantified inside the induction because the implicit chart changes it. -/
private theorem image_zero_derivative_null_aux (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E],
      finrank ℝ E ≤ n → ∀ (k : ℕ), n * n + 1 ≤ k → ∀ (f : E → F) (s : Set E),
        (∀ x ∈ s, ContDiffAt ℝ k f x) → (∀ x ∈ s, fderiv ℝ f x = 0) → ν (f '' s) = 0 := by
  induction n with
  | zero =>
    intro E _ _ _ hE k _ f s _ _
    have : Subsingleton E := Module.finrank_zero_iff.mp (Nat.le_zero.mp hE)
    exact (Set.Subsingleton.image (fun x _ y _ ↦ Subsingleton.elim x y) f).measure_zero ν
  | succ n ih =>
    intro E _ _ _ hE k hk f s hf hs
    have hF : 0 < finrank ℝ F := finrank_pos
    have hk' : n * n + n + 2 ≤ k := by nlinarith
    have hkK : n + 2 ≤ k := by omega
    have hsub := critical_subset_strata f s (n + 1) hs
    refine measure_mono_null (image_mono hsub) ?_
    rw [image_union, image_iUnion₂]
    refine measure_union_null ?_ ((measure_biUnion_null_iff (Set.to_countable _)).2 fun i hi ↦ ?_)
    · refine measure_image_null_of_locally_null fun a ha ↦ ?_
      obtain ⟨u, hu, hfu⟩ := (hf a ha.1).contDiffOn (m := ((n + 1 + 1 : ℕ) : ℕ∞ω))
        (mod_cast hkK) fun h ↦ absurd h (finite_order_ne_infty _)
      have humem : interior u ∈ 𝓝 a := isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hu)
      refine ⟨_ ∩ interior u, inter_mem_nhdsWithin _ humem, ?_⟩
      refine addHaar_image_flat_eq_zero (k := n + 1) ν isOpen_interior
        (hfu.mono interior_subset) inter_subset_right (fun x hx ↦ hx.1.2) ?_
      calc finrank ℝ E ≤ n + 1 := hE
        _ < n + 2 := by omega
        _ ≤ (n + 1 + 1) * finrank ℝ F := Nat.le_mul_of_pos_right _ hF
    · refine measure_image_null_of_locally_null fun a ha ↦ ?_
      obtain ⟨has, hai, hai1⟩ := ha
      have hfa : ContDiffAt ℝ ((n * n + 1 + i : ℕ)) f a :=
        (hf a has).of_le (mod_cast show n * n + 1 + i ≤ k by have := hi.2; omega)
      obtain ⟨g, g', θ, -, -, -, -, -, hθ, -, hcover, hrank⟩ :=
        exists_parametrization_flat_stratum (r := n * n + 1) hfa (by positivity) hai hai1
      obtain ⟨w, hw, hθw⟩ := hθ.contDiffOn (m := ((n * n + 1 : ℕ) : ℕ∞ω)) le_rfl
        fun h ↦ absurd h (finite_order_ne_infty _)
      have hwmem : interior w ∈ 𝓝 (0 : ↥g'.ker) :=
        isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.2 hw)
      refine ⟨_ ∩ {x | iteratedFDeriv ℝ i f x = 0 → x ∈ θ '' interior w},
        inter_mem_nhdsWithin _ (hcover _ hwmem), ?_⟩
      have hθz : ∀ z ∈ interior w, ContDiffAt ℝ ((n * n + 1 : ℕ)) θ z := fun z hz ↦
        (hθw.mono interior_subset).contDiffAt (isOpen_interior.mem_nhds hz)
      refine measure_mono_null (fun y hy ↦ ?_)
        (ih ↥g'.ker (by omega) (n * n + 1) le_rfl (f ∘ θ) (interior w ∩ θ ⁻¹' s) ?_ ?_)
      · obtain ⟨x, ⟨⟨hxs, hxi, -⟩, hxV⟩, rfl⟩ := hy
        obtain ⟨z, hz, rfl⟩ := hxV hxi
        exact ⟨z, ⟨hz, hxs⟩, rfl⟩
      · rintro z ⟨hzw, hzs⟩
        exact ((hf (θ z) hzs).of_le (mod_cast show n * n + 1 ≤ k by omega)).comp z
          (hθz z hzw)
      · rintro z ⟨hzw, hzs⟩
        have hone : (1 : ℕ∞ω) ≤ ((n * n + 1 : ℕ) : ℕ∞ω) := mod_cast Nat.le_add_left 1 (n * n)
        have hfz : DifferentiableAt ℝ f (θ z) :=
          ((hf (θ z) hzs).of_le (mod_cast show 1 ≤ k by omega)).differentiableAt_one
        rw [fderiv_comp z hfz ((hθz z hzw).of_le hone).differentiableAt_one, hs (θ z) hzs,
          ContinuousLinearMap.zero_comp]

/-- Finite regularity Sard for the vanishing derivative locus. In real scalar
codomain this is the entire critical locus. No image-null premise occurs. -/
theorem image_zero_derivative_null {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : E → F} {s : Set E} {n : ℕ∞ω}
    (hk : ((finrank ℝ E * finrank ℝ E + 1 : ℕ) : ℕ∞ω) ≤ n)
    (hf : ∀ x ∈ s, ContDiffAt ℝ n f x) (hs : ∀ x ∈ s, fderiv ℝ f x = 0) :
    ν (f '' s) = 0 :=
  image_zero_derivative_null_aux ν (finrank ℝ E) E le_rfl
    (finrank ℝ E * finrank ℝ E + 1) le_rfl f s (fun x hx ↦ (hf x hx).of_le hk) hs

end DimensionInduction

/-- Actual scalar planar Sard with a sufficient C5 hypothesis. -/
theorem volume_criticalValues_eq_zero_of_contDiff_five {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ 5 f) : volume (criticalValues f) = 0 := by
  exact image_zero_derivative_null volume (by simp [PlanarSpace])
    (fun _ _ ↦ hf.contDiffAt) (fun _ hx ↦ hx)

/-- The actual smooth hypothesis used in the stationary proof. -/
theorem volume_criticalValues_eq_zero {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) : volume (criticalValues f) = 0 :=
  volume_criticalValues_eq_zero_of_contDiff_five (hf.of_le (by simp))

/-- Criticality uses the existing physical torus gradient, with no new
representative or convention for derivatives. -/
def torusCriticalPoints (v : Torus → ℝ) : Set Torus :=
  {z | torusOrdinaryGradient v z = 0}

def torusCriticalValues (v : Torus → ℝ) : Set ℝ :=
  v '' torusCriticalPoints v

theorem mem_torusCriticalPoints_lift_iff (v : Torus → ℝ) (x : PlanarSpace) :
    torusQuotient x ∈ torusCriticalPoints v ↔
      x ∈ criticalPoints (fun y ↦ v (torusQuotient y)) := by
  change torusOrdinaryGradient v (torusQuotient x) = 0 ↔
    fderiv ℝ (fun y ↦ v (torusQuotient y)) x = 0
  rw [← norm_eq_zero, norm_torusOrdinaryGradient_lift, norm_eq_zero]

/-- Surjectivity of the actual periodic cover identifies the value sets
exactly; no choice of a fundamental cell or omission of boundary points occurs. -/
theorem criticalValues_lift_eq (v : Torus → ℝ) :
    criticalValues (fun y ↦ v (torusQuotient y)) = torusCriticalValues v := by
  ext t
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨torusQuotient x, (mem_torusCriticalPoints_lift_iff v x).mpr hx, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, rfl⟩ := torusQuotient_surjective z
    exact ⟨x, (mem_torusCriticalPoints_lift_iff v x).mp hz, rfl⟩

theorem volume_torusCriticalValues_eq_zero_of_contDiff_five {v : Torus → ℝ}
    (hv : ContDiff ℝ 5 (fun y : PlanarSpace ↦ v (torusQuotient y))) :
    volume (torusCriticalValues v) = 0 := by
  rw [← criticalValues_lift_eq]
  exact volume_criticalValues_eq_zero_of_contDiff_five hv

theorem volume_torusCriticalValues_eq_zero {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun y : PlanarSpace ↦ v (torusQuotient y))) :
    volume (torusCriticalValues v) = 0 := by
  rw [← criticalValues_lift_eq]
  exact volume_criticalValues_eq_zero hv

/-- Compactness of the critical values is derived from continuity of the
physical gradient norm and the compact original torus. -/
theorem isCompact_torusCriticalValues {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun y : PlanarSpace ↦ v (torusQuotient y))) :
    IsCompact (torusCriticalValues v) := by
  have hvc : Continuous v :=
    isOpenQuotientMap_torusQuotient.isQuotientMap.continuous_iff.mpr hv.continuous
  have hgc : Continuous (fun z : Torus ↦ ‖torusOrdinaryGradient v z‖) := by
    apply isOpenQuotientMap_torusQuotient.isQuotientMap.continuous_iff.mpr
    simpa only [Function.comp_def, norm_torusOrdinaryGradient_lift] using
      (hv.fderiv_right (m := 0) (by norm_num)).continuous.norm
  have heq : torusCriticalPoints v = {z | ‖torusOrdinaryGradient v z‖ = 0} := by
    ext z
    simp only [torusCriticalPoints, mem_ofPred_eq, norm_eq_zero]
  have hclosed : IsClosed (torusCriticalPoints v) := by
    rw [heq]
    exact isClosed_eq hgc continuous_const
  exact hclosed.isCompact.image hvc

/-- The complete actual critical-value input for the stationary level-set
proof: a compact Lebesgue-null exceptional set with nonzero physical gradient
at every point of each complementary level. -/
theorem torus_sard {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun y : PlanarSpace ↦ v (torusQuotient y))) :
    IsCompact (torusCriticalValues v) ∧ volume (torusCriticalValues v) = 0 ∧
      ∀ t ∉ torusCriticalValues v, ∀ z, v z = t → torusOrdinaryGradient v z ≠ 0 := by
  refine ⟨isCompact_torusCriticalValues (hv.of_le (by simp)),
    volume_torusCriticalValues_eq_zero hv, ?_⟩
  intro t ht z hzt hz
  exact ht ⟨z, hz, hzt⟩

end PeriodicAttractiveLogGas.StationarySard
