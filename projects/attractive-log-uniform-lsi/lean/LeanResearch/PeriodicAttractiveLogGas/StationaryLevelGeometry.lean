import LeanResearch.PeriodicAttractiveLogGas.StationarySard
import LeanResearch.PeriodicAttractiveLogGas.StationaryDistribution
import LeanResearch.PeriodicAttractiveLogGas.TorusLocalGeometry
import LeanResearch.PeriodicAttractiveLogGas.SmoothContraction
import Mathlib.Analysis.SpecialFunctions.Sigmoid

/-!
Actual regular-level geometry for manuscript lines 1602--1641. The first
steps derive regular-fibre nullity from the proved implicit parametrization
and transfer it through the actual probability-Haar periodic cover. No
null-fibre, coarea, flux, or isoperimetric conclusion is an input.

The implicit and Hausdorff arguments are applications of the attributed,
locally adapted proofs in `StationarySard`; no additional package is used.
The exact development and checking status is recorded separately in
`research/reviews/stationary-level-geometry-development.md`.
-/

noncomputable section

open Filter Function MeasureTheory MeasureTheory.Measure Module Set
open scoped ContDiff ENNReal NNReal Topology BigOperators RealInnerProductSpace

namespace PeriodicAttractiveLogGas.StationaryLevelGeometry

open StationarySard StationaryDistribution

private theorem continuous_integrable {f : Torus → ℝ} (hf : Continuous f) :
    Integrable f torusMeasure :=
  memLp_one_iff_integrable.mp
    (ContinuousMap.memLp (μ := torusMeasure) (p := 1) ℝ ⟨f, hf⟩)

/-- Every regular planar scalar level is area-null. The level is locally
covered by a genuine C1 map from the kernel of a surjective scalar derivative;
that kernel has dimension one. No global graph or atom-free premise is used. -/
theorem volume_regular_level_eq_zero {f : PlanarSpace → ℝ}
    (hf : ContDiff ℝ 1 f) {t : ℝ}
    (ht : ∀ x, f x = t → fderiv ℝ f x ≠ 0) :
    volume {x | f x = t} = 0 := by
  let g : PlanarSpace → ℝ := fun x ↦ f x - t
  have hg : ContDiff ℝ 1 g := hf.sub contDiff_const
  have hzero : ∀ x, f x = t → iteratedFDeriv ℝ 0 g x = 0 := by
    intro x hx
    rw [← norm_eq_zero, iteratedFDeriv_zero_eq_comp, comp_apply,
      LinearIsometryEquiv.norm_map]
    simp only [g, hx, sub_self, norm_zero]
  have hnull : volume (id '' {x | f x = t}) = 0 := by
    apply measure_image_null_of_locally_null
    intro a ha
    have hnext : iteratedFDeriv ℝ (0 + 1) g a ≠ 0 := by
      intro hz
      have hn : ‖fderiv ℝ g a‖ = 0 := by
        rw [← norm_iteratedFDeriv_one, hz, norm_zero]
      apply ht a ha
      have hd : fderiv ℝ g a = fderiv ℝ f a := by
        change fderiv ℝ (fun x ↦ f x - t) a = _
        rw [fderiv_sub_const]
      exact norm_eq_zero.mp (hd ▸ hn)
    obtain ⟨g₀, L, θ, -, -, -, -, -, hθ, -, hcover, hdim⟩ :=
      exists_parametrization_flat_stratum (i := 0) (r := 1)
        (by simpa only [add_zero, Nat.cast_one] using hg.contDiffAt)
        (by decide) (hzero a ha) hnext
    obtain ⟨w, hw, hθw⟩ := hθ.contDiffOn (m := (1 : ℕ∞ω)) le_rfl (by simp)
    have hwmem : interior w ∈ 𝓝 (0 : ↥L.ker) :=
      isOpen_interior.mem_nhds (mem_interior_iff_mem_nhds.mpr hw)
    have hchart : volume (θ '' interior w) = 0 := by
      apply addHaar_image_flat_eq_zero (k := 0) volume isOpen_interior
        (hθw.mono interior_subset) (subset_refl _) (by omega)
      have hp : finrank ℝ PlanarSpace = 2 := by simp [PlanarSpace]
      rw [hp] at hdim ⊢
      omega
    refine ⟨{x | f x = t} ∩
      {x | iteratedFDeriv ℝ 0 g x = 0 → x ∈ θ '' interior w},
      inter_mem_nhdsWithin _ (hcover _ hwmem), ?_⟩
    rw [image_id]
    apply measure_mono_null (t := θ '' interior w) ?_ hchart
    rintro y ⟨hy, hyθ⟩
    exact hyθ (hzero y hy)
  simpa only [image_id] using hnull

/-- Continuity of the actual scalar function follows from its smooth periodic
lift, rather than being a second independent assumption. -/
theorem continuous_of_contDiff_lift {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) : Continuous v :=
  isOpenQuotientMap_torusQuotient.isQuotientMap.continuous_iff.mpr hv.continuous

/-- A regular fibre has zero mass for the original probability Haar measure.
The transfer includes fundamental-box boundary points through the actual
measure-preserving periodic cover. -/
theorem torusMeasure_regular_level_eq_zero {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) : torusMeasure {z | v z = t} = 0 := by
  have hvc := continuous_of_contDiff_lift hv
  have hnull : volume {x : PlanarSpace | v (torusQuotient x) = t} = 0 := by
    apply volume_regular_level_eq_zero hv
    intro x hx hd
    exact ht ⟨torusQuotient x, (mem_torusCriticalPoints_lift_iff v x).mpr hd, hx⟩
  have hlevel : MeasurableSet {z | v z = t} :=
    (isClosed_eq hvc continuous_const).measurableSet
  have hmp := measurePreserving_torusQuotient_box (0 : PlanarSpace)
  rw [← hmp.measure_preimage hlevel.nullMeasurableSet]
  rw [Measure.restrict_apply (hlevel.preimage hmp.measurable)]
  exact measure_mono_null inter_subset_left hnull

/-- Literal absence of an atom in the actual scalar push-forward law. -/
theorem map_singleton_regular_eq_zero {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) : (torusMeasure.map v) {t} = 0 := by
  rw [Measure.map_apply (continuous_of_contDiff_lift hv).measurable (measurableSet_singleton t)]
  exact torusMeasure_regular_level_eq_zero hv ht

/-- A probability CDF is continuous at every point without an atom. This
uses its actual Stieltjes singleton formula, including both one-sided limits. -/
theorem continuousAt_cdf_of_singleton_eq_zero (μ : Measure ℝ)
    [IsProbabilityMeasure μ] {t : ℝ} (ht : μ {t} = 0) :
    ContinuousAt (ProbabilityTheory.cdf μ) t := by
  let F := ProbabilityTheory.cdf μ
  have hmass : ENNReal.ofReal (F t - Function.leftLim F t) = 0 := by
    rw [← StieltjesFunction.measure_singleton, ProbabilityTheory.measure_cdf]
    exact ht
  have hleft : Function.leftLim F t = F t := by
    have hle : F t - Function.leftLim F t ≤ 0 := ENNReal.ofReal_eq_zero.mp hmass
    exact le_antisymm (F.mono.leftLim_le le_rfl) (by linarith)
  have hright : Function.rightLim F t = F t :=
    F.mono.continuousWithinAt_Ioi_iff_rightLim_eq.mp
      ((F.right_continuous t).mono Ioi_subset_Ici_self)
  exact F.mono.continuousAt_iff_leftLim_eq_rightLim.mpr (hleft.trans hright.symm)

/-- The literal source rank is two-sided continuous at every regular value.
Possible atoms at critical values have not been discarded. -/
theorem rank_continuousAt_regular {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) : ContinuousAt (rank v) t := by
  have hvc := continuous_of_contDiff_lift hv
  let : IsProbabilityMeasure (torusMeasure.map v) :=
    (Measure.isProbabilityMeasure_map_iff hvc.measurable.aemeasurable).mpr inferInstance
  have hc := continuousAt_cdf_of_singleton_eq_zero (torusMeasure.map v)
    (map_singleton_regular_eq_zero hv ht)
  have he : rank v = fun r ↦ 1 - ProbabilityTheory.cdf (torusMeasure.map v) r :=
    funext (rank_eq_one_sub_cdf hvc)
  rw [he]
  exact continuousAt_const.sub hc

/-- The regular values form an open set and every rank point in that set is
continuous in a whole neighbourhood, as required by the inverse theorem. -/
theorem rank_eventually_continuousAt_regular {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    ∀ᶠ r in 𝓝 t, ContinuousAt (rank v) r := by
  filter_upwards [(isCompact_torusCriticalValues hv).isClosed.isOpen_compl.mem_nhds ht]
    with r hr
  exact rank_continuousAt_regular hv hr

/-- The original exponentially weighted superlevel mass is continuous at
regular values. The proved equidistribution identity identifies it with the
actual cumulative profile; no continuity of moving-set integrals is assumed. -/
theorem superlevelMass_continuousAt_regular {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) : ContinuousAt (superlevelMass v) t := by
  have hvc := continuous_of_contDiff_lift hv
  have hq := StationaryCumulative.continuous_extendProfile (profile_continuousOn hvc)
  have he : superlevelMass v = fun r ↦ StationaryCumulative.cumulative
      (StationaryCumulative.extendProfile (profile v)) (rank v r) := by
    funext r
    rw [superlevelMass_eq_cumulative hvc,
      StationaryCumulative.cumulative_extendProfile ⟨rank_nonneg v r, rank_le_one v r⟩]
  rw [he]
  exact (StationaryCumulative.cumulative_hasDerivAt hq (rank v t)).continuousAt.comp
    (rank_continuousAt_regular hv ht)

/-- The inverse identity is now unconditional at a regular profile value;
the continuity premise of the general distribution construction is proved. -/
theorem rank_profile_eq_regular {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) (hr : profile v s ∉ torusCriticalValues v) :
    rank v (profile v s) = s :=
  rank_profile_eq_of_continuousAt (continuous_of_contDiff_lift hv) hs hs1
    (rank_continuousAt_regular hv hr)

/-- The physical gradient norm is a genuine continuous torus function. -/
theorem continuous_norm_gradient {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    Continuous (fun z : Torus ↦ ‖torusOrdinaryGradient v z‖) := by
  apply isOpenQuotientMap_torusQuotient.isQuotientMap.continuous_iff.mpr
  simpa only [Function.comp_def, norm_torusOrdinaryGradient_lift] using
    (hv.fderiv_right (m := 0) (by norm_num)).continuous.norm

/-- The actual periodic lift is globally Lipschitz in the physical Euclidean
norm. Its bound comes from the continuous gradient on the compact torus,
not from the default product metric on `Torus`. -/
theorem exists_lipschitz_lift {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) :
    ∃ L : ℝ≥0, LipschitzWith L (fun x : PlanarSpace ↦ v (torusQuotient x)) := by
  let G : C(Torus, ℝ) := ⟨fun z ↦ ‖torusOrdinaryGradient v z‖, continuous_norm_gradient hv⟩
  refine ⟨‖G‖₊, ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hv.differentiable (by norm_num))
  intro x
  have h : ‖fderiv ℝ (fun y : PlanarSpace ↦ v (torusQuotient y)) x‖ ≤ ‖G‖ := by
    rw [← norm_torusOrdinaryGradient_lift]
    simpa only [G, ContinuousMap.coe_mk, norm_norm] using G.norm_coe_le_norm (torusQuotient x)
  exact_mod_cast h

/-- Compactness gives a positive lower gradient bound on an actual band
around every regular value. This supplies a uniform local denominator for
submersion coordinates, even when the level is empty. -/
theorem exists_regular_band_gradient_lower {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z, |v z - t| ≤ ε → ε ≤ ‖torusOrdinaryGradient v z‖ := by
  let H : Torus → ℝ := fun z ↦ |v z - t| + ‖torusOrdinaryGradient v z‖
  have hH : Continuous H :=
    ((continuous_of_contDiff_lift hv).sub continuous_const).abs.add (continuous_norm_gradient hv)
  have hpos : ∀ z, 0 < H z := by
    intro z
    by_cases hz : v z = t
    · have hg : torusOrdinaryGradient v z ≠ 0 := fun hg ↦ ht ⟨z, hg, hz⟩
      simpa only [H, hz, sub_self, abs_zero, zero_add] using norm_pos_iff.mpr hg
    · exact add_pos_of_pos_of_nonneg (abs_pos.mpr (sub_ne_zero.mpr hz)) (norm_nonneg _)
  obtain ⟨z₀, -, hmin⟩ := (isCompact_univ : IsCompact (univ : Set Torus)).exists_isMinOn
    univ_nonempty hH.continuousOn
  have hmin' : ∀ z, H z₀ ≤ H z := isMinOn_univ_iff.mp hmin
  refine ⟨H z₀ / 2, half_pos (hpos z₀), ?_⟩
  intro z hz
  have hm := hmin' z
  dsimp only [H] at hm hz ⊢
  linarith

/-- First-gradient pairing for the ordinary smooth torus Laplacian. Every
summand is continuous on the compact original torus, so the finite integral
interchanges require no separate analytic assumption. -/
theorem torus_gradient_pairing (f g : SmoothPair 1) :
    (∫ z, inner ℝ (f.torusGradient z) (g.torusGradient z) ∂torusMeasure) =
      -(∫ z, f.torusValue z * g.laplacian.torusValue z ∂torusMeasure) := by
  let D (j : Fin 2) := g.directionalDerivativePair (EuclideanSpace.single (0, j) 1)
  have hd (j : Fin 2) (z : Torus) :
      (D j).torusValue z = inner ℝ (g.torusGradient z) (EuclideanSpace.single j 1) := by
    simpa only [singleParticleCoordinates_single, D] using
      g.torus_directionalDerivative_value z (EuclideanSpace.single j 1)
  have hi (j : Fin 2) : Integrable
      (fun z ↦ (D j).torusValue z * inner ℝ (f.torusGradient z) (EuclideanSpace.single j 1))
      torusMeasure := continuous_integrable
    ((D j).torusValue.continuous.mul (f.torusGradient.continuous.inner continuous_const))
  have hj (j : Fin 2) : Integrable
      (fun z ↦ f.torusValue z * inner ℝ ((D j).torusGradient z) (EuclideanSpace.single j 1))
      torusMeasure := continuous_integrable
    (f.torusValue.continuous.mul ((D j).torusGradient.continuous.inner continuous_const))
  calc
    (∫ z, inner ℝ (f.torusGradient z) (g.torusGradient z) ∂torusMeasure) =
        ∫ z, ∑ j : Fin 2, (D j).torusValue z *
          inner ℝ (f.torusGradient z) (EuclideanSpace.single j 1) ∂torusMeasure := by
      apply integral_congr_ae
      filter_upwards with z
      simp [hd, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]
    _ = ∑ j : Fin 2, ∫ z, (D j).torusValue z *
        inner ℝ (f.torusGradient z) (EuclideanSpace.single j 1) ∂torusMeasure :=
      integral_finsetSum Finset.univ (fun j _ ↦ hi j)
    _ = ∑ j : Fin 2, -(∫ z, f.torusValue z *
        inner ℝ ((D j).torusGradient z) (EuclideanSpace.single j 1) ∂torusMeasure) := by
      apply Finset.sum_congr rfl
      intro j _
      exact f.torus_integration_by_parts (D j) (EuclideanSpace.single j 1)
    _ = -(∫ z, f.torusValue z * g.laplacian.torusValue z ∂torusMeasure) := by
      rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ (fun j _ ↦ hj j)]
      congr 1
      apply integral_congr_ae
      filter_upwards with z
      rw [← Finset.mul_sum]
      congr 1
      simp only [SmoothPair.torusValue, SmoothPair.laplacian_value_apply,
        Fin.sum_univ_one, SmoothPair.secondDirectionalDerivativePair_value_apply,
        SmoothPair.torusGradient, ContinuousMap.coe_mk, inner_firstParticleCoordinates,
        singleParticleCoordinates_single, D]

theorem norm_torusGradient_eq_ordinary (f : SmoothPair 1) (z : Torus) :
    ‖f.torusGradient z‖ = ‖torusOrdinaryGradient f.torusValue z‖ := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective z
  rw [norm_torusOrdinaryGradient_lift, (f.torus_differential x).fderiv, innerSL_apply_norm]

theorem torusGradient_compSmooth (f : SmoothPair 1) (T : ℝ → ℝ)
    (hT : ContDiff ℝ ∞ T) (z : Torus) :
    (f.compSmooth T hT).torusGradient z =
      deriv T (f.torusValue z) • f.torusGradient z := by
  change firstParticleCoordinates ((f.compSmooth T hT).gradient (singleConfiguration z)) = _
  rw [SmoothPair.compSmooth_gradient, map_smul]
  rfl

/-- Both terms of the actual weak flux law are integrable before the
integration-by-parts identity is applied. -/
theorem integrable_weak_flux_terms {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {T : ℝ → ℝ} (hT : ContDiff ℝ ∞ T) :
    Integrable (fun z ↦ deriv T (v z) * ‖torusOrdinaryGradient v z‖ ^ 2) torusMeasure ∧
      Integrable (fun z ↦ T (v z) * (Real.exp (v z) - 1)) torusMeasure := by
  have hvc := continuous_of_contDiff_lift (hv.of_le (by simp))
  refine ⟨continuous_integrable ?_, continuous_integrable ?_⟩
  · exact ((hT.continuous_deriv (by simp)).comp hvc).mul
      ((continuous_norm_gradient (hv.of_le (by simp))).pow 2)
  · exact (hT.continuous.comp hvc).mul ((Real.continuous_exp.comp hvc).sub continuous_const)

/-- Actual periodic weak flux from the normalized mean-field PDE. This is
proved for every smooth scalar test, with the physical gradient and original
probability Haar measure. It is not asserted to be the H1 level-flux formula;
identifying that formula still requires the separate geometric coarea step. -/
theorem stationary_weak_flux {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    {T : ℝ → ℝ} (hT : ContDiff ℝ ∞ T) :
    (∫ z, deriv T (v z) * ‖torusOrdinaryGradient v z‖ ^ 2 ∂torusMeasure) =
      ρ * ∫ z, T (v z) * (Real.exp (v z) - 1) ∂torusMeasure := by
  let V : C(Torus, ℝ) := ⟨v, continuous_of_contDiff_lift (hv.of_le (by simp))⟩
  let f : SmoothPair 1 := SmoothPair.ofTorusContDiffLift V hv
  have hvalue : f.torusValue = V := rfl
  have hLap (z : Torus) : -f.laplacian.torusValue z = ρ * (Real.exp (v z) - 1) := by
    obtain ⟨x, rfl⟩ := torusQuotient_surjective z
    change torusNegativeLaplacian V hv (torusQuotient x) = _
    rw [torusNegativeLaplacian_lift_eq]
    exact hpde x
  have hg := torus_gradient_pairing (f.compSmooth T hT) f
  have he (z : Torus) :
      inner ℝ ((f.compSmooth T hT).torusGradient z) (f.torusGradient z) =
        deriv T (v z) * ‖torusOrdinaryGradient v z‖ ^ 2 := by
    rw [torusGradient_compSmooth, inner_smul_left, conj_trivial,
      real_inner_self_eq_norm_sq, norm_torusGradient_eq_ordinary]
    rfl
  simp_rw [he] at hg
  calc
    (∫ z, deriv T (v z) * ‖torusOrdinaryGradient v z‖ ^ 2 ∂torusMeasure) =
        -(∫ z, T (v z) * f.laplacian.torusValue z ∂torusMeasure) := hg
    _ = ∫ z, ρ * (T (v z) * (Real.exp (v z) - 1)) ∂torusMeasure := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards with z
      calc -(T (v z) * f.laplacian.torusValue z) =
          T (v z) * (-f.laplacian.torusValue z) := by ring
        _ = _ := by rw [hLap]; ring
    _ = _ := integral_const_mul ρ _

/-- Smooth bounded approximation to the strict superlevel indicator. At
the level itself its value is one half; the actual regular-fibre nullity
is used below rather than changing that value artificially. -/
def superlevelCutoff (t : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  Real.sigmoid ((n : ℝ) * (r - t))

theorem contDiff_superlevelCutoff (t : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (superlevelCutoff t n) := by
  exact (contDiff_sigmoid.of_le (by simp) : ContDiff ℝ ∞ Real.sigmoid).comp
    (contDiff_const.mul (contDiff_id.sub contDiff_const))

theorem hasDerivAt_superlevelCutoff (t : ℝ) (n : ℕ) (r : ℝ) :
    HasDerivAt (superlevelCutoff t n)
      ((n : ℝ) * superlevelCutoff t n r * (1 - superlevelCutoff t n r)) r := by
  change HasDerivAt (fun s : ℝ ↦ Real.sigmoid ((n : ℝ) * (s - t))) _ r
  simpa only [superlevelCutoff, Function.comp_def, id_eq, mul_one,
    mul_comm, mul_left_comm, mul_assoc] using
    (Real.hasDerivAt_sigmoid ((n : ℝ) * (r - t))).comp r
      (((hasDerivAt_id r).sub_const t).const_mul (n : ℝ))

theorem superlevelCutoff_mem_unitInterval (t : ℝ) (n : ℕ) (r : ℝ) :
    0 ≤ superlevelCutoff t n r ∧ superlevelCutoff t n r ≤ 1 :=
  ⟨Real.sigmoid_nonneg _, Real.sigmoid_le_one _⟩

theorem tendsto_superlevelCutoff {r t : ℝ} (hrt : r ≠ t) :
    Tendsto (fun n : ℕ ↦ superlevelCutoff t n r) atTop
      (𝓝 (if t < r then 1 else 0)) := by
  by_cases h : t < r
  · have hm := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (sub_pos.mpr h)
    simpa only [superlevelCutoff, Function.comp_def, ite_eq_left h] using
      Real.tendsto_sigmoid_atTop.comp hm
  · have hr : r < t := lt_of_le_of_ne (le_of_not_gt h) hrt
    have hm := (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_mul_const (sub_pos.mpr hr)
    have hp := Real.tendsto_sigmoid_atTop.comp hm
    have he : (fun n : ℕ ↦ superlevelCutoff t n r) =
        fun n : ℕ ↦ 1 - Real.sigmoid ((n : ℝ) * (t - r)) := by
      funext n
      rw [← Real.sigmoid_neg]
      unfold superlevelCutoff
      congr 1
      ring
    rw [ite_eq_right h, he]
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    simpa only [sub_self, Function.comp_def] using hone.sub hp

/-- Genuine dominated convergence to a strict superlevel integral. The
weight is only required to be integrable, and absence of an atom at the
chosen value is the precise reason the half-value at the boundary disappears. -/
theorem tendsto_integral_superlevelCutoff {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {v w : α → ℝ} {t : ℝ} (hv : Measurable v)
    (hw : Integrable w μ) (ht : μ {x | v x = t} = 0) :
    Tendsto (fun n : ℕ ↦ ∫ x, superlevelCutoff t n (v x) * w x ∂μ) atTop
      (𝓝 (∫ x in {x | t < v x}, w x ∂μ)) := by
  have hae : ∀ᵐ x ∂μ, v x ≠ t := by
    simpa only [ae_iff, not_not] using ht
  rw [← integral_indicator (measurableSet_lt measurable_const hv)]
  apply tendsto_integral_of_dominated_convergence (fun x ↦ ‖w x‖)
    (fun n ↦
      ((contDiff_superlevelCutoff t n).continuous.measurable.comp hv).aestronglyMeasurable.mul
        hw.aestronglyMeasurable) hw.norm
  · intro n
    filter_upwards with x
    change ‖superlevelCutoff t n (v x) * w x‖ ≤ ‖w x‖
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (superlevelCutoff_mem_unitInterval t n (v x)).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (superlevelCutoff_mem_unitInterval t n (v x)).2
  · filter_upwards [hae] with x hx
    have hh := (tendsto_superlevelCutoff hx).mul_const (w x)
    by_cases h : t < v x
    · rw [Set.indicator_of_mem (show x ∈ {a | t < v a} from h)]
      simpa only [ite_eq_left h, one_mul, Pi.mul_apply, Function.comp_apply] using hh
    · rw [Set.indicator_of_notMem (show x ∉ {a | t < v a} from h)]
      simpa only [ite_eq_right h, zero_mul, Pi.mul_apply, Function.comp_apply] using hh

theorem superlevel_source_integral {v : Torus → ℝ} (hv : Continuous v) (t : ℝ) :
    (∫ z in {z | t < v z}, Real.exp (v z) - 1 ∂torusMeasure) =
      superlevelMass v t - rank v t := by
  have hi : Integrable (fun z ↦ Real.exp (v z)) torusMeasure :=
    continuous_integrable (Real.continuous_exp.comp hv)
  rw [integral_sub hi.restrict (integrable_const (1 : ℝ))]
  simp only [superlevelMass, rank, setIntegral_const, smul_eq_mul, mul_one]

theorem integrable_superlevel_boundaryLayer {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x))) (t : ℝ) (n : ℕ) :
    Integrable (fun z ↦
      ((n : ℝ) * superlevelCutoff t n (v z) * (1 - superlevelCutoff t n (v z))) *
        ‖torusOrdinaryGradient v z‖ ^ 2) torusMeasure := by
  simpa only [(hasDerivAt_superlevelCutoff t n _).deriv] using
    (integrable_weak_flux_terms hv (contDiff_superlevelCutoff t n)).1

/-- Exact regular-superlevel flux as a limit of actual physical-gradient
boundary layers. This proves the PDE side of the source flux law, with no
coarea or divergence certificate. Equality with the Hausdorff level integral
is a separate geometric obligation and is not asserted here. -/
theorem stationary_superlevel_flux_limit {v : Torus → ℝ} {ρ t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    (ht : t ∉ torusCriticalValues v) :
    Tendsto (fun n : ℕ ↦ ∫ z,
      ((n : ℝ) * superlevelCutoff t n (v z) * (1 - superlevelCutoff t n (v z))) *
        ‖torusOrdinaryGradient v z‖ ^ 2 ∂torusMeasure) atTop
      (𝓝 (ρ * (superlevelMass v t - rank v t))) := by
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  have hvc := continuous_of_contDiff_lift hv1
  have hw : Integrable (fun z ↦ Real.exp (v z) - 1) torusMeasure :=
    continuous_integrable ((Real.continuous_exp.comp hvc).sub continuous_const)
  have hlim := tendsto_integral_superlevelCutoff (w := fun z ↦ Real.exp (v z) - 1)
    hvc.measurable hw
    (torusMeasure_regular_level_eq_zero hv1 ht)
  rw [superlevel_source_integral hvc t] at hlim
  have he (n : ℕ) :
      (∫ z, ((n : ℝ) * superlevelCutoff t n (v z) * (1 - superlevelCutoff t n (v z))) *
          ‖torusOrdinaryGradient v z‖ ^ 2 ∂torusMeasure) =
        ρ * ∫ z, superlevelCutoff t n (v z) * (Real.exp (v z) - 1) ∂torusMeasure := by
    have hh := stationary_weak_flux hv hpde (contDiff_superlevelCutoff t n)
    simpa only [(hasDerivAt_superlevelCutoff t n _).deriv] using hh
  simp_rw [he]
  exact hlim.const_mul ρ

theorem stationary_superlevel_flux_nonneg {v : Torus → ℝ} {ρ t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    (ht : t ∉ torusCriticalValues v) :
    0 ≤ ρ * (superlevelMass v t - rank v t) := by
  apply ge_of_tendsto (stationary_superlevel_flux_limit hv hpde ht)
  exact Eventually.of_forall fun n ↦ integral_nonneg fun z ↦
    mul_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n)
      (superlevelCutoff_mem_unitInterval t n (v z)).1)
      (sub_nonneg.mpr (superlevelCutoff_mem_unitInterval t n (v z)).2)) (sq_nonneg _)

end PeriodicAttractiveLogGas.StationaryLevelGeometry
