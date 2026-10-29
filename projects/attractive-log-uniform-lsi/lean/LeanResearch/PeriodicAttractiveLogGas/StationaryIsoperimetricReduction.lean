import LeanResearch.PeriodicAttractiveLogGas.StationaryLevelContinuity
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Analytic stationary reduction from sharp physical isoperimetry

This is the supplied argument at manuscript lines 1612–1656. The only
remaining geometric input is named explicitly below and concerns the
actual physical H1 measure of regular strict-superlevel frontiers. All
rank, rearrangement, cumulative and differential data are constructed
from the original scalar function. This intermediate reduction does not
assert that the geometric input or the full manuscript theorem is proved.

The development record is
`research/reviews/stationary-isoperimetric-reduction-development.md`.
-/

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal

namespace PeriodicAttractiveLogGas.StationaryIsoperimetricReduction

open StationarySard StationaryDistribution StationaryLevelGeometry
  StationaryCoarea StationaryLevelBoundary StationaryLevelContinuity

/-- The literal sharp physical isoperimetric input, kept separate from
the analytic stationary argument. No rank derivative, flux, rearrangement
regularity, or stationary conclusion is included in this proposition. -/
def SharpPhysicalSuperlevelIsoperimetry (v : Torus → ℝ) : Prop :=
  ∀ t : ℝ, t ∉ torusCriticalValues v →
    StationaryRearrangement.profile (rank v t) ≤
      (physicalCurveMeasure.real (frontier {z | t < v z})) ^ 2

private theorem continuous_integrable {f : Torus → ℝ} (hf : Continuous f) :
    Integrable f torusMeasure :=
  memLp_one_iff_integrable.mp
    (ContinuousMap.memLp (μ := torusMeasure) (p := 1) ℝ ⟨f, hf⟩)

theorem superlevelMass_le_one {v : Torus → ℝ} (hv : Continuous v)
    (hmass : (∫ z, Real.exp (v z) ∂torusMeasure) = 1) (t : ℝ) :
    superlevelMass v t ≤ 1 := by
  have hi := continuous_integrable (Real.continuous_exp.comp hv)
  have hh := setIntegral_le_integral (s := {z | t < v z}) hi
    (Eventually.of_forall fun z ↦ (Real.exp_pos (v z)).le)
  simpa only [Function.comp_def, superlevelMass, hmass] using hh

theorem neg_rank_deriv_nonneg_regular {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)))
    {t : ℝ} (ht : t ∉ torusCriticalValues v) : 0 ≤ -deriv (rank v) t := by
  rw [(hasDerivAt_rank_regular hv ht).deriv, neg_neg]
  exact integral_nonneg fun z ↦ inv_nonneg.mpr (norm_nonneg _)

/-- The source level inequality, derived from the actual pointwise flux
and rank identities and the sole named geometric input. -/
theorem level_inequality {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    (hiso : SharpPhysicalSuperlevelIsoperimetry v)
    {t : ℝ} (ht : t ∉ torusCriticalValues v) :
    StationaryRearrangement.profile (rank v t) ≤
      ρ * (superlevelMass v t - rank v t) * (-deriv (rank v) t) := by
  have hh := hiso t ht
  rw [frontier_strict_superlevel_eq (hv.of_le (by simp)) ht] at hh
  exact hh.trans (level_length_squared_le_flux_rank_regular hv hpde ht)

/-- The exact source central-rank slope bound. It applies to all regular
values whose actual ranks are central, without an extra value-range premise. -/
theorem central_rank_slope {v : Torus → ℝ} {ρ ε t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    (hmass : (∫ z, Real.exp (v z) ∂torusMeasure) = 1)
    (hiso : SharpPhysicalSuperlevelIsoperimetry v) (hρ : 0 < ρ)
    (hrank : rank v t ∈ Icc ε (1 - ε)) (ht : t ∉ torusCriticalValues v) :
    4 * Real.pi * ε * (1 - ε) / ρ ≤ -deriv (rank v) t := by
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  have hquad : ε * (1 - ε) ≤ rank v t * (1 - rank v t) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrank.1) (sub_nonneg.mpr hrank.2)]
  have hlow : 4 * Real.pi * ε * (1 - ε) ≤
      StationaryRearrangement.profile (rank v t) := by
    have hh := mul_le_mul_of_nonneg_left hquad (by positivity : 0 ≤ 4 * Real.pi)
    have hp := StationaryRearrangement.profile_ge ⟨rank_nonneg v t, rank_le_one v t⟩
    nlinarith only [hh, hp]
  have hd := neg_rank_deriv_nonneg_regular hv1 ht
  have hB := superlevelMass_le_one (continuous_of_contDiff_lift hv1) hmass t
  have hsub : superlevelMass v t - rank v t ≤ 1 := by linarith [rank_nonneg v t]
  have hfactor : ρ * (superlevelMass v t - rank v t) ≤ ρ := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hsub hρ.le
  have hh := hlow.trans ((level_inequality hv hpde hiso ht).trans
    (mul_le_mul_of_nonneg_right hfactor hd))
  apply (div_le_iff₀ hρ).mpr
  simpa only [mul_comm] using hh

/-- A strictly interior actual rank has a strictly negative derivative
at every regular value. This supplies the nonzero inverse derivative. -/
theorem rank_deriv_neg_regular {v : Torus → ℝ} {ρ t : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    (hmass : (∫ z, Real.exp (v z) ∂torusMeasure) = 1)
    (hiso : SharpPhysicalSuperlevelIsoperimetry v) (hρ : 0 < ρ)
    (hrank : rank v t ∈ Ioo 0 1) (ht : t ∉ torusCriticalValues v) :
    deriv (rank v) t < 0 := by
  let ε := min (rank v t) (1 - rank v t) / 2
  have he : 0 < ε := div_pos (lt_min hrank.1 (sub_pos.mpr hrank.2)) (by norm_num)
  have hes : ε < 1 / 2 := by
    have hh := min_le_left (rank v t) (1 - rank v t)
    dsimp only [ε]
    linarith [hrank.2]
  have hr : rank v t ∈ Icc ε (1 - ε) := by
    have h1 := min_le_left (rank v t) (1 - rank v t)
    have h2 := min_le_right (rank v t) (1 - rank v t)
    dsimp only [ε]
    constructor <;> linarith [hrank.1, hrank.2]
  have hh := central_rank_slope hv hpde hmass hiso hρ hr ht
  have hc : 0 < 4 * Real.pi * ε * (1 - ε) / ρ := by
    have h : 0 < 1 - ε := by linarith
    positivity
  linarith

/-- Absolute continuity on the full closed rank interval is proved for
the actual generalized inverse. Singular rank variation and endpoint
atoms are handled by the frozen monotone-variation and endpoint arguments. -/
theorem actual_profile_ac {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    (hmass : (∫ z, Real.exp (v z) ∂torusMeasure) = 1)
    (hiso : SharpPhysicalSuperlevelIsoperimetry v) (hρ : 0 < ρ) :
    AbsolutelyContinuousOnInterval (StationaryDistribution.profile v) 0 1 := by
  apply profile_ac_of_slope (continuous_of_contDiff_lift (hv.of_le (by simp))) hρ
    (volume_torusCriticalValues_eq_zero hv)
  intro ε _ _ t _ hr ht
  exact central_rank_slope hv hpde hmass hiso hρ hr ht

/-- Complete analytic data for the actual cumulative rearrangement,
including mass, endpoint conditions, positive excess and true second
derivatives. None of these conclusions is a constructor premise. -/
theorem actual_cumulative_data {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    (hmass : (∫ z, Real.exp (v z) ∂torusMeasure) = 1)
    (hiso : SharpPhysicalSuperlevelIsoperimetry v) (hρ : 0 < ρ)
    (hne : ¬ ∃ c : ℝ, ∀ z, v z = c) :
    let q := StationaryDistribution.profile v
    let M := StationaryCumulative.cumulative (StationaryCumulative.extendProfile q)
    AbsolutelyContinuousOnInterval M 0 1 ∧
      AbsolutelyContinuousOnInterval (deriv M) 0 1 ∧
      M 0 = 0 ∧ M 1 = 1 ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        M s = StationaryCumulative.cumulative q s ∧ deriv M s = Real.exp (q s)) ∧
      ConcaveOn ℝ univ M ∧ (∀ s ∈ Icc (0 : ℝ) 1, s ≤ M s) ∧
      0 < StationaryRearrangement.excessArea M ∧
      (∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
        deriv (deriv M) s = Real.exp (q s) * deriv q s ∧ 0 ≤ -deriv (deriv M) s) := by
  have hc := continuous_of_contDiff_lift (hv.of_le (by simp))
  apply cumulative_profile_data hc hmass hne hρ (volume_torusCriticalValues_eq_zero hv)
  intro ε _ _ t _ hr ht
  exact central_rank_slope hv hpde hmass hiso hρ hr ht

/-- The actual profile is locally the inverse of the actual rank at every
regular profile value. Continuity, the inverse identity, and the nonzero
derivative are all proved from the original objects. -/
theorem actual_profile_derivative_regular {v : Torus → ℝ} {ρ s : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    (hmass : (∫ z, Real.exp (v z) ∂torusMeasure) = 1)
    (hiso : SharpPhysicalSuperlevelIsoperimetry v) (hρ : 0 < ρ)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (ht : StationaryDistribution.profile v s ∉ torusCriticalValues v) :
    HasDerivAt (StationaryDistribution.profile v)
        (deriv (rank v) (StationaryDistribution.profile v s))⁻¹ s ∧
      deriv (rank v) (StationaryDistribution.profile v s) < 0 ∧
      rank v (StationaryDistribution.profile v s) = s := by
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  have hc := continuous_of_contDiff_lift hv1
  have he := rank_profile_eq_of_continuousAt hc hs.1.le hs.2
    (rank_continuousAt_regular hv1 ht)
  have hn := rank_deriv_neg_regular hv hpde hmass hiso hρ (by rw [he]; exact hs) ht
  have hcont : ∀ᶠ t in 𝓝 (StationaryDistribution.profile v s),
      ContinuousAt (rank v) t := by
    filter_upwards [(isCompact_torusCriticalValues hv1).isClosed.isOpen_compl.mem_nhds ht]
      with t htc
    exact rank_continuousAt_regular hv1 htc
  have hd := (hasDerivAt_rank_regular hv1 ht).differentiableAt.hasDerivAt
  exact ⟨profile_hasDerivAt hc hs hd hn.ne hcont, hn, he⟩

/-- Source multiplication by the negative inverse derivative at an
actual regular profile value. The curvature is expressed here by the
true profile derivative; the AE cumulative chain rule is applied below. -/
theorem rearranged_inequality_regular {v : Torus → ℝ} {ρ s : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    (hmass : (∫ z, Real.exp (v z) ∂torusMeasure) = 1)
    (hiso : SharpPhysicalSuperlevelIsoperimetry v) (hρ : 0 < ρ)
    (hs : s ∈ Ioo (0 : ℝ) 1)
    (ht : StationaryDistribution.profile v s ∉ torusCriticalValues v) :
    let q := StationaryDistribution.profile v
    let M := StationaryCumulative.cumulative (StationaryCumulative.extendProfile q)
    StationaryRearrangement.profile s * (-(Real.exp (q s) * deriv q s)) ≤
      ρ * Real.exp (q s) * (M s - s) := by
  let q := StationaryDistribution.profile v
  let M := StationaryCumulative.cumulative (StationaryCumulative.extendProfile q)
  let r := deriv (rank v) (q s)
  have hd := actual_profile_derivative_regular hv hpde hmass hiso hρ hs ht
  have hr : r < 0 := hd.2.1
  have hq : deriv q s = r⁻¹ := hd.1.deriv
  have hB : superlevelMass v (q s) = M s := by
    rw [superlevelMass_eq_cumulative
      (continuous_of_contDiff_lift (hv.of_le (by simp))), hd.2.2]
    exact (StationaryCumulative.cumulative_extendProfile ⟨hs.1.le, hs.2.le⟩).symm
  have hlevel := level_inequality hv hpde hiso ht
  rw [hd.2.2, hB] at hlevel
  have hnonneg : 0 ≤ -(r⁻¹) * Real.exp (q s) :=
    mul_nonneg (neg_nonneg.mpr (inv_nonpos.mpr hr.le)) (Real.exp_pos _).le
  have hscaled := mul_le_mul_of_nonneg_right hlevel hnonneg
  have hcancel : (-r) * (-(r⁻¹)) = 1 := by
    rw [neg_mul_neg, mul_inv_cancel₀ hr.ne]
  calc
    StationaryRearrangement.profile s * (-(Real.exp (q s) * deriv q s)) =
        StationaryRearrangement.profile s * (-(r⁻¹) * Real.exp (q s)) := by rw [hq]; ring
    _ ≤ (ρ * (M s - s) * (-r)) * (-(r⁻¹) * Real.exp (q s)) := hscaled
    _ = ρ * Real.exp (q s) * (M s - s) * ((-r) * (-(r⁻¹))) := by ring
    _ = ρ * Real.exp (q s) * (M s - s) := by rw [hcancel, mul_one]

/-- The actual rearranged inequality holds almost everywhere on the
full rank interval. On critical ranks the one-dimensional null-image
argument gives zero curvature, with no null-preimage assumption. -/
theorem actual_rearranged_inequality {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    (hmass : (∫ z, Real.exp (v z) ∂torusMeasure) = 1)
    (hiso : SharpPhysicalSuperlevelIsoperimetry v) (hρ : 0 < ρ)
    (hne : ¬ ∃ c : ℝ, ∀ z, v z = c) :
    let q := StationaryDistribution.profile v
    let M := StationaryCumulative.cumulative (StationaryCumulative.extendProfile q)
    ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) 1),
      StationaryRearrangement.profile s * (-deriv (deriv M) s) ≤
        ρ * deriv M s * (M s - s) := by
  let q := StationaryDistribution.profile v
  let M := StationaryCumulative.cumulative (StationaryCumulative.extendProfile q)
  have hc := continuous_of_contDiff_lift (hv.of_le (by simp))
  have hac := actual_profile_ac hv hpde hmass hiso hρ
  rcases actual_cumulative_data hv hpde hmass hiso hρ hne with
    ⟨hM, hp, h0, h1, hident, hconc, hge, hA, hsecond⟩
  have hcrit := RearrangementRegularity.critical_rank_curvature_zero
    (profile_antitone hc) hac (volume_torusCriticalValues_eq_zero hv)
  rw [restrict_Ioo_eq_restrict_Ioc] at hcrit
  have hne1 : ∀ᵐ s : ℝ ∂volume.restrict (Ioc (0 : ℝ) 1), s ≠ 1 :=
    ae_restrict_of_ae (by simp [ae_iff, measure_singleton])
  filter_upwards [hsecond, hcrit, hne1, ae_restrict_mem measurableSet_Ioc]
    with s hd hz hs1 hs
  have hs' : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
  have hMp : deriv M s = Real.exp (q s) := (hident s ⟨hs.1.le, hs.2⟩).2
  by_cases hreg : q s ∈ torusCriticalValues v
  · have hzero : deriv (deriv M) s = 0 := hz hreg
    rw [hzero, neg_zero, mul_zero, hMp]
    exact mul_nonneg (mul_nonneg hρ.le (Real.exp_pos _).le)
      (sub_nonneg.mpr (hge s ⟨hs.1.le, hs.2⟩))
  · rw [hd.1, hMp]
    exact rearranged_inequality_regular hv hpde hmass hiso hρ hs' hreg

/-- Complete positive-coupling analytic contradiction from the one
explicit sharp physical isoperimetric input. In particular the endpoint
rho = 8*pi is included by the proved strict scalar profile comparison. -/
theorem positive_rho_contradiction {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    (hmass : (∫ z, Real.exp (v z) ∂torusMeasure) = 1)
    (hiso : SharpPhysicalSuperlevelIsoperimetry v) (hρ : 0 < ρ) (hρmax : ρ ≤ 8 * Real.pi)
    (hne : ¬ ∃ c : ℝ, ∀ z, v z = c) : False := by
  rcases actual_cumulative_data hv hpde hmass hiso hρ hne with
    ⟨hM, hp, h0, h1, hident, hconc, hge, hA, hsecond⟩
  exact StationaryRearrangement.rearranged_contradiction hM hp h0 h1 hA
    (hsecond.mono fun _ h ↦ h.2)
    (actual_rearranged_inequality hv hpde hmass hiso hρ hne) hρmax

/-- The zero-coupling branch has genuinely zero physical Dirichlet
energy, obtained by testing the actual periodic equation with the function
itself. No isoperimetric input is used. -/
theorem harmonic_energy_eq_zero {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x = 0) :
    (∫ z, ‖torusOrdinaryGradient v z‖ ^ 2 ∂torusMeasure) = 0 := by
  have he := stationary_weak_flux (ρ := 0) (T := id) hv
    (fun x ↦ by simpa only [zero_mul] using hpde x) contDiff_id
  have hid (r : ℝ) : deriv (id : ℝ → ℝ) r = 1 := (hasDerivAt_id r).deriv
  simpa only [hid, one_mul, zero_mul] using he

/-- Actual zero-energy rigidity on the original torus. Haar full support
upgrades the continuous squared gradient from AE zero to pointwise zero,
then the planar lift is constant by the proved mean-value theorem. -/
theorem harmonic_constant {v : Torus → ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x = 0) :
    ∃ c : ℝ, ∀ z, v z = c := by
  have hv1 : ContDiff ℝ 1 (fun x : PlanarSpace ↦ v (torusQuotient x)) := hv.of_le (by simp)
  have hc : Continuous (fun z ↦ ‖torusOrdinaryGradient v z‖ ^ 2) :=
    (continuous_norm_gradient hv1).pow 2
  have hi := continuous_integrable hc
  have hzero : (fun z ↦ ‖torusOrdinaryGradient v z‖ ^ 2) =ᵐ[torusMeasure]
      (fun _ ↦ (0 : ℝ)) :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun z ↦ sq_nonneg _) hi).mp
      (harmonic_energy_eq_zero hv hpde)
  have hfun : (fun z ↦ ‖torusOrdinaryGradient v z‖ ^ 2) = (fun _ : Torus ↦ (0 : ℝ)) :=
    Measure.eq_of_ae_eq hzero hc continuous_const
  have hgrad (z : Torus) : torusOrdinaryGradient v z = 0 := by
    apply norm_eq_zero.mp
    have hh := congrFun hfun z
    nlinarith only [hh]
  have hd (x : PlanarSpace) : fderiv ℝ (fun y : PlanarSpace ↦ v (torusQuotient y)) x = 0 := by
    apply norm_eq_zero.mp
    rw [← norm_torusOrdinaryGradient_lift, hgrad, norm_zero]
  refine ⟨v (torusQuotient 0), ?_⟩
  intro z
  obtain ⟨x, rfl⟩ := torusQuotient_surjective z
  exact is_const_of_fderiv_eq_zero (hv.differentiable (by simp)) hd x 0

/-- The complete conditional stationary reduction, including rho zero
and rho = 8*pi. The only unresolved geometric premise is the explicitly
named sharp physical superlevel isoperimetry proposition. -/
theorem constant_of_sharp_isoperimetry {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    (hmass : (∫ z, Real.exp (v z) ∂torusMeasure) = 1)
    (hiso : SharpPhysicalSuperlevelIsoperimetry v)
    (hρ : 0 ≤ ρ) (hρmax : ρ ≤ 8 * Real.pi) :
    ∃ c : ℝ, ∀ z, v z = c := by
  classical
  by_cases hz : ρ = 0
  · apply harmonic_constant hv
    intro x
    simpa only [hz, zero_mul] using hpde x
  · by_contra hne
    exact positive_rho_contradiction hv hpde hmass hiso
      (lt_of_le_of_ne hρ (Ne.symm hz)) hρmax hne

/-- Normalization fixes the resulting constant to zero. This remains a
conditional geometric reduction, not an unconditional stationary theorem. -/
theorem eq_zero_of_sharp_isoperimetry {v : Torus → ℝ} {ρ : ℝ}
    (hv : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ v (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      -Laplacian.laplacian (fun y : PlanarSpace ↦ v (torusQuotient y)) x =
        ρ * (Real.exp (v (torusQuotient x)) - 1))
    (hmass : (∫ z, Real.exp (v z) ∂torusMeasure) = 1)
    (hiso : SharpPhysicalSuperlevelIsoperimetry v)
    (hρ : 0 ≤ ρ) (hρmax : ρ ≤ 8 * Real.pi) : ∀ z, v z = 0 := by
  obtain ⟨c, hc⟩ := constant_of_sharp_isoperimetry hv hpde hmass hiso hρ hρmax
  have he : Real.exp c = 1 := by
    have hh := hmass
    simp_rw [hc] at hh
    simpa only [integral_const, probReal_univ, one_smul] using hh
  have hc0 : c = 0 := by
    simpa only [Real.log_exp, Real.log_one] using congrArg Real.log he
  intro z
  rw [hc z, hc0]

end PeriodicAttractiveLogGas.StationaryIsoperimetricReduction
