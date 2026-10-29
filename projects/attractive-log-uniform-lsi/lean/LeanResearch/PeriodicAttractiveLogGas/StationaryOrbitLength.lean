import LeanResearch.PeriodicAttractiveLogGas.StationaryClosedCurves

/-! A uniform lower length bound for actual regular-level orbits. This will
make the family of distinct orbits finite and identify its circles with
the actual connected components in the source isoperimetric proof. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal NNReal
namespace PeriodicAttractiveLogGas.StationaryOrbitLength
open StationaryLevelCircles StationaryClosedCurves StationaryCurveLength
  StationaryCoarea StationarySard StationaryLevelContinuity StationaryLevelGeometry

/-- A uniform short-time return gap for the original tangent equation.
The estimate is obtained from the first-order displacement and the global
Lipschitz bounds already proved for the actual periodic vector field. -/
theorem uniform_return_gap {v : Torus → ℝ} {K L : ℝ≥0}
    (hK : LipschitzWith K (tangentField v)) (hL : ∀ x, ‖tangentField v x‖ ≤ L)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : ℝ → PlanarSpace,
      (∀ s, HasDerivAt γ (tangentField v (γ s)) s) →
      ε ≤ ‖tangentField v (γ 0)‖ →
      ∀ s : ℝ, 0 < s → s < δ → torusQuotient (γ s) ≠ torusQuotient (γ 0) := by
  let δ : ℝ := min (1 / (16 * ((L : ℝ) + 1)))
    (ε / (4 * ((K : ℝ) + 1) * ((L : ℝ) + 1)))
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδL := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * ((L : ℝ) + 1))).mp
    (min_le_left (1 / (16 * ((L : ℝ) + 1))) (ε / (4 * ((K : ℝ) + 1) * ((L : ℝ) + 1))))
  have hδK := (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * ((K : ℝ) + 1) * ((L : ℝ) + 1))).mp
    (min_le_right (1 / (16 * ((L : ℝ) + 1))) (ε / (4 * ((K : ℝ) + 1) * ((L : ℝ) + 1))))
  have hsmallL : (L : ℝ) * δ < 1 / 8 := by
    change δ * (16 * ((L : ℝ) + 1)) ≤ 1 at hδL
    nlinarith only [hδL, hδ]
  have hsmallK : (K : ℝ) * L * δ ≤ ε / 2 := by
    change δ * (4 * ((K : ℝ) + 1) * ((L : ℝ) + 1)) ≤ ε at hδK
    have hkl : (K : ℝ) * L ≤ ((K : ℝ) + 1) * ((L : ℝ) + 1) := by
      nlinarith only [K.coe_nonneg, L.coe_nonneg]
    have hh := mul_le_mul_of_nonneg_right hkl hδ.le
    nlinarith only [hδK, hh, hε]
  refine ⟨δ, hδ, fun γ hγ hspeed s hs hsδ he => ?_⟩
  have hg : LipschitzWith L γ := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun r => (hγ r).differentiableAt)
    intro r
    rw [(hγ r).deriv]
    exact_mod_cast hL (γ r)
  have hd (r : ℝ) (hr : r ∈ Icc 0 s) : ‖γ r - γ 0‖ ≤ (L : ℝ) * s := by
    have hh := hg.dist_le_mul r 0
    rw [dist_eq_norm, Real.dist_eq, sub_zero, abs_of_nonneg hr.1] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hr.2 L.coe_nonneg)
  have hbs : γ s ∈ Metric.ball (γ 0) (1 / 8 : ℝ) := by
    rw [Metric.mem_ball, dist_eq_norm]
    exact ((hd s ⟨hs.le, le_rfl⟩).trans
      (mul_le_mul_of_nonneg_left hsδ.le L.coe_nonneg)).trans_lt hsmallL
  have heq : γ s = γ 0 := by
    have hh : (⟨γ s, hbs⟩ : Metric.ball (γ 0) (1 / 8 : ℝ)) =
        ⟨γ 0, Metric.mem_ball_self (by norm_num)⟩ :=
      (physicalQuotient_isometry_ball (γ 0)).injective (congrArg physicalEquiv he)
    exact congrArg Subtype.val hh
  let F : ℝ → PlanarSpace := fun r => γ r - r • tangentField v (γ 0)
  have hF (r : ℝ) : HasDerivAt F (tangentField v (γ r) - tangentField v (γ 0)) r := by
    simpa only [F, id_eq, one_smul, Pi.sub_apply] using!
      (hγ r).sub ((hasDerivAt_id r).smul_const (tangentField v (γ 0)))
  have hbound (r : ℝ) (hr : r ∈ Icc 0 s) :
      ‖tangentField v (γ r) - tangentField v (γ 0)‖ ≤ ε / 2 := by
    have hh := hK.dist_le_mul (γ r) (γ 0)
    rw [dist_eq_norm, dist_eq_norm] at hh
    calc
      _ ≤ (K : ℝ) * ‖γ r - γ 0‖ := hh
      _ ≤ (K : ℝ) * ((L : ℝ) * s) := mul_le_mul_of_nonneg_left (hd r hr) K.coe_nonneg
      _ ≤ (K : ℝ) * ((L : ℝ) * δ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsδ.le L.coe_nonneg) K.coe_nonneg
      _ ≤ ε / 2 := by simpa only [mul_assoc] using hsmallK
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (C := ε / 2)
    (fun r _ => (hF r).hasDerivWithinAt) hbound (convex_Icc (0 : ℝ) s)
    (show (0 : ℝ) ∈ Icc 0 s from ⟨le_rfl, hs.le⟩) (show s ∈ Icc 0 s from ⟨hs.le, le_rfl⟩)
  have hdiff : F s - F 0 = -(s • tangentField v (γ 0)) := by
    dsimp only [F]
    rw [heq, zero_smul]
    abel
  rw [hdiff, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos hs] at hm
  simp only [sub_zero, Real.norm_eq_abs, abs_of_pos hs] at hm
  nlinarith only [hm, hspeed, hs, hε]


/-- The same positive speed lower bound works at every point of the
specified regular level. -/
theorem exists_level_speed_lower {v : Torus → ℝ}
    (hv : ContDiff ℝ 1 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : PlanarSpace, v (torusQuotient x) = t →
      ε ≤ ‖tangentField v x‖ := by
  obtain ⟨ε, hε, hlower⟩ := exists_regular_band_gradient_lower hv ht
  refine ⟨ε, hε, fun x hx => ?_⟩
  rw [norm_tangentField]
  exact hlower _ (by rw [hx, sub_self, abs_zero]; exact hε.le)

/-- The circle parametrization is available for any actual global
trajectory on this regular level, not only for one chosen by existence. -/
theorem regular_trajectory_circle {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) {γ : ℝ → PlanarSpace}
    (hγ : ∀ s, HasDerivAt γ (tangentField v (γ s)) s)
    (hlevel : ∀ s, v (torusQuotient (γ s)) = t) :
    ∃ P : ℝ, 0 < P ∧ Function.Periodic (fun s => torusQuotient (γ s)) P ∧
      InjOn (fun s => torusQuotient (γ s)) (Ico 0 P) ∧
      ∃ c : C(AddCircle P, Torus), Topology.IsClosedEmbedding c ∧
        (∀ s : ℝ, c (s : AddCircle P) = torusQuotient (γ s)) ∧
        Set.range c = Set.range (fun s => torusQuotient (γ s)) := by
  obtain ⟨ε, hε, hlower⟩ := exists_level_speed_lower (hv.of_le (by norm_num)) ht
  have hspeed (s : ℝ) := hlower (γ s) (hlevel s)
  have hn : tangentField v (γ 0) ≠ 0 := by
    intro hz
    have hh := hspeed 0
    rw [hz, norm_zero] at hh
    linarith
  obtain ⟨P, hP, hp, _, hi⟩ := exists_least_period_and_injective hv hγ hn
    (exists_positive_period_of_regular_trajectory hv ht hγ hlevel hε hspeed)
  have hc := isOpenQuotientMap_torusQuotient.continuous.comp
    (continuous_iff_continuousAt.mpr fun s => (hγ s).continuousAt)
  exact ⟨P, hP, hp, hi, circle_embedding_of_simple_periodic hP hc hp hi⟩

/-- Each distinct actual orbit has a uniformly positive physical length.
A fixed initial arc of length in time δ/2 is injective for every orbit,
and its speed is bounded below by the same ε. -/
theorem exists_uniform_orbit_length_lower {v : Torus → ℝ}
    (hv : ContDiff ℝ 2 (fun x : PlanarSpace => v (torusQuotient x))) {t : ℝ}
    (ht : t ∉ torusCriticalValues v) :
    ∃ c : ℝ, 0 < c ∧ ∀ γ : ℝ → PlanarSpace,
      (∀ s, HasDerivAt γ (tangentField v (γ s)) s) →
      (∀ s, v (torusQuotient (γ s)) = t) →
      ENNReal.ofReal c ≤ physicalCurveMeasure (Set.range (fun s => torusQuotient (γ s))) := by
  obtain ⟨ε, hε, hlower⟩ := exists_level_speed_lower (hv.of_le (by norm_num)) ht
  obtain ⟨K, hK⟩ := exists_lipschitz_tangentField hv
  obtain ⟨L, hL⟩ := exists_tangentField_bound (hv.of_le (by norm_num))
  obtain ⟨δ, hδ, hgap⟩ := uniform_return_gap hK hL hε
  refine ⟨ε * (δ / 2), by positivity, fun γ hγ hlevel => ?_⟩
  have hspeed (s : ℝ) := hlower (γ s) (hlevel s)
  obtain ⟨P, hP, hp, hi, _, _, _, _⟩ := regular_trajectory_circle hv ht hγ hlevel
  have hδP : δ ≤ P := by
    by_contra hlt
    exact hgap γ hγ (hspeed 0) P hP (lt_of_not_ge hlt) hp.eq
  have hiarc : InjOn (fun s => torusQuotient (γ s)) (Icc 0 (δ / 2)) := by
    apply hi.mono
    intro s hs
    exact ⟨hs.1, by linarith only [hs.2, hδP, hδ]⟩
  have hlen := length_Icc (a := 0) (b := δ / 2)
    (fun s _ => (hγ s).hasDerivWithinAt)
    (fun s _ => by
      intro hz
      have hh := hspeed s
      rw [hz, norm_zero] at hh
      linarith) hiarc
  calc
    _ = ∫⁻ s in Icc (0 : ℝ) (δ / 2), ENNReal.ofReal ε := by
      rw [ENNReal.ofReal_mul hε.le]
      simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ,
        univ_inter, Real.volume_Icc, sub_zero]
    _ ≤ ∫⁻ s in Icc (0 : ℝ) (δ / 2), ENNReal.ofReal ‖tangentField v (γ s)‖ :=
      lintegral_mono fun s => ENNReal.ofReal_le_ofReal (hspeed s)
    _ = physicalCurveMeasure ((fun s => torusQuotient (γ s)) '' Icc (0 : ℝ) (δ / 2)) := hlen.symm
    _ ≤ _ := measure_mono (by rintro z ⟨s, _, rfl⟩; exact ⟨s, rfl⟩)

end PeriodicAttractiveLogGas.StationaryOrbitLength
