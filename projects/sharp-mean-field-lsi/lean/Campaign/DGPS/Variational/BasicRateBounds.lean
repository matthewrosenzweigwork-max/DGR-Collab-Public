import DGPS.Foundations.AbsoluteDensity
import DGPS.Foundations.PeriodicSmoothing
import DGPS.Foundations.RateArithmetic
import DGPS.Foundations.SmoothingLp
import DGPS.Model.ScalarRate
import DGPS.Model.SpeciesRate
import DGPS.Particle.ProductRecoveryLimits
import DGPS.Variational.SpeciesInclusion

/-!
# Rate finiteness, single-species inclusion and the zero case (LIP024)

Under the hypotheses of T01 (`LipschitzData A`, a weak drift provider `b`, and `0 < d`):

* `0 ≤ r_ms ≤ r_* < ∞`: the inclusion `r_ms ≤ r_*` is `speciesRate_le_scalarRate`
  (a one-species family is a competitor), and `r_* < ∞` comes from exhibiting one absolute density
  with positive gap and finite dissipation;
* the positive-gap density is a normalised mollified indicator of a thin cylinder, whose entropy
  is large because its `L¹` norm is small (`entropy_lower_of_integral_sqrt_le`), while all the
  potential contributions are bounded, so the free energy exceeds `F_*`;
* finite dissipation of every finite family is part of LIP023;
* if `r_* = 0` then `r_ms = 0`, and both particle rate sequences tend to `0` (`0 ≤ liminf` and
  `limsup ≤ r_ms ≤ r_* = 0`), also in real-valued form.

The hypothesis `0 < d` is needed: on the point torus `d = 0` there is no positive-gap density and
`r_* = ⊤`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}


theorem sq_mul_log_sq_ge (u c : ℝ) (hu : 0 ≤ u) (hc : 0 < c) :
    -2 * c * u + 2 * (1 + Real.log c) * u ^ 2 ≤ u ^ 2 * Real.log (u ^ 2) := by
  rcases hu.eq_or_lt with rfl | hpos
  · simp
  · have h := Real.log_le_sub_one_of_pos (div_pos hc hpos)
    rw [Real.log_div hc.ne' hpos.ne'] at h
    have h2 : Real.log u ≥ Real.log c + 1 - c / u := by linarith
    rw [Real.log_pow]
    have h3 : u ^ 2 * (c / u) = u * c := by field_simp
    have h4 : u ^ 2 * Real.log u ≥ u ^ 2 * (Real.log c + 1 - c / u) :=
      mul_le_mul_of_nonneg_left h2 (sq_nonneg u)
    push_cast
    nlinarith [h3, h4]


theorem entropy_lower_of_integral_sqrt_le (ρ : AbsoluteDensity d) {m : ℝ} (hm : 0 < m)
    (hint : ∫ x, ρ.sqrt x ∂haar d ≤ m) :
    -2 * Real.log m ≤ ∫ x, ρ.density x * Real.log (ρ.density x) ∂haar d := by
  have hu1 : Integrable ρ.sqrt (haar d) := ρ.memLp_sqrt.integrable (by norm_num)
  have hu2 : Integrable (fun x => ρ.sqrt x ^ 2) (haar d) := ρ.integrable_density
  have hlog := (absoluteDensity_entropy_finite ρ).1
  set c : ℝ := 1 / m with hc
  have hcpos : 0 < c := by positivity
  have hle : ∫ x, (-2 * c * ρ.sqrt x + 2 * (1 + Real.log c) * ρ.sqrt x ^ 2) ∂haar d ≤
      ∫ x, ρ.density x * Real.log (ρ.density x) ∂haar d := by
    refine integral_mono_ae ((hu1.const_mul _).add (hu2.const_mul _)) hlog ?_
    filter_upwards [ρ.sqrt_nonneg] with x hx
    exact sq_mul_log_sq_ge _ c hx hcpos
  have heq : ∫ x, (-2 * c * ρ.sqrt x + 2 * (1 + Real.log c) * ρ.sqrt x ^ 2) ∂haar d =
      -2 * c * ∫ x, ρ.sqrt x ∂haar d + 2 * (1 + Real.log c) * 1 := by
    rw [integral_add (hu1.const_mul _) (hu2.const_mul _), integral_const_mul,
      integral_const_mul, ρ.mass_one]
  have h1 : -2 * c * m ≤ -2 * c * ∫ x, ρ.sqrt x ∂haar d := by
    have : 0 ≤ 2 * c := by positivity
    nlinarith
  have h2 : c * m = 1 := by rw [hc]; field_simp
  have h3 : Real.log c = - Real.log m := by rw [hc, one_div, Real.log_inv]
  rw [heq] at hle
  nlinarith [h1, h2, h3]

theorem scalarGap_pos_of_entropy (A : InteractionData d) (ρ : AbsoluteDensity d) {C : ℝ}
    (hV : ∀ x, |A.V x| ≤ C) {C' : ℝ} (hW : ∀ x y, |A.W x y| ≤ C')
    (hH : 2 * C + C' < ∫ x, ρ.density x * Real.log (ρ.density x) ∂haar d) :
    0 < scalarGap A ρ := by
  rw [scalarGap_pos_iff]
  have hfin := (absoluteDensity_entropy_finite ρ).2.2
  have hdens : densityFreeEnergy A ρ =
      (relativeEntropy (densityMeasure ρ : Measure (Torus d)) (haar d)).toReal +
        potentialEnergy A (densityMeasure ρ) +
        (1 / 2 : ℝ) * interactionEnergy A (densityMeasure ρ) := by
    have h1 := coe_densityFreeEnergy A ρ
    rw [freeEnergy_eq_real A _ hfin.1] at h1
    exact EReal.coe_eq_coe_iff.mp h1
  have hmin := freeEnergyMinimumReal_le A (haarProbability d) (by
    show relativeEntropy (haar d) (haar d) ≠ ⊤
    rw [relativeEntropy_self]; exact ENNReal.zero_ne_top)
  have hbV : ∀ ν : ProbabilityMeasure (Torus d), |potentialEnergy A ν| ≤ C := fun ν => by
    unfold potentialEnergy
    have := norm_integral_le_of_norm_le_const (μ := (ν : Measure (Torus d))) (f := A.V)
      (C := C) (Filter.Eventually.of_forall fun x => by simpa using hV x)
    simpa using this
  have hbW : ∀ ν : ProbabilityMeasure (Torus d), |interactionEnergy A ν| ≤ C' := fun ν => by
    unfold interactionEnergy
    have := norm_integral_le_of_norm_le_const
      (μ := ((ν : Measure (Torus d)).prod (ν : Measure (Torus d)))) (f := fun p => A.W p.1 p.2)
      (C := C') (Filter.Eventually.of_forall fun p => by simpa using hW p.1 p.2)
    simpa using this
  rw [hdens, hfin.2]
  have e1 := abs_le.mp (hbV (densityMeasure ρ))
  have e2 := abs_le.mp (hbW (densityMeasure ρ))
  have e3 := abs_le.mp (hbV (haarProbability d))
  have e4 := abs_le.mp (hbW (haarProbability d))
  have hrel : (relativeEntropy (haarProbability d : Measure (Torus d)) (haar d)).toReal = 0 := by
    show (relativeEntropy (haar d) (haar d)).toReal = 0
    rw [relativeEntropy_self]; rfl
  rw [hrel] at hmin
  have hC : 0 ≤ C := (abs_nonneg _).trans (hV (0 : Torus d))
  have hC' : 0 ≤ C' := (abs_nonneg _).trans (hW 0 0)
  linarith [e1.1, e1.2, e2.1, e2.2, e3.1, e3.2, e4.1, e4.2]



theorem exists_small_cylinder (hd : 0 < d) {s : ℝ} (hs : 0 < s) :
    ∃ S : Set (Torus d), MeasurableSet S ∧ 0 < (haar d S).toReal ∧ (haar d S).toReal ≤ s := by
  classical
  set i0 : Fin d := ⟨0, hd⟩
  set ε : ℝ := min s 1 / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : 2 * ε ≤ 1 := by rw [hε]; linarith [min_le_right s 1]
  have hεs : 2 * ε ≤ s := by rw [hε]; linarith [min_le_left s 1]
  let t : Fin d → Set (AddCircle (1 : ℝ)) := fun i => if i = i0 then Metric.closedBall 0 ε else Set.univ
  have ht : ∀ i, MeasurableSet (t i) := fun i => by
    by_cases h : i = i0
    · simp only [t, h, ite_true]; exact Metric.isClosed_closedBall.measurableSet
    · simp [t, h]
  refine ⟨Set.univ.pi t, MeasurableSet.univ_pi ht, ?_⟩
  have hv : haar d (Set.univ.pi t) = ENNReal.ofReal (2 * ε) := by
    show (volume : Measure (Fin d → AddCircle (1 : ℝ))) (Set.univ.pi t) = _
    rw [volume_pi, Measure.pi_pi]
    rw [Finset.prod_eq_single i0]
    · simp only [t, ite_true]
      rw [AddCircle.volume_closedBall, min_eq_right hε1]
    · intro i _ hi
      simp [t, hi]
    · simp
  rw [hv, ENNReal.toReal_ofReal (by positivity)]
  exact ⟨by positivity, hεs⟩


theorem sq_toReal_eLpNorm_two_torus {f : Torus d → ℝ} (hf : MemLp f 2 (haar d)) :
    (eLpNorm f 2 (haar d)).toReal ^ 2 = ∫ x, f x ^ 2 ∂haar d := by
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [hf.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num), h2]
  have : ∀ x, ‖f x‖ ^ (2 : ℝ) = f x ^ 2 := fun x => by
    rw [Real.rpow_two, Real.norm_eq_abs, sq_abs]
  simp_rw [this]
  have hnn : 0 ≤ ∫ x, f x ^ 2 ∂haar d := integral_nonneg fun x => sq_nonneg _
  rw [ENNReal.toReal_ofReal (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul hnn]
  norm_num

theorem integral_norm_eq_toReal_eLpNorm_one {f : Torus d → ℝ} (hf : MemLp f 1 (haar d)) :
    ∫ x, ‖f x‖ ∂haar d = (eLpNorm f 1 (haar d)).toReal := by
  have h := integral_norm_eq_lintegral_enorm (μ := haar d) hf.aestronglyMeasurable
  rw [h, eLpNorm_one_eq_lintegral_enorm]
  exact hf.aestronglyMeasurable


theorem exists_density_small_integral (hd : 0 < d) {m : ℝ} (hm : 0 < m) :
    ∃ ρ : AbsoluteDensity d, ∫ x, ρ.sqrt x ∂haar d ≤ m := by
  obtain ⟨S, hSm, hs0, hsm⟩ := exists_small_cylinder (d := d) hd (s := m ^ 2 / 4) (by positivity)
  set s : ℝ := (haar d S).toReal with hs
  let v : Torus d → ℝ := S.indicator fun _ => (1 : ℝ)
  have hvnn : ∀ x, 0 ≤ v x := fun x => by
    simp only [v, Set.indicator]; split_ifs <;> norm_num
  have hSfin : haar d S ≠ ⊤ := measure_ne_top _ _
  have hv2 : MemLp v 2 (haar d) := memLp_indicator_const 2 hSm.nullMeasurableSet 1 (Or.inr hSfin)
  have hv1 : MemLp v 1 (haar d) := memLp_indicator_const 1 hSm.nullMeasurableSet 1 (Or.inr hSfin)
  have hvint : ∫ x, v x ∂haar d = s := by
    simp only [v]
    rw [integral_indicator_const _ hSm]
    simp [hs, Measure.real]
  have hvsq : ∫ x, v x ^ 2 ∂haar d = s := by
    have : (fun x => v x ^ 2) = v := by
      funext x; simp only [v, Set.indicator]; split_ifs <;> norm_num
    rw [this, hvint]
  set a : ℝ := (eLpNorm v 2 (haar d)).toReal with ha
  have ha2 : a ^ 2 = s := by rw [ha, sq_toReal_eLpNorm_two_torus hv2, hvsq]
  have ha0 : 0 < a := by
    have : 0 ≤ a := ENNReal.toReal_nonneg
    rcases this.eq_or_lt with h | h
    · rw [← h] at ha2; nlinarith
    · exact h
  have hev := (tendsto_eLpNorm_moll_sub (p := 2) (by norm_num) (by norm_num) hv2).eventually_lt_const
    (u := ENNReal.ofReal (a / 2)) (by simpa using ha0)
  obtain ⟨n, hn⟩ := hev.exists
  set u₀ : Torus d → ℝ := SharpLSI.moll n v with hu₀
  have hu₀2 : MemLp u₀ 2 (haar d) := memLp_moll n (by norm_num) (by norm_num) hv2
  have hu₀1 : MemLp u₀ 1 (haar d) := memLp_moll n (by norm_num) (by norm_num) hv1
  have hu₀nn : ∀ x, 0 ≤ u₀ x := fun x => by
    rw [hu₀, moll_apply_eq]
    exact integral_nonneg fun y => mul_nonneg (phiSeq_nonneg _ _) (hvnn _)
  have hu₀sm : IsSmoothPeriodic u₀ := isSmoothPeriodic_moll n (hv1.integrable le_rfl)
  set t : ℝ := (eLpNorm u₀ 2 (haar d)).toReal with ht
  have hdiff : MemLp (fun y => u₀ y - v y) 2 (haar d) := hu₀2.sub hv2
  -- lower bound on `t`
  have hta : a / 2 ≤ t := by
    have h1 : eLpNorm v 2 (haar d) ≤ eLpNorm u₀ 2 (haar d) +
        eLpNorm (fun y => u₀ y - v y) 2 (haar d) := by
      have := eLpNorm_sub_le (μ := haar d) (p := 2) (f := u₀) (g := fun y => u₀ y - v y)
        (by norm_num)
      have e : (u₀ - fun y => u₀ y - v y) = v := by funext y; simp
      rwa [e] at this
    have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hu₀2.eLpNorm_ne_top, hdiff.eLpNorm_ne_top⟩) h1
    rw [ENNReal.toReal_add hu₀2.eLpNorm_ne_top hdiff.eLpNorm_ne_top] at h2
    have h3 : (eLpNorm (fun y => u₀ y - v y) 2 (haar d)).toReal ≤ a / 2 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hn.le
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    linarith
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) hta
  have ht2 : t ^ 2 = ∫ x, u₀ x ^ 2 ∂haar d := sq_toReal_eLpNorm_two_torus hu₀2
  -- L¹ bound
  have hl1 : ∫ x, u₀ x ∂haar d ≤ s := by
    have h1 : eLpNorm u₀ 1 (haar d) ≤ eLpNorm v 1 (haar d) :=
      eLpNorm_moll_le n (le_refl _) (by norm_num) hv1
    have h2 := ENNReal.toReal_mono hv1.eLpNorm_ne_top h1
    rw [← integral_norm_eq_toReal_eLpNorm_one hu₀1, ← integral_norm_eq_toReal_eLpNorm_one hv1] at h2
    have e1 : ∫ x, ‖u₀ x‖ ∂haar d = ∫ x, u₀ x ∂haar d :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp [Real.norm_eq_abs, abs_of_nonneg (hu₀nn x)])
    have e2 : ∫ x, ‖v x‖ ∂haar d = s := by
      rw [← hvint]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
        simp [Real.norm_eq_abs, abs_of_nonneg (hvnn x)])
    linarith
  refine ⟨⟨fun x => u₀ x / t, ?_, ?_, ?_⟩, ?_⟩
  · exact ⟨_, IsSmoothPeriodic.isWeakGradient (φ := fun x => u₀ x / t) (hu₀sm.div_const t)⟩
  · exact Filter.Eventually.of_forall fun x => div_nonneg (hu₀nn x) ht0.le
  · simp_rw [div_pow]
    rw [integral_div, ← ht2]
    field_simp
  · show ∫ x, u₀ x / t ∂haar d ≤ m
    rw [integral_div, div_le_iff₀ ht0]
    have hm2 : a ≤ m / 2 := by nlinarith
    nlinarith


/-- There is an absolute-admissible density with positive gap (for `d > 0`). -/
theorem exists_scalarGap_pos (hd : 0 < d) (A : InteractionData d) :
    ∃ ρ : AbsoluteDensity d, 0 < scalarGap A ρ := by
  obtain ⟨C, hC⟩ := InteractionData.V_bounded A
  obtain ⟨C', hC'⟩ := InteractionData.W_bounded A
  set K : ℝ := 2 * C + C' + 1 with hK
  have hm : 0 < Real.exp (-K / 2) := Real.exp_pos _
  obtain ⟨ρ, hρ⟩ := exists_density_small_integral (d := d) hd hm
  refine ⟨ρ, scalarGap_pos_of_entropy A ρ hC hC' ?_⟩
  have := entropy_lower_of_integral_sqrt_le ρ hm hρ
  rw [Real.log_exp] at this
  linarith

/-- The scalar rate is finite: some positive-gap density has finite dissipation. -/
theorem scalarRate_ne_top (hd : 0 < d) (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) : scalarRate A b ≠ ⊤ := by
  obtain ⟨ρ, hρ⟩ := exists_scalarGap_pos hd A
  obtain ⟨t, σ, f, -, -, -, -, -, -, hD, -⟩ :=
    (full_domain_product_recovery_and_particle_upper_limits A hLip b).1 (SpeciesFamily.single ρ)
  rw [speciesDissipation_single] at hD
  have hq : scalarQuotient A b ρ < ⊤ :=
    (scalarQuotient_lt_top_iff A b ρ hρ).mpr (lt_top_iff_ne_top.mpr hD)
  exact ne_top_of_le_ne_top hq.ne (scalarRate_le_quotient A b ρ hρ)

/-- LIP024: `0 ≤ r_ms ≤ r_* < ∞` (also in real-valued form), and if `r_* = 0` then `r_ms = 0` and
both particle rate sequences tend to `0`, in `ℝ≥0∞` and in `ℝ`. -/
theorem rate_finiteness_single_species_inclusion_and_zero_case (hd : 0 < d)
    (A : InteractionData d) (hLip : LipschitzData A) (b : AbsoluteDrift A) :
    speciesRate A b ≤ scalarRate A b ∧ scalarRate A b ≠ ⊤ ∧ speciesRate A b ≠ ⊤ ∧
      0 ≤ (speciesRate A b).toReal ∧ (speciesRate A b).toReal ≤ (scalarRate A b).toReal ∧
      (scalarRate A b = 0 →
        speciesRate A b = 0 ∧
          Tendsto (fun N : ℕ+ => particleRateAll A N) atTop (𝓝 0) ∧
          Tendsto (fun N : ℕ+ => particleRateSym A N) atTop (𝓝 0) ∧
          Tendsto (fun N : ℕ+ => (particleRateAll A N).toReal) atTop (𝓝 0) ∧
          Tendsto (fun N : ℕ+ => (particleRateSym A N).toReal) atTop (𝓝 0)) := by
  have hincl := speciesRate_le_scalarRate A b
  have hst := scalarRate_ne_top hd A hLip b
  have hms : speciesRate A b ≠ ⊤ := ne_top_of_le_ne_top hst hincl
  refine ⟨hincl, hst, hms, ENNReal.toReal_nonneg, ENNReal.toReal_mono hst hincl, ?_⟩
  intro h0
  obtain ⟨-, hall, hsym⟩ := full_domain_product_recovery_and_particle_upper_limits A hLip b
  have hms0 : speciesRate A b = 0 := le_antisymm (h0 ▸ hincl) zero_le
  have hT1 : Tendsto (fun N : ℕ+ => particleRateAll A N) atTop (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le (by simp) (by rw [← hms0]; exact hall)
  have hT2 : Tendsto (fun N : ℕ+ => particleRateSym A N) atTop (𝓝 0) :=
    tendsto_of_le_liminf_of_limsup_le (by simp) (by rw [← h0]; exact hsym)
  refine ⟨hms0, hT1, hT2, ?_, ?_⟩
  · have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT1
    rwa [ENNReal.toReal_zero] at h
  · have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hT2
    rwa [ENNReal.toReal_zero] at h

end DGPS.Lipschitz
