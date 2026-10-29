import DGPS.Examples.HarmonicNonattainment
import DGPS.Examples.HarmonicFamilyDeficit
import DGPS.Examples.HarmonicDeficitQuantitative
import DGPS.Analysis.CircleMoments
import DGPS.Variational.SpeciesInclusion

/-!
# EX079: subcritical sharp rate by first-harmonic trials

For `0 ≤ k < 1` put `r = 4π² (1 - k)`. Both the scalar rate `r_*` and the species rate `r_ms`
equal `r` for every drift, and the first-harmonic densities `ρ_t = 1 + t cos (2π x)`,
`0 < |t| < 1`, have positive gap and scalar quotient tending to `r` as `t → 0`.

Route: `r ≤ r_ms` from the EX078 quantitative deficit; `r_ms ≤ r_*` from the one-species
inclusion; `r_* ≤ r` from the trial quotients. For a trial, the exact deficit identity (EX077)
together with the moment identities of `ρ_t` and the circle Taylor bounds gives
`|D/(2G) - r| ≤ 6 · 4π² t² / (1 - k)`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Examples

open DGPS.Examples.AttractiveXY DGPS.Examples.AttractiveXYCritical DGPS.Models
open DGPS.Analysis.CircleMoments

/-! ### Trigonometric moments on the Haar circle -/

theorem integral_sin_two_pi_ex079 :
    ∫ s in (0:ℝ)..1, Real.sin (2 * Real.pi * s) = 0 := by
  have h := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := 1)
    (fun x => Real.sin x) (c := 2 * Real.pi) (by positivity)
  rw [h, integral_sin]
  simp

theorem trial_cos_ex079 (t : ℝ) :
    ∫ s in (0:ℝ)..1, (1 + t * Real.cos (2 * Real.pi * s)) * Real.cos (2 * Real.pi * s)
      = t / 2 := by
  have hc : Continuous fun s : ℝ => Real.cos (2 * Real.pi * s) := by fun_prop
  have hc2 : Continuous fun s : ℝ => t * Real.cos (2 * Real.pi * s) ^ 2 := by fun_prop
  have e : (fun s : ℝ => (1 + t * Real.cos (2 * Real.pi * s)) * Real.cos (2 * Real.pi * s))
      = fun s => Real.cos (2 * Real.pi * s) + t * Real.cos (2 * Real.pi * s) ^ 2 := by
    funext s; ring
  rw [e, intervalIntegral.integral_add (hc.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_cos_two_pi, integral_cos_sq_two_pi]
  ring

theorem trial_sin_ex079 (t : ℝ) :
    ∫ s in (0:ℝ)..1, (1 + t * Real.cos (2 * Real.pi * s)) * Real.sin (2 * Real.pi * s) = 0 := by
  have hs : Continuous fun s : ℝ => Real.sin (2 * Real.pi * s) := by fun_prop
  have hsc : Continuous fun s : ℝ => Real.sin (2 * Real.pi * s) * Real.cos (2 * Real.pi * s) := by
    fun_prop
  have hodd : ∫ s in (0:ℝ)..1, Real.sin (2 * Real.pi * s) * Real.cos (2 * Real.pi * s) = 0 := by
    have h := integral_sin_pow_mul_cos_odd_two_pi 1 0
    simpa only [pow_one, mul_zero, zero_add] using h
  have e : (fun s : ℝ => (1 + t * Real.cos (2 * Real.pi * s)) * Real.sin (2 * Real.pi * s))
      = fun s => Real.sin (2 * Real.pi * s)
          + t * (Real.sin (2 * Real.pi * s) * Real.cos (2 * Real.pi * s)) := by
    funext s; ring
  rw [e, intervalIntegral.integral_add (hs.intervalIntegrable _ _) ((hsc.const_mul t).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_sin_two_pi_ex079, hodd]
  ring

theorem trial_sin_sq_ex079 (t : ℝ) :
    ∫ s in (0:ℝ)..1, (1 + t * Real.cos (2 * Real.pi * s)) *
        (Real.sin (2 * Real.pi * s) * Real.sin (2 * Real.pi * s)) = 1 / 2 := by
  have hs2 : Continuous fun s : ℝ => Real.sin (2 * Real.pi * s) ^ 2 := by fun_prop
  have hsc : Continuous fun s : ℝ => Real.sin (2 * Real.pi * s) ^ 2 * Real.cos (2 * Real.pi * s) := by
    fun_prop
  have e : (fun s : ℝ => (1 + t * Real.cos (2 * Real.pi * s)) *
        (Real.sin (2 * Real.pi * s) * Real.sin (2 * Real.pi * s)))
      = fun s => Real.sin (2 * Real.pi * s) ^ 2
          + t * (Real.sin (2 * Real.pi * s) ^ 2 * Real.cos (2 * Real.pi * s)) := by
    funext s; ring
  rw [e, intervalIntegral.integral_add (hs2.intervalIntegrable _ _) ((hsc.const_mul t).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_sin_sq_two_pi, integral_sin_sq_mul_cos_two_pi]
  ring

/-- Haar integral of `firstHarmonic t * f` as an interval integral. -/
theorem haar_trial_ex079 (t : ℝ) (f : DGPS.Torus 1 → ℝ) (hf : DGPS.IsSmoothPeriodic f) :
    ∫ x, firstHarmonic t x * f x ∂DGPS.haar 1 =
      ∫ s in (0:ℝ)..1, (1 + t * Real.cos (2 * Real.pi * s)) * f (DGPS.torusLift fun _ => s) := by
  rw [integral_haar_eq ((isSmoothPeriodic_firstHarmonic t).mul hf).continuous]
  apply intervalIntegral.integral_congr
  intro s _
  simp only [firstHarmonic_lift]

/-! ### Moments of the trial densities -/

theorem xyZ1_trial_ex079 (t : ℝ) (ht : |t| < 1) :
    xyZ1 (DGPS.densityMeasure (firstHarmonicDensity t ht) : Measure (DGPS.Torus 1)) = t / 2 := by
  unfold xyZ1
  rw [integral_densityMeasure (firstHarmonicDensity t ht) (fun y => (xyMode y).re),
    firstHarmonicDensity_density ht]
  show ∫ x, firstHarmonic t x * cosMode x ∂DGPS.haar 1 = t / 2
  rw [haar_trial_ex079 t cosMode isSmoothPeriodic_cosMode]
  simp only [cosMode_lift]
  exact trial_cos_ex079 t

theorem xyZ2_trial_ex079 (t : ℝ) (ht : |t| < 1) :
    xyZ2 (DGPS.densityMeasure (firstHarmonicDensity t ht) : Measure (DGPS.Torus 1)) = 0 := by
  unfold xyZ2
  rw [integral_densityMeasure (firstHarmonicDensity t ht) (fun y => (xyMode y).im),
    firstHarmonicDensity_density ht]
  rw [haar_trial_ex079 t (fun y => (xyMode y).im)
    (isSmoothPeriodic_im_mFourier (fun _ : Fin 1 => (1 : ℤ)))]
  simp only [xyMode_im_lift]
  exact trial_sin_ex079 t

theorem sq_integral_trial_ex079 (t : ℝ) (ht : |t| < 1) :
    ∫ x, ((t / 2) * (xyMode x).im - 0 * (xyMode x).re) ^ 2
      ∂(DGPS.densityMeasure (firstHarmonicDensity t ht) : Measure (DGPS.Torus 1)) = t ^ 2 / 8 := by
  rw [integral_densityMeasure (firstHarmonicDensity t ht)
    (fun x => ((t / 2) * (xyMode x).im - 0 * (xyMode x).re) ^ 2), firstHarmonicDensity_density ht]
  have e : ∀ x : DGPS.Torus 1,
      firstHarmonic t x * ((t / 2) * (xyMode x).im - 0 * (xyMode x).re) ^ 2
        = t ^ 2 / 4 * (firstHarmonic t x * ((xyMode x).im * (xyMode x).im)) := by
    intro x; ring
  simp_rw [e]
  rw [integral_const_mul]
  have hs : DGPS.IsSmoothPeriodic (fun x => (xyMode x).im * (xyMode x).im) :=
    (isSmoothPeriodic_im_mFourier (fun _ : Fin 1 => (1 : ℤ))).mul
      (isSmoothPeriodic_im_mFourier (fun _ : Fin 1 => (1 : ℤ)))
  rw [haar_trial_ex079 t (fun x => (xyMode x).im * (xyMode x).im) hs]
  simp only [xyMode_im_lift]
  rw [trial_sin_sq_ex079]
  ring

/-! ### Single-species sums -/

theorem single_sum_ex079 (ρ : DGPS.AbsoluteDensity 1) (g : DGPS.AbsoluteDensity 1 → ℝ) :
    ∑ s, (DGPS.SpeciesFamily.single ρ).weight s *
        g ((DGPS.SpeciesFamily.single ρ).density s) = g ρ := by
  rw [DGPS.sum_single_count ρ (fun s => (DGPS.SpeciesFamily.single ρ).weight s *
    g ((DGPS.SpeciesFamily.single ρ).density s))]
  show (1:ℝ) * g ρ = g ρ
  exact one_mul _

theorem single_entropy_sum_ex079 (ρ : DGPS.AbsoluteDensity 1) :
    ∑ s, (DGPS.SpeciesFamily.single ρ).weight s *
        (DGPS.relativeEntropy (DGPS.densityMeasure ((DGPS.SpeciesFamily.single ρ).density s)
          : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal
      = (DGPS.relativeEntropy (DGPS.densityMeasure ρ : Measure (DGPS.Torus 1))
          (DGPS.haar 1)).toReal :=
  single_sum_ex079 ρ (fun r => (DGPS.relativeEntropy (DGPS.densityMeasure r
    : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal)

theorem single_fisher_sum_ex079 (ρ : DGPS.AbsoluteDensity 1) :
    ∑ s, (DGPS.SpeciesFamily.single ρ).weight s *
        DGPS.Analysis.circleFisherInformation ((DGPS.SpeciesFamily.single ρ).density s)
      = DGPS.Analysis.circleFisherInformation ρ :=
  single_sum_ex079 ρ DGPS.Analysis.circleFisherInformation

theorem circleFisherInformation_trial_ex079 (t : ℝ) (ht : |t| < 1) :
    DGPS.Analysis.circleFisherInformation (firstHarmonicDensity t ht) = firstHarmonicFisher t := by
  rw [firstHarmonicFisher_of_lt ht]
  rfl

/-! ### Real estimates -/

theorem trial_real_ex079 {H I Dr G : ℝ} (k t : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) (ht0 : t ≠ 0)
    (hG : (1 - k) * H ≤ G) (hH : (t / 2) ^ 2 + 0 ^ 2 ≤ H)
    (hHb : |H - t ^ 2 / 4| ≤ 7 / 8 * t ^ 4)
    (hIb : |I - 4 * Real.pi ^ 2 * t ^ 2 / 2| ≤ 4 * Real.pi ^ 2 * t ^ 4)
    (hdef : (Dr - 2 * (4 * Real.pi ^ 2 * (1 - k)) * G) / (2 * (4 * Real.pi ^ 2))
      = (I / (2 * (4 * Real.pi ^ 2)) - H) + k * (H - ((t / 2) ^ 2 + 0 ^ 2))
        + k ^ 2 * (2 * (t ^ 2 / 8) - ((t / 2) ^ 2 + 0 ^ 2))) :
    |Dr / (2 * G) - 4 * Real.pi ^ 2 * (1 - k)| ≤ 6 * (4 * Real.pi ^ 2) * t ^ 2 / (1 - k) := by
  have h1k : 0 < 1 - k := by linarith
  have ht2 : 0 < t ^ 2 := by positivity
  have hH' : t ^ 2 / 4 ≤ H := by nlinarith [hH]
  have hGpos : (1 - k) * (t ^ 2 / 4) ≤ G :=
    (mul_le_mul_of_nonneg_left hH' h1k.le).trans hG
  have hGp : 0 < G := lt_of_lt_of_le (mul_pos h1k (by positivity)) hGpos
  have h2a : (2 * (4 * Real.pi ^ 2)) ≠ 0 := by positivity
  have key : Dr - 2 * (4 * Real.pi ^ 2 * (1 - k)) * G
      = I - 2 * (4 * Real.pi ^ 2) * H + 2 * (4 * Real.pi ^ 2) * k * (H - t ^ 2 / 4) := by
    have h := (div_eq_iff h2a).mp hdef
    rw [h]
    field_simp
    ring
  have hx : |(1 - k) * (H - t ^ 2 / 4)| ≤ 7 / 8 * t ^ 4 := by
    rw [abs_mul, abs_of_pos h1k]
    nlinarith [abs_nonneg (H - t ^ 2 / 4), hHb]
  have hQ : |2 * (4 * Real.pi ^ 2) * ((1 - k) * (H - t ^ 2 / 4))|
      ≤ 2 * (4 * Real.pi ^ 2) * (7 / 8 * t ^ 4) := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * (4 * Real.pi ^ 2))]
    exact mul_le_mul_of_nonneg_left hx (by positivity)
  have hN : I - 2 * (4 * Real.pi ^ 2) * H + 2 * (4 * Real.pi ^ 2) * k * (H - t ^ 2 / 4)
      = (I - 4 * Real.pi ^ 2 * t ^ 2 / 2)
          - 2 * (4 * Real.pi ^ 2) * ((1 - k) * (H - t ^ 2 / 4)) := by
    ring
  have hN_bound : |I - 2 * (4 * Real.pi ^ 2) * H + 2 * (4 * Real.pi ^ 2) * k * (H - t ^ 2 / 4)|
      ≤ 3 * (4 * Real.pi ^ 2) * t ^ 4 := by
    rw [hN]
    have hab := abs_sub (I - 4 * Real.pi ^ 2 * t ^ 2 / 2)
      (2 * (4 * Real.pi ^ 2) * ((1 - k) * (H - t ^ 2 / 4)))
    have h4 : 0 ≤ 4 * Real.pi ^ 2 * t ^ 4 := by positivity
    linarith [hIb, hQ, hab, h4]
  have e2 : Dr / (2 * G) - 4 * Real.pi ^ 2 * (1 - k)
      = (Dr - 2 * (4 * Real.pi ^ 2 * (1 - k)) * G) / (2 * G) := by
    field_simp
  have h2G : 0 < 2 * G := by linarith
  rw [e2, key, abs_div, abs_of_pos h2G, div_le_div_iff₀ h2G h1k]
  have m1 := mul_le_mul_of_nonneg_right hN_bound h1k.le
  have m2 := mul_le_mul_of_nonneg_left hGpos (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2 * t ^ 2)
  nlinarith [m1, m2]

/-! ### Trial bound for a single first-harmonic species -/

theorem trial_bound_ex079 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0)) (t : ℝ) (ht : |t| < 1)
    (ht0 : t ≠ 0) (ht2 : |t| ≤ 1 / 2) :
    DGPS.speciesDissipation (DGPS.Models.attractiveXY (2 * k) 0) b
        (DGPS.SpeciesFamily.single (firstHarmonicDensity t ht)) ≠ ⊤ ∧
      |(DGPS.speciesDissipation (DGPS.Models.attractiveXY (2 * k) 0) b
          (DGPS.SpeciesFamily.single (firstHarmonicDensity t ht))).toReal /
          (2 * (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0)
            (DGPS.SpeciesFamily.single (firstHarmonicDensity t ht)) : ℝ))
        - 4 * Real.pi ^ 2 * (1 - k)| ≤ 6 * (4 * Real.pi ^ 2) * t ^ 2 / (1 - k) := by
  obtain ⟨hDfin, hdef⟩ := exact_harmonic_family_deficit_polynomial k hk0 hk1 b
    (DGPS.SpeciesFamily.single (firstHarmonicDensity t ht))
  rw [single_fisher_sum_ex079, single_entropy_sum_ex079, DGPS.densityMeasure_barycenter_single,
    xyZ1_trial_ex079 t ht, xyZ2_trial_ex079 t ht, sq_integral_trial_ex079 t ht,
    circleFisherInformation_trial_ex079 t ht] at hdef
  refine ⟨hDfin, ?_⟩
  have h4 : |t| ^ 4 = t ^ 4 := by
    have h := sq_abs t
    calc |t| ^ 4 = (|t| ^ 2) ^ 2 := by ring
      _ = (t ^ 2) ^ 2 := by rw [h]
      _ = t ^ 4 := by ring
  have hHb := (entropy_bounds ht2 ht0 ht).2.2
  rw [firstHarmonicEntropy_of_lt ht, h4] at hHb
  have hIb := fisher_bounds ht2 ht
  rw [h4] at hIb
  unfold a0 at hIb
  have hG := (speciesGap_bounds_ex076 k hk0 hk1 (DGPS.SpeciesFamily.single
    (firstHarmonicDensity t ht))).1
  rw [single_entropy_sum_ex079] at hG
  have hf := species_fourier_ex076 (firstHarmonicDensity t ht)
  rw [xyZ1_trial_ex079 t ht, xyZ2_trial_ex079 t ht] at hf
  exact trial_real_ex079 k t hk0 hk1 ht0 hG hf hHb hIb hdef

theorem gap_pos_ex079 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) (t : ℝ) (ht : |t| < 1) (ht0 : t ≠ 0) :
    0 < (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0)
      (DGPS.SpeciesFamily.single (firstHarmonicDensity t ht)) : ℝ) := by
  have hG := (speciesGap_bounds_ex076 k hk0 hk1 (DGPS.SpeciesFamily.single
    (firstHarmonicDensity t ht))).1
  rw [single_entropy_sum_ex079] at hG
  have hf := species_fourier_ex076 (firstHarmonicDensity t ht)
  rw [xyZ1_trial_ex079 t ht, xyZ2_trial_ex079 t ht] at hf
  have h1k : 0 < 1 - k := by linarith
  have hH : t ^ 2 / 4 ≤ (DGPS.relativeEntropy (DGPS.densityMeasure (firstHarmonicDensity t ht)
      : Measure (DGPS.Torus 1)) (DGPS.haar 1)).toReal := by
    nlinarith [hf]
  exact lt_of_lt_of_le (mul_pos h1k (by positivity : (0:ℝ) < t ^ 2 / 4))
    ((mul_le_mul_of_nonneg_left hH h1k.le).trans hG)

/-! ### The first-harmonic trial family -/

/-- The trial density `1 + t cos (2π x)` for `|t| < 1`, and the value `1` outside this range. -/
noncomputable def trialDensity_ex079 (t : ℝ) : DGPS.AbsoluteDensity 1 :=
  if h : |t| < 1 then firstHarmonicDensity t h else firstHarmonicDensity 0 (by norm_num)

theorem trialDensity_eq_ex079 {t : ℝ} (h : |t| < 1) :
    trialDensity_ex079 t = firstHarmonicDensity t h := by
  simp [trialDensity_ex079, h]

/-- The trial scalar quotient transported to the real axis. -/
noncomputable def trialRatio_ex079 (k : ℝ)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0)) (t : ℝ) : ℝ :=
  (DGPS.speciesDissipation (DGPS.Models.attractiveXY (2 * k) 0) b
      (DGPS.SpeciesFamily.single (trialDensity_ex079 t))).toReal /
    (2 * (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0)
      (DGPS.SpeciesFamily.single (trialDensity_ex079 t)) : ℝ))

theorem two_mul_coe_ex079 (G : ℝ≥0) :
    (2 : ℝ≥0∞) * (G : ℝ≥0∞) = ENNReal.ofReal (2 * (G : ℝ)) := by
  rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]

theorem quotient_eq_ofReal_ex079 (A : DGPS.InteractionData 1) (b : DGPS.AbsoluteDrift A)
    (ρ : DGPS.AbsoluteDensity 1)
    (hD : DGPS.speciesDissipation A b (DGPS.SpeciesFamily.single ρ) ≠ ⊤)
    (hG : 0 < (DGPS.speciesGap A (DGPS.SpeciesFamily.single ρ) : ℝ)) :
    DGPS.scalarQuotient A b ρ = ENNReal.ofReal
      ((DGPS.speciesDissipation A b (DGPS.SpeciesFamily.single ρ)).toReal /
        (2 * (DGPS.speciesGap A (DGPS.SpeciesFamily.single ρ) : ℝ))) := by
  have hpos : 0 < 2 * (DGPS.speciesGap A (DGPS.SpeciesFamily.single ρ) : ℝ) :=
    mul_pos two_pos hG
  rw [ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_toReal hD, ← two_mul_coe_ex079,
    ← DGPS.speciesQuotient_single]
  rfl

theorem quotient_trial_ex079 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0)) (t : ℝ) (ht : |t| < 1)
    (ht0 : t ≠ 0) (ht2 : |t| ≤ 1 / 2) :
    DGPS.scalarQuotient (DGPS.Models.attractiveXY (2 * k) 0) b (trialDensity_ex079 t)
      = ENNReal.ofReal (trialRatio_ex079 k b t) := by
  have hD : DGPS.speciesDissipation (DGPS.Models.attractiveXY (2 * k) 0) b
      (DGPS.SpeciesFamily.single (trialDensity_ex079 t)) ≠ ⊤ := by
    rw [trialDensity_eq_ex079 ht]
    exact (trial_bound_ex079 k hk0 hk1 b t ht ht0 ht2).1
  have hG : 0 < (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0)
      (DGPS.SpeciesFamily.single (trialDensity_ex079 t)) : ℝ) := by
    rw [trialDensity_eq_ex079 ht]
    exact gap_pos_ex079 k hk0 hk1 t ht ht0
  unfold trialRatio_ex079
  exact quotient_eq_ofReal_ex079 _ b _ hD hG

theorem trial_eventually_ex079 : ∀ᶠ t in 𝓝[≠] (0:ℝ), |t| < 1 / 2 ∧ t ≠ 0 := by
  have h0 : ∀ᶠ t in 𝓝 (0:ℝ), |t| < 1 / 2 := by
    have h := continuous_abs.tendsto (0:ℝ)
    simp only [abs_zero] at h
    exact h.eventually (Iio_mem_nhds (by norm_num))
  exact (eventually_nhdsWithin_of_eventually_nhds h0).and self_mem_nhdsWithin

theorem trial_scalar_gap_ex079 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1) (t : ℝ) (ht : |t| < 1)
    (ht0 : t ≠ 0) :
    0 < DGPS.scalarGap (DGPS.Models.attractiveXY (2 * k) 0) (trialDensity_ex079 t) := by
  rw [trialDensity_eq_ex079 ht, ← DGPS.speciesGap_single]
  exact NNReal.coe_pos.mp (gap_pos_ex079 k hk0 hk1 t ht ht0)

theorem trial_tendsto_ex079 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0)) :
    Tendsto (fun t : ℝ => DGPS.scalarQuotient (DGPS.Models.attractiveXY (2 * k) 0) b
        (trialDensity_ex079 t)) (𝓝[≠] 0)
      (𝓝 (ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k)))) := by
  have hev := trial_eventually_ex079
  have hbound : ∀ᶠ t in 𝓝[≠] (0:ℝ),
      ‖trialRatio_ex079 k b t - 4 * Real.pi ^ 2 * (1 - k)‖
        ≤ 6 * (4 * Real.pi ^ 2) * t ^ 2 / (1 - k) := by
    filter_upwards [hev] with t ht
    have h1 : |t| < 1 := by linarith [ht.1]
    have hb := (trial_bound_ex079 k hk0 hk1 b t h1 ht.2 ht.1.le).2
    rw [Real.norm_eq_abs]
    unfold trialRatio_ex079
    rw [trialDensity_eq_ex079 h1]
    exact hb
  have hc : Continuous (fun t : ℝ => 6 * (4 * Real.pi ^ 2) * t ^ 2 / (1 - k)) := by fun_prop
  have hlim : Tendsto (fun t : ℝ => 6 * (4 * Real.pi ^ 2) * t ^ 2 / (1 - k)) (𝓝[≠] 0) (𝓝 0) := by
    have h0 := hc.tendsto 0
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hQ : Tendsto (trialRatio_ex079 k b) (𝓝[≠] 0) (𝓝 (4 * Real.pi ^ 2 * (1 - k))) :=
    tendsto_sub_nhds_zero_iff.mp (squeeze_zero_norm' hbound hlim)
  have hEq : (fun t : ℝ => ENNReal.ofReal (trialRatio_ex079 k b t)) =ᶠ[𝓝[≠] 0]
      (fun t : ℝ => DGPS.scalarQuotient (DGPS.Models.attractiveXY (2 * k) 0) b
        (trialDensity_ex079 t)) := by
    filter_upwards [hev] with t ht
    have h1 : |t| < 1 := by linarith [ht.1]
    exact (quotient_trial_ex079 k hk0 hk1 b t h1 ht.2 ht.1.le).symm
  exact Tendsto.congr' hEq (ENNReal.tendsto_ofReal hQ)

theorem scalar_rate_upper_ex079 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0)) :
    DGPS.scalarRate (DGPS.Models.attractiveXY (2 * k) 0) b
      ≤ ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k)) := by
  refine ge_of_tendsto (trial_tendsto_ex079 k hk0 hk1 b) ?_
  filter_upwards [trial_eventually_ex079] with t ht
  have h1 : |t| < 1 := by linarith [ht.1]
  exact DGPS.scalarRate_le_quotient _ b _ (trial_scalar_gap_ex079 k hk0 hk1 t h1 ht.2)

/-! ### Species lower bound -/

theorem species_rate_lower_ex079 (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0)) :
    ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k)) ≤ DGPS.speciesRate (DGPS.Models.attractiveXY (2 * k) 0) b := by
  refine le_iInf fun F : {F // 0 < DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F} => ?_
  have hF : (0:ℝ) < (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F.1 : ℝ) :=
    NNReal.coe_pos.mpr F.2
  obtain ⟨hD, hq⟩ := quantitative_positive_harmonic_deficit k hk0 hk1 b F.1
  have h1k : 0 ≤ 1 - k := by linarith
  have hnn : ∀ E : ℝ, 0 ≤ (1 - k) * E ^ 2 / 12 := fun E =>
    div_nonneg (mul_nonneg h1k (sq_nonneg E)) (by norm_num)
  have h3 := le_trans (hnn _) hq
  have h2a : (0:ℝ) < 2 * (4 * Real.pi ^ 2) := by positivity
  have h4 : 0 ≤ (DGPS.speciesDissipation (DGPS.Models.attractiveXY (2 * k) 0) b F.1).toReal -
      2 * (4 * Real.pi ^ 2 * (1 - k)) *
        (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F.1 : ℝ) := by
    by_contra hneg
    have hneg' := not_le.mp hneg
    have := div_neg_of_neg_of_pos hneg' h2a
    linarith
  have hG0 : (2 : ℝ≥0∞) * (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F.1 : ℝ≥0∞) ≠ 0 := by
    exact mul_ne_zero two_ne_zero (ENNReal.coe_ne_zero.mpr F.2.ne')
  have hGt : (2 : ℝ≥0∞) * (DGPS.speciesGap (DGPS.Models.attractiveXY (2 * k) 0) F.1 : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.coe_ne_top
  unfold DGPS.speciesQuotient
  rw [ENNReal.le_div_iff_mul_le (Or.inl hG0) (Or.inl hGt), two_mul_coe_ex079,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_toReal hD]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-! ### Main theorem -/

/-- EX079: for `0 ≤ k < 1` the scalar and species rates both equal `4π²(1-k) > 0`, and the
first-harmonic trials `1 + t cos (2π x)`, `0 < |t| < 1`, have positive gap and scalar quotient
tending to `4π²(1-k)` as `t → 0`. -/
theorem subcritical_sharp_rate_by_first_harmonic_trials (k : ℝ) (hk0 : 0 ≤ k) (hk1 : k < 1)
    (b : DGPS.AbsoluteDrift (DGPS.Models.attractiveXY (2 * k) 0)) :
    0 < 4 * Real.pi ^ 2 * (1 - k) ∧
    DGPS.scalarRate (DGPS.Models.attractiveXY (2 * k) 0) b =
        ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k)) ∧
    DGPS.speciesRate (DGPS.Models.attractiveXY (2 * k) 0) b =
        ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k)) ∧
    ∃ ρ : ℝ → DGPS.AbsoluteDensity 1,
      (∀ t : ℝ, 0 < |t| → |t| < 1 →
        (ρ t).density = firstHarmonic t ∧
          0 < DGPS.scalarGap (DGPS.Models.attractiveXY (2 * k) 0) (ρ t)) ∧
      Tendsto (fun t : ℝ => DGPS.scalarQuotient (DGPS.Models.attractiveXY (2 * k) 0) b (ρ t))
        (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (4 * Real.pi ^ 2 * (1 - k)))) := by
  have hr : 0 < 4 * Real.pi ^ 2 * (1 - k) := mul_pos (by positivity) (by linarith)
  have hlow := species_rate_lower_ex079 k hk0 hk1 b
  have hup := scalar_rate_upper_ex079 k hk0 hk1 b
  have hsp := DGPS.speciesRate_le_scalarRate (DGPS.Models.attractiveXY (2 * k) 0) b
  refine ⟨hr, le_antisymm hup (hlow.trans hsp), le_antisymm (hsp.trans hup) hlow,
    trialDensity_ex079, ?_, trial_tendsto_ex079 k hk0 hk1 b⟩
  intro t h0 h1
  have ht0 : t ≠ 0 := abs_pos.mp h0
  refine ⟨?_, trial_scalar_gap_ex079 k hk0 hk1 t h1 ht0⟩
  rw [trialDensity_eq_ex079 h1, firstHarmonicDensity_density h1]

end DGPS.Examples
