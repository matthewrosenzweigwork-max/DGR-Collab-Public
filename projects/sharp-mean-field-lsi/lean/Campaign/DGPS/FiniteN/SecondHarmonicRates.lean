import DGPS.FiniteN.SecondHarmonic
import DGPS.Analysis.CircleMoments

/-!
# Second harmonic: first-mode recovery and exact nonlinear rates (FIN088)

For `ρ_t = 1 + t cos 2πx`, `0 < |t| < 1`, the second Fourier mode vanishes (`Q = 0`) and so does
the interaction-force term (`J = 0`); hence on these densities the FIN087 dissipation is the
plain Fisher information and the gap is the plain entropy.  The first-harmonic estimates give
`I/(2H) → a0 = 4π²`, which together with the FIN087 lower bounds gives `r_* = r_ms = a0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.FiniteN

theorem integrable_mode (k : ℤ) : Integrable (mode k) (DGPS.haar 1) :=
  (continuous_mode k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem integral_mode_haar {k : ℤ} (hk : k ≠ 0) : ∫ x, mode k x ∂DGPS.haar 1 = 0 := by
  have h := SharpLSI.integral_mFourier (ι := Fin 1) (fun _ => k)
  have hne : (fun _ : Fin 1 => k) ≠ 0 := fun h0 => hk (congrFun h0 0)
  rw [ite_eq_right_iff.mpr (fun h0 => absurd h0 hne)] at h
  exact h

theorem mode_mul (k l : ℤ) (x : DGPS.Torus 1) : mode k x * mode l x = mode (k + l) x := by
  simp [mode_apply]

theorem density_mul_mode_two (t : ℝ) (x : DGPS.Torus 1) :
    ((DGPS.Analysis.CircleMoments.firstHarmonic t x : ℝ) : ℂ) * mode 2 x =
      mode 2 x + ((t : ℂ) / 2) * mode 3 x + ((t : ℂ) / 2) * mode 1 x := by
  have hc : ((mode 1 x).re : ℂ) = (mode 1 x + mode (-1) x) / 2 := by
    rw [mode_neg, Complex.re_eq_add_conj]
  have h3 : mode 1 x * mode 2 x = mode 3 x := by rw [mode_mul]; norm_num
  have h1 : mode (-1) x * mode 2 x = mode 1 x := by rw [mode_mul]; norm_num
  have e : DGPS.Analysis.CircleMoments.firstHarmonic t x = 1 + t * (mode 1 x).re := rfl
  rw [e]
  push_cast
  rw [hc]
  linear_combination ((t : ℂ) / 2) * h3 + ((t : ℂ) / 2) * h1

theorem moments_zero {t : ℝ} (σ : DGPS.AbsoluteDensity 1)
    (hσ : σ.density = DGPS.Analysis.CircleMoments.firstHarmonic t) :
    (∫ y, (mode 2 y).re ∂(DGPS.densityMeasure σ : Measure (DGPS.Torus 1))) = 0 ∧
    (∫ y, (mode 2 y).im ∂(DGPS.densityMeasure σ : Measure (DGPS.Torus 1))) = 0 := by
  have hfun : (fun x => ((σ.density x : ℝ) : ℂ) * mode 2 x) =
      fun x => mode 2 x + ((t : ℂ) / 2) * mode 3 x + ((t : ℂ) / 2) * mode 1 x := by
    funext x; rw [hσ]; exact density_mul_mode_two t x
  have hi2 : Integrable (fun x => mode 2 x + ((t : ℂ) / 2) * mode 3 x) (DGPS.haar 1) :=
    (integrable_mode 2).add ((integrable_mode 3).const_mul _)
  have hint : Integrable (fun x => ((σ.density x : ℝ) : ℂ) * mode 2 x) (DGPS.haar 1) := by
    rw [hfun]; exact hi2.add ((integrable_mode 1).const_mul _)
  have hZ : ∫ x, ((σ.density x : ℝ) : ℂ) * mode 2 x ∂DGPS.haar 1 = 0 := by
    rw [hfun, integral_add hi2 ((integrable_mode 1).const_mul _),
      integral_add (integrable_mode 2) ((integrable_mode 3).const_mul _),
      integral_const_mul, integral_const_mul, integral_mode_haar (by norm_num : (2 : ℤ) ≠ 0),
      integral_mode_haar (by norm_num : (3 : ℤ) ≠ 0),
      integral_mode_haar (by norm_num : (1 : ℤ) ≠ 0)]
    simp
  have hr := integral_re hint
  have hm := integral_im hint
  simp only [RCLike.re_to_complex, RCLike.im_to_complex, hZ, Complex.zero_re,
    Complex.zero_im] at hr hm
  simp only [integral_densityMeasure]
  constructor
  · rw [← hr]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp)
  · rw [← hm]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp)

theorem Q_J_zero {t : ℝ} (σ : DGPS.AbsoluteDensity 1)
    (hσ : σ.density = DGPS.Analysis.CircleMoments.firstHarmonic t) :
    secondHarmonicQ σ = 0 ∧ secondHarmonicJ σ = 0 := by
  obtain ⟨hC, hS⟩ := moments_zero σ hσ
  refine ⟨by rw [secondHarmonicQ_eq, hC, hS]; norm_num, ?_⟩
  rw [secondHarmonicJ_eq σ 0 0 hC.symm hS.symm]
  simp [trig]

theorem ofReal_div_two_mul {G : ℝ≥0} {I : ℝ} {D : ℝ≥0∞} (hD : D = ENNReal.ofReal I) {H : ℝ}
    (hH : (G : ℝ) = H) (hHpos : 0 < H) :
    D / (2 * (G : ℝ≥0∞)) = ENNReal.ofReal (I / (2 * H)) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), hD, ENNReal.ofReal_mul (by norm_num), ← hH,
    ENNReal.ofReal_coe_nnreal]
  simp

theorem entropy_pos_firstHarmonic {t : ℝ} (ht1 : |t| < 1) (ht0 : t ≠ 0) (hle : |t| ≤ 1 / 2) :
    0 < DGPS.Analysis.CircleMoments.firstHarmonicEntropy t := by
  obtain ⟨hp, hne, -⟩ := DGPS.Analysis.CircleMoments.entropy_bounds hle ht0 ht1
  rw [DGPS.Analysis.CircleMoments.firstHarmonicEntropy_of_lt ht1]
  exact ENNReal.toReal_pos hp.ne' hne

theorem circleEntropy_firstHarmonic {t : ℝ} (ht1 : |t| < 1) :
    DGPS.Analysis.circleEntropy (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1) =
      DGPS.Analysis.CircleMoments.firstHarmonicEntropy t := by
  rw [DGPS.circleEntropy_eq_relativeEntropy,
    DGPS.Analysis.CircleMoments.firstHarmonicEntropy_of_lt ht1]

theorem circleFisher_firstHarmonic {t : ℝ} (ht1 : |t| < 1) :
    DGPS.Analysis.circleFisherInformation
        (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1) =
      DGPS.Analysis.CircleMoments.firstHarmonicFisher t := by
  rw [DGPS.Analysis.CircleMoments.firstHarmonicFisher_of_lt ht1]; rfl

theorem scalar_quotient_firstHarmonic {κ : ℝ} (hκ : 0 < κ)
    (b : DGPS.AbsoluteDrift (secondHarmonicData κ)) {t : ℝ} (ht1 : |t| < 1) (ht0 : t ≠ 0)
    (hle : |t| ≤ 1 / 2) :
    0 < DGPS.scalarGap (secondHarmonicData κ)
        (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1) ∧
    DGPS.scalarQuotient (secondHarmonicData κ) b
        (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1) =
      ENNReal.ofReal (DGPS.Analysis.CircleMoments.firstHarmonicFisher t /
        (2 * DGPS.Analysis.CircleMoments.firstHarmonicEntropy t)) := by
  obtain ⟨hQ, hJ⟩ := Q_J_zero (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1)
    (DGPS.Analysis.CircleMoments.firstHarmonicDensity_density ht1)
  obtain ⟨-, hD, hG, -⟩ :=
    (second_harmonic_scalar_and_species_dissipation κ hκ b).1
      (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1)
  have hEpos := entropy_pos_firstHarmonic ht1 ht0 hle
  have hGr : ((DGPS.scalarGap (secondHarmonicData κ)
      (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1) : ℝ≥0) : ℝ) =
      DGPS.Analysis.CircleMoments.firstHarmonicEntropy t := by
    rw [hG, hQ, circleEntropy_firstHarmonic ht1]; ring
  have hD' : DGPS.scalarDissipation (secondHarmonicData κ) b
      (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1) =
      ENNReal.ofReal (DGPS.Analysis.CircleMoments.firstHarmonicFisher t) := by
    rw [hD, hQ, hJ, circleFisher_firstHarmonic ht1]; simp
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_pos, hGr]; exact hEpos
  · unfold DGPS.scalarQuotient
    exact ofReal_div_two_mul hD' hGr hEpos

/-- The one-species family consisting of a single density. -/
noncomputable def singleSpecies (ρ : DGPS.AbsoluteDensity 1) : DGPS.SpeciesFamily 1 where
  count := 1
  weight := fun _ => 1
  weight_pos := fun _ => one_pos
  weight_sum := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; simp
  density := fun _ => ρ

theorem sum_single (ρ : DGPS.AbsoluteDensity 1) (g : Fin (singleSpecies ρ).count → ℝ) :
    ∑ s, g s = g ⟨0, PNat.pos _⟩ :=
  Fin.sum_univ_one g

theorem barycenter_single_density (ρ : DGPS.AbsoluteDensity 1) :
    (DGPS.barycenter (singleSpecies ρ)).density = ρ.density := by
  funext x
  rw [DGPS.SpeciesFamily.barycenter_density_apply]
  rw [sum_single ρ]
  simp [singleSpecies, DGPS.AbsoluteDensity.density]

theorem species_quotient_firstHarmonic {κ : ℝ} (hκ : 0 < κ)
    (b : DGPS.AbsoluteDrift (secondHarmonicData κ)) {t : ℝ} (ht1 : |t| < 1) (ht0 : t ≠ 0)
    (hle : |t| ≤ 1 / 2) :
    0 < DGPS.speciesGap (secondHarmonicData κ)
        (singleSpecies (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1)) ∧
    DGPS.speciesQuotient (secondHarmonicData κ) b
        (singleSpecies (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1)) =
      ENNReal.ofReal (DGPS.Analysis.CircleMoments.firstHarmonicFisher t /
        (2 * DGPS.Analysis.CircleMoments.firstHarmonicEntropy t)) := by
  obtain ⟨hQ, hJ⟩ := Q_J_zero (DGPS.barycenter (singleSpecies (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1)))
    (by rw [barycenter_single_density]
        exact DGPS.Analysis.CircleMoments.firstHarmonicDensity_density ht1)
  obtain ⟨-, hD, hG, -⟩ := (second_harmonic_scalar_and_species_dissipation κ hκ b).2.2.1
    (singleSpecies (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1))
  have hEpos := entropy_pos_firstHarmonic ht1 ht0 hle
  have hGr : ((DGPS.speciesGap (secondHarmonicData κ) (singleSpecies (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1)) : ℝ≥0) : ℝ) =
      DGPS.Analysis.CircleMoments.firstHarmonicEntropy t := by
    rw [hG, hQ, ← circleEntropy_firstHarmonic ht1,
      sum_single (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1)]
    simp [singleSpecies]
  have hD' : DGPS.speciesDissipation (secondHarmonicData κ) b (singleSpecies (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1)) =
      ENNReal.ofReal (DGPS.Analysis.CircleMoments.firstHarmonicFisher t) := by
    rw [hD, hQ, hJ, ← circleFisher_firstHarmonic ht1,
      sum_single (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht1)]
    simp [singleSpecies]
  refine ⟨?_, ?_⟩
  · rw [← NNReal.coe_pos, hGr]; exact hEpos
  · unfold DGPS.speciesQuotient
    exact ofReal_div_two_mul hD' hGr hEpos

/-- **FIN088.** For `ρ_t = 1 + t cos 2πx` (`|t| < 1`) the second Fourier mode vanishes
(`Q = 0`) and the force term vanishes (`J = 0`); for `0 < |t| ≤ 1/2` these are positive-gap
one-species tests with quotient `I_t/(2H_t)` (scalar and species), and `I_t/(2H_t) → a0`.
Together with the FIN087 lower bounds, `r_* = r_ms = a0 = 4π²` for every `κ > 0`. -/
theorem second_harmonic_first_mode_recovery_and_exact_nonlinear_rates (κ : ℝ) (hκ : 0 < κ)
    (b : DGPS.AbsoluteDrift (secondHarmonicData κ)) :
    (∀ (t : ℝ) (ht : |t| < 1),
      secondHarmonicQ (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht) = 0 ∧
      secondHarmonicJ (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht) = 0) ∧
    (∀ (t : ℝ) (ht : |t| < 1), t ≠ 0 → |t| ≤ 1 / 2 →
      0 < DGPS.scalarGap (secondHarmonicData κ)
          (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht) ∧
      DGPS.scalarQuotient (secondHarmonicData κ) b
          (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht) =
        ENNReal.ofReal (DGPS.Analysis.CircleMoments.firstHarmonicFisher t /
          (2 * DGPS.Analysis.CircleMoments.firstHarmonicEntropy t)) ∧
      0 < DGPS.speciesGap (secondHarmonicData κ)
          (singleSpecies (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht)) ∧
      DGPS.speciesQuotient (secondHarmonicData κ) b
          (singleSpecies (DGPS.Analysis.CircleMoments.firstHarmonicDensity t ht)) =
        ENNReal.ofReal (DGPS.Analysis.CircleMoments.firstHarmonicFisher t /
          (2 * DGPS.Analysis.CircleMoments.firstHarmonicEntropy t))) ∧
    Tendsto (fun t : ℝ => DGPS.Analysis.CircleMoments.firstHarmonicFisher t /
        (2 * DGPS.Analysis.CircleMoments.firstHarmonicEntropy t)) (𝓝[≠] 0)
      (𝓝 (4 * Real.pi ^ 2)) ∧
    DGPS.scalarRate (secondHarmonicData κ) b = ENNReal.ofReal (4 * Real.pi ^ 2) ∧
    DGPS.speciesRate (secondHarmonicData κ) b = ENNReal.ofReal (4 * Real.pi ^ 2) := by
  obtain ⟨ha0, -, -, -, hlim⟩ := DGPS.Analysis.CircleMoments.circle_first_harmonic_estimates
  have ha0' : DGPS.Analysis.CircleMoments.a0 = 4 * Real.pi ^ 2 := ha0
  rw [ha0'] at hlim
  have hlim' := ENNReal.tendsto_ofReal hlim
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| < 1 / 2 ∧ t ≠ 0 := by
    refine Filter.Eventually.and ?_ self_mem_nhdsWithin
    have : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < 1 / 2 := by
      have := (continuous_abs.tendsto (0 : ℝ)).eventually
        (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1 / 2))
      simpa using this
    exact nhdsWithin_le_nhds this
  obtain ⟨-, hscal, -, hspec⟩ := second_harmonic_scalar_and_species_dissipation κ hκ b
  refine ⟨fun t ht => Q_J_zero _ (DGPS.Analysis.CircleMoments.firstHarmonicDensity_density ht),
    fun t ht ht0 hle => ?_, hlim, ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := scalar_quotient_firstHarmonic hκ b ht ht0 hle
    obtain ⟨h3, h4⟩ := species_quotient_firstHarmonic hκ b ht ht0 hle
    exact ⟨h1, h2, h3, h4⟩
  · refine le_antisymm ?_ hscal
    refine ge_of_tendsto hlim' ?_
    filter_upwards [hev] with t ⟨h1, h0⟩
    have ht1 : |t| < 1 := by linarith
    obtain ⟨hpos, hq⟩ := scalar_quotient_firstHarmonic hκ b ht1 h0 h1.le
    rw [← hq]
    exact DGPS.scalarRate_le_quotient _ _ _ hpos
  · refine le_antisymm ?_ hspec
    refine ge_of_tendsto hlim' ?_
    filter_upwards [hev] with t ⟨h1, h0⟩
    have ht1 : |t| < 1 := by linarith
    obtain ⟨hpos, hq⟩ := species_quotient_firstHarmonic hκ b ht1 h0 h1.le
    rw [← hq]
    exact DGPS.speciesRate_le _ _ _ hpos

end DGPS.FiniteN
