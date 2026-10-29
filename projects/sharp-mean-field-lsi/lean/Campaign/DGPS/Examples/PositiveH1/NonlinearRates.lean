import DGPS.Examples.PositiveH1.NonlinearLowerBound
import DGPS.Examples.PositiveH1.Harmonic

/-!
# H1014: exact nonlinear rates for the rough model and every fixed smooth cutoff

For the rough model `positiveH1` and for every cutoff `positiveH1Cutoff M` (`M ≥ 2`) we prove
`r_* = r_ms = a0 = 4π²`.  The lower bound for the rough model is H1012; for the cutoff the
identical nonnegative Fourier computation is repeated on the finite sum `R_M`.  The upper bound
is first-mode recovery: on `ρ_t = 1 + t cos 2πx` the force vanishes and the gap is the entropy,
so the quotient is `I/(2H) → a0`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DGPS.Examples.PositiveH1.Nonlinear
open DGPS DGPS.Examples.PositiveH1.Fourier DGPS.Examples.PositiveH1.Model
  DGPS.Examples.PositiveH1.CrossTerm

/-! ### (A) the drift of the cutoff model -/

theorem cut_potential_eq (M : ℕ) (ρ : AbsoluteDensity 1) (x : Torus 1) :
    interactionPotential (positiveH1Cutoff M) ρ x =
      kappa * (conv ρ.density (RM M) x - RM M 0) := by
  rw [interactionPotential_eq]
  have hi : Integrable (fun y => ρ.density y * RM M (x - y)) (haar 1) :=
    (memLp_density_two ρ).integrable_mul
      (memLp_sub_left (memLp_of_cont (continuous_RM M) 2) x)
  have e : ∀ y, ρ.density y * (positiveH1Cutoff M).W x y =
      kappa * (ρ.density y * RM M (x - y)) - kappa * RM M 0 * ρ.density y := fun y => by
    show ρ.density y * (kappa * (RM M (x - y) - RM M 0)) = _
    ring
  simp_rw [e]
  rw [integral_sub (hi.const_mul _) (ρ.integrable_density.const_mul _), integral_const_mul,
    integral_const_mul, ρ.integral_density]
  show (0 : ℝ) + _ = _
  unfold conv
  ring

theorem cut_potential_ibp (M : ℕ) (ρ : AbsoluteDensity 1) {φ : Torus 1 → ℝ}
    (hφ : IsSmoothPeriodic φ) :
    ∫ x, interactionPotential (positiveH1Cutoff M) ρ x * coordPartial 0 φ x ∂haar 1 =
      -∫ x, kappa * conv ρ.density (dRM M) x * φ x ∂haar 1 := by
  have hc1 : Continuous (conv ρ.density (RM M)) :=
    conv_continuous ρ.integrable_density (continuous_RM M)
  have hd := hφ.continuous_coordPartial 0
  have i1 : Integrable (fun x => conv ρ.density (RM M) x * coordPartial 0 φ x) (haar 1) :=
    integrable_of_cont (hc1.mul hd)
  have i2 : Integrable (fun x => coordPartial 0 φ x) (haar 1) := integrable_of_cont hd
  have key := conv_ibp (f := ρ.density) (g := RM M) (G := dRM M) ρ.integrable_density
    (integrable_of_cont (continuous_RM M)) (integrable_of_cont (continuous_dRM M))
    (fun ψ hψ => ibp_RM M hψ) φ hφ
  simp_rw [cut_potential_eq]
  have e : ∀ x, kappa * (conv ρ.density (RM M) x - RM M 0) * coordPartial 0 φ x =
      kappa * (conv ρ.density (RM M) x * coordPartial 0 φ x)
        - kappa * RM M 0 * coordPartial 0 φ x :=
    fun x => by ring
  simp_rw [e]
  rw [integral_sub (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
    integral_coordPartial_zero hφ, key]
  have h2 : ∫ x, kappa * conv ρ.density (dRM M) x * φ x ∂haar 1 =
      kappa * ∫ x, conv ρ.density (dRM M) x * φ x ∂haar 1 := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    ring
  rw [h2]
  ring

/-- The actual drift of the cutoff model: `κ R_M′ * ρ` as a vector field on `𝕋¹`. -/
noncomputable def cutDrift (M : ℕ) : AbsoluteDrift (positiveH1Cutoff M) where
  force ρ x := EuclideanSpace.single (0 : Fin 1) (kappa * conv ρ.density (dRM M) x)
  measurable_force ρ :=
    (continuous_single_comp (continuous_const.mul
      (conv_continuous ρ.integrable_density (continuous_dRM M)))).measurable
  weak_gradient ρ := by
    have hpc : Continuous (interactionPotential (positiveH1Cutoff M) ρ) := by
      have : interactionPotential (positiveH1Cutoff M) ρ =
          fun x => kappa * (conv ρ.density (RM M) x - RM M 0) :=
        funext (cut_potential_eq M ρ)
      rw [this]
      exact continuous_const.mul
        ((conv_continuous ρ.integrable_density (continuous_RM M)).sub continuous_const)
    refine ⟨memLp_of_cont hpc 1,
      memLp_of_cont (continuous_single_comp (continuous_const.mul
        (conv_continuous ρ.integrable_density (continuous_dRM M)))) 1,
      fun φ hφ j => ?_⟩
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simpa using cut_potential_ibp M ρ hφ

theorem cut_force_ae (M : ℕ) (b : AbsoluteDrift (positiveH1Cutoff M)) (τ : AbsoluteDensity 1) :
    ∀ᵐ x ∂haar 1, b.force τ x =
      (EuclideanSpace.single (0 : Fin 1) (kappa * conv τ.density (dRM M) x) : Tangent 1) :=
  absoluteDrift_unique b (cutDrift M) τ

/-! ### (E) upper bound: force-free first harmonics -/

theorem scalarDissipation_eq_fisher {A : InteractionData 1} (b : AbsoluteDrift A)
    (ρ : AbsoluteDensity 1) (h : ∀ᵐ x ∂haar 1, b.force ρ x = 0) :
    scalarDissipation A b ρ =
      ENNReal.ofReal (4 * ∫ x, ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar 1) := by
  have hI : Integrable (fun x => ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2) (haar 1) :=
    (isWeakGradient_weakGradient ρ.sqrt_mem).memLp_grad.norm.integrable_sq
  have hpt : ∀ᵐ x ∂haar 1,
      ‖scalarScore A b ρ x‖ ^ 2 = 4 * ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 := by
    filter_upwards [h] with x hx
    unfold scalarScore
    rw [hx, smul_zero, add_zero, norm_smul]
    simp only [Real.norm_ofNat]
    ring
  unfold scalarDissipation
  rw [lintegral_congr_ae (hpt.mono fun x hx => by rw [hx]),
    ← ofReal_integral_eq_lintegral_ofReal (hI.const_mul 4)
      (Eventually.of_forall fun x => by positivity), integral_const_mul]

theorem ofReal_div_two_mul' {G : ℝ≥0} {I : ℝ} {D : ℝ≥0∞} (hD : D = ENNReal.ofReal I) {H : ℝ}
    (hH : (G : ℝ) = H) (hHpos : 0 < H) :
    D / (2 * (G : ℝ≥0∞)) = ENNReal.ofReal (I / (2 * H)) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), hD, ENNReal.ofReal_mul (by norm_num), ← hH,
    ENNReal.ofReal_coe_nnreal]
  simp

theorem entropy_pos_fh {t : ℝ} (ht1 : |t| < 1) (ht0 : t ≠ 0) (hle : |t| ≤ 1 / 2) :
    0 < Analysis.CircleMoments.firstHarmonicEntropy t := by
  obtain ⟨hp, hne, -⟩ := Analysis.CircleMoments.entropy_bounds hle ht0 ht1
  rw [Analysis.CircleMoments.firstHarmonicEntropy_of_lt ht1]
  exact ENNReal.toReal_pos hp.ne' hne

theorem scalarRate_le_a0 {A : InteractionData 1} (b : AbsoluteDrift A)
    (hF : ∀ (t : ℝ) (ht : |t| < 1),
      ∀ᵐ x ∂haar 1, b.force (Analysis.CircleMoments.firstHarmonicDensity t ht) x = 0)
    (hG : ∀ (t : ℝ) (ht : |t| < 1),
      (scalarGap A (Analysis.CircleMoments.firstHarmonicDensity t ht) : ℝ) =
        Analysis.CircleMoments.firstHarmonicEntropy t) :
    scalarRate A b ≤ ENNReal.ofReal (4 * Real.pi ^ 2) := by
  obtain ⟨ha0, -, -, -, hlim⟩ := Analysis.CircleMoments.circle_first_harmonic_estimates
  have ha0' : Analysis.CircleMoments.a0 = 4 * Real.pi ^ 2 := ha0
  rw [ha0'] at hlim
  have hlim' := ENNReal.tendsto_ofReal hlim
  have hev : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| < 1 / 2 ∧ t ≠ 0 := by
    refine Filter.Eventually.and ?_ self_mem_nhdsWithin
    have : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < 1 / 2 := by
      have := (continuous_abs.tendsto (0 : ℝ)).eventually
        (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1 / 2))
      simpa using this
    exact nhdsWithin_le_nhds this
  refine ge_of_tendsto hlim' ?_
  filter_upwards [hev] with t ⟨h1, h0⟩
  have ht1 : |t| < 1 := by linarith
  have hEpos := entropy_pos_fh ht1 h0 h1.le
  have hGr := hG t ht1
  have hpos : 0 < scalarGap A (Analysis.CircleMoments.firstHarmonicDensity t ht1) := by
    rw [← NNReal.coe_pos, hGr]; exact hEpos
  have hD : scalarDissipation A b (Analysis.CircleMoments.firstHarmonicDensity t ht1) =
      ENNReal.ofReal (Analysis.CircleMoments.firstHarmonicFisher t) := by
    rw [scalarDissipation_eq_fisher b _ (hF t ht1),
      Analysis.CircleMoments.firstHarmonicFisher_of_lt ht1]
  have hq : scalarQuotient A b (Analysis.CircleMoments.firstHarmonicDensity t ht1) =
      ENNReal.ofReal (Analysis.CircleMoments.firstHarmonicFisher t /
        (2 * Analysis.CircleMoments.firstHarmonicEntropy t)) := by
    unfold scalarQuotient
    exact ofReal_div_two_mul' hD hGr hEpos
  rw [← hq]
  exact scalarRate_le_quotient _ _ _ hpos

/-! ### (B) energies of the cutoff model -/

/-- The finite Fourier energy `∑_{n ≤ M} a_n |ν̂(n)|²`. -/
noncomputable def cutP (M : ℕ) (ν : ProbabilityMeasure (Torus 1)) : ℝ :=
  ∑ n ∈ Finset.range (M + 1), a n * ‖measureFourier ν n‖ ^ 2

/-- The finite Fourier energy of a density. -/
noncomputable def cutPd (M : ℕ) (σ : AbsoluteDensity 1) : ℝ :=
  ∑ n ∈ Finset.range (M + 1), a n * ‖fourierCoeff σ.density (freq n)‖ ^ 2

theorem cutP_densityMeasure (M : ℕ) (σ : AbsoluteDensity 1) :
    cutP M (densityMeasure σ) = cutPd M σ := by
  unfold cutP cutPd
  exact Finset.sum_congr rfl fun n _ => by rw [h1011_measureFourier]

theorem cutP_nonneg (M : ℕ) (ν : ProbabilityMeasure (Torus 1)) : 0 ≤ cutP M ν :=
  Finset.sum_nonneg fun n _ => mul_nonneg (a_nonneg n) (sq_nonneg _)

theorem sum_Icc_eq_range (M : ℕ) (f : ℕ → ℝ) (hf : ∀ n, n < 2 → f n = 0) :
    ∑ n ∈ Finset.Icc 2 M, f n = ∑ n ∈ Finset.range (M + 1), f n := by
  refine Finset.sum_subset ?_ fun n hn hn' => hf n ?_
  · intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2)
  · by_contra hc
    exact hn' (Finset.mem_Icc.mpr ⟨by omega, by
      have := Finset.mem_range.mp hn; omega⟩)

theorem cut_interactionEnergy (M : ℕ) (ν : ProbabilityMeasure (Torus 1)) :
    interactionEnergy (positiveH1Cutoff M) ν = kappa * (cutP M ν - RM M 0) := by
  have hcn : ∀ n : ℕ, Continuous fun p : Torus 1 × Torus 1 => a n * cosMode n (p.1 - p.2) :=
    fun n => continuous_const.mul ((continuous_cosMode n).comp (continuous_fst.sub continuous_snd))
  have hi : ∀ n : ℕ, Integrable (fun p : Torus 1 × Torus 1 => a n * cosMode n (p.1 - p.2))
      ((ν : Measure (Torus 1)).prod (ν : Measure (Torus 1))) := fun n =>
    (hcn n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hc : Continuous fun p : Torus 1 × Torus 1 => RM M (p.1 - p.2) :=
    (continuous_RM M).comp (continuous_fst.sub continuous_snd)
  have hRi : Integrable (fun p : Torus 1 × Torus 1 => RM M (p.1 - p.2))
      ((ν : Measure (Torus 1)).prod (ν : Measure (Torus 1))) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hE : ∫ p : Torus 1 × Torus 1, RM M (p.1 - p.2)
      ∂((ν : Measure (Torus 1)).prod (ν : Measure (Torus 1))) = cutP M ν := by
    unfold RM cutP
    rw [integral_finsetSum _ fun n _ => hi n]
    rw [sum_Icc_eq_range M (fun n => ∫ p : Torus 1 × Torus 1, a n * cosMode n (p.1 - p.2)
      ∂((ν : Measure (Torus 1)).prod (ν : Measure (Torus 1)))) (fun n hn => by
        simp [a_zero_of_lt hn])]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, integral_cosMode_sub]
  show ∫ p : Torus 1 × Torus 1, kappa * (RM M (p.1 - p.2) - RM M 0) ∂_ = _
  rw [integral_const_mul, integral_sub hRi (integrable_const _), hE]
  simp

theorem cut_freeEnergy_eq (M : ℕ) (ν : ProbabilityMeasure (Torus 1)) :
    freeEnergy (positiveH1Cutoff M) ν =
      ((relativeEntropy (ν : Measure (Torus 1)) (haar 1) : ℝ≥0∞) : EReal) +
        ((-(kappa * RM M 0 / 2) + kappa / 2 * cutP M ν : ℝ) : EReal) := by
  unfold freeEnergy
  have hV : potentialEnergy (positiveH1Cutoff M) ν = 0 := by
    simp [potentialEnergy, positiveH1Cutoff]
  rw [hV, cut_interactionEnergy, add_assoc, ← EReal.coe_add]
  congr 2
  ring

theorem cutP_haar (M : ℕ) : cutP M (haarProbability 1) = 0 := by
  unfold cutP
  refine Finset.sum_eq_zero fun n _ => ?_
  by_cases hn : 2 ≤ n
  · have hne : -freq (n : ℤ) ≠ 0 := by
      intro h
      have := congrFun h 0
      simp [freq] at this
      omega
    have : measureFourier (haarProbability 1) n = 0 := by
      unfold measureFourier
      show ∫ x, UnitAddTorus.mFourier (-freq (n : ℤ)) x ∂haar 1 = 0
      rw [integral_mFourier]; simp [hne]
    rw [this]; simp
  · rw [a_zero_of_lt (by omega)]; simp

theorem cut_freeEnergy_haar (M : ℕ) :
    freeEnergy (positiveH1Cutoff M) (haarProbability 1) =
      ((-(kappa * RM M 0 / 2) : ℝ) : EReal) := by
  rw [cut_freeEnergy_eq, cutP_haar]
  show ((relativeEntropy (haar 1) (haar 1) : ℝ≥0∞) : EReal) + _ = _
  rw [relativeEntropy_self]
  simp

theorem freeEnergyMinimum_cut (M : ℕ) :
    freeEnergyMinimum (positiveH1Cutoff M) = ((-(kappa * RM M 0 / 2) : ℝ) : EReal) := by
  refine le_antisymm ?_ (le_iInf fun ν => ?_)
  · rw [← cut_freeEnergy_haar M]; exact iInf_le _ _
  · rw [cut_freeEnergy_eq]
    have h0 : (0 : EReal) ≤ ((relativeEntropy (ν : Measure (Torus 1)) (haar 1) : ℝ≥0∞) : EReal) :=
      EReal.coe_ennreal_nonneg _
    have hs : ((-(kappa * RM M 0 / 2) : ℝ) : EReal) ≤
        ((-(kappa * RM M 0 / 2) + kappa / 2 * cutP M ν : ℝ) : EReal) := by
      have := cutP_nonneg M ν
      have hk := kappa_pos
      exact_mod_cast (by nlinarith :
        -(kappa * RM M 0 / 2) ≤ -(kappa * RM M 0 / 2) + kappa / 2 * cutP M ν)
    exact hs.trans (le_add_of_nonneg_left h0)

theorem cut_freeEnergy_form (M : ℕ) (σ : ProbabilityMeasure (Torus 1)) :
    potentialEnergy (positiveH1Cutoff M) σ + (1 / 2 : ℝ) * interactionEnergy (positiveH1Cutoff M) σ
      - freeEnergyMinimumReal (positiveH1Cutoff M) = kappa / 2 * cutP M σ := by
  have hV : potentialEnergy (positiveH1Cutoff M) σ = 0 := by
    unfold potentialEnergy
    show ∫ x, (0 : ℝ) ∂(σ : Measure (Torus 1)) = 0
    simp
  have hF : freeEnergyMinimumReal (positiveH1Cutoff M) = -(kappa * RM M 0 / 2) := by
    have h := coe_freeEnergyMinimumReal (positiveH1Cutoff M)
    rw [freeEnergyMinimum_cut] at h
    exact EReal.coe_injective h
  rw [hV, hF, cut_interactionEnergy]; ring

theorem cut_gap_species (M : ℕ) (F : SpeciesFamily 1) :
    (speciesGap (positiveH1Cutoff M) F : ℝ) =
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal
        + kappa / 2 * cutPd M (barycenter F) := by
  rw [coe_speciesGap, speciesRawGap, ← cutP_densityMeasure, ← cut_freeEnergy_form M
    (densityMeasure (barycenter F))]
  simp only [densityMeasure]
  ring

theorem cut_gap_scalar (M : ℕ) (ρ : AbsoluteDensity 1) :
    (scalarGap (positiveH1Cutoff M) ρ : ℝ) =
      (relativeEntropy (densityMeasure ρ) (haar 1)).toReal + kappa / 2 * cutPd M ρ := by
  have h1 := coe_densityFreeEnergy (positiveH1Cutoff M) ρ
  rw [freeEnergy_eq_real (positiveH1Cutoff M) (densityMeasure ρ)
    (absoluteDensity_entropy_finite ρ).2.2.1] at h1
  have h2 := EReal.coe_injective h1
  rw [coe_scalarGap, h2, ← cutP_densityMeasure, ← cut_freeEnergy_form M (densityMeasure ρ)]
  ring

/-! ### (E') the force-free first harmonics -/

theorem conv_dRM_firstHarmonic (M : ℕ) (t : ℝ) (x : Torus 1) :
    conv (dRM M) (Analysis.CircleMoments.firstHarmonic t) x = 0 := by
  obtain ⟨z, rfl⟩ := lift1_exists x
  have hcos : Continuous Analysis.CircleMoments.cosMode :=
    Analysis.CircleMoments.continuous_cosMode
  have hsin : Continuous (sinMode 1) := continuous_sinMode 1
  have hpt : ∀ y : Torus 1, dRM M y * Analysis.CircleMoments.firstHarmonic t (lift1 z - y) =
      dRM M y + (t * Real.cos (2 * Real.pi * z)) *
          (dRM M y * Analysis.CircleMoments.cosMode y) +
        (t * Real.sin (2 * Real.pi * z)) * (dRM M y * sinMode 1 y) := by
    intro y
    obtain ⟨w, rfl⟩ := lift1_exists y
    rw [Harmonic.firstHarmonic_sub]; ring
  have hI0 : Integrable (dRM M) (haar 1) := (memLp_dRM M).integrable one_le_two
  have hIc : Integrable (fun y => dRM M y * Analysis.CircleMoments.cosMode y) (haar 1) :=
    (memLp_dRM M).integrable_mul (memLp_two_of_continuous hcos)
  have hIs : Integrable (fun y => dRM M y * sinMode 1 y) (haar 1) :=
    (memLp_dRM M).integrable_mul (memLp_two_of_continuous hsin)
  have o0 : ∫ y, dRM M y ∂haar 1 = 0 := Harmonic.integral_odd_eq_zero (dRM_neg M)
  have oc : ∫ y, dRM M y * Analysis.CircleMoments.cosMode y ∂haar 1 = 0 := by
    refine Harmonic.integral_dRM_mul_eq_zero M
      (fun n _ => Harmonic.integral_odd_eq_zero fun y => ?_) hcos
    rw [sinMode_neg, Harmonic.cosMode_one_eq, cosMode_neg]; ring
  have os : ∫ y, dRM M y * sinMode 1 y ∂haar 1 = 0 := by
    refine Harmonic.integral_dRM_mul_eq_zero M (fun n hn => ?_) hsin
    rw [integral_sinMode_mul n 1 (by omega) le_rfl]
    simp; omega
  show ∫ y, dRM M y * Analysis.CircleMoments.firstHarmonic t (lift1 z - y) ∂haar 1 = 0
  simp_rw [hpt]
  have hA : Integrable (fun y => dRM M y + (t * Real.cos (2 * Real.pi * z)) *
      (dRM M y * Analysis.CircleMoments.cosMode y)) (haar 1) := hI0.add (hIc.const_mul _)
  rw [integral_add hA (hIs.const_mul _),
    integral_add hI0 (hIc.const_mul _), integral_const_mul, integral_const_mul, o0, oc, os]
  simp

theorem cutPd_firstHarmonic (M : ℕ) {t : ℝ} (ht : |t| < 1) :
    cutPd M (Analysis.CircleMoments.firstHarmonicDensity t ht) = 0 := by
  unfold cutPd
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [Analysis.CircleMoments.firstHarmonicDensity_density ht]
  by_cases hn : 2 ≤ n
  · rw [Harmonic.coeff_freq_firstHarmonic t hn]; simp
  · rw [a_zero_of_lt (by omega)]; simp

theorem rough_scalarRate_le (b : AbsoluteDrift positiveH1) :
    scalarRate positiveH1 b ≤ ENNReal.ofReal (4 * Real.pi ^ 2) := by
  refine scalarRate_le_a0 b (fun t ht => ?_) (fun t ht => ?_)
  · filter_upwards [absoluteDrift_unique b positiveH1Drift
      (Analysis.CircleMoments.firstHarmonicDensity t ht)] with x hx
    rw [hx]; exact Harmonic.force_firstHarmonic ht x
  · rw [h1011_gap_scalar]
    have : P (Analysis.CircleMoments.firstHarmonicDensity t ht) = 0 := by
      show Harmonic.specP (Analysis.CircleMoments.firstHarmonicDensity t ht).density = 0
      rw [Analysis.CircleMoments.firstHarmonicDensity_density ht]
      exact Harmonic.specP_firstHarmonic t
    rw [this, Analysis.CircleMoments.firstHarmonicEntropy_of_lt ht]; ring

theorem cut_scalarRate_le (M : ℕ) (b : AbsoluteDrift (positiveH1Cutoff M)) :
    scalarRate (positiveH1Cutoff M) b ≤ ENNReal.ofReal (4 * Real.pi ^ 2) := by
  refine scalarRate_le_a0 b (fun t ht => ?_) (fun t ht => ?_)
  · filter_upwards [cut_force_ae M b (Analysis.CircleMoments.firstHarmonicDensity t ht)] with x hx
    rw [hx, Analysis.CircleMoments.firstHarmonicDensity_density ht, ← conv_comm,
      conv_dRM_firstHarmonic]
    simp
  · rw [cut_gap_scalar, cutPd_firstHarmonic M ht,
      Analysis.CircleMoments.firstHarmonicEntropy_of_lt ht]; ring

/-! ### (C) dissipation of the cutoff model -/

theorem core_gen {A : InteractionData 1} (ρ τ : AbsoluteDensity 1) (b : AbsoluteDrift A)
    (c : Torus 1 → ℝ) (hc : Continuous c)
    (hforce : ∀ᵐ x ∂haar 1, b.force τ x =
      (EuclideanSpace.single (0 : Fin 1) (kappa * c x) : Tangent 1)) :
    ∃ J : ℝ, 0 ≤ J ∧
      J = 4 * ∫ x, (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ∂haar 1
        + 2 * kappa * ∫ x, densityDeriv ρ x * c x ∂haar 1
        + kappa ^ 2 * ∫ x, ρ.density x * (c x) ^ 2 ∂haar 1 ∧
      ∫⁻ x, ENNReal.ofReal
        (‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force τ x‖ ^ 2) ∂haar 1
        = ENNReal.ofReal J := by
  set g0 : Torus 1 → ℝ := fun x => weakGradient ρ.sqrt ρ.sqrt_mem x 0 with hg0
  have hg : MemLp g0 2 (haar 1) :=
    memLp_coord_of_memLp (isWeakGradient_weakGradient ρ.sqrt_mem).memLp_grad 0
  have hcb : MemLp c ⊤ (haar 1) := memLp_of_cont hc _
  have hw : MemLp (fun x => ρ.sqrt x * c x) 2 (haar 1) := by
    have h : MemLp (ρ.sqrt * c) 2 (haar 1) := ρ.memLp_sqrt.smul hcb
    exact h
  have hpt : ∀ᵐ x ∂haar 1,
      ‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force τ x‖ ^ 2
        = 4 * g0 x ^ 2 + 4 * kappa * (g0 x * (ρ.sqrt x * c x))
          + kappa ^ 2 * (ρ.sqrt x * c x) ^ 2 := by
    filter_upwards [hforce] with x hx
    rw [hx, h1011_norm_sq]
    simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, ite_true,
      smul_eq_mul, hg0]
    ring
  have i1 : Integrable (fun x => g0 x ^ 2) (haar 1) := hg.integrable_sq
  have i2 : Integrable (fun x => g0 x * (ρ.sqrt x * c x)) (haar 1) := hg.integrable_mul hw
  have i3 : Integrable (fun x => (ρ.sqrt x * c x) ^ 2) (haar 1) := hw.integrable_sq
  have hint : ∫ x, ‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force τ x‖ ^ 2
        ∂haar 1 = 4 * ∫ x, g0 x ^ 2 ∂haar 1
        + 4 * kappa * ∫ x, g0 x * (ρ.sqrt x * c x) ∂haar 1
        + kappa ^ 2 * ∫ x, (ρ.sqrt x * c x) ^ 2 ∂haar 1 := by
    have j1 := i1.const_mul 4
    have j2 := i2.const_mul (4 * kappa)
    have j3 := i3.const_mul (kappa ^ 2)
    have h12 := integral_add j1 j2
    have h123 := integral_add (j1.add j2) j3
    simp only [Pi.add_apply] at h123
    rw [integral_congr_ae hpt, h123, h12, integral_const_mul, integral_const_mul,
      integral_const_mul]
  have hJ : 4 * ∫ x, g0 x ^ 2 ∂haar 1 + 2 * kappa * ∫ x, densityDeriv ρ x * c x ∂haar 1
        + kappa ^ 2 * ∫ x, ρ.density x * (c x) ^ 2 ∂haar 1
      = ∫ x, ‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force τ x‖ ^ 2
        ∂haar 1 := by
    rw [hint]
    have e1 : ∫ x, densityDeriv ρ x * c x ∂haar 1
        = 2 * ∫ x, g0 x * (ρ.sqrt x * c x) ∂haar 1 := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [densityDeriv, hg0]; ring
    have e2 : ∫ x, ρ.density x * (c x) ^ 2 ∂haar 1 = ∫ x, (ρ.sqrt x * c x) ^ 2 ∂haar 1 := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [AbsoluteDensity.density]; ring
    rw [e1, e2]; ring
  have hnn : 0 ≤ ∫ x, ‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force τ x‖ ^ 2
        ∂haar 1 := integral_nonneg fun x => sq_nonneg _
  have hI : Integrable (fun x => ‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x
      + ρ.sqrt x • b.force τ x‖ ^ 2) (haar 1) := by
    have := ((i1.const_mul 4).add (i2.const_mul (4 * kappa))).add (i3.const_mul (kappa ^ 2))
    refine this.congr ?_
    filter_upwards [hpt] with x hx
    rw [hx]; rfl
  refine ⟨_, hJ ▸ hnn, rfl, ?_⟩
  rw [hJ, ← ofReal_integral_eq_lintegral_ofReal hI (Eventually.of_forall fun x => sq_nonneg _)]

/-- The exact species dissipation expansion for the cutoff model. -/
noncomputable def cutX (M : ℕ) (F : SpeciesFamily 1) : ℝ :=
  ∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1)
    + 2 * kappa * ∑ n ∈ Finset.range (M + 1), qTerm (barycenter F) n
    + kappa ^ 2 * ∫ x, (barycenter F).density x *
        (conv (barycenter F).density (dRM M) x) ^ 2 ∂haar 1

theorem cut_species_dissipation (M : ℕ) (b : AbsoluteDrift (positiveH1Cutoff M))
    (F : SpeciesFamily 1) :
    0 ≤ cutX M F ∧ speciesDissipation (positiveH1Cutoff M) b F = ENNReal.ofReal (cutX M F) := by
  have hnorm : ∀ (ρ : AbsoluteDensity 1),
      ∫ x, (weakGradient ρ.sqrt ρ.sqrt_mem x 0) ^ 2 ∂haar 1
        = ∫ x, ‖weakGradient ρ.sqrt ρ.sqrt_mem x‖ ^ 2 ∂haar 1 := fun ρ =>
    integral_congr_ae (Eventually.of_forall fun x => (h1011_norm_sq _).symm)
  set c : Torus 1 → ℝ := conv (barycenter F).density (dRM M) with hc
  have hcc : Continuous c := conv_continuous (barycenter F).integrable_density (continuous_dRM M)
  choose J hJ0 hJ hl using fun s =>
    core_gen (F.density s) (barycenter F) b c hcc (cut_force_ae M b (barycenter F))
  have hB : ∀ s, Integrable (fun x => densityDeriv (F.density s) x * c x) (haar 1) := fun s =>
    h1011_int_mul_cont ((memLp_densityDeriv (F.density s)).integrable one_le_two) hcc
  have hC : ∀ s, Integrable (fun x => (F.density s).density x * (c x) ^ 2) (haar 1) := fun s =>
    h1011_int_mul_cont (F.density s).integrable_density (hcc.pow 2)
  have hBsum : ∑ s, F.weight s * ∫ x, densityDeriv (F.density s) x * c x ∂haar 1
      = ∑ n ∈ Finset.range (M + 1), qTerm (barycenter F) n := by
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun s _ => (hB s).const_mul (F.weight s)]
    rw [← partial_eq (barycenter F) M]
    refine integral_congr_ae ?_
    filter_upwards [h1011_bary_deriv F] with x hx
    rw [hx, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  have hCsum : ∑ s, F.weight s * ∫ x, (F.density s).density x * (c x) ^ 2 ∂haar 1
      = ∫ x, (barycenter F).density x * (c x) ^ 2 ∂haar 1 := by
    simp_rw [← integral_const_mul]
    rw [← integral_finsetSum _ fun s _ => (hC s).const_mul (F.weight s)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [F.barycenter_density_apply x, Finset.sum_mul]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [AbsoluteDensity.density]; ring
  have hX : ∑ s, F.weight s * J s = cutX M F := by
    unfold cutX
    rw [← hBsum, ← hCsum]
    have : ∀ s, F.weight s * J s = F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1)
        + 2 * kappa * (F.weight s * ∫ x, densityDeriv (F.density s) x * c x ∂haar 1)
        + kappa ^ 2 * (F.weight s * ∫ x, (F.density s).density x * (c x) ^ 2 ∂haar 1) := by
      intro s
      rw [hJ s]
      simp only [SpeciesFamily.sqrtGradient]
      rw [hnorm (F.density s)]
      ring
    simp_rw [this, Finset.sum_add_distrib, ← Finset.mul_sum]
  refine ⟨?_, ?_⟩
  · rw [← hX]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (F.weight_nonneg s) (hJ0 s)
  · rw [← hX]
    unfold speciesDissipation
    rw [ENNReal.ofReal_sum_of_nonneg fun s _ => mul_nonneg (F.weight_nonneg s) (hJ0 s)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ENNReal.ofReal_mul (F.weight_nonneg s)]
    congr 1
    exact hl s

/-! ### (D) the cutoff lower bound -/

theorem cut_lower_nonneg (M : ℕ) (F : SpeciesFamily 1) :
    0 ≤ cutX M F - 2 * (4 * Real.pi ^ 2) *
      (∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal
        + kappa / 2 * cutPd M (barycenter F)) := by
  have hT : ∑ n ∈ Finset.range (M + 1), (2 * (2 * Real.pi * n) ^ 2 - 4 * Real.pi ^ 2) * a n *
        ‖fourierCoeff (barycenter F).density (freq n)‖ ^ 2
      = 2 * ∑ n ∈ Finset.range (M + 1), qTerm (barycenter F) n
        - 4 * Real.pi ^ 2 * cutPd M (barycenter F) := by
    unfold cutPd qTerm
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  have hsp : ∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1
          - 2 * (4 * Real.pi ^ 2) *
            (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal)
      = ∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1)
        - 2 * (4 * Real.pi ^ 2) *
          ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hkey : cutX M F - 2 * (4 * Real.pi ^ 2) *
      (∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal
        + kappa / 2 * cutPd M (barycenter F))
      = ∑ s, F.weight s * (4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1
          - 2 * (4 * Real.pi ^ 2) *
            (relativeEntropy (densityMeasure (F.density s)) (haar 1)).toReal)
        + kappa * ∑ n ∈ Finset.range (M + 1), (2 * (2 * Real.pi * n) ^ 2 - 4 * Real.pi ^ 2) *
            a n * ‖fourierCoeff (barycenter F).density (freq n)‖ ^ 2
        + kappa ^ 2 * ∫ x, (barycenter F).density x *
            (conv (barycenter F).density (dRM M) x) ^ 2 ∂haar 1 := by
    rw [hsp, hT]; unfold cutX; ring
  rw [hkey]
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · refine Finset.sum_nonneg fun s _ => mul_nonneg (F.weight_nonneg s) ?_
    obtain ⟨-, -, h⟩ := haar_circle_lsi (F.density s)
    rw [circleEntropy_eq_relativeEntropy] at h
    have : 4 * ∫ x, ‖F.sqrtGradient s x‖ ^ 2 ∂haar 1
        = Analysis.circleFisherInformation (F.density s) := rfl
    linarith
  · refine mul_nonneg (by unfold kappa; norm_num) (Finset.sum_nonneg fun n _ => ?_)
    exact h1012_term_nonneg n _ (sq_nonneg _)
  · refine mul_nonneg (sq_nonneg _) (integral_nonneg fun x => ?_)
    exact mul_nonneg ((barycenter F).density_nonneg x) (sq_nonneg _)

theorem cut_speciesRate_ge (M : ℕ) (b : AbsoluteDrift (positiveH1Cutoff M)) :
    ENNReal.ofReal (4 * Real.pi ^ 2) ≤ speciesRate (positiveH1Cutoff M) b := by
  refine le_iInf fun F => ?_
  obtain ⟨-, hD⟩ := cut_species_dissipation M b F.1
  have hG := cut_gap_species M F.1
  have hm := cut_lower_nonneg M F.1
  have hpos : (0 : ℝ) < (speciesGap (positiveH1Cutoff M) F.1 : ℝ) := by exact_mod_cast F.2
  unfold speciesQuotient
  rw [hD]
  have hne : (2 * (speciesGap (positiveH1Cutoff M) F.1 : ℝ≥0∞)) ≠ 0 := by
    have := F.2
    simpa using this.ne'
  rw [ENNReal.le_div_iff_mul_le (Or.inl hne) (Or.inl (ENNReal.mul_ne_top (by simp)
    ENNReal.coe_ne_top))]
  have e : ENNReal.ofReal (4 * Real.pi ^ 2) * (2 * (speciesGap (positiveH1Cutoff M) F.1 : ℝ≥0∞))
      = ENNReal.ofReal (4 * Real.pi ^ 2 * (2 * (speciesGap (positiveH1Cutoff M) F.1 : ℝ))) := by
    have h2 : ENNReal.ofReal (2 * (speciesGap (positiveH1Cutoff M) F.1 : ℝ))
        = 2 * (speciesGap (positiveH1Cutoff M) F.1 : ℝ≥0∞) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_coe_nnreal]
      simp
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2), h2]
  rw [e]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hG]
  linarith

/-- **H1014.** Exact nonlinear rates: for the rough positive-`H¹` model and for every fixed
cutoff `W_M` (`M ≥ 2`), the canonical absolute-domain rates satisfy
`r_* = r_ms = a0 = 4π²`. -/
theorem exact_nonlinear_rates_for_rough_and_every_fixed_smooth_cutoff :
    (∀ b : AbsoluteDrift positiveH1,
      scalarRate positiveH1 b = ENNReal.ofReal (4 * Real.pi ^ 2) ∧
      speciesRate positiveH1 b = ENNReal.ofReal (4 * Real.pi ^ 2)) ∧
    (∀ M : ℕ, 2 ≤ M → ∀ b : AbsoluteDrift (positiveH1Cutoff M),
      scalarRate (positiveH1Cutoff M) b = ENNReal.ofReal (4 * Real.pi ^ 2) ∧
      speciesRate (positiveH1Cutoff M) b = ENNReal.ofReal (4 * Real.pi ^ 2)) := by
  refine ⟨fun b => ?_, fun M _ b => ?_⟩
  · obtain ⟨hms, -, -⟩ := uniform_nonlinear_lower_bound.2 b
    have hup := rough_scalarRate_le b
    have hle := speciesRate_le_scalarRate positiveH1 b
    exact ⟨le_antisymm hup (hms.trans hle), le_antisymm (hle.trans hup) hms⟩
  · have hms := cut_speciesRate_ge M b
    have hup := cut_scalarRate_le M b
    have hle := speciesRate_le_scalarRate (positiveH1Cutoff M) b
    exact ⟨le_antisymm hup (hms.trans hle), le_antisymm (hle.trans hup) hms⟩

end DGPS.Examples.PositiveH1.Nonlinear
