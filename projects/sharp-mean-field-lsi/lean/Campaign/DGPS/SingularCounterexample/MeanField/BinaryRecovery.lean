import DGPS.SingularCounterexample.MeanField.SpeciesPL

/-! # Binary first-harmonic recovery for the species PL rate -/

open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.SingularCounterexample

open Analysis.CircleMoments

/-- SLC-S008: two opposite first harmonics, with equal positive weights. -/
noncomputable def binaryRecovery (t : ℝ) (ht : |t| < 1) : SpeciesFamily 1 :=
  SpeciesFamily.uniform 2 fun s =>
    if s.val = 0 then firstHarmonicDensity t ht
    else firstHarmonicDensity (-t) (by simpa using ht)

/-- SLC-S009: both species are absolute densities, with weight `1/2`. -/
theorem binaryRecovery_weight (t : ℝ) (ht : |t| < 1)
    (s : Fin (binaryRecovery t ht).count) :
    (binaryRecovery t ht).weight s = 1 / 2 := rfl

theorem binaryRecovery_density (t : ℝ) (ht : |t| < 1)
    (s : Fin (binaryRecovery t ht).count) (x : Torus 1) :
    ((binaryRecovery t ht).density s).density x =
      if s.val = 0 then 1 + t * cosMode x else 1 - t * cosMode x := by
  simp only [binaryRecovery, SpeciesFamily.uniform]
  split_ifs
  · simp [firstHarmonicDensity_density, firstHarmonic]
  · simp [firstHarmonicDensity_density, firstHarmonic]
    ring

theorem binaryRecovery_density_pos (t : ℝ) (ht : |t| < 1)
    (s : Fin (binaryRecovery t ht).count) (x : Torus 1) :
    0 < ((binaryRecovery t ht).density s).density x := by
  simp only [binaryRecovery, SpeciesFamily.uniform]
  split_ifs
  · rw [firstHarmonicDensity_density]
    exact firstHarmonic_pos ht x
  · rw [firstHarmonicDensity_density]
    exact firstHarmonic_pos (by simpa using ht) x

/-- SLC-S010: the opposite harmonics cancel exactly in the barycenter. -/
theorem binaryRecovery_barycenter_density (t : ℝ) (ht : |t| < 1) :
    (barycenter (binaryRecovery t ht)).density = fun _ => 1 := by
  funext x
  rw [species_barycenter_density]
  change (∑ s : Fin 2, (1 / 2 : ℝ) *
    (if s.val = 0 then (firstHarmonicDensity t ht).density x
      else (firstHarmonicDensity (-t) (by simpa using ht)).density x)) = 1
  simp [Fin.sum_univ_two, firstHarmonicDensity_density, firstHarmonic]
  ring

theorem binaryRecovery_interactionGap (k : Torus 1 → ℝ) (t : ℝ) (ht : |t| < 1) :
    interactionGap k (barycenter (binaryRecovery t ht)) = 0 := by
  simp [interactionGap, binaryRecovery_barycenter_density]

theorem binaryRecovery_densityDeriv (t : ℝ) (ht : |t| < 1) :
    densityDeriv (barycenter (binaryRecovery t ht)) =ᵐ[haar 1] 0 := by
  have hg := density_weak_gradient (barycenter (binaryRecovery t ht))
  rw [binaryRecovery_barycenter_density] at hg
  have he := hg.ae_eq (isWeakGradient_const 1)
  filter_upwards [he] with x hx
  have hc := congrArg (fun v : Tangent 1 => v 0) hx
  simpa [densityDeriv, Examples.PositiveH1.Nonlinear.densityDeriv] using hc

theorem binaryRecovery_force (k : Torus 1 → ℝ) (hk : MemLp k 2 (haar 1))
    (t : ℝ) (ht : |t| < 1) :
    singularForce k (barycenter (binaryRecovery t ht)) = fun _ => 0 := by
  funext x
  have hb := conv_densityDeriv_bound k hk (barycenter (binaryRecovery t ht)) x
  have hz : (∫ y, (densityDeriv (barycenter (binaryRecovery t ht)) y) ^ 2 ∂haar 1) = 0 := by
    have he := binaryRecovery_densityDeriv t ht
    calc
      _ = ∫ _ : Torus 1, (0 : ℝ) ∂haar 1 := integral_congr_ae (he.mono fun y hy => by simp [hy])
      _ = 0 := integral_zero _ _
  rw [hz, Real.sqrt_zero, mul_zero] at hb
  exact abs_nonpos_iff.mp hb

private theorem firstHarmonic_entropy (t : ℝ) (ht : |t| < 1) :
    Analysis.circleEntropy (firstHarmonicDensity t ht) = firstHarmonicEntropy t := by
  rw [circleEntropy_eq_relativeEntropy, firstHarmonicEntropy_of_lt ht]

private theorem firstHarmonic_fisher (t : ℝ) (ht : |t| < 1) :
    Analysis.circleFisherInformation (firstHarmonicDensity t ht) = firstHarmonicFisher t := by
  rw [firstHarmonicFisher_of_lt ht]
  rfl

theorem binaryRecovery_gap (k : Torus 1 → ℝ) (t : ℝ) (ht : |t| < 1) :
    speciesGap k (binaryRecovery t ht) =
      (firstHarmonicEntropy t + firstHarmonicEntropy (-t)) / 2 := by
  rw [speciesGap, binaryRecovery_interactionGap]
  change (∑ s : Fin 2, (1 / 2 : ℝ) * Analysis.circleEntropy
    ((binaryRecovery t ht).density s)) + (1 / 2 : ℝ) * 0 = _
  simp [Fin.sum_univ_two, binaryRecovery, SpeciesFamily.uniform,
    firstHarmonic_entropy]
  ring

theorem binaryRecovery_dissipation (k : Torus 1 → ℝ) (hk : MemLp k 2 (haar 1))
    (t : ℝ) (ht : |t| < 1) :
    speciesDissipation k (binaryRecovery t ht) =
      (firstHarmonicFisher t + firstHarmonicFisher (-t)) / 2 := by
  rw [speciesDissipation_expansion k hk, binaryRecovery_force k hk]
  change (∑ s : Fin 2, (1 / 2 : ℝ) * Analysis.circleFisherInformation
    ((binaryRecovery t ht).density s)) + 2 * (∫ x, _ * 0 ∂haar 1) + (∫ x, _ * 0 ^ 2 ∂haar 1) = _
  simp [Fin.sum_univ_two, binaryRecovery, SpeciesFamily.uniform,
    firstHarmonic_fisher]
  ring

end DGPS.SingularCounterexample

namespace DGPS.SingularCounterexample
open Analysis.CircleMoments

private theorem quadratic_limit (f : ℝ → ℝ) (A C : ℝ)
    (h : ∀ᶠ t in 𝓝[≠] (0 : ℝ), |f t - A * t ^ 2| ≤ C * t ^ 4) :
    Tendsto (fun t => f t / t ^ 2) (𝓝[≠] 0) (𝓝 A) := by
  have hsmall : Tendsto (fun t : ℝ => C * t ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    have hc : Tendsto (fun t : ℝ => C * t ^ 2) (𝓝 0) (𝓝 (C * 0 ^ 2)) :=
      (continuous_const.mul (continuous_pow 2)).tendsto 0
    simpa using hc.mono_left nhdsWithin_le_nhds
  have hz : Tendsto (fun t => f t / t ^ 2 - A) (𝓝[≠] 0) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hsmall
    filter_upwards [h, self_mem_nhdsWithin] with t ht ht0
    have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht0
    rw [Real.norm_eq_abs]
    have he : f t / t ^ 2 - A = (f t - A * t ^ 2) / t ^ 2 := by field_simp [show t ≠ 0 from ht0]
    rw [he, abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
    calc
      _ ≤ C * t ^ 4 := ht
      _ = C * t ^ 2 * t ^ 2 := by ring
  simpa using hz.add_const A

private theorem binaryRecovery_small :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), |t| < 1 / 2 ∧ t ≠ 0 := by
  refine Filter.Eventually.and ?_ self_mem_nhdsWithin
  exact nhdsWithin_le_nhds ((continuous_abs.tendsto (0 : ℝ)).eventually
    (gt_mem_nhds (by norm_num : |(0 : ℝ)| < 1 / 2)))

/-- SLC-S011: the real binary recovery quotient tends to the sharp Haar rate. -/
theorem binaryRecovery_quotient_limit :
    Tendsto (fun t : ℝ =>
      (firstHarmonicFisher t + firstHarmonicFisher (-t)) /
        (2 * (firstHarmonicEntropy t + firstHarmonicEntropy (-t))))
      (𝓝[≠] 0) (𝓝 (4 * Real.pi ^ 2)) := by
  have hH : Tendsto (fun t : ℝ =>
      (firstHarmonicEntropy t + firstHarmonicEntropy (-t)) / t ^ 2)
      (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    apply quadratic_limit _ _ (7 / 4)
    filter_upwards [binaryRecovery_small] with t ⟨ht, ht0⟩
    have ht1 : |t| < 1 := by linarith
    have hp := (entropy_bounds ht.le ht0 ht1).2.2
    have hm := (entropy_bounds (t := -t) (by simpa using ht.le)
      (neg_ne_zero.mpr ht0) (by simpa using ht1)).2.2
    have he : |t| ^ 4 = t ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]; ring
    simp only [abs_neg, neg_sq] at hm
    rw [he] at hp hm
    have hab := abs_add_le (firstHarmonicEntropy t - t ^ 2 / 4)
      (firstHarmonicEntropy (-t) - t ^ 2 / 4)
    have heq : firstHarmonicEntropy t + firstHarmonicEntropy (-t) - 1 / 2 * t ^ 2 =
      (firstHarmonicEntropy t - t ^ 2 / 4) +
        (firstHarmonicEntropy (-t) - t ^ 2 / 4) := by ring
    rw [heq]
    linarith
  have hI : Tendsto (fun t : ℝ =>
      (firstHarmonicFisher t + firstHarmonicFisher (-t)) / t ^ 2)
      (𝓝[≠] 0) (𝓝 (4 * Real.pi ^ 2)) := by
    apply quadratic_limit _ _ (8 * Real.pi ^ 2)
    filter_upwards [binaryRecovery_small] with t ⟨ht, ht0⟩
    have ht1 : |t| < 1 := by linarith
    have hp := fisher_bounds ht.le ht1
    have hm := fisher_bounds (t := -t) (by simpa using ht.le) (by simpa using ht1)
    have he : |t| ^ 4 = t ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]; ring
    simp only [abs_neg, neg_sq] at hm
    rw [he] at hp hm
    change |firstHarmonicFisher t - 4 * Real.pi ^ 2 * t ^ 2 / 2| ≤ _ at hp
    change |firstHarmonicFisher (-t) - 4 * Real.pi ^ 2 * t ^ 2 / 2| ≤ _ at hm
    have hab := abs_add_le (firstHarmonicFisher t - 4 * Real.pi ^ 2 * t ^ 2 / 2)
      (firstHarmonicFisher (-t) - 4 * Real.pi ^ 2 * t ^ 2 / 2)
    have heq : firstHarmonicFisher t + firstHarmonicFisher (-t) - 4 * Real.pi ^ 2 * t ^ 2 =
      (firstHarmonicFisher t - 4 * Real.pi ^ 2 * t ^ 2 / 2) +
        (firstHarmonicFisher (-t) - 4 * Real.pi ^ 2 * t ^ 2 / 2) := by ring
    rw [heq]
    nlinarith
  have hq := hI.div (hH.const_mul 2) (by norm_num)
  norm_num at hq
  refine hq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht0
  simp only [Pi.div_apply]
  rw [← mul_div_assoc, div_div_div_cancel_right₀ (pow_ne_zero 2 ht0)]

theorem binaryRecovery_gap_pos (k : Torus 1 → ℝ) (t : ℝ) (ht : |t| < 1)
    (ht0 : t ≠ 0) (htsmall : |t| ≤ 1 / 2) :
    0 < speciesGap k (binaryRecovery t ht) := by
  rw [binaryRecovery_gap]
  have hp := entropy_bounds htsmall ht0 ht
  have hm := entropy_bounds (t := -t) (by simpa using htsmall)
    (neg_ne_zero.mpr ht0) (by simpa using ht)
  have hpos : 0 < firstHarmonicEntropy t := by
    rw [firstHarmonicEntropy_of_lt ht]
    exact ENNReal.toReal_pos hp.1.ne' hp.2.1
  have hmpos : 0 < firstHarmonicEntropy (-t) := by
    rw [firstHarmonicEntropy_of_lt (show |-t| < 1 by simpa using ht)]
    exact ENNReal.toReal_pos hm.1.ne' hm.2.1
  positivity

/-- The actual species quotient along the admissible binary family has the sharp limit. -/
theorem binaryRecovery_speciesQuotient_limit (k : Torus 1 → ℝ)
    (hk : MemLp k 2 (haar 1)) :
    Tendsto (fun t : ℝ => if ht : |t| < 1 then speciesQuotient k (binaryRecovery t ht) else 0)
      (𝓝[≠] 0) (𝓝 (ENNReal.ofReal (4 * Real.pi ^ 2))) := by
  have hlim := (ENNReal.continuous_ofReal.tendsto (4 * Real.pi ^ 2)).comp
    binaryRecovery_quotient_limit
  apply hlim.congr'
  filter_upwards [binaryRecovery_small] with t ⟨ht, _⟩
  have ht1 : |t| < 1 := by linarith
  rw [dite_eq_left ht1, speciesQuotient, binaryRecovery_dissipation k hk, binaryRecovery_gap]
  simp only [Function.comp_apply]
  congr 1
  symm
  rw [← mul_div_assoc, div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]

theorem species_PL_rate_upper (k : Torus 1 → ℝ) (hk : MemLp k 2 (haar 1)) :
    singularSpeciesPLRate k ≤ ENNReal.ofReal (4 * Real.pi ^ 2) := by
  have hlim := (ENNReal.continuous_ofReal.tendsto (4 * Real.pi ^ 2)).comp
    binaryRecovery_quotient_limit
  apply ge_of_tendsto hlim
  filter_upwards [binaryRecovery_small] with t ⟨ht, ht0⟩
  have ht1 : |t| < 1 := by linarith
  have hle := iInf_le (fun F : {F : SpeciesFamily 1 // 0 < speciesGap k F} =>
    speciesQuotient k F.1) ⟨binaryRecovery t ht1, binaryRecovery_gap_pos k t ht1 ht0 ht.le⟩
  change singularSpeciesPLRate k ≤ _ at hle
  convert hle using 1
  unfold speciesQuotient
  rw [binaryRecovery_dissipation k hk, binaryRecovery_gap]
  simp only [Function.comp_apply]
  congr 1
  symm
  rw [← mul_div_assoc, div_div_div_cancel_right₀ (by norm_num : (2 : ℝ) ≠ 0)]

/-- SLC-S012: the optimal species PL rate is exactly the sharp Haar circle rate. -/
theorem species_PL_rate_exact (k : Circle → ℝ) (hk : MemLp k 2 (haar 1))
    (hfourier : HasNonnegNonzeroFourier k) :
    singularSpeciesPLRate k = ENNReal.ofReal (4 * Real.pi ^ 2) :=
  le_antisymm (species_PL_rate_upper k hk) (species_PL_rate_lower k hk hfourier)

end DGPS.SingularCounterexample
