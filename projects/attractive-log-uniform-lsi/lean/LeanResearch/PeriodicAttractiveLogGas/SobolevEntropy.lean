import LeanResearch.PeriodicAttractiveLogGas.DensityEntropy

/-! Appendix A: the entropy consequence of a Sobolev exponent strictly
above two. Jensen is applied to the actual square-weighted probability;
homogeneity includes zero squared mass. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal NNReal
namespace PeriodicAttractiveLogGas.SobolevEntropy
open EntropyMoment DensityMoments
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

lemma square_mul_rpow {p : ℝ} (hp : 2 < p) (x : ℝ) :
    x ^ 2 * |x| ^ (p - 2) = |x| ^ p := by
  rw [← sq_abs, ← Real.rpow_two,
    ← Real.rpow_add_of_nonneg (abs_nonneg x) (by norm_num) (by linarith)]
  congr 1
  ring

/-- The normalized source Jensen inequality, with no positivity assumption
on the observable. Zeros are null only for its square-weighted probability. -/
theorem normalized_entropy [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    {p : ℝ} (hp : 2 < p) (hmass : (∫ x, f x ^ 2 ∂μ) = 1) :
    Rothaus.squareEntropy μ f ≤
      p / (p - 2) * Real.log (lpNorm f (ENNReal.ofReal p) μ ^ 2) := by
  obtain ⟨M, hM⟩ := hb
  have h3 := integrable_abs_cube_bounded (μ := μ) hf hM
  have h2 := integrable_sq_of_integrable_abs_cube hf h3
  let ν := squareWeightedMeasure μ f
  let : IsProbabilityMeasure ν := squareWeightedMeasure_isProbability h2 hmass
  let g : α → ℝ := fun x => |f x| ^ (p - 2)
  have hp0 : 0 < p := by linarith
  have hg0 (x : α) : 0 ≤ g x := Real.rpow_nonneg (abs_nonneg _) _
  have hgi : Integrable g ν := by
    apply (integrable_squareWeightedMeasure_iff hf).mpr
    have hh := integrable_norm_rpow_bounded (μ := μ) hf ⟨M, hM⟩ hp0.le
    simpa only [g, square_mul_rpow hp, Real.norm_eq_abs] using hh
  have hgp : ∀ᵐ x ∂ν, 0 < g x :=
    (ae_abs_pos_squareWeightedMeasure hf).mono fun x hx => Real.rpow_pos_of_pos hx _
  have hlogeq : (fun x => Real.log (g x)) =ᵐ[ν]
      (fun x => (p - 2) * Real.log |f x|) := by
    filter_upwards [ae_abs_pos_squareWeightedMeasure hf] with x hx
    exact Real.log_rpow hx _
  have hlog : Integrable (fun x => Real.log (g x)) ν :=
    ((integrable_log_abs_squareWeightedMeasure hf h3).const_mul (p - 2)).congr hlogeq.symm
  have hgpos : 0 < ∫ x, g x ∂ν := by
    have hnonneg : 0 ≤ ∫ x, g x ∂ν := integral_nonneg hg0
    by_contra hn
    have hz : (∫ x, g x ∂ν) = 0 := le_antisymm (le_of_not_gt hn) hnonneg
    have hae := (integral_eq_zero_iff_of_nonneg hg0 hgi).mp hz
    obtain ⟨x, hx, hx0⟩ := (hgp.and hae).exists
    exact (ne_of_gt hx) hx0
  have hmoment : (∫ x, g x ∂ν) = ∫ x, |f x| ^ p ∂μ := by
    rw [integral_squareWeightedMeasure hf]
    exact integral_congr_ae (Eventually.of_forall fun x => square_mul_rpow hp (f x))
  have hj := integral_log_le_log_integral hgi hlog hgp hgpos
  rw [integral_congr_ae hlogeq, integral_const_mul, hmoment] at hj
  have hnorm : lpNorm f (ENNReal.ofReal p) μ ^ p = ∫ x, |f x| ^ p ∂μ := by
    simpa only [Real.norm_eq_abs] using lpNorm_rpow_eq_integral hp0 hf.aestronglyMeasurable
  have hnp : 0 < lpNorm f (ENNReal.ofReal p) μ := by
    have hnn := lpNorm_nonneg (f := f) (p := ENNReal.ofReal p) (μ := μ)
    by_contra hn
    have hz : lpNorm f (ENNReal.ofReal p) μ = 0 := le_antisymm (le_of_not_gt hn) hnn
    rw [← hnorm, hz, Real.zero_rpow hp0.ne'] at hmoment
    rw [hmoment] at hgpos
    exact (lt_irrefl (0 : ℝ)) hgpos
  rw [← hnorm, Real.log_rpow hnp] at hj
  have he : Rothaus.squareEntropy μ f = 2 * ∫ x, Real.log |f x| ∂ν := by
    unfold Rothaus.squareEntropy
    rw [hmass, Real.log_one, mul_zero, sub_zero, integral_squareWeightedMeasure hf]
    simp_rw [sq_mul_log_sq_eq]
    exact integral_const_mul _ _
  rw [he, Real.log_pow]
  have hdiv : (∫ x, Real.log |f x| ∂ν) ≤
      (p * Real.log (lpNorm f (ENNReal.ofReal p) μ)) / (p - 2) :=
    (le_div_iff₀ (by linarith : 0 < p - 2)).mpr (by nlinarith only [hj])
  calc
    _ ≤ 2 * ((p * Real.log (lpNorm f (ENNReal.ofReal p) μ)) / (p - 2)) :=
      mul_le_mul_of_nonneg_left hdiv (by norm_num)
    _ = _ := by norm_num only [Nat.cast_ofNat]; ring

/-- Normalized defective entropy, before restoring arbitrary squared mass. -/
theorem normalized_defective [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    {p K₁ K₂ E : ℝ} (hp : 2 < p) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hE : 0 ≤ E) (hmass : (∫ x, f x ^ 2 ∂μ) = 1)
    (hSob : lpNorm f (ENNReal.ofReal p) μ ≤ K₁ * Real.sqrt E + K₂) :
    Rothaus.squareEntropy μ f ≤
      p / (p - 2) * (2 * K₁ ^ 2 * E + 2 * K₂ ^ 2 - 1) := by
  have hh := normalized_entropy hf hb hp hmass
  have hge : (1 : ℝ) ≤ lpNorm f (ENNReal.ofReal p) μ := by
    have htwo : lpNorm f 2 μ = 1 := by
      rw [DensityEntropy.lpNorm_two_sqrt hf.aestronglyMeasurable]
      simp only [Real.norm_eq_abs, sq_abs, hmass, Real.sqrt_one]
    rw [← htwo]
    apply lpNorm_mono_exponent (memLp_of_bounded hf hb _)
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp.le
  have hlog := Real.log_le_sub_one_of_pos (sq_pos_of_pos (zero_lt_one.trans_le hge))
  have hsq := pow_le_pow_left₀ lpNorm_nonneg hSob 2
  have hS : (K₁ * Real.sqrt E + K₂) ^ 2 ≤ 2 * K₁ ^ 2 * E + 2 * K₂ ^ 2 := by
    nlinarith [sq_nonneg (K₁ * Real.sqrt E - K₂), Real.sq_sqrt hE]
  exact hh.trans (mul_le_mul_of_nonneg_left (hlog.trans (by linarith only [hsq, hS]))
    (div_nonneg (by linarith) (by linarith)))


/-- Source homogeneity restores every bounded observable, including zero
squared mass. The actual energy argument may vanish. -/
theorem defective [IsProbabilityMeasure μ] {f : α → ℝ}
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    {p K₁ K₂ E : ℝ} (hp : 2 < p) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hE : 0 ≤ E)
    (hSob : lpNorm f (ENNReal.ofReal p) μ ≤ K₁ * Real.sqrt E + K₂ * lpNorm f 2 μ) :
    Rothaus.squareEntropy μ f ≤
      p / (p - 2) * (2 * K₁ ^ 2 * E + (2 * K₂ ^ 2 - 1) * ∫ x, f x ^ 2 ∂μ) := by
  let M := ∫ x, f x ^ 2 ∂μ
  have hM : 0 ≤ M := integral_nonneg fun x => sq_nonneg (f x)
  by_cases hz : M = 0
  · rw [EntropyScaling.squareEntropy_zero_mass hf hb hz]
    change 0 ≤ p / (p - 2) * (2 * K₁ ^ 2 * E + (2 * K₂ ^ 2 - 1) * M)
    rw [hz, mul_zero, add_zero]
    exact mul_nonneg (div_nonneg (by linarith) (by linarith)) (by positivity)
  have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hz)
  let a := (Real.sqrt M)⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr hMp)
  have haM : a * Real.sqrt M = 1 := inv_mul_cancel₀ (Real.sqrt_pos.mpr hMp).ne'
  have ha2M : a ^ 2 * M = 1 := by
    calc
      _ = (a * Real.sqrt M) ^ 2 := by rw [mul_pow, Real.sq_sqrt hM]
      _ = 1 := by rw [haM]; norm_num
  have hf2 : lpNorm f 2 μ = Real.sqrt M := by
    simpa only [Real.norm_eq_abs, sq_abs] using
      DensityEntropy.lpNorm_two_sqrt (μ := μ) hf.aestronglyMeasurable
  have hscale : Real.sqrt (a ^ 2 * E) = a * Real.sqrt E := by
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  have hscaled : lpNorm (fun x => a * f x) (ENNReal.ofReal p) μ ≤
      K₁ * Real.sqrt (a ^ 2 * E) + K₂ := by
    rw [DensityEntropy.lpNorm_const_mul, abs_of_pos ha]
    calc
      _ ≤ a * (K₁ * Real.sqrt E + K₂ * lpNorm f 2 μ) := mul_le_mul_of_nonneg_left hSob ha.le
      _ = K₁ * (a * Real.sqrt E) + K₂ * (a * Real.sqrt M) := by rw [hf2]; ring
      _ = _ := by rw [haM, mul_one, hscale]
  have hbscaled := EntropyScaling.bounded_const_mul hb a
  have hmass : (∫ x, (a * f x) ^ 2 ∂μ) = 1 := by
    simpa only [mul_pow, integral_const_mul] using ha2M
  have hh := normalized_defective (measurable_const.mul hf) hbscaled hp hK₁ hK₂
    (mul_nonneg (sq_nonneg a) hE) hmass hscaled
  change Rothaus.squareEntropy μ (fun x => a * f x) ≤
    p / (p - 2) * (2 * K₁ ^ 2 * (a ^ 2 * E) + 2 * K₂ ^ 2 - 1) at hh
  rw [EntropyScaling.squareEntropy_const_mul hf hb] at hh
  apply le_of_mul_le_mul_left _ (sq_pos_of_pos ha)
  calc
    _ ≤ p / (p - 2) * (2 * K₁ ^ 2 * (a ^ 2 * E) + 2 * K₂ ^ 2 - 1) := hh
    _ = p / (p - 2) * (2 * K₁ ^ 2 * (a ^ 2 * E) + (2 * K₂ ^ 2 - 1) * (a ^ 2 * M)) := by
      rw [ha2M]; ring
    _ = _ := by ring

end PeriodicAttractiveLogGas.SobolevEntropy

