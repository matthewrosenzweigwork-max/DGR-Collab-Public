import LeanResearch.PeriodicAttractiveLogGas.DensityMoments
import LeanResearch.PeriodicAttractiveLogGas.EntropyMoment
import LeanResearch.PeriodicAttractiveLogGas.EntropyScaling

/-! Density transfer for the entropy estimate of source Lemma 3.2.
Every norm and entropy is attached to its actual measure. The unweighted
Sobolev input is the preceding source lemma, not a weighted conclusion. -/

noncomputable section

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace PeriodicAttractiveLogGas.DensityEntropy

open DensityMoments

variable {A : Type*} [MeasurableSpace A]
variable {μ ν : Measure A} {p f : A → ℝ} {c q K : ℝ}

theorem lpNorm_two_sqrt {E : Type*} [NormedAddCommGroup E]
    {G : A → E} (hG : AEStronglyMeasurable G μ) :
    lpNorm G 2 μ = Real.sqrt (∫ x, ‖G x‖ ^ 2 ∂μ) := by
  rw [lpNorm_two_eq hG, Real.sqrt_eq_rpow]

theorem lpNorm_const_mul (a : ℝ) (f : A → ℝ) (r : ℝ≥0∞) :
    lpNorm (fun x ↦ a * f x) r μ = |a| * lpNorm f r μ := by
  simpa only [Pi.smul_apply, smul_eq_mul, coe_nnnorm, Real.norm_eq_abs] using!
    lpNorm_const_smul a f μ (p := r)

/-- The actual L3 estimate before normalization, with the source coefficient. -/
theorem third_norm [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {G : A → E} {S : ℝ → ℝ}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K)
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (hG : MemLp G 2 ν)
    (hS : ∀ r : ℝ, 2 ≤ r → 0 ≤ S r)
    (hSob : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ f x - ∫ y, f y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ) :
    lpNorm f 3 ν ≤ K ^ (1 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ)) *
      (lpNorm f 2 ν + S (3 * (q / (q - 1))) * lpNorm G 2 ν) := by
  have hqq : q.HolderConjugate (q / (q - 1)) := Real.HolderConjugate.conjExponent hq
  have hr : 2 ≤ 3 * (q / (q - 1)) := by nlinarith [hqq.symm.lt]
  have hr0 : 0 < 3 * (q / (q - 1)) := by linarith
  have hre : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (3 * (q / (q - 1))) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (by linarith : 1 ≤ 3 * (q / (q - 1)))
  let a := ∫ x, f x ∂μ
  have hfc := memLp_of_bounded (μ := μ) (hf.sub measurable_const)
    (bounded_sub_const hb a) (ENNReal.ofReal (3 * (q / (q - 1))))
  have hmean : |a| ≤ c ^ (-(1 / 2 : ℝ)) * lpNorm f 2 ν := by
    simpa only [neg_div] using
      (norm_integral_le_lpNorm (memLp_of_bounded (μ := μ) hf hb 2) (by norm_num)).trans
        (lpNorm_energy_comparison hν hc hpc (memLp_of_bounded hf hb 2))
  have href : lpNorm f (ENNReal.ofReal (3 * (q / (q - 1)))) μ ≤
      c ^ (-(1 / 2 : ℝ)) *
        (lpNorm f 2 ν + S (3 * (q / (q - 1))) * lpNorm G 2 ν) := by
    have hadd := lpNorm_add_le hfc hre (g := fun _ ↦ a)
    change lpNorm ((fun x ↦ f x - a) + (fun _ ↦ a)) _ μ ≤
      lpNorm (fun x ↦ f x - a) _ μ + lpNorm (fun _ ↦ a) _ μ at hadd
    have he : (fun x ↦ f x - a) + (fun _ ↦ a) = f := by ext x; simp
    rw [he] at hadd
    have hcst : lpNorm (fun _ : A ↦ a) (ENNReal.ofReal (3 * (q / (q - 1)))) μ = |a| := by
      rw [lpNorm_const' (by positivity : ENNReal.ofReal (3 * (q / (q - 1))) ≠ 0)
        ENNReal.ofReal_ne_top]
      simp only [probReal_univ, Real.one_rpow, mul_one, Real.norm_eq_abs]
    rw [hcst] at hadd
    calc
      _ ≤ S (3 * (q / (q - 1))) * lpNorm G 2 μ + |a| :=
        hadd.trans (add_le_add (hSob _ hr) le_rfl)
      _ ≤ S (3 * (q / (q - 1))) *
          (c ^ (-(1 / 2 : ℝ)) * lpNorm G 2 ν) +
            c ^ (-(1 / 2 : ℝ)) * lpNorm f 2 ν :=
        add_le_add (mul_le_mul_of_nonneg_left (by
          simpa only [neg_div] using lpNorm_energy_comparison hν hc hpc hG)
          (hS _ hr)) hmean
      _ = _ := by ring
  have hH := (lpNorm_density_le hν hp (hpc.mono fun _ hx ↦ hc.le.trans hx)
    hq hpq hK hf hb (by norm_num : (0 : ℝ) < 3)).2
  simp only [ENNReal.ofReal_ofNat] at hH
  exact hH.trans (by
    calc
      _ ≤ K ^ (1 / 3 : ℝ) * (c ^ (-(1 / 2 : ℝ)) *
          (lpNorm f 2 ν + S (3 * (q / (q - 1))) * lpNorm G 2 ν)) :=
        mul_le_mul_of_nonneg_left href (Real.rpow_nonneg (lpNorm_nonneg.trans hK) _)
      _ = _ := by ring)

/-- Homogeneity removes the unit-mass restriction without assuming positive
mass. The third-norm premise will be discharged by the preceding theorem. -/
theorem defective_of_third_norm [IsProbabilityMeasure ν]
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M)
    {S E : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hK : 1 ≤ K)
    (hS : 0 ≤ S) (hE : 0 ≤ E)
    (hnorm : lpNorm f 3 ν ≤ K ^ (1 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ)) *
      (lpNorm f 2 ν + S * Real.sqrt E)) :
    Rothaus.squareEntropy ν f ≤ 3 * S ^ 2 * E +
      (3 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ)))) * (∫ x, f x ^ 2 ∂ν) := by
  let M := ∫ x, f x ^ 2 ∂ν
  have hM : 0 ≤ M := integral_nonneg fun x ↦ sq_nonneg (f x)
  by_cases hz : M = 0
  · rw [EntropyScaling.squareEntropy_zero_mass hf hb hz]
    change 0 ≤ 3 * S ^ 2 * E + _ * M
    rw [hz, mul_zero, add_zero]
    positivity
  have hMp : 0 < M := lt_of_le_of_ne hM (Ne.symm hz)
  let a := (Real.sqrt M)⁻¹
  have ha : 0 < a := inv_pos.mpr (Real.sqrt_pos.mpr hMp)
  have haM : a * Real.sqrt M = 1 := inv_mul_cancel₀ (Real.sqrt_pos.mpr hMp).ne'
  have ha2M : a ^ 2 * M = 1 := by
    calc
      _ = (a * Real.sqrt M) ^ 2 := by rw [mul_pow, Real.sq_sqrt hM]
      _ = 1 := by rw [haM]; norm_num
  have hf2 : lpNorm f 2 ν = Real.sqrt M := by
    simpa only [Real.norm_eq_abs, sq_abs] using lpNorm_two_sqrt (μ := ν) hf.aestronglyMeasurable
  have hscale : Real.sqrt (a ^ 2 * E) = a * Real.sqrt E := by
    rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha.le]
  have hscalednorm : lpNorm (fun x ↦ a * f x) 3 ν ≤
      K ^ (1 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ)) * (1 + S * Real.sqrt (a ^ 2 * E)) := by
    rw [lpNorm_const_mul, abs_of_pos ha]
    calc
      _ ≤ a * (K ^ (1 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ)) *
          (lpNorm f 2 ν + S * Real.sqrt E)) := mul_le_mul_of_nonneg_left hnorm ha.le
      _ = _ := by
        rw [hf2, hscale]
        calc
          _ = K ^ (1 / 3 : ℝ) * c ^ (-(1 / 2 : ℝ)) *
            (a * Real.sqrt M + S * (a * Real.sqrt E)) := by ring
          _ = _ := by rw [haM]
  obtain ⟨B, hB⟩ := EntropyScaling.bounded_const_mul hb a
  have hmass : (∫ x, (a * f x) ^ 2 ∂ν) = 1 := by
    simpa only [mul_pow, integral_const_mul] using ha2M
  have h := EntropyMoment.entropy_sq_defective_bounded
    (measurable_const.mul hf) hB hmass hc hc1 hK hS (mul_nonneg (sq_nonneg a) hE) hscalednorm
  rw [Rothaus.entropy_sq_eq (measurable_const.mul hf) hB] at h
  change (Rothaus.squareEntropy ν (fun x ↦ a * f x) : EReal) ≤ _ at h
  rw [EntropyScaling.squareEntropy_const_mul hf hb] at h
  have hr : a ^ 2 * Rothaus.squareEntropy ν f ≤
      3 * S ^ 2 * (a ^ 2 * E) + 3 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ))) := by
    exact_mod_cast h
  apply le_of_mul_le_mul_left _ (sq_pos_of_pos ha)
  calc
    _ ≤ 3 * S ^ 2 * (a ^ 2 * E) + 3 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ))) := hr
    _ = _ := by
      change _ = a ^ 2 * (3 * S ^ 2 * E + _ * M)
      calc
        _ = a ^ 2 * (3 * S ^ 2 * E) +
          (3 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ)))) * 1 := by ring
        _ = _ := by rw [← ha2M]; ring

/-- The complete defective entropy estimate; the density and Sobolev inputs
now discharge the actual third-moment bound. -/
theorem defective [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {G : A → E} {S : ℝ → ℝ}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K)
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (hG : MemLp G 2 ν)
    (hS : ∀ r : ℝ, 2 ≤ r → 0 ≤ S r)
    (hSob : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ f x - ∫ y, f y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ) :
    Rothaus.squareEntropy ν f ≤
      3 * S (3 * (q / (q - 1))) ^ 2 * (∫ x, ‖G x‖ ^ 2 ∂ν) +
        (3 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ)))) * (∫ x, f x ^ 2 ∂ν) := by
  have hconst := density_constants hν hp hc hpc hq hpq hK
  have hqq : q.HolderConjugate (q / (q - 1)) := Real.HolderConjugate.conjExponent hq
  have hr : 2 ≤ 3 * (q / (q - 1)) := by nlinarith [hqq.symm.lt]
  apply defective_of_third_norm hf hb hc hconst.1 hconst.2 (hS _ hr)
    (integral_nonneg fun x ↦ sq_nonneg ‖G x‖)
  rw [← lpNorm_two_sqrt hG.aestronglyMeasurable]
  exact third_norm hν hp hc hpc hq hpq hK hf hb hG hS hSob

/-- Exact source LSI constant, obtained from the proved defective estimate,
Rothaus centering, and the already proved density Poincare estimate. -/
theorem logSobolev [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {G : A → E} {S : ℝ → ℝ}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K)
    (hf : Measurable f) (hb : ∃ M : ℝ, ∀ x, |f x| ≤ M) (hG : MemLp G 2 ν)
    (hS : ∀ r : ℝ, 2 ≤ r → 0 ≤ S r)
    (hSob : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ f x - ∫ y, f y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ) :
    entropy ν (fun x ↦ f x ^ 2) ≤
      (((3 * S (3 * (q / (q - 1))) ^ 2 +
        (5 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ)))) *
          (K * S (2 * (q / (q - 1))) ^ 2 / c)) * (∫ x, ‖G x‖ ^ 2 ∂ν) : ℝ) : EReal) := by
  let a := ∫ x, f x ∂ν
  let g : A → ℝ := fun x ↦ f x - a
  have hg : Measurable g := hf.sub measurable_const
  have hgb := bounded_sub_const hb a
  have hfi : Integrable f μ := (memLp_of_bounded hf hb 1).integrable le_rfl
  have hmean : (∫ x, g x ∂μ) = (∫ x, f x ∂μ) - a := by
    rw [integral_sub hfi (integrable_const a)]
    simp
  have hgc : (fun x ↦ g x - ∫ y, g y ∂μ) = (fun x ↦ f x - ∫ y, f y ∂μ) := by
    ext x
    rw [hmean]
    dsimp [g]
    ring
  have hSobg : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ g x - ∫ y, g y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ := by
    intro r hr
    rw [hgc]
    exact hSob r hr
  have hd := defective hν hp hc hpc hq hpq hK hg hgb hG hS hSobg
  have hP := (poincare_integral hν hp hc hpc hq hpq hK hf hb hG hS hSob).2
  have hconst := density_constants hν hp hc hpc hq hpq hK
  have hB : 0 ≤ 5 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ))) := by
    simpa only [neg_div] using (logarithmic_coefficient_nonneg hc hconst.1 hconst.2).2.2
  obtain ⟨M, hM⟩ := hb
  obtain ⟨B, hBg⟩ := hgb
  have hr := rothaus_centering (μ := ν) hf ⟨M, hM⟩
  change entropy ν (fun x ↦ f x ^ 2) ≤ entropy ν (fun x ↦ g x ^ 2) +
    ((2 * ∫ x, g x ^ 2 ∂ν : ℝ) : EReal) at hr
  rw [Rothaus.entropy_sq_eq hf hM, Rothaus.entropy_sq_eq hg hBg, ← EReal.coe_add] at hr
  have hr' : Rothaus.squareEntropy ν f ≤ Rothaus.squareEntropy ν g + 2 * ∫ x, g x ^ 2 ∂ν := by
    exact_mod_cast hr
  rw [Rothaus.entropy_sq_eq hf hM]
  apply EReal.coe_le_coe_iff.mpr
  calc
    _ ≤ Rothaus.squareEntropy ν g + 2 * ∫ x, g x ^ 2 ∂ν := hr'
    _ ≤ (3 * S (3 * (q / (q - 1))) ^ 2 * (∫ x, ‖G x‖ ^ 2 ∂ν) +
          (3 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ)))) * (∫ x, g x ^ 2 ∂ν)) +
            2 * ∫ x, g x ^ 2 ∂ν := add_le_add hd le_rfl
    _ = 3 * S (3 * (q / (q - 1))) ^ 2 * (∫ x, ‖G x‖ ^ 2 ∂ν) +
          (5 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ)))) * (∫ x, g x ^ 2 ∂ν) := by ring
    _ ≤ 3 * S (3 * (q / (q - 1))) ^ 2 * (∫ x, ‖G x‖ ^ 2 ∂ν) +
          (5 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ)))) *
            ((K * S (2 * (q / (q - 1))) ^ 2 / c) * (∫ x, ‖G x‖ ^ 2 ∂ν)) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hP hB)
    _ = _ := by ring

/-- Functions need only be measurable and bounded on the measured support;
the representative transport preserves the actual entropy and energy. -/
theorem logSobolev_ae [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {G : A → E} {S : ℝ → ℝ}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hp : Measurable p) (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K)
    (hf : AEMeasurable f μ) (hb : ∃ M : ℝ, ∀ᵐ x ∂μ, |f x| ≤ M) (hG : MemLp G 2 ν)
    (hS : ∀ r : ℝ, 2 ≤ r → 0 ≤ S r)
    (hSob : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ f x - ∫ y, f y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ) :
    entropy ν (fun x ↦ f x ^ 2) ≤
      (((3 * S (3 * (q / (q - 1))) ^ 2 +
        (5 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ)))) *
          (K * S (2 * (q / (q - 1))) ^ 2 / c)) * (∫ x, ‖G x‖ ^ 2 ∂ν) : ℝ) : EReal) := by
  obtain ⟨g, hg, hgb, hfgμ, hfgν⟩ := exists_bounded_representative hν hf hb
  have hSobg : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ g x - ∫ y, g y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ := by
    intro r hr
    rw [← lpNorm_center_congr_ae hfgμ]
    exact hSob r hr
  rw [entropy_congr_ae (hfgν.mono fun x hx ↦ congrArg (fun t : ℝ ↦ t ^ 2) hx)]
  exact logSobolev hν hp hc hpc hq hpq hK hg hgb hG hS hSobg

/-- The source coefficients, named here only to expose the three conclusions
without repeatedly expanding the same formulas. -/
def poincareConstant (S : ℝ → ℝ) (c q K : ℝ) : ℝ :=
  K * S (2 * (q / (q - 1))) ^ 2 / c

def logSobolevConstant (S : ℝ → ℝ) (c q K : ℝ) : ℝ :=
  3 * S (3 * (q / (q - 1))) ^ 2 +
    (5 + 2 * Real.log (K * c ^ (-(3 / 2 : ℝ)))) * poincareConstant S c q K

def momentConstant (S : ℝ → ℝ) (c q K s : ℝ) : ℝ :=
  2 * K ^ (1 / s) * S (s * (q / (q - 1))) * c ^ (-1 / 2 : ℝ)

/-- All three density estimates. The density itself need only belong to the
actual Lq space: its measurable representative gives the same measure. -/
theorem density_estimates [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Type*} [NormedAddCommGroup E] {G : A → E} {S : ℝ → ℝ}
    (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p x)))
    (hc : 0 < c) (hpc : ∀ᵐ x ∂μ, c ≤ p x)
    (hq : 1 < q) (hpq : MemLp p (ENNReal.ofReal q) μ)
    (hK : lpNorm p (ENNReal.ofReal q) μ ≤ K)
    (hf : AEMeasurable f μ) (hb : ∃ M : ℝ, ∀ᵐ x ∂μ, |f x| ≤ M) (hG : MemLp G 2 ν)
    (hS : ∀ r : ℝ, 2 ≤ r → 0 ≤ S r)
    (hSob : ∀ r : ℝ, 2 ≤ r →
      lpNorm (fun x ↦ f x - ∫ y, f y ∂μ) (ENNReal.ofReal r) μ ≤
        S r * lpNorm G 2 μ) :
    MemLp f 2 ν ∧
      ProbabilityTheory.variance f ν ≤ poincareConstant S c q K * (∫ x, ‖G x‖ ^ 2 ∂ν) ∧
      entropy ν (fun x ↦ f x ^ 2) ≤
        ((logSobolevConstant S c q K * (∫ x, ‖G x‖ ^ 2 ∂ν) : ℝ) : EReal) ∧
      ∀ s : ℝ, 2 ≤ s →
        MemLp (fun x ↦ f x - ∫ y, f y ∂ν) (ENNReal.ofReal s) ν ∧
          lpNorm (fun x ↦ f x - ∫ y, f y ∂ν) (ENNReal.ofReal s) ν ≤
            momentConstant S c q K s * lpNorm G 2 ν := by
  let hp := hpq.aestronglyMeasurable.aemeasurable
  let p' := hp.mk p
  have hp' : Measurable p' := hp.measurable_mk
  have he : p =ᵐ[μ] p' := hp.ae_eq_mk
  have hν' : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (p' x)) := by
    rw [hν]
    exact withDensity_congr_ae (he.mono fun x hx ↦ congrArg ENNReal.ofReal hx)
  have hpc' : ∀ᵐ x ∂μ, c ≤ p' x := by
    filter_upwards [he, hpc] with x hx hc'
    simpa only [← hx] using hc'
  have hpq' : MemLp p' (ENNReal.ofReal q) μ := (memLp_congr_ae he).mp hpq
  have hK' : lpNorm p' (ENNReal.ofReal q) μ ≤ K := by
    rw [← show lpNorm p (ENNReal.ofReal q) μ = lpNorm p' (ENNReal.ofReal q) μ from
      congrArg ENNReal.toReal (eLpNorm_congr_ae he)]
    exact hK
  have hP := poincare_ae hν' hp' hc hpc' hq hpq' hK' hf hb hG hS hSob
  refine ⟨hP.1, hP.2, logSobolev_ae hν' hp' hc hpc' hq hpq' hK' hf hb hG hS hSob, ?_⟩
  intro s hs
  exact centered_moment_ae hν' hp' hc hpc' hq hpq' hK' hf hb hG hS hSob hs

end PeriodicAttractiveLogGas.DensityEntropy
