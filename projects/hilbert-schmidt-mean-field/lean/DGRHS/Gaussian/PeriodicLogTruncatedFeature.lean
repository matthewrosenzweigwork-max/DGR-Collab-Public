import DGRHS.Gaussian.PeriodicLogLatticeLogSum
import DGRHS.Gaussian.PeriodicLogMellin
import DGRHS.Gaussian.PeriodicRieszTruncatedFeature

/-!
Packet P9g, unit 2 (part 1): the heat-shifted torus LOG truncation
`g_τ = periodicLogMellinGreen τ` (Fourier coefficients `ĝ(k) e^{-τ‖k‖²}`, `ĝ(k) ∝ ‖k‖^{-d}`, `k ≠ 0`)
is, for `τ > 0`, a.e. the continuous positive Fourier kernel with nonnegative summable
coefficients, hence a bounded Hilbert feature Gram kernel (the `s = 0` analogue of
`PeriodicRieszTruncatedFeature`, TeX 1972-2023 `eq:truncatedFeatureCentering` with the LOG kernel).
The feature diagonal is only *logarithmic*: `Σ_k ĝ_τ(k) ≤ C (1 + log (1/τ))` for `0 < τ ≤ 1`.
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Real Fourier coefficient of the periodic LOG kernel (`c_d/(2π)^d ‖k‖^{-d}` off the zero mode). -/
def periodicLogCoeffReal (k : PeriodicFrequency ι) : ℝ :=
  if k = 0 then 0 else
    periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι) *
      (‖periodicFrequencyVector k‖⁻¹) ^ (Fintype.card ι)

lemma periodicLogFourierCoeff_eq_ofReal (k : PeriodicFrequency ι) :
    periodicLogFourierCoeff k = ((periodicLogCoeffReal k : ℝ) : ℂ) := by
  unfold periodicLogFourierCoeff periodicLogCoeffReal
  split_ifs <;> simp

lemma periodicLogCoeffReal_nonneg (k : PeriodicFrequency ι) : 0 ≤ periodicLogCoeffReal k := by
  unfold periodicLogCoeffReal
  split_ifs
  · exact le_rfl
  · have := periodicLogConstant_pos (ι := ι)
    positivity

lemma periodicLogCoeffReal_neg (k : PeriodicFrequency ι) :
    periodicLogCoeffReal (-k) = periodicLogCoeffReal k := by
  unfold periodicLogCoeffReal
  simp [periodicFrequencyVector_neg]

lemma periodicLogCoeffReal_zero : periodicLogCoeffReal (0 : PeriodicFrequency ι) = 0 := by
  simp [periodicLogCoeffReal]

lemma periodicLogCoeffReal_le (k : PeriodicFrequency ι) :
    periodicLogCoeffReal k ≤ periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι) := by
  have hA : 0 < periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι) := by
    have := periodicLogConstant_pos (ι := ι)
    positivity
  unfold periodicLogCoeffReal
  split_ifs with hk
  · exact hA.le
  · have h1 : 1 ≤ ‖periodicFrequencyVector k‖ := one_le_norm_periodicFrequencyVector hk
    have h2 : (‖periodicFrequencyVector k‖⁻¹) ^ (Fintype.card ι) ≤ 1 :=
      pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1)
    nlinarith

/-- Coefficients of the heat-shifted periodic LOG kernel. -/
def periodicLogTruncCoeff (τ : ℝ) (k : PeriodicFrequency ι) : ℝ :=
  Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) * periodicLogCoeffReal k

lemma periodicLogTruncCoeff_nonneg (τ : ℝ) (k : PeriodicFrequency ι) :
    0 ≤ periodicLogTruncCoeff τ k :=
  mul_nonneg (Real.exp_pos _).le (periodicLogCoeffReal_nonneg k)

lemma periodicLogTruncCoeff_neg (τ : ℝ) (k : PeriodicFrequency ι) :
    periodicLogTruncCoeff τ (-k) = periodicLogTruncCoeff τ k := by
  unfold periodicLogTruncCoeff
  rw [periodicLogCoeffReal_neg, periodicFrequencyVector_neg, norm_neg]

lemma periodicLogTruncCoeff_zero (τ : ℝ) :
    periodicLogTruncCoeff τ (0 : PeriodicFrequency ι) = 0 := by
  simp [periodicLogTruncCoeff, periodicLogCoeffReal_zero]

lemma periodicLogTruncCoeff_le (τ : ℝ) (k : PeriodicFrequency ι) :
    periodicLogTruncCoeff τ k ≤
      periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι) *
        Real.exp (-τ * ‖periodicFrequencyVector k‖ ^ 2) := by
  unfold periodicLogTruncCoeff
  have h := periodicLogCoeffReal_le k
  have he : Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) =
      Real.exp (-τ * ‖periodicFrequencyVector k‖ ^ 2) := by congr 1; ring
  rw [he, mul_comm]
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

lemma periodicLogTruncCoeff_summable (τ : ℝ) (hτ : 0 < τ) :
    Summable (periodicLogTruncCoeff (ι := ι) τ) :=
  ((summable_periodicGaussian τ hτ).mul_left _).of_nonneg_of_le
    (periodicLogTruncCoeff_nonneg τ) (periodicLogTruncCoeff_le τ)

lemma periodicLogTruncCoeff_sqrt_summable (τ : ℝ) (hτ : 0 < τ) :
    Summable (fun k : PeriodicFrequency ι => Real.sqrt (periodicLogTruncCoeff τ k)) := by
  have hA : 0 ≤ periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι) := by
    have := periodicLogConstant_pos (ι := ι)
    positivity
  refine ((summable_periodicGaussian (τ / 2) (by positivity)).mul_left
    (Real.sqrt (periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι)))).of_nonneg_of_le
    (fun k => Real.sqrt_nonneg _) (fun k => ?_)
  have he : (Real.exp (-(τ / 2) * ‖periodicFrequencyVector k‖ ^ 2)) ^ 2 =
      Real.exp (-τ * ‖periodicFrequencyVector k‖ ^ 2) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)).mp
  rw [Real.sq_sqrt (periodicLogTruncCoeff_nonneg τ k), mul_pow, Real.sq_sqrt hA, he]
  exact periodicLogTruncCoeff_le τ k

/-- The continuous positive Fourier kernel of the LOG truncation coefficients. -/
abbrev periodicLogTruncKernel (τ : ℝ) : PeriodicTorus ι → ℝ :=
  periodicPositiveFourierKernel (periodicLogTruncCoeff (ι := ι) τ)

/-- Fourier coefficients of the heat-time LOG kernel at any heat shift `τ ≥ 0`. -/
lemma periodicLogMellinGreen_fourier (τ : ℝ) (hτ : 0 ≤ τ) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicLogMellinGreen (ι := ι) τ x : ℂ)) k =
      ((periodicLogTruncCoeff τ k : ℝ) : ℂ) := by
  unfold periodicLogMellinGreen
  rw [periodic_mFourierCoeff_real_const_mul]
  have hp := periodicLogMellinExponent_gt (ι := ι)
  by_cases hk : k = 0
  · subst k
    rw [periodicUnshiftedMellinHeatGreen_fourier_zero _ τ hp hτ]
    simp [periodicLogTruncCoeff_zero]
  · rw [periodicUnshiftedMellinHeatGreen_fourier_nonzero _ τ hp hτ k hk, ← Complex.ofReal_mul]
    congr 1
    have h := periodicLogMellinFactor_mul_gamma_eq (ι := ι) k hk
    simp only [mul_zero, neg_zero, Real.exp_zero, one_mul] at h
    have hreal : periodicLogCoeffReal k =
        periodicLogConstant ι / (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ (Fintype.card ι) := by
      apply Complex.ofReal_injective
      rw [← periodicLogFourierCoeff_eq_ofReal, periodicLogFourierCoeff_eq_source k hk]
    unfold periodicLogTruncCoeff
    rw [hreal, ← h]
    ring

/-- For `τ > 0` the heat-time LOG representative is a.e. the continuous positive Fourier kernel. -/
theorem periodicLogMellinGreen_ae_truncKernel (τ : ℝ) (hτ : 0 < τ) :
    periodicLogMellinGreen τ =ᵐ[periodicHaar ι] periodicLogTruncKernel τ := by
  have ha := periodicLogTruncCoeff_nonneg (ι := ι) τ
  have hsum := periodicLogTruncCoeff_summable (ι := ι) τ hτ
  have hev := periodicLogTruncCoeff_neg (ι := ι) τ
  have hint : Integrable (fun x : PeriodicTorus ι => (periodicLogTruncKernel τ x : ℂ))
      (periodicHaar ι) :=
    ((periodicPositiveFourierKernel_continuous _ ha hsum).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).ofReal
  have h := periodicL1_fourier_unique (fun x : PeriodicTorus ι => (periodicLogMellinGreen τ x : ℂ))
    (fun x => (periodicLogTruncKernel τ x : ℂ))
    (periodicLogMellinGreen_integrable τ hτ.le).ofReal hint (fun k => by
      rw [periodicLogMellinGreen_fourier τ hτ.le,
        periodicPositiveFourierKernel_fourierCoeff _ ha hsum hev])
  filter_upwards [h] with x hx
  exact Complex.ofReal_injective hx

lemma periodicLogTruncCoeff_eq_of_ne (τ : ℝ) {k : PeriodicFrequency ι} (hk : k ≠ 0) :
    periodicLogTruncCoeff τ k = Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) *
      (periodicLogConstant ι / (2 * Real.pi) ^ (Fintype.card ι) *
        (‖periodicFrequencyVector k‖⁻¹) ^ (Fintype.card ι)) := by
  unfold periodicLogTruncCoeff periodicLogCoeffReal
  rw [ite_eq_right hk]

/-- Diagonal of the truncated LOG feature: `g_τ(0) = Σ_k ĝ_τ(k) ≤ C (1 + log (1/τ))` for
`0 < τ ≤ 1` (the logarithmic replacement of `C τ^{-s/2}`). -/
theorem periodicLogTruncCoeff_tsum_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∑' k : PeriodicFrequency ι, periodicLogTruncCoeff τ k ≤ C * (1 + Real.log (1 / τ)) := by
  classical
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  set d : ℕ := Fintype.card ι with hd_def
  set s' : ℝ := ((d : ℝ) - 2) / 2 with hs'
  have hs'2 : 2 * s' < (d : ℝ) := by rw [hs']; linarith
  obtain ⟨C1, hC1, hlow⟩ := periodicFrequency_low_sum_log_le (ι := ι)
  obtain ⟨C2, hC2, hhigh⟩ := periodicFrequency_tail_sum_le (ι := ι) s' hs'2
  set A : ℝ := periodicLogConstant ι / (2 * Real.pi) ^ d with hA
  have hApos : 0 < A := by
    have := periodicLogConstant_pos (ι := ι)
    rw [hA]; positivity
  refine ⟨A * (C1 + C2), by positivity, ?_⟩
  intro τ hτ hτ1
  set K : ℝ := τ ^ (-(1 / 2 : ℝ)) with hK
  have hK1 : 1 ≤ K := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ hτ1 (by norm_num)
  have hKpos : 0 < K := by linarith
  let low : PeriodicFrequency ι → ℝ := fun k => periodicLogLowTerm K k
  let high : PeriodicFrequency ι → ℝ := fun k =>
    if K < ‖periodicFrequencyVector k‖ then ‖periodicFrequencyVector k‖ ^ (2 * (s' - d)) else 0
  have hlow_nn : ∀ k, 0 ≤ low k := fun k => periodicLogLowTerm_nonneg K k
  have hhigh_nn : ∀ k, 0 ≤ high k := fun k => by
    simp only [high]; split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hlow_sum : Summable low := periodicLogLowTerm_summable K hKpos.le
  have hr : 2 * (s' - d) < -(d : ℝ) := by rw [hs']; linarith
  have hhigh_sum : Summable high := by
    refine (summable_periodicFrequency_rpow (ι := ι) _ hr).of_nonneg_of_le hhigh_nn (fun k => ?_)
    simp only [high]; split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (norm_nonneg _) _
  set c : ℝ := 1 / τ with hc
  have hcpos : 0 < c := by positivity
  have hterm : ∀ k, periodicLogTruncCoeff τ k ≤ A * (low k + c * high k) := by
    intro k
    by_cases hk : k = 0
    · subst k
      rw [periodicLogTruncCoeff_zero]
      have := hlow_nn 0; have := hhigh_nn 0
      positivity
    · have h1 : 1 ≤ ‖periodicFrequencyVector k‖ := one_le_norm_periodicFrequencyVector hk
      have hpos : 0 < ‖periodicFrequencyVector k‖ := by linarith
      rw [periodicLogTruncCoeff_eq_of_ne τ hk]
      have hpow_nn : 0 ≤ (‖periodicFrequencyVector k‖⁻¹) ^ d := by positivity
      by_cases hkK : ‖periodicFrequencyVector k‖ ≤ K
      · have hlk : low k = (‖periodicFrequencyVector k‖⁻¹) ^ d := by
          simp only [low]; unfold periodicLogLowTerm; rw [ite_eq_left ⟨hk, hkK⟩]
        have hhk : high k = 0 := by
          simp only [high]; rw [ite_eq_right (not_lt.mpr hkK)]
        rw [hlk, hhk]
        have he : Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (sq_nonneg _) hτ.le))
        nlinarith [mul_le_mul_of_nonneg_right he (mul_nonneg hApos.le hpow_nn)]
      · have hKk : K < ‖periodicFrequencyVector k‖ := lt_of_not_ge hkK
        have hlk : low k = 0 := by
          simp only [low]; unfold periodicLogLowTerm; rw [ite_eq_right]; intro h; exact hkK h.2
        have hhk : high k = ‖periodicFrequencyVector k‖ ^ (2 * (s' - d)) := by
          simp only [high]; rw [ite_eq_left hKk]
        rw [hlk, hhk]
        have hb := periodic_gaussian_inverse_power_bound τ ‖periodicFrequencyVector k‖ hτ hpos 1
        have hb' : Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) ≤
            c * (‖periodicFrequencyVector k‖⁻¹) ^ 2 := by
          have : -(‖periodicFrequencyVector k‖ ^ 2 * τ) = -τ * ‖periodicFrequencyVector k‖ ^ 2 := by
            ring
          rw [this]
          simpa [hc] using hb
        have hpw : (‖periodicFrequencyVector k‖⁻¹) ^ 2 * (‖periodicFrequencyVector k‖⁻¹) ^ d =
            ‖periodicFrequencyVector k‖ ^ (2 * (s' - d)) := by
          have h2 : 2 * (s' - (d : ℝ)) = -(((2 + d : ℕ)) : ℝ) := by
            rw [hs']; push_cast; ring
          rw [h2, Real.rpow_neg hpos.le, Real.rpow_natCast, ← inv_pow, ← pow_add]
        calc Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) *
              (A * (‖periodicFrequencyVector k‖⁻¹) ^ d)
            ≤ (c * (‖periodicFrequencyVector k‖⁻¹) ^ 2) *
              (A * (‖periodicFrequencyVector k‖⁻¹) ^ d) :=
              mul_le_mul_of_nonneg_right hb' (mul_nonneg hApos.le hpow_nn)
          _ = A * (0 + c * ‖periodicFrequencyVector k‖ ^ (2 * (s' - d))) := by
              rw [← hpw]; ring
  have hsumL : Summable (periodicLogTruncCoeff (ι := ι) τ) :=
    periodicLogTruncCoeff_summable τ hτ
  have hR : Summable (fun k => A * (low k + c * high k)) :=
    (hlow_sum.add (hhigh_sum.mul_left c)).mul_left A
  have h1 := hsumL.tsum_le_tsum hterm hR
  rw [tsum_mul_left, hlow_sum.tsum_add (hhigh_sum.mul_left c), tsum_mul_left] at h1
  refine h1.trans ?_
  have hL : ∑' k, low k ≤ C1 * (1 + Real.log K) := hlow K hK1
  have hH : ∑' k, high k ≤ C2 * K ^ (2 * s' - d) := hhigh K hK1
  have hKs' : K ^ (2 * s' - d) = τ := by
    rw [hK, ← Real.rpow_mul hτ.le]
    have : -(1 / 2 : ℝ) * (2 * s' - d) = 1 := by rw [hs']; ring
    rw [this, Real.rpow_one]
  have hlogK : Real.log K = Real.log (1 / τ) / 2 := by
    rw [hK, Real.log_rpow hτ, show (1 : ℝ) / τ = τ⁻¹ from one_div τ, Real.log_inv]
    ring
  have hl0 : 0 ≤ Real.log (1 / τ) := Real.log_nonneg (by rw [le_div_iff₀ hτ]; linarith)
  have hcτ : c * (C2 * K ^ (2 * s' - d)) = C2 := by
    rw [hKs', hc]; field_simp
  have step : ∑' k, low k + c * ∑' k, high k ≤ (C1 + C2) * (1 + Real.log (1 / τ)) := by
    calc ∑' k, low k + c * ∑' k, high k ≤ C1 * (1 + Real.log K) + c * (C2 * K ^ (2 * s' - d)) :=
          add_le_add hL (mul_le_mul_of_nonneg_left hH hcpos.le)
      _ = C1 * (1 + Real.log (1 / τ) / 2) + C2 := by rw [hcτ, hlogK]
      _ ≤ _ := by nlinarith [mul_nonneg hC1 hl0, mul_nonneg hC2 hl0]
  calc A * (∑' k, low k + c * ∑' k, high k) ≤ A * ((C1 + C2) * (1 + Real.log (1 / τ))) :=
        mul_le_mul_of_nonneg_left step hApos.le
    _ = _ := by ring

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogCoeffReal
#print axioms DGRHS.Periodic.periodicLogFourierCoeff_eq_ofReal
#print axioms DGRHS.Periodic.periodicLogCoeffReal_nonneg
#print axioms DGRHS.Periodic.periodicLogCoeffReal_neg
#print axioms DGRHS.Periodic.periodicLogCoeffReal_zero
#print axioms DGRHS.Periodic.periodicLogCoeffReal_le
#print axioms DGRHS.Periodic.periodicLogTruncCoeff
#print axioms DGRHS.Periodic.periodicLogTruncCoeff_nonneg
#print axioms DGRHS.Periodic.periodicLogTruncCoeff_neg
#print axioms DGRHS.Periodic.periodicLogTruncCoeff_zero
#print axioms DGRHS.Periodic.periodicLogTruncCoeff_le
#print axioms DGRHS.Periodic.periodicLogTruncCoeff_summable
#print axioms DGRHS.Periodic.periodicLogTruncCoeff_sqrt_summable
#print axioms DGRHS.Periodic.periodicLogTruncKernel
#print axioms DGRHS.Periodic.periodicLogMellinGreen_fourier
#print axioms DGRHS.Periodic.periodicLogMellinGreen_ae_truncKernel
#print axioms DGRHS.Periodic.periodicLogTruncCoeff_eq_of_ne
#print axioms DGRHS.Periodic.periodicLogTruncCoeff_tsum_le
