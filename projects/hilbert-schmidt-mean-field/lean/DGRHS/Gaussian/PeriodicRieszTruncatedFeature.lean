import DGRHS.Gaussian.PeriodicRieszSingularPartition
import DGRHS.Gaussian.PeriodicRieszCompressionPositive
import DGRHS.Gaussian.PeriodicRieszMellinIdentification
import DGRHS.Gaussian.PeriodicPositiveFourierGram
import DGRHS.Gaussian.PeriodicGaussianLatticeBounds
import DGRHS.Gaussian.PeriodicLatticeShellSums
import DGRHS.Gaussian.PeriodicHeatFourierKernel

/-!
Packet P9d, unit 1 (part 1): the heat-shifted torus Riesz truncation
`g_τ = periodicRieszMellinGreen s τ` (Fourier coefficients `ĝ(k) e^{-τ‖k‖²}`) is, for `τ > 0`,
a.e. the continuous positive Fourier kernel with nonnegative summable coefficients, hence a
bounded Hilbert feature Gram kernel (the torus form of the Fourier feature of the Euclidean
truncation, TeX 1972-2023 eq. truncatedFeatureCentering).
-/

noncomputable section
open MeasureTheory Filter
open scoped ENNReal BigOperators Topology
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Real Fourier coefficients of the heat-shifted periodic Riesz kernel. -/
def periodicRieszTruncCoeff (s τ : ℝ) (k : PeriodicFrequency ι) : ℝ :=
  (periodicRieszHeatFourierCoeff s τ k).re

lemma periodicRieszTruncCoeff_eq (s τ : ℝ) (k : PeriodicFrequency ι) :
    periodicRieszTruncCoeff s τ k =
      Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) * (periodicRieszFourierCoeff s k).re := by
  unfold periodicRieszTruncCoeff periodicRieszHeatFourierCoeff
  exact Complex.re_ofReal_mul _ _

lemma periodicRieszTruncCoeff_coe (s τ : ℝ) (k : PeriodicFrequency ι) :
    ((periodicRieszTruncCoeff s τ k : ℝ) : ℂ) = periodicRieszHeatFourierCoeff s τ k := by
  rw [periodicRieszTruncCoeff_eq]
  unfold periodicRieszHeatFourierCoeff
  rw [Complex.ofReal_mul, periodicRieszFourierCoeff_real]

lemma periodicRieszTruncCoeff_nonneg (s τ : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (k : PeriodicFrequency ι) :
    0 ≤ periodicRieszTruncCoeff s τ k := by
  rw [periodicRieszTruncCoeff_eq]
  exact mul_nonneg (Real.exp_pos _).le (periodicRieszFourierCoeff_re_nonneg s hs0 hs2 k)

lemma periodicRieszTruncCoeff_neg (s τ : ℝ) (k : PeriodicFrequency ι) :
    periodicRieszTruncCoeff s τ (-k) = periodicRieszTruncCoeff s τ k := by
  rw [periodicRieszTruncCoeff_eq, periodicRieszTruncCoeff_eq, periodicRieszFourierCoeff_neg,
    periodicFrequencyVector_neg, norm_neg]

lemma periodicRieszFourierCoeff_re_le (s : ℝ) (hs0 : 0 < s)
    (hsd : s < (Fintype.card ι : ℝ)) (k : PeriodicFrequency ι) :
    (periodicRieszFourierCoeff s k).re ≤ periodicRieszFourierAmplitude ι s := by
  have hA := periodicRieszFourierAmplitude_pos (ι := ι) s hs0 hsd
  by_cases hk : k = 0
  · subst k
    simpa using hA.le
  · simp only [periodicRieszFourierCoeff, ite_eq_right hk, Complex.ofReal_re]
    have h1 : 1 ≤ ‖periodicFrequencyVector k‖ := one_le_norm_periodicFrequencyVector hk
    have h2 : ‖periodicFrequencyVector k‖ ^ (s - (Fintype.card ι : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
    nlinarith

lemma periodicRieszTruncCoeff_le (s τ : ℝ) (hs0 : 0 < s)
    (hsd : s < (Fintype.card ι : ℝ)) (k : PeriodicFrequency ι) :
    periodicRieszTruncCoeff s τ k ≤
      periodicRieszFourierAmplitude ι s * Real.exp (-τ * ‖periodicFrequencyVector k‖ ^ 2) := by
  rw [periodicRieszTruncCoeff_eq]
  have h := periodicRieszFourierCoeff_re_le s hs0 hsd k
  have he : Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) =
      Real.exp (-τ * ‖periodicFrequencyVector k‖ ^ 2) := by congr 1; ring
  rw [he, mul_comm]
  exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

lemma periodicRieszTruncCoeff_summable (s τ : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ) :
    Summable (periodicRieszTruncCoeff (ι := ι) s τ) := by
  have hsd : s < (Fintype.card ι : ℝ) := by
    have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
    linarith
  exact ((summable_periodicGaussian τ hτ).mul_left _).of_nonneg_of_le
    (periodicRieszTruncCoeff_nonneg s τ hs0 hs2) (periodicRieszTruncCoeff_le s τ hs0 hsd)

lemma periodicRieszTruncCoeff_sqrt_summable (s τ : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ) :
    Summable (fun k : PeriodicFrequency ι => Real.sqrt (periodicRieszTruncCoeff s τ k)) := by
  have hsd : s < (Fintype.card ι : ℝ) := by
    have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
    linarith
  have hA := (periodicRieszFourierAmplitude_pos (ι := ι) s hs0 hsd).le
  refine ((summable_periodicGaussian (τ / 2) (by positivity)).mul_left
    (Real.sqrt (periodicRieszFourierAmplitude ι s))).of_nonneg_of_le
    (fun k => Real.sqrt_nonneg _) (fun k => ?_)
  have he : (Real.exp (-(τ / 2) * ‖periodicFrequencyVector k‖ ^ 2)) ^ 2 =
      Real.exp (-τ * ‖periodicFrequencyVector k‖ ^ 2) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)).mp
  rw [Real.sq_sqrt (periodicRieszTruncCoeff_nonneg s τ hs0 hs2 k), mul_pow, Real.sq_sqrt hA, he]
  exact periodicRieszTruncCoeff_le s τ hs0 hsd k

/-- The continuous positive Fourier kernel of the truncation coefficients. -/
abbrev periodicRieszTruncKernel (s τ : ℝ) : PeriodicTorus ι → ℝ :=
  periodicPositiveFourierKernel (periodicRieszTruncCoeff (ι := ι) s τ)

lemma periodicPositiveFourierKernel_coe (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a) (hev : ∀ k, a (-k) = a k) (x : PeriodicTorus ι) :
    (periodicPositiveFourierKernel a x : ℂ) =
      ∑' k : PeriodicFrequency ι, (a k : ℂ) * UnitAddTorus.mFourier k x := by
  apply RCLike.conj_eq_iff_re.mp
  rw [Complex.conj_tsum]
  simp only [map_mul, Complex.conj_ofReal, ← UnitAddTorus.mFourier_neg]
  have he := (Equiv.neg (PeriodicFrequency ι)).tsum_eq
    (fun k : PeriodicFrequency ι => (a k : ℂ) * UnitAddTorus.mFourier k x)
  simpa only [Equiv.neg_apply, hev] using he

lemma periodicPositiveFourierKernel_fourierCoeff (a : PeriodicFrequency ι → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hs : Summable a) (hev : ∀ k, a (-k) = a k) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicPositiveFourierKernel a x : ℂ)) k = (a k : ℂ) := by
  simp only [periodicPositiveFourierKernel_coe a ha hs hev]
  apply periodicFourierSeries_coefficient
  simpa only [Complex.norm_real, Real.norm_of_nonneg (ha _)] using hs

/-- For `τ > 0` the Mellin representative of the heat-shifted Riesz kernel is a.e. the
continuous positive Fourier kernel. -/
theorem periodicRieszMellinGreen_ae_truncKernel (s τ : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 < τ) :
    periodicRieszMellinGreen s τ =ᵐ[periodicHaar ι] periodicRieszTruncKernel s τ := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hsd : s < (Fintype.card ι : ℝ) := by linarith
  have ha := periodicRieszTruncCoeff_nonneg (ι := ι) s τ hs0 hs2
  have hsum := periodicRieszTruncCoeff_summable (ι := ι) s τ hs0 hs2 hτ
  have hev := periodicRieszTruncCoeff_neg (ι := ι) s τ
  have hint : Integrable (fun x : PeriodicTorus ι => (periodicRieszTruncKernel s τ x : ℂ))
      (periodicHaar ι) :=
    ((periodicPositiveFourierKernel_continuous _ ha hsum).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)).ofReal
  have h := periodicL1_fourier_unique (fun x : PeriodicTorus ι => (periodicRieszMellinGreen s τ x : ℂ))
    (fun x => (periodicRieszTruncKernel s τ x : ℂ))
    (periodicRieszMellinGreen_integrable s τ hsd hτ.le).ofReal hint (fun k => by
      rw [periodicRieszMellinGreen_fourier s τ hsd hτ.le,
        periodicPositiveFourierKernel_fourierCoeff _ ha hsum hev, periodicRieszTruncCoeff_coe])
  filter_upwards [h] with x hx
  exact Complex.ofReal_injective hx


lemma periodicRieszTruncCoeff_eq_of_ne (s τ : ℝ) {k : PeriodicFrequency ι} (hk : k ≠ 0) :
    periodicRieszTruncCoeff s τ k = Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) *
      (periodicRieszFourierAmplitude ι s * ‖periodicFrequencyVector k‖ ^ (s - (Fintype.card ι : ℝ))) := by
  rw [periodicRieszTruncCoeff_eq]
  simp only [periodicRieszFourierCoeff, ite_eq_right hk, Complex.ofReal_re]

lemma periodicRieszTruncCoeff_zero (s τ : ℝ) : periodicRieszTruncCoeff s τ (0 : PeriodicFrequency ι) = 0 := by
  rw [periodicRieszTruncCoeff_eq]; simp

/-- Diagonal of the truncated feature: `g_τ(0) = Σ_k ĝ_τ(k) ≤ C τ^{-s/2}` for `0 < τ ≤ 1`. -/
theorem periodicRieszTruncCoeff_tsum_le (s : ℝ) (hs0 : 0 < s)
    (hs2 : 2 * s < (Fintype.card ι : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, 0 < τ → τ ≤ 1 →
      ∑' k : PeriodicFrequency ι, periodicRieszTruncCoeff s τ k ≤ C * τ ^ (-s / 2) := by
  classical
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  have hsd : s < (Fintype.card ι : ℝ) := by linarith
  set d : ℝ := (Fintype.card ι : ℝ) with hd_def
  set m : ℕ := ⌊s⌋₊ + 1 with hm
  have hms : s < (m : ℝ) := by
    have := Nat.lt_floor_add_one s
    simpa [hm] using this
  set s' : ℝ := (s + d) / 2 - (m : ℝ) with hs'
  have hs'2 : 2 * s' < d := by rw [hs']; linarith
  obtain ⟨C1, hC1, hlow⟩ := periodicFrequency_low_sum_le (ι := ι) s hs0 hsd
  obtain ⟨C2, hC2, hhigh⟩ := periodicFrequency_tail_sum_le (ι := ι) s' hs'2
  set A := periodicRieszFourierAmplitude ι s with hA
  have hApos : 0 < A := periodicRieszFourierAmplitude_pos (ι := ι) s hs0 hsd
  refine ⟨A * (C1 + (m.factorial : ℝ) * C2), by positivity, ?_⟩
  intro τ hτ hτ1
  set K : ℝ := τ ^ (-(1 / 2 : ℝ)) with hK
  have hK1 : 1 ≤ K := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hτ hτ1 (by norm_num)
  have hKpos : 0 < K := by linarith
  let low : PeriodicFrequency ι → ℝ := fun k =>
    if k ≠ 0 ∧ ‖periodicFrequencyVector k‖ ≤ K then ‖periodicFrequencyVector k‖ ^ (s - d) else 0
  let high : PeriodicFrequency ι → ℝ := fun k =>
    if K < ‖periodicFrequencyVector k‖ then ‖periodicFrequencyVector k‖ ^ (2 * (s' - d)) else 0
  have hlow_nn : ∀ k, 0 ≤ low k := fun k => by
    simp only [low]; split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hhigh_nn : ∀ k, 0 ≤ high k := fun k => by
    simp only [high]; split_ifs
    · exact Real.rpow_nonneg (norm_nonneg _) _
    · exact le_rfl
  have hlow_sum : Summable low := by
    apply summable_of_hasFiniteSupport
    apply (finite_periodicFrequency_norm_le (ι := ι) K hKpos.le).subset
    intro k hk
    by_contra hnot
    apply hk
    simp only [low]
    rw [ite_eq_right]
    intro h
    exact hnot h.2
  have hr : 2 * (s' - d) < -d := by rw [hs']; linarith
  have hhigh_sum : Summable high := by
    refine (summable_periodicFrequency_rpow (ι := ι) _ hr).of_nonneg_of_le hhigh_nn (fun k => ?_)
    simp only [high]; split_ifs
    · exact le_rfl
    · exact Real.rpow_nonneg (norm_nonneg _) _
  set c : ℝ := (m.factorial : ℝ) / τ ^ m with hc
  have hcpos : 0 < c := by positivity
  have hterm : ∀ k, periodicRieszTruncCoeff s τ k ≤ A * (low k + c * high k) := by
    intro k
    by_cases hk : k = 0
    · subst k
      rw [periodicRieszTruncCoeff_zero]
      have := hlow_nn 0; have := hhigh_nn 0
      positivity
    · have h1 : 1 ≤ ‖periodicFrequencyVector k‖ := one_le_norm_periodicFrequencyVector hk
      have hpos : 0 < ‖periodicFrequencyVector k‖ := by linarith
      rw [periodicRieszTruncCoeff_eq_of_ne s τ hk]
      have hpow_nn : 0 ≤ ‖periodicFrequencyVector k‖ ^ (s - d) := Real.rpow_nonneg hpos.le _
      by_cases hkK : ‖periodicFrequencyVector k‖ ≤ K
      · have hlk : low k = ‖periodicFrequencyVector k‖ ^ (s - d) := by
          simp only [low]; rw [ite_eq_left ⟨hk, hkK⟩]
        have hhk : high k = 0 := by
          simp only [high]; rw [ite_eq_right (not_lt.mpr hkK)]
        rw [hlk, hhk]
        have he : Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (sq_nonneg _) hτ.le))
        nlinarith [mul_le_mul_of_nonneg_right he (mul_nonneg hApos.le hpow_nn)]
      · have hKk : K < ‖periodicFrequencyVector k‖ := lt_of_not_ge hkK
        have hlk : low k = 0 := by
          simp only [low]; rw [ite_eq_right]; intro h; exact hkK h.2
        have hhk : high k = ‖periodicFrequencyVector k‖ ^ (2 * (s' - d)) := by
          simp only [high]; rw [ite_eq_left hKk]
        rw [hlk, hhk]
        have hb := periodic_gaussian_inverse_power_bound τ ‖periodicFrequencyVector k‖ hτ hpos m
        have hb' : Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) ≤
            c * (‖periodicFrequencyVector k‖⁻¹) ^ (2 * m) := by
          have : -(‖periodicFrequencyVector k‖ ^ 2 * τ) = -τ * ‖periodicFrequencyVector k‖ ^ 2 := by ring
          rw [this]; exact hb
        have hpw : ‖periodicFrequencyVector k‖ ^ (s - d) * (‖periodicFrequencyVector k‖⁻¹) ^ (2 * m) =
            ‖periodicFrequencyVector k‖ ^ (2 * (s' - d)) := by
          have h2 : (‖periodicFrequencyVector k‖⁻¹) ^ (2 * m) =
              ‖periodicFrequencyVector k‖ ^ (-(2 * (m : ℝ))) := by
            rw [Real.rpow_neg hpos.le,
              show (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, inv_pow]
          rw [h2, ← Real.rpow_add hpos]
          congr 1
          rw [hs']; ring
        calc Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) *
              (A * ‖periodicFrequencyVector k‖ ^ (s - d))
            ≤ (c * (‖periodicFrequencyVector k‖⁻¹) ^ (2 * m)) *
              (A * ‖periodicFrequencyVector k‖ ^ (s - d)) :=
              mul_le_mul_of_nonneg_right hb' (mul_nonneg hApos.le hpow_nn)
          _ = A * (0 + c * ‖periodicFrequencyVector k‖ ^ (2 * (s' - d))) := by
              rw [← hpw]; ring
  have hsumL : Summable (periodicRieszTruncCoeff (ι := ι) s τ) :=
    periodicRieszTruncCoeff_summable s τ hs0 hs2 hτ
  have hR : Summable (fun k => A * (low k + c * high k)) :=
    (hlow_sum.add (hhigh_sum.mul_left c)).mul_left A
  have h1 := hsumL.tsum_le_tsum hterm hR
  rw [tsum_mul_left, hlow_sum.tsum_add (hhigh_sum.mul_left c), tsum_mul_left] at h1
  refine h1.trans ?_
  -- bounds
  have hL : ∑' k, low k ≤ C1 * K ^ s := hlow K hK1
  have hH : ∑' k, high k ≤ C2 * K ^ (2 * s' - d) := hhigh K hK1
  have hKs : K ^ s = τ ^ (-s / 2) := by
    rw [hK, ← Real.rpow_mul hτ.le]; congr 1; ring
  have hKs' : K ^ (2 * s' - d) = τ ^ (-(s - 2 * m) / 2) := by
    rw [hK, ← Real.rpow_mul hτ.le]; congr 1; rw [hs']; ring
  have hcτ : c * τ ^ (-(s - 2 * m) / 2) = (m.factorial : ℝ) * τ ^ (-s / 2) := by
    rw [hc, div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_neg hτ.le, mul_assoc,
      ← Real.rpow_add hτ]
    congr 2; ring
  have step : ∑' k, low k + c * ∑' k, high k ≤ (C1 + (m.factorial : ℝ) * C2) * τ ^ (-s / 2) := by
    calc ∑' k, low k + c * ∑' k, high k ≤ C1 * τ ^ (-s / 2) + c * (C2 * τ ^ (-(s - 2 * m) / 2)) := by
          rw [hKs] at hL; rw [hKs'] at hH
          exact add_le_add hL (mul_le_mul_of_nonneg_left hH hcpos.le)
      _ = _ := by rw [show c * (C2 * τ ^ (-(s - 2 * m) / 2)) = C2 * (c * τ ^ (-(s - 2 * m) / 2)) by ring, hcτ]; ring
  calc A * (∑' k, low k + c * ∑' k, high k) ≤ A * ((C1 + (m.factorial : ℝ) * C2) * τ ^ (-s / 2)) :=
        mul_le_mul_of_nonneg_left step hApos.le
    _ = _ := by ring

end DGRHS.Periodic
