import DGRHS.Gaussian.PeriodicRieszL2Fourier
import Mathlib.Analysis.Normed.Group.Tannery

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Heat removal in actual Haar L2 by real-exponent
square summability and Tannery's theorem. This is not pointwise monotonicity.
Native Tannery proof: David Loeffler, Apache-2.0, pinned source preserved. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal lp Topology
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

def periodicRieszHeatFourierCoeff (s τ : ℝ) (k : PeriodicFrequency ι) : ℂ :=
  (Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ)) : ℂ) * periodicRieszFourierCoeff s k

@[simp] lemma periodicRieszHeatFourierCoeff_zero_time (s : ℝ) (k : PeriodicFrequency ι) :
    periodicRieszHeatFourierCoeff s 0 k = periodicRieszFourierCoeff s k := by
  simp [periodicRieszHeatFourierCoeff]

@[simp] lemma periodicRieszHeatFourierCoeff_zero_mode (s τ : ℝ) :
    periodicRieszHeatFourierCoeff s τ (0 : PeriodicFrequency ι) = 0 := by
  simp [periodicRieszHeatFourierCoeff]

lemma norm_periodicRieszHeatFourierCoeff_le (s τ : ℝ) (hτ : 0 ≤ τ)
    (k : PeriodicFrequency ι) :
    ‖periodicRieszHeatFourierCoeff s τ k‖ ≤ ‖periodicRieszFourierCoeff s k‖ := by
  simp only [periodicRieszHeatFourierCoeff, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le]
  apply mul_le_of_le_one_left (norm_nonneg _)
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (sq_nonneg _) hτ))

lemma summable_periodicRieszHeatFourierCoeff_sq (s τ : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) :
    Summable (fun k : PeriodicFrequency ι => ‖periodicRieszHeatFourierCoeff s τ k‖ ^ 2) := by
  apply (summable_periodicRieszFourierCoeff_sq s hs).of_nonneg_of_le
    (fun k => sq_nonneg _)
  intro k
  have h := norm_periodicRieszHeatFourierCoeff_le s τ hτ k
  nlinarith [norm_nonneg (periodicRieszHeatFourierCoeff s τ k),
    norm_nonneg (periodicRieszFourierCoeff s k)]

lemma periodicRieszHeatFourierCoeff_memℓp (s τ : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) :
    Memℓp (periodicRieszHeatFourierCoeff (ι := ι) s τ) 2 := by
  apply (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).2
  simpa using summable_periodicRieszHeatFourierCoeff_sq s τ hs hτ

def periodicRieszHeatCoefficientVector (s τ : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) : ℓ²(PeriodicFrequency ι, ℂ) :=
  ⟨periodicRieszHeatFourierCoeff s τ, periodicRieszHeatFourierCoeff_memℓp s τ hs hτ⟩

def periodicRieszHeatL2 (s τ : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) : Lp ℂ 2 (periodicHaar ι) :=
  (periodicFourierBasis (ι := ι)).repr.symm (periodicRieszHeatCoefficientVector s τ hs hτ)

lemma periodicRieszHeatL2_fourierCoeff (s τ : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (hτ : 0 ≤ τ) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (periodicRieszHeatL2 s τ hs hτ) k =
      periodicRieszHeatFourierCoeff s τ k := by
  rw [← periodicFourierBasis_repr]
  simp [periodicRieszHeatL2, periodicRieszHeatCoefficientVector]

lemma periodicRieszHeatFourierCoeff_tendsto (s : ℝ) (τ : ℕ → ℝ)
    (hτ : Tendsto τ atTop (𝓝 0)) (k : PeriodicFrequency ι) :
    Tendsto (fun n => periodicRieszHeatFourierCoeff s (τ n) k) atTop
      (𝓝 (periodicRieszFourierCoeff s k)) := by
  have he : Tendsto (fun n => Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * τ n)))
      atTop (𝓝 1) := by
    have hk : Tendsto (fun _ : ℕ => ‖periodicFrequencyVector k‖ ^ 2) atTop
        (𝓝 (‖periodicFrequencyVector k‖ ^ 2)) := tendsto_const_nhds
    have harg : Tendsto (fun n => -(‖periodicFrequencyVector k‖ ^ 2 * τ n))
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero, neg_zero] using (hk.mul hτ).neg
    simpa only [Function.comp_def, Real.exp_zero] using
      Real.continuous_exp.continuousAt.tendsto.comp harg
  have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp he
  simpa [periodicRieszHeatFourierCoeff] using hc.mul_const (periodicRieszFourierCoeff s k)

lemma periodicRieszHeatFourierCoeff_difference_sq_bound (s τ : ℝ) (hτ : 0 ≤ τ)
    (k : PeriodicFrequency ι) :
    ‖periodicRieszHeatFourierCoeff s τ k - periodicRieszFourierCoeff s k‖ ^ 2 ≤
      4 * ‖periodicRieszFourierCoeff s k‖ ^ 2 := by
  have ht := norm_sub_le (periodicRieszHeatFourierCoeff s τ k) (periodicRieszFourierCoeff s k)
  have h := norm_periodicRieszHeatFourierCoeff_le s τ hτ k
  have h0 := norm_nonneg (periodicRieszFourierCoeff s k)
  have hd0 := norm_nonneg (periodicRieszHeatFourierCoeff s τ k - periodicRieszFourierCoeff s k)
  have hd : ‖periodicRieszHeatFourierCoeff s τ k - periodicRieszFourierCoeff s k‖ ≤
      2 * ‖periodicRieszFourierCoeff s k‖ := by linarith
  nlinarith

/-- A sequence formulation avoids any uncountable intersection of AE sets. -/
theorem periodicRieszHeatCoefficientVector_tendsto (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (τ : ℕ → ℝ)
    (hτ0 : ∀ n, 0 ≤ τ n) (hτ : Tendsto τ atTop (𝓝 0)) :
    Tendsto (fun n => periodicRieszHeatCoefficientVector s (τ n) hs (hτ0 n)) atTop
      (𝓝 (periodicRieszCoefficientVector s hs)) := by
  have hsum : Tendsto (fun n => ∑' k : PeriodicFrequency ι,
      ‖periodicRieszHeatFourierCoeff s (τ n) k - periodicRieszFourierCoeff s k‖ ^ 2)
      atTop (𝓝 0) := by
    have ht := tendsto_tsum_of_dominated_convergence
      ((summable_periodicRieszFourierCoeff_sq s hs).mul_left 4)
      (g := fun _ : PeriodicFrequency ι => (0 : ℝ))
      (fun k => by
        simpa using (((periodicRieszHeatFourierCoeff_tendsto s τ hτ k).sub_const
          (periodicRieszFourierCoeff s k)).norm.pow 2))
      (Eventually.of_forall (fun n k => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact periodicRieszHeatFourierCoeff_difference_sq_bound s (τ n) (hτ0 n) k))
    simpa only [tsum_zero] using ht
  have hn (n : ℕ) :
      ‖periodicRieszHeatCoefficientVector s (τ n) hs (hτ0 n) -
        periodicRieszCoefficientVector s hs‖ ^ 2 =
        ∑' k : PeriodicFrequency ι,
          ‖periodicRieszHeatFourierCoeff s (τ n) k - periodicRieszFourierCoeff s k‖ ^ 2 := by
    calc
      _ = ∑' k : PeriodicFrequency ι,
          ‖(periodicRieszHeatCoefficientVector s (τ n) hs (hτ0 n) -
            periodicRieszCoefficientVector s hs) k‖ ^ 2 := by
        simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
          lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
            (periodicRieszHeatCoefficientVector s (τ n) hs (hτ0 n) -
              periodicRieszCoefficientVector s hs)
      _ = _ := by
        apply tsum_congr
        intro k
        rfl
  have hnlim : Tendsto (fun n =>
      ‖periodicRieszHeatCoefficientVector s (τ n) hs (hτ0 n) -
        periodicRieszCoefficientVector s hs‖ ^ 2) atTop (𝓝 0) :=
    hsum.congr' (Eventually.of_forall (fun n => (hn n).symm))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hnlim
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _),
    Real.sqrt_zero] using hsqrt

/-- Strong L2 heat removal, with all positive-Riesz Hilbert--Schmidt exponents. -/
theorem periodicRieszHeatL2_tendsto (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (τ : ℕ → ℝ)
    (hτ0 : ∀ n, 0 ≤ τ n) (hτ : Tendsto τ atTop (𝓝 0)) :
    Tendsto (fun n => periodicRieszHeatL2 s (τ n) hs (hτ0 n)) atTop
      (𝓝 (periodicRieszL2 s hs)) :=
  (periodicFourierBasis (ι := ι)).repr.symm.continuous.continuousAt.tendsto.comp
    (periodicRieszHeatCoefficientVector_tendsto s hs τ hτ0 hτ)

end DGRHS.Periodic
