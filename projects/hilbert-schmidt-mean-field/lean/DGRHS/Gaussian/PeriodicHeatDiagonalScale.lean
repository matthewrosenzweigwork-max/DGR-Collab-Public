import DGRHS.Gaussian.PeriodicHeatTimeEnvelope

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. The actual diagonal heat kernel is decreasing
in time by its positive Fourier coefficients. This does not assert that the
heat kernel is pointwise monotone away from the diagonal. Poisson summation
gives the exact project-time small-scale power, including pi. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicGaussianHeat_zero_series (t : ℝ) :
    periodicGaussianHeat t (0 : PeriodicTorus ι) =
      ((∑' k : PeriodicFrequency ι,
        Real.exp (-t * ‖periodicFrequencyVector k‖ ^ 2) : ℝ) : ℂ) := by
  have he (k : PeriodicFrequency ι) : UnitAddTorus.mFourier k (0 : PeriodicTorus ι) = 1 := by
    simp [UnitAddTorus.mFourier, fourier_apply]
  simp only [periodicGaussianHeat, he, mul_one, Complex.ofReal_tsum]

lemma periodicGaussianHeat_zero_antitone (t v : ℝ) (ht : 0 < t) (htv : t ≤ v) :
    (periodicGaussianHeat v (0 : PeriodicTorus ι)).re ≤
      (periodicGaussianHeat t (0 : PeriodicTorus ι)).re := by
  simp only [periodicGaussianHeat_zero_series, Complex.ofReal_re]
  apply Summable.tsum_le_tsum _ (summable_periodicGaussian v (ht.trans_le htv))
    (summable_periodicGaussian t ht)
  intro k
  apply Real.exp_le_exp.mpr
  simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right htv (sq_nonneg _))

lemma periodicGaussianHeat_norm_le_zero (t : ℝ) (ht : 0 < t)
    (x : PeriodicTorus ι) :
    ‖periodicGaussianHeat t x‖ ≤ (periodicGaussianHeat t (0 : PeriodicTorus ι)).re := by
  have hs : Summable (fun k : PeriodicFrequency ι =>
      ‖(Real.exp (-t * ‖periodicFrequencyVector k‖ ^ 2) : ℂ) * UnitAddTorus.mFourier k x‖) := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      periodic_mFourier_norm_apply, mul_one] using summable_periodicGaussian (ι := ι) t ht
  rw [periodicGaussianHeat_zero_series, Complex.ofReal_re]
  simpa only [periodicGaussianHeat, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, periodic_mFourier_norm_apply, mul_one]
    using norm_tsum_le_tsum_norm hs

lemma periodicGaussianHeat_shifted_norm_le_zero (t τ : ℝ) (ht : 0 < t) (hτ : 0 ≤ τ)
    (x : PeriodicTorus ι) :
    ‖periodicGaussianHeat (t + τ) x‖ ≤ (periodicGaussianHeat t (0 : PeriodicTorus ι)).re :=
  (periodicGaussianHeat_norm_le_zero (t + τ) (add_pos_of_pos_of_nonneg ht hτ) x).trans
    (periodicGaussianHeat_zero_antitone t (t + τ) ht (le_add_of_nonneg_right hτ))

lemma periodic_sqrt_nat_power (a : ℝ) (ha : 0 ≤ a) (d : ℕ) :
    (Real.sqrt a) ^ d = a ^ ((d : ℝ) / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul ha]
  congr 1
  ring

lemma periodicGaussianHeat_zero_poisson (t : ℝ) (ht : 0 < t) :
    (periodicGaussianHeat t (0 : PeriodicTorus ι)).re =
      (Real.pi / t) ^ ((Fintype.card ι : ℝ) / 2) *
        ∑' k : PeriodicFrequency ι,
          Real.exp (-(Real.pi ^ 2 / t) * ‖periodicFrequencyVector k‖ ^ 2) := by
  have h := periodicGaussianHeat_physical_formula (Real.pi / t)
    (div_pos Real.pi_pos ht) (0 : EuclideanSpace ℝ ι)
  have htt : Real.pi / (Real.pi / t) = t := by field_simp
  have hzero : (fun i : ι => ((0 : EuclideanSpace ℝ ι) i : UnitAddCircle)) = 0 := by
    ext i
    simp
  rw [htt, hzero] at h
  rw [h, Complex.ofReal_re, periodic_sqrt_nat_power _ (by positivity)]
  congr 1
  apply tsum_congr
  intro k
  simp only [zero_add]
  congr 1
  ring

def periodicHeatDiagonalSmallConstant (ι : Type u) [Fintype ι] : ℝ :=
  Real.pi ^ ((Fintype.card ι : ℝ) / 2) *
    ∑' k : PeriodicFrequency ι, Real.exp (-Real.pi ^ 2 * ‖periodicFrequencyVector k‖ ^ 2)

lemma periodicHeatDiagonalSmallConstant_nonneg : 0 ≤ periodicHeatDiagonalSmallConstant ι :=
  mul_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
    (tsum_nonneg (fun _ => (Real.exp_pos _).le))

lemma periodicGaussianHeat_zero_small_bound (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    (periodicGaussianHeat t (0 : PeriodicTorus ι)).re ≤
      periodicHeatDiagonalSmallConstant ι * t ^ (-((Fintype.card ι : ℝ) / 2)) := by
  have hcoeff : Real.pi ^ 2 ≤ Real.pi ^ 2 / t := by
    apply (le_div_iff₀ ht).2
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht1 (sq_nonneg Real.pi)
  have hsum : (∑' k : PeriodicFrequency ι,
      Real.exp (-(Real.pi ^ 2 / t) * ‖periodicFrequencyVector k‖ ^ 2)) ≤
      ∑' k : PeriodicFrequency ι, Real.exp (-Real.pi ^ 2 * ‖periodicFrequencyVector k‖ ^ 2) := by
    apply Summable.tsum_le_tsum _
      (summable_periodicGaussian _ (by positivity : 0 < Real.pi ^ 2 / t))
      (summable_periodicGaussian _ (by positivity : 0 < Real.pi ^ 2))
    intro k
    apply Real.exp_le_exp.mpr
    simpa only [neg_mul] using neg_le_neg (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _))
  rw [periodicGaussianHeat_zero_poisson t ht]
  calc
    _ ≤ (Real.pi / t) ^ ((Fintype.card ι : ℝ) / 2) *
        ∑' k : PeriodicFrequency ι, Real.exp (-Real.pi ^ 2 * ‖periodicFrequencyVector k‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (by positivity) _)
    _ = _ := by
      rw [Real.div_rpow Real.pi_pos.le ht.le, Real.rpow_neg ht.le]
      unfold periodicHeatDiagonalSmallConstant
      ring

lemma periodicGaussianHeat_shifted_small_bound (t τ : ℝ) (ht : 0 < t)
    (ht1 : t ≤ 1) (hτ : 0 ≤ τ) (x : PeriodicTorus ι) :
    ‖periodicGaussianHeat (t + τ) x‖ ≤
      periodicHeatDiagonalSmallConstant ι * t ^ (-((Fintype.card ι : ℝ) / 2)) :=
  (periodicGaussianHeat_shifted_norm_le_zero t τ ht hτ x).trans
    (periodicGaussianHeat_zero_small_bound t ht ht1)

lemma periodicGaussianHeat_centered_shifted_small_bound (t τ : ℝ) (ht : 0 < t)
    (ht1 : t ≤ 1) (hτ : 0 ≤ τ) (x : PeriodicTorus ι) :
    ‖periodicGaussianHeat (t + τ) x - 1‖ ≤
      (periodicHeatDiagonalSmallConstant ι + 1) *
        t ^ (-((Fintype.card ι : ℝ) / 2)) := by
  have hd : 0 ≤ (Fintype.card ι : ℝ) / 2 := by positivity
  have hpow : 1 ≤ t ^ (-((Fintype.card ι : ℝ) / 2)) := by
    rw [Real.rpow_neg ht.le]
    apply (one_le_inv₀ (Real.rpow_pos_of_pos ht _)).2
    exact Real.rpow_le_one ht.le ht1 hd
  have hb := periodicGaussianHeat_shifted_small_bound t τ ht ht1 hτ x
  have htri := norm_sub_le (periodicGaussianHeat (t + τ) x) (1 : ℂ)
  simp only [norm_one] at htri
  nlinarith

lemma periodicGaussianHeat_centered_shifted_large_bound (t τ : ℝ) (ht : 1 ≤ t)
    (hτ : 0 ≤ τ) (x : PeriodicTorus ι) :
    ‖periodicGaussianHeat (t + τ) x - 1‖ ≤
      Real.exp (-t / 2) * periodicHeatTailMass ι := by
  exact (periodicGaussianHeat_centered_time_bound (t + τ) (by linarith) x).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
      periodicHeatTailMass_nonneg)

lemma periodic_exp_half_le_dimension_power (d : ℕ) (t : ℝ) (ht : 1 ≤ t) :
    Real.exp (-t / 2) ≤ ((d.factorial : ℝ) * (2 : ℝ) ^ d) * t ^ (-((d : ℝ) / 2)) := by
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hf : 0 < (d.factorial : ℝ) := by positivity
  have h2 : 0 < (2 : ℝ) ^ d := by positivity
  have h := Real.pow_div_factorial_le_exp (t / 2) (by positivity) d
  have h' := (div_le_iff₀ hf).1 h
  rw [div_pow] at h'
  have h'' := (div_le_iff₀ h2).1 h'
  have hpoly : t ^ d ≤ ((d.factorial : ℝ) * (2 : ℝ) ^ d) * Real.exp (t / 2) := by
    calc
      _ ≤ (Real.exp (t / 2) * (d.factorial : ℝ)) * (2 : ℝ) ^ d := h''
      _ = _ := by ring
  have hpower : t ^ ((d : ℝ) / 2) ≤ t ^ d := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht
      (div_le_self (by positivity) (by norm_num))
  have hscaled := mul_le_mul_of_nonneg_right (hpower.trans hpoly)
    (Real.exp_pos (-(t / 2))).le
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at hscaled
  have hout : Real.exp (-(t / 2)) ≤ ((d.factorial : ℝ) * (2 : ℝ) ^ d) / t ^ ((d : ℝ) / 2) := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos ht0 _)).2
    simpa only [mul_comm] using hscaled
  simpa only [neg_div, div_eq_mul_inv, neg_mul, Real.rpow_neg ht0.le] using hout

def periodicHeatDiagonalGlobalConstant (ι : Type u) [Fintype ι] : ℝ :=
  periodicHeatDiagonalSmallConstant ι + 1 +
    periodicHeatTailMass ι * ((Fintype.card ι).factorial : ℝ) * (2 : ℝ) ^ Fintype.card ι

lemma periodicHeatDiagonalGlobalConstant_nonneg : 0 ≤ periodicHeatDiagonalGlobalConstant ι := by
  have hC := periodicHeatDiagonalSmallConstant_nonneg (ι := ι)
  have hD := periodicHeatTailMass_nonneg (ι := ι)
  unfold periodicHeatDiagonalGlobalConstant
  positivity

lemma periodicGaussianHeat_centered_shifted_power_bound (t τ : ℝ) (ht : 0 < t)
    (hτ : 0 ≤ τ) (x : PeriodicTorus ι) :
    ‖periodicGaussianHeat (t + τ) x - 1‖ ≤
      periodicHeatDiagonalGlobalConstant ι * t ^ (-((Fintype.card ι : ℝ) / 2)) := by
  have hp : 0 ≤ t ^ (-((Fintype.card ι : ℝ) / 2)) := Real.rpow_nonneg ht.le _
  have hC := periodicHeatDiagonalSmallConstant_nonneg (ι := ι)
  have hD := periodicHeatTailMass_nonneg (ι := ι)
  by_cases ht1 : t ≤ 1
  · apply (periodicGaussianHeat_centered_shifted_small_bound t τ ht ht1 hτ x).trans
    apply mul_le_mul_of_nonneg_right _ hp
    unfold periodicHeatDiagonalGlobalConstant
    exact le_add_of_nonneg_right (by positivity)
  · have hl := periodicGaussianHeat_centered_shifted_large_bound t τ (le_of_not_ge ht1) hτ x
    have he := mul_le_mul_of_nonneg_right
      (periodic_exp_half_le_dimension_power (Fintype.card ι) t (le_of_not_ge ht1)) hD
    apply (hl.trans he).trans
    calc
      _ = (periodicHeatTailMass ι * ((Fintype.card ι).factorial : ℝ) *
          (2 : ℝ) ^ Fintype.card ι) * t ^ (-((Fintype.card ι : ℝ) / 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by
        unfold periodicHeatDiagonalGlobalConstant
        linarith) hp

end DGRHS.Periodic
