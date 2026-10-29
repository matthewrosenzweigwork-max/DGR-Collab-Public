import DGRHS.Gaussian.PeriodicRieszMellinIdentification
import DGRHS.Gaussian.PeriodicLogKernelSections

/-!
Packet P9e, unit 1: the torus LOG kernel (Theorem 2.2(i), `s = 0`, Remark 2.1) as an actual proper
heat-time (Mellin) integral, the `s -> 0` limit of the Riesz Mellin representative:

`periodicLogMellinGreen tau x = c0 * int_0^infty t^(d/2-1) (heat(t+tau)(x) - 1) dt`,  `c0 = pi^(-d/2)/2`
(`lim_{s->0} 1/(s Gamma(s/2)) = 1/2`).

No infrared truncation is needed on the torus: the zero Fourier mode is removed (`heat - 1`), so the
`t -> infinity` end converges absolutely, and the Euclidean finite-`T` infrared family of
`gaussianLogInfraredPair` is not required.  The Fourier coefficients at `tau = 0` are exactly
`periodicLogFourierCoeff` (so the Mellin integral is almost everywhere `periodicLogKernel`).  All the
heat-time (Mellin-level) objects used later carry the exponent `p = d/2 - 1` and no normalization.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

/-- Mellin exponent `p = (d - s)/2 - 1` of the LOG kernel (`s = 0`, written literally so that the
generic `s`-parametrized heat-time lemmas of the Riesz chain apply at `s = 0` without rewriting). -/
def periodicLogMellinExponent (ι : Type u) [Fintype ι] : ℝ := ((Fintype.card ι : ℝ) - 0) / 2 - 1

lemma periodicLogMellinExponent_gt : -1 < periodicLogMellinExponent ι := by
  have hd : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Fintype.card_pos (α := ι)
  unfold periodicLogMellinExponent
  linarith

lemma periodicLogMellinExponent_add_one :
    periodicLogMellinExponent ι + 1 = (Fintype.card ι : ℝ) / 2 := by
  unfold periodicLogMellinExponent
  ring

/-- The `s -> 0` limit `pi^(s-d/2)/(s Gamma(s/2)) -> pi^(-d/2)/2` of the Riesz Mellin prefactor. -/
def periodicLogMellinFactor (ι : Type u) [Fintype ι] : ℝ :=
  Real.pi ^ (-((Fintype.card ι : ℝ) / 2)) / 2

lemma periodicLogMellinFactor_pos : 0 < periodicLogMellinFactor ι := by
  unfold periodicLogMellinFactor
  exact div_pos (Real.rpow_pos_of_pos Real.pi_pos _) (by norm_num)

/-- The proper heat-time integral representing the LOG kernel (heat shift `tau >= 0`; `tau = 0` is
the exact kernel). -/
def periodicLogMellinGreen (τ : ℝ) (x : PeriodicTorus ι) : ℝ :=
  periodicLogMellinFactor ι *
    periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) τ x

lemma periodicLogMellinGreen_measurable (τ : ℝ) :
    Measurable (periodicLogMellinGreen (ι := ι) τ) := by
  unfold periodicLogMellinGreen periodicUnshiftedMellinHeatGreen
  refine measurable_const.mul ?_
  have hm : Measurable (fun q : ℝ × PeriodicTorus ι => (q.1 + τ, q.2)) := by fun_prop
  have hh := (periodicGaussianHeat_joint_measurable (ι := ι)).comp hm
  have hf : Measurable (fun q : ℝ × PeriodicTorus ι =>
      q.1 ^ (periodicLogMellinExponent ι) *
        ((periodicGaussianHeat (q.1 + τ) q.2).re - 1)) :=
    (by fun_prop : Measurable (fun q : ℝ × PeriodicTorus ι =>
      q.1 ^ (periodicLogMellinExponent ι))).mul
      ((Complex.continuous_re.measurable.comp hh).sub measurable_const)
  exact (hf.stronglyMeasurable.integral_prod_left'
    (μ := (volume : Measure ℝ).restrict (Set.Ioi 0))).measurable

lemma periodicLogMellinGreen_integrable (τ : ℝ) (hτ : 0 ≤ τ) :
    Integrable (periodicLogMellinGreen (ι := ι) τ) (periodicHaar ι) :=
  (periodicUnshiftedMellinHeatGreen_integrable _ τ periodicLogMellinExponent_gt hτ).const_mul _

lemma four_pi_rpow_half (n : ℕ) :
    (4 * Real.pi) ^ ((n : ℝ) / 2) = (2 * Real.pi) ^ n * Real.pi ^ (-((n : ℝ) / 2)) := by
  have hpi := Real.pi_pos
  have h1 : (4 * Real.pi) ^ ((n : ℝ) / 2) * Real.pi ^ ((n : ℝ) / 2) = (2 * Real.pi) ^ n := by
    rw [← Real.mul_rpow (by positivity) hpi.le]
    rw [show 4 * Real.pi * Real.pi = (2 * Real.pi) ^ (2 : ℝ) by
      rw [Real.rpow_two]; ring]
    rw [← Real.rpow_mul (by positivity)]
    rw [show (2 : ℝ) * ((n : ℝ) / 2) = (n : ℝ) by ring, Real.rpow_natCast]
  have hp : 0 < Real.pi ^ ((n : ℝ) / 2) := Real.rpow_pos_of_pos hpi _
  rw [Real.rpow_neg hpi.le, ← h1, mul_assoc, mul_inv_cancel₀ hp.ne', mul_one]

lemma periodicLogMellinFactor_mul_gamma_eq (k : PeriodicFrequency ι) (hk : k ≠ 0) :
    periodicLogMellinFactor ι *
        (Real.exp (-(‖periodicFrequencyVector k‖ ^ 2 * (0 : ℝ))) *
          ((1 / ‖periodicFrequencyVector k‖ ^ 2) ^ (periodicLogMellinExponent ι + 1) *
            Real.Gamma (periodicLogMellinExponent ι + 1))) =
      periodicLogConstant ι / (2 * Real.pi * ‖periodicFrequencyVector k‖) ^ (Fintype.card ι) := by
  have hr : 0 < ‖periodicFrequencyVector k‖ := periodicFrequency_norm_pos hk
  have hpi := Real.pi_pos
  rw [periodicLogMellinExponent_add_one, mul_zero, neg_zero, Real.exp_zero, one_mul,
    periodic_inverse_square_rpow _ _ hr.le]
  have hneg : ‖periodicFrequencyVector k‖ ^ (-2 * ((Fintype.card ι : ℝ) / 2)) =
      (‖periodicFrequencyVector k‖ ^ (Fintype.card ι))⁻¹ := by
    rw [show -2 * ((Fintype.card ι : ℝ) / 2) = -((Fintype.card ι : ℕ) : ℝ) by ring,
      Real.rpow_neg hr.le, Real.rpow_natCast]
  rw [hneg]
  unfold periodicLogMellinFactor periodicLogConstant
  rw [four_pi_rpow_half (Fintype.card ι), mul_pow]
  have h2 : (2 * Real.pi) ^ (Fintype.card ι) ≠ 0 := by positivity
  have h3 : ‖periodicFrequencyVector k‖ ^ (Fintype.card ι) ≠ 0 := by positivity
  have h4 : Real.pi ^ (-((Fintype.card ι : ℝ) / 2)) ≠ 0 := (Real.rpow_pos_of_pos hpi _).ne'
  field_simp
  rw [mul_pow, mul_pow]
  ring

/-- At `tau = 0` the Fourier coefficients of the Mellin integral are exactly the printed LOG
coefficients `periodicLogFourierCoeff`. -/
lemma periodicLogMellinGreen_fourier_zero_time (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicLogMellinGreen (ι := ι) 0 x : ℂ)) k =
      periodicLogFourierCoeff k := by
  unfold periodicLogMellinGreen
  rw [periodic_mFourierCoeff_real_const_mul]
  have hp := periodicLogMellinExponent_gt (ι := ι)
  by_cases hk : k = 0
  · subst k
    rw [periodicUnshiftedMellinHeatGreen_fourier_zero _ 0 hp le_rfl]
    simp
  · rw [periodicUnshiftedMellinHeatGreen_fourier_nonzero _ 0 hp le_rfl k hk,
      periodicLogFourierCoeff_eq_source k hk, ← Complex.ofReal_mul]
    congr 1
    exact periodicLogMellinFactor_mul_gamma_eq k hk

/-- L1 uniqueness: the Mellin integral at `tau = 0` is Haar-almost everywhere the L2 LOG kernel
representative `periodicLogKernel` (so the proper heat-time representative is the printed kernel). -/
theorem periodicLogMellinGreen_ae_kernel :
    periodicLogMellinGreen (ι := ι) 0 =ᵐ[periodicHaar ι] periodicLogKernel := by
  have h : (fun x => (periodicLogMellinGreen (ι := ι) 0 x : ℂ)) =ᵐ[periodicHaar ι]
      (fun x => (periodicLogKernel x : ℂ)) := by
    apply periodicL1_fourier_unique _ _
      (periodicLogMellinGreen_integrable 0 le_rfl).ofReal
      periodicLogKernel_integrable.ofReal
    intro k
    exact (periodicLogMellinGreen_fourier_zero_time k).trans
      (periodicLogKernel_fourierCoeff k).symm
  filter_upwards [h] with x hx
  exact Complex.ofReal_injective hx

lemma periodicLogMellinGreen_memLp :
    MemLp (periodicLogMellinGreen (ι := ι) 0) 2 (periodicHaar ι) :=
  (memLp_congr_ae periodicLogMellinGreen_ae_kernel).2 periodicLogKernel_memLp

lemma periodicLogMellinGreen_integral_zero (τ : ℝ) (hτ : 0 ≤ τ) :
    (∫ x, periodicLogMellinGreen (ι := ι) τ x ∂periodicHaar ι) = 0 := by
  have hp := periodicLogMellinExponent_gt (ι := ι)
  have h := periodic_mFourierCoeff_real_const_mul (ι := ι) (periodicLogMellinFactor ι)
    (periodicUnshiftedMellinHeatGreen (periodicLogMellinExponent ι) τ) (0 : PeriodicFrequency ι)
  rw [periodicUnshiftedMellinHeatGreen_fourier_zero _ τ hp hτ, mul_zero] at h
  simp only [UnitAddTorus.mFourierCoeff, neg_zero, UnitAddTorus.mFourier_zero,
    ContinuousMap.one_apply, one_smul] at h
  have hc : ((∫ x, periodicLogMellinGreen (ι := ι) τ x ∂periodicHaar ι : ℝ) : ℂ) = 0 := by
    exact ((@RCLike.ofRealLI ℂ _).integral_comp_comm _).symm.trans h
  exact Complex.ofReal_injective (by simpa using hc)

end DGRHS.Periodic

#print axioms DGRHS.Periodic.periodicLogMellinExponent_gt
#print axioms DGRHS.Periodic.periodicLogMellinFactor_pos
#print axioms DGRHS.Periodic.periodicLogMellinGreen_measurable
#print axioms DGRHS.Periodic.periodicLogMellinGreen_integrable
#print axioms DGRHS.Periodic.four_pi_rpow_half
#print axioms DGRHS.Periodic.periodicLogMellinFactor_mul_gamma_eq
#print axioms DGRHS.Periodic.periodicLogMellinGreen_fourier_zero_time
#print axioms DGRHS.Periodic.periodicLogMellinGreen_ae_kernel
#print axioms DGRHS.Periodic.periodicLogMellinGreen_memLp
#print axioms DGRHS.Periodic.periodicLogMellinGreen_integral_zero
