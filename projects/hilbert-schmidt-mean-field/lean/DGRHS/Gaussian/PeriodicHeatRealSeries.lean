import DGRHS.Gaussian.PeriodicTransportLift
import DGRHS.Gaussian.PeriodicGaussianHeatFourier
import DGRHS.Gaussian.PeriodicMultidimensionalPoisson

/-!
Packet P9h, unit 2 (part 5): the periodic heat series on `ℝ^d` as a real cosine series and its
position-space (Poisson) form.

For `u > 0` and `z ∈ ℝ^d`:
`Re periodicGaussianHeat u (lift z) = Σ_k e^{-u‖k‖²} cos(2π⟨k,z⟩) = (π/u)^{d/2} Σ_m e^{-π²‖z+m‖²/u}`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

/-- The phase `⟨k, z⟩` of the Fourier mode `k` at `z ∈ ℝ^d`. -/
def periodicPhase (k : PeriodicFrequency ι) (z : E) : ℝ := inner ℝ (periodicFrequencyVector k) z

lemma periodicPhase_eq (k : PeriodicFrequency ι) (z : E) :
    periodicPhase k z = ∑ i, (k i : ℝ) * z i := by
  simp only [periodicPhase, PiLp.inner_apply, periodicFrequencyVector_apply, RCLike.inner_apply,
    conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

lemma periodicMFourier_lift (k : PeriodicFrequency ι) (z : E) :
    UnitAddTorus.mFourier k (periodicLift z) =
      Complex.exp (2 * Real.pi * Complex.I * (periodicPhase k z : ℝ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, periodicLift, fourier_coe_apply,
    div_one, periodicPhase_eq]
  rw [← Complex.exp_sum, Complex.ofReal_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

lemma periodicMFourier_lift_re (k : PeriodicFrequency ι) (z : E) :
    (UnitAddTorus.mFourier k (periodicLift z)).re = Real.cos (2 * Real.pi * periodicPhase k z) := by
  rw [periodicMFourier_lift, ← Complex.exp_ofReal_mul_I_re]
  congr 2
  push_cast
  ring

lemma periodicGaussianHeat_lift_re (u : ℝ) (hu : 0 < u) (z : E) :
    (periodicGaussianHeat u (periodicLift z)).re =
      ∑' k : PeriodicFrequency ι, Real.exp (-u * ‖periodicFrequencyVector k‖ ^ 2) *
        Real.cos (2 * Real.pi * periodicPhase k z) := by
  unfold periodicGaussianHeat
  rw [Complex.re_tsum]
  · refine tsum_congr fun k => ?_
    rw [Complex.re_ofReal_mul, periodicMFourier_lift_re]
  · apply Summable.of_norm
    simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      periodic_mFourier_norm_apply, mul_one]
    exact summable_periodicGaussian (ι := ι) u hu

/-- Poisson summation for the real heat series: position-space form. -/
lemma periodicGaussianHeat_lift_re_eq_image_sum (u : ℝ) (hu : 0 < u) (z : E) :
    (periodicGaussianHeat u (periodicLift z)).re =
      (Real.pi / u) ^ ((Fintype.card ι : ℝ) / 2) *
        ∑' m : PeriodicFrequency ι, Real.exp (-Real.pi ^ 2 * ‖z + periodicFrequencyVector m‖ ^ 2 / u) := by
  have ha : 0 < Real.pi / u := div_pos Real.pi_pos hu
  have h := periodicMultidimensionalGaussian_poisson (ι := ι) (Real.pi / u) ha z
  have hrhs : ∑' k : PeriodicFrequency ι, Complex.exp (-(Real.pi : ℂ) / ((Real.pi / u : ℝ) : ℂ) *
      (‖periodicFrequencyVector k‖ : ℂ) ^ 2) * UnitAddTorus.mFourier k (fun i => (z i : UnitAddCircle)) =
      periodicGaussianHeat u (periodicLift z) := by
    unfold periodicGaussianHeat
    refine tsum_congr fun k => ?_
    congr 1
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp
  have hL : (∑' m : PeriodicFrequency ι, Complex.exp (-(Real.pi : ℂ) * ((Real.pi / u : ℝ) : ℂ) *
      (‖z + periodicFrequencyVector m‖ : ℂ) ^ 2)) =
      ((∑' m : PeriodicFrequency ι, Real.exp (-Real.pi ^ 2 * ‖z + periodicFrequencyVector m‖ ^ 2 / u) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun m => ?_
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp
  have hc : (1 / ((Real.pi / u : ℝ) : ℂ) ^ (1 / 2 : ℂ)) ^ (Fintype.card ι) =
      (((Real.pi / u) ^ (-(Fintype.card ι : ℝ) / 2) : ℝ) : ℂ) := by
    rw [show ((1 / 2 : ℂ)) = (((1 / 2 : ℝ)) : ℂ) by push_cast; rfl, ← Complex.ofReal_cpow ha.le,
      ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_pow]
    congr 1
    rw [← Real.rpow_natCast, one_div, ← Real.rpow_neg ha.le, ← Real.rpow_mul ha.le]
    congr 1
    ring
  rw [hrhs, hL, hc] at h
  have hne : ((((Real.pi / u) ^ (-(Fintype.card ι : ℝ) / 2) : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos ha _).ne'
  have hc2 : (Real.pi / u) ^ (-(Fintype.card ι : ℝ) / 2) = ((Real.pi / u) ^ ((Fintype.card ι : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg ha.le]
    congr 1
    ring
  have h2 : ((((Real.pi / u) ^ (-(Fintype.card ι : ℝ) / 2) : ℝ)) : ℂ) *
      periodicGaussianHeat u (periodicLift z) = ((∑' m : PeriodicFrequency ι,
        Real.exp (-Real.pi ^ 2 * ‖z + periodicFrequencyVector m‖ ^ 2 / u) : ℝ) : ℂ) := h.symm
  rw [mul_comm, ← eq_div_iff hne, ← Complex.ofReal_div] at h2
  rw [h2, Complex.ofReal_re, hc2, div_inv_eq_mul, mul_comm]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicGaussianHeat_lift_re
#print axioms DGRHS.Periodic.periodicGaussianHeat_lift_re_eq_image_sum
