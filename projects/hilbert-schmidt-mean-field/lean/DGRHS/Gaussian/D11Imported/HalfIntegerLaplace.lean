/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.ReciprocalGaussianRecurrence

/-! The actual Laplace integral at order 11/2. This is the half-integer
Bessel evaluation used by the manuscript, proved by its Gaussian base case
and the integration-by-parts recurrence. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DGRHS.Gaussian.D11Imported.ReciprocalGaussian

lemma moment_continuous (n : ℕ) : Continuous (moment n) := by
  apply continuous_of_dominated (F := fun a x : ℝ => x^(2*n)*kernel a x)
    (μ := volume.restrict (Ioi (0:ℝ)))
    (bound := fun x : ℝ => x^(2*n)*Real.exp (-x^2))
  · intro a
    unfold kernel
    exact Measurable.aestronglyMeasurable (by fun_prop)
  · intro a
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (pow_nonneg hx.le _) (kernel_pos a x).le)]
    exact mul_le_mul_of_nonneg_left (kernel_le_gaussian a x) (pow_nonneg hx.le _)
  · change IntegrableOn (fun x : ℝ => x^(2*n)*Real.exp (-x^2)) (Ioi 0)
    simpa only [Real.rpow_natCast, neg_mul, one_mul] using integrableOn_rpow_mul_exp_neg_mul_sq
      (by norm_num : (0:ℝ)<1) (by exact lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg (2*n)) : (-1:ℝ)<((2*n:ℕ):ℝ))
  · exact ae_of_all _ (fun x => by unfold kernel; fun_prop)

lemma moment_five_pos {a : ℝ} (ha : 0 < a) :
    moment 5 a = ((2*a)^5+15*(2*a)^4+105*(2*a)^3+420*(2*a)^2+945*(2*a)+945)/32 * mass a := by
  have h0 := moment_zero a
  have h1 := moment_one ha
  have h2 := moment_recurrence 0 ha
  have h3 := moment_recurrence 1 ha
  have h4 := moment_recurrence 2 ha
  have h5 := moment_recurrence 3 ha
  norm_num at h2 h3 h4 h5
  rw [h5, h4, h3, h2, h1, h0]
  ring

lemma moment_five {a : ℝ} (ha : 0 ≤ a) :
    moment 5 a = ((2*a)^5+15*(2*a)^4+105*(2*a)^3+420*(2*a)^2+945*(2*a)+945)/32 * mass a := by
  have he : EqOn (moment 5)
      (fun a => ((2*a)^5+15*(2*a)^4+105*(2*a)^3+420*(2*a)^2+945*(2*a)+945)/32 * mass a)
      (Ioi (0:ℝ)) := fun _ ha => moment_five_pos ha
  have hc : Continuous (fun a : ℝ =>
      ((2*a)^5+15*(2*a)^4+105*(2*a)^3+420*(2*a)^2+945*(2*a)+945)/32 * mass a) := by
    apply Continuous.mul _ mass_continuous
    fun_prop
  have he' := he.closure (moment_continuous 5) hc
  rw [closure_Ioi] at he'
  exact he' ha

lemma square_image : (fun x : ℝ => x^2) '' Ioi 0 = Ioi 0 := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact sq_pos_of_pos (show (0:ℝ)<x from hx)
  · intro hy
    exact ⟨Real.sqrt y, Real.sqrt_pos.mpr hy, Real.sq_sqrt hy.le⟩

lemma square_injOn : InjOn (fun x : ℝ => x^2) (Ioi 0) := by
  intro x hx y hy he
  change 0 < x at hx
  change 0 < y at hy
  change x^2=y^2 at he
  nlinarith

lemma laplace_half_eleven {z : ℝ} (hz : 0 ≤ z) :
    (∫ t in Ioi (0:ℝ), t^((9:ℝ)/2)*Real.exp (-t-z^2/(4*t))) =
      Real.sqrt Real.pi * Real.exp (-z) *
        (z^5+15*z^4+105*z^3+420*z^2+945*z+945)/32 := by
  have hd (x : ℝ) (_ : x ∈ Ioi (0:ℝ)) :
      HasDerivWithinAt (fun x : ℝ => x^2) (2*x) (Ioi 0) x := by
    simpa using (hasDerivAt_pow 2 x).hasDerivWithinAt
  have h := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hd square_injOn
    (fun t : ℝ => t^((9:ℝ)/2)*Real.exp (-t-z^2/(4*t)))
  rw [square_image] at h
  have hi : (∫ t in Ioi (0:ℝ), t^((9:ℝ)/2)*Real.exp (-t-z^2/(4*t))) =
      2*moment 5 (z/2) := by
    rw [h, moment, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    have hp : (x^2)^((9:ℝ)/2)=x^9 := by
      rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx0.le]
      norm_num
    have he : -x^2-z^2/(4*x^2) = -x^2-((z/2)/x)^2 := by ring
    simp only [smul_eq_mul, abs_of_pos (mul_pos (by norm_num : (0:ℝ)<2) hx0), hp, he, kernel]
    ring
  rw [hi, moment_five (by linarith : 0 ≤ z/2), mass_formula (by linarith : 0 ≤ z/2)]
  have he : -2*(z/2) = -z := by ring
  rw [he]
  ring

#print axioms laplace_half_eleven
end DGRHS.Gaussian.D11Imported.ReciprocalGaussian
