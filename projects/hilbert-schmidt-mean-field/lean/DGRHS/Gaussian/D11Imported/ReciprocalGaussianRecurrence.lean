/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.ReciprocalGaussianMoments

noncomputable section
open MeasureTheory Set Filter
open scoped Topology
namespace DGRHS.Gaussian.D11Imported.ReciprocalGaussian

lemma quotient_pow_kernel_integrable (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => (x^(2*n)/x^2)*kernel a x) (Ioi 0) := by
  cases n with
  | zero =>
    have he : (fun x : ℝ => (x^(2*0)/x^2)*kernel a x) =
        (fun x : ℝ => (1/a)*((a/x^2)*kernel a x)) := by
      funext x
      simp only [mul_zero, pow_zero]
      field_simp
    rw [he]
    exact (weighted_integrable ha).const_mul (1/a)
  | succ n =>
    apply (pow_kernel_integrable (2*n) a).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [Nat.mul_succ, pow_add]
    field_simp [ne_of_gt (show (0:ℝ)<x from hx)]

def momentDerivative (n : ℕ) (a x : ℝ) : ℝ :=
  (2*(n:ℝ)+1)*(x^(2*n)*kernel a x) - 2*(x^(2*n+2)*kernel a x) +
    (2*a^2)*((x^(2*n)/x^2)*kernel a x)

lemma momentDerivative_integrable (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (momentDerivative n a) (Ioi 0) := by
  exact (((pow_kernel_integrable (2*n) a).const_mul (2*(n:ℝ)+1)).sub
    ((pow_kernel_integrable (2*n+2) a).const_mul 2)).add
    ((quotient_pow_kernel_integrable n ha).const_mul (2*a^2))

lemma momentDerivative_eq (n : ℕ) (a : ℝ) {x : ℝ} (hx : 0 < x) :
    (2*(n:ℝ)+1)*x^(2*n)*kernel a x +
      x^(2*n+1)*((-2*x+2*a^2/x^3)*kernel a x) = momentDerivative n a x := by
  unfold momentDerivative
  simp only [pow_add]
  field_simp
  ring

lemma integral_momentDerivative (n : ℕ) {a : ℝ} (ha : 0 < a) :
    (∫ x in Ioi (0:ℝ), momentDerivative n a x) = 0 := by
  have hp (x : ℝ) (_ : x ∈ Ioi (0:ℝ)) :
      HasDerivAt (fun x : ℝ => x^(2*n+1)) ((2*(n:ℝ)+1)*x^(2*n)) x := by
    simpa only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
      using hasDerivAt_pow (2*n+1) x
  have hi : IntegrableOn (fun x : ℝ => (2*(n:ℝ)+1)*x^(2*n)*kernel a x +
      x^(2*n+1)*((-2*x+2*a^2/x^3)*kernel a x)) (Ioi 0) := by
    apply (momentDerivative_integrable n ha).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (momentDerivative_eq n a hx).symm
  have h := integral_Ioi_deriv_mul_eq_sub hp (fun x hx => kernel_spatial_hasDerivAt a hx)
    hi (pow_kernel_tendsto_zero (2*n+1) (by omega) a) (pow_kernel_tendsto_atTop (2*n+1) a)
  rw [sub_self] at h
  calc
    _ = ∫ x in Ioi (0:ℝ), (2*(n:ℝ)+1)*x^(2*n)*kernel a x +
        x^(2*n+1)*((-2*x+2*a^2/x^3)*kernel a x) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact (momentDerivative_eq n a hx).symm
    _ = 0 := h

lemma moment_one {a : ℝ} (ha : 0 < a) :
    moment 1 a = (a+1/2)*mass a := by
  have hw : (∫ x in Ioi (0:ℝ), (x^(2*0)/x^2)*kernel a x) = mass a/a := by
    calc
      _ = ∫ x in Ioi (0:ℝ), (1/a)*((a/x^2)*kernel a x) := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by simp only [mul_zero, pow_zero]; field_simp)
      _ = mass a/a := by rw [integral_const_mul, weighted_integral ha]; ring
  have h := integral_momentDerivative 0 ha
  unfold momentDerivative at h
  simp only [Nat.cast_zero, Nat.mul_zero, Nat.zero_add] at h
  rw [integral_add
      (f := fun x : ℝ => (2*(0:ℝ)+1)*(x^0*kernel a x) - 2*(x^2*kernel a x))
      (g := fun x : ℝ => (2*a^2)*((x^0/x^2)*kernel a x))
      (((pow_kernel_integrable 0 a).const_mul (2*(0:ℝ)+1)).sub
        ((pow_kernel_integrable 2 a).const_mul 2))
      ((quotient_pow_kernel_integrable 0 ha).const_mul (2*a^2)),
    integral_sub ((pow_kernel_integrable 0 a).const_mul (2*(0:ℝ)+1))
      ((pow_kernel_integrable 2 a).const_mul 2),
    integral_const_mul, integral_const_mul, integral_const_mul, hw] at h
  change (2*(0:ℝ)+1)*moment 0 a - 2*moment 1 a + (2*a^2)*(mass a/a) = 0 at h
  rw [moment_zero] at h
  field_simp at h
  nlinarith

lemma moment_recurrence (n : ℕ) {a : ℝ} (ha : 0 < a) :
    moment (n+2) a = ((n:ℝ)+3/2)*moment (n+1) a + a^2*moment n a := by
  have hw : (∫ x in Ioi (0:ℝ), (x^(2*(n+1))/x^2)*kernel a x) = moment n a := by
    unfold moment
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [Nat.mul_add, Nat.mul_one, pow_add]
    field_simp [ne_of_gt (show (0:ℝ)<x from hx)]
  have h := integral_momentDerivative (n+1) ha
  unfold momentDerivative at h
  rw [integral_add
      (f := fun x : ℝ => (2*((n+1:ℕ):ℝ)+1)*(x^(2*(n+1))*kernel a x) - 2*(x^(2*(n+1)+2)*kernel a x))
      (g := fun x : ℝ => (2*a^2)*((x^(2*(n+1))/x^2)*kernel a x))
      (((pow_kernel_integrable (2*(n+1)) a).const_mul (2*((n+1:ℕ):ℝ)+1)).sub
        ((pow_kernel_integrable (2*(n+1)+2) a).const_mul 2))
      ((quotient_pow_kernel_integrable (n+1) ha).const_mul (2*a^2)),
    integral_sub ((pow_kernel_integrable (2*(n+1)) a).const_mul (2*((n+1:ℕ):ℝ)+1))
      ((pow_kernel_integrable (2*(n+1)+2) a).const_mul 2),
    integral_const_mul, integral_const_mul, integral_const_mul, hw] at h
  have hn : 2*(n+1)+2 = 2*(n+2) := by omega
  rw [hn] at h
  change (2*((n+1:ℕ):ℝ)+1)*moment (n+1) a - 2*moment (n+2) a + (2*a^2)*moment n a = 0 at h
  push_cast at h
  linarith

#print axioms moment_recurrence
end DGRHS.Gaussian.D11Imported.ReciprocalGaussian
