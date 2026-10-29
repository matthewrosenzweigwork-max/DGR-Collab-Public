/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic

/-! The beta-integral normalization of the manuscript's Euclidean profile.
The proof evaluates its positive Gamma/Gaussian mixture by Tonelli. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DGRHS.Gaussian.D11Imported.StudentIntegral

lemma gamma_laplace {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    (∫ t : ℝ in Ioi 0, t^(a-1) * Real.exp (-(R*t))) =
      R^(-a) * Real.Gamma a := by
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi ha hR, one_div,
    Real.inv_rpow hR.le, ← Real.rpow_neg hR.le]

lemma gamma_laplace_integrable {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    IntegrableOn (fun t : ℝ => t^(a-1) * Real.exp (-(R*t))) (Ioi 0) := by
  apply Integrable.of_integral_ne_zero
  rw [gamma_laplace ha hR]
  exact (mul_pos (Real.rpow_pos_of_pos hR _) (Real.Gamma_pos_of_pos ha)).ne'

lemma gamma_laplace_lintegral {a R : ℝ} (ha : 0 < a) (hR : 0 < R) :
    (∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t^(a-1) * Real.exp (-(R*t)))) =
      ENNReal.ofReal (R^(-a) * Real.Gamma a) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (gamma_laplace_integrable ha hR),
    gamma_laplace ha hR]
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le

lemma gaussian_integral (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ (Fin d), Real.exp (-t*‖x‖^2)) = (Real.pi/t)^((d:ℝ)/2) := by
  simpa using GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin d)) ht

lemma gaussian_lintegral (d : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫⁻ x : EuclideanSpace ℝ (Fin d), ENNReal.ofReal (Real.exp (-t*‖x‖^2))) =
      ENNReal.ofReal ((Real.pi/t)^((d:ℝ)/2)) := by
  have hi : Integrable (fun x : EuclideanSpace ℝ (Fin d) => Real.exp (-t*‖x‖^2)) := by
    apply Integrable.of_integral_ne_zero
    rw [gaussian_integral d ht]
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (fun _ => (Real.exp_pos _).le)),
    gaussian_integral d ht]

lemma student_laplace (d : ℕ) {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (x : EuclideanSpace ℝ (Fin d)) :
    ENNReal.ofReal ((1+c*‖x‖^2)^(-a) * Real.Gamma a) =
      ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal (t^(a-1)*Real.exp (-t)*Real.exp (-(c*t)*‖x‖^2)) := by
  rw [← gamma_laplace_lintegral ha (by positivity : 0 < 1+c*‖x‖^2)]
  apply lintegral_congr
  intro t
  rw [show -((1+c*‖x‖^2)*t) = -t + -(c*t)*‖x‖^2 by ring, Real.exp_add]
  congr 1
  ring

lemma powers (d : ℕ) {a c t : ℝ} (hc : 0 < c) (ht : 0 < t) :
    t^(a-1) * (Real.pi/(c*t))^((d:ℝ)/2) =
      (Real.pi/c)^((d:ℝ)/2) * t^(a-(d:ℝ)/2-1) := by
  rw [show Real.pi/(c*t) = (Real.pi/c)/t by field_simp,
    Real.div_rpow (by positivity) ht.le, div_eq_mul_inv,
    ← Real.rpow_neg ht.le]
  calc
    _ = (Real.pi/c)^((d:ℝ)/2) * (t^(a-1)*t^(-((d:ℝ)/2))) := by ring
    _ = _ := by rw [← Real.rpow_add ht]; congr 2 <;> ring

lemma student_lintegral (d : ℕ) {a c : ℝ} (ha : (d:ℝ)/2 < a) (hc : 0 < c) :
    (∫⁻ x : EuclideanSpace ℝ (Fin d), ENNReal.ofReal ((1+c*‖x‖^2)^(-a))) *
      ENNReal.ofReal (Real.Gamma a) =
    ENNReal.ofReal ((Real.pi/c)^((d:ℝ)/2) * Real.Gamma (a-(d:ℝ)/2)) := by
  have ha0 : 0 < a := lt_of_le_of_lt (by positivity) ha
  have hme : Measurable (fun p : EuclideanSpace ℝ (Fin d) × ℝ =>
      ENNReal.ofReal (p.2^(a-1)*Real.exp (-p.2)*Real.exp (-(c*p.2)*‖p.1‖^2))) := by fun_prop
  calc
    _ = ∫⁻ x : EuclideanSpace ℝ (Fin d),
        ENNReal.ofReal ((1+c*‖x‖^2)^(-a) * Real.Gamma a) := by
      rw [← lintegral_mul_const _ (by fun_prop)]
      apply lintegral_congr
      intro x
      exact (ENNReal.ofReal_mul (by positivity)).symm
    _ = ∫⁻ x : EuclideanSpace ℝ (Fin d), ∫⁻ t : ℝ in Ioi 0,
        ENNReal.ofReal (t^(a-1)*Real.exp (-t)*Real.exp (-(c*t)*‖x‖^2)) := by
      simp_rw [student_laplace d ha0 hc]
    _ = ∫⁻ t : ℝ in Ioi 0, ∫⁻ x : EuclideanSpace ℝ (Fin d),
        ENNReal.ofReal (t^(a-1)*Real.exp (-t)*Real.exp (-(c*t)*‖x‖^2)) :=
      lintegral_lintegral_swap hme.aemeasurable
    _ = ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal
        ((Real.pi/c)^((d:ℝ)/2) * (t^(a-(d:ℝ)/2-1)*Real.exp (-t))) := by
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ t^(a-1)*Real.exp (-t))]
      rw [lintegral_const_mul _ (by fun_prop), gaussian_lintegral d (mul_pos hc ht0),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      calc
        _ = (t^(a-1)*(Real.pi/(c*t))^((d:ℝ)/2))*Real.exp (-t) := by ring
        _ = _ := by rw [powers d hc ht0]; ring
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ (Real.pi/c)^((d:ℝ)/2))]
      rw [lintegral_const_mul _ (by fun_prop)]
      have hg := gamma_laplace_lintegral (show 0 < a-(d:ℝ)/2 by linarith) (by norm_num : (0:ℝ)<1)
      simp only [one_mul, Real.one_rpow] at hg
      rw [hg, ← ENNReal.ofReal_mul (by positivity)]

lemma student_lintegral_eq (d : ℕ) {a c : ℝ} (ha : (d:ℝ)/2 < a) (hc : 0 < c) :
    (∫⁻ x : EuclideanSpace ℝ (Fin d), ENNReal.ofReal ((1+c*‖x‖^2)^(-a))) =
      ENNReal.ofReal ((Real.pi/c)^((d:ℝ)/2) * Real.Gamma (a-(d:ℝ)/2) / Real.Gamma a) := by
  have ha0 : 0 < a := lt_of_le_of_lt (by positivity) ha
  have hg := Real.Gamma_pos_of_pos ha0
  apply (ENNReal.mul_left_inj (show ENNReal.ofReal (Real.Gamma a) ≠ 0 by positivity)
    ENNReal.ofReal_ne_top).mp
  rw [student_lintegral d ha hc, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

lemma student_integral (d : ℕ) {a c : ℝ} (ha : (d:ℝ)/2 < a) (hc : 0 < c) :
    (∫ x : EuclideanSpace ℝ (Fin d), (1+c*‖x‖^2)^(-a)) =
      (Real.pi/c)^((d:ℝ)/2) * Real.Gamma (a-(d:ℝ)/2) / Real.Gamma a := by
  have ha0 : 0 < a := lt_of_le_of_lt (by positivity) ha
  have hag : 0 < a-(d:ℝ)/2 := by linarith
  have hm : Measurable (fun x : EuclideanSpace ℝ (Fin d) => (1+c*‖x‖^2)^(-a)) := by fun_prop
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun _ => by positivity))
    hm.aestronglyMeasurable, student_lintegral_eq d ha hc, ENNReal.toReal_ofReal (by positivity)]

lemma student_integrable (d : ℕ) {a c : ℝ} (ha : (d:ℝ)/2 < a) (hc : 0 < c) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => (1+c*‖x‖^2)^(-a)) := by
  apply Integrable.of_integral_ne_zero
  rw [student_integral d ha hc]
  have ha0 : 0 < a := lt_of_le_of_lt (by positivity) ha
  have hag : 0 < a-(d:ℝ)/2 := by linarith
  positivity

lemma student_integral_pi (d : ℕ) {a c : ℝ} (ha : (d:ℝ)/2 < a) (hc : 0 < c) :
    (∫ x : Fin d → ℝ, (1+c*∑ i, (x i)^2)^(-a)) =
      (Real.pi/c)^((d:ℝ)/2) * Real.Gamma (a-(d:ℝ)/2) / Real.Gamma a := by
  have h := (PiLp.volume_preserving_toLp (Fin d)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding
    (fun x : EuclideanSpace ℝ (Fin d) => (1+c*‖x‖^2)^(-a))
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] at h
  refine h.trans ?_
  simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] using student_integral d ha hc

#print axioms student_integral_pi

end DGRHS.Gaussian.D11Imported.StudentIntegral
