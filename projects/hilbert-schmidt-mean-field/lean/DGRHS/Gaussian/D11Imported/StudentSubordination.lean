/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.StudentFourierGaussian

/-! Absolute integrability of the Gamma-Gaussian mixture. This supplies the
Fubini justification for the oscillatory Fourier integral. -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace DGRHS.Gaussian.D11Imported.StudentIntegral

def mixture {d : ℕ} (a c : ℝ) (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) : ℝ :=
  t^(a-1)*Real.exp (-t)*Real.exp (-(c*t)*‖x‖^2)

lemma mixture_measurable (d : ℕ) (a c : ℝ) :
    Measurable (Function.uncurry (mixture (d := d) a c)) := by
  unfold mixture Function.uncurry
  fun_prop

lemma mixture_nonneg {d : ℕ} (a c : ℝ) (x : EuclideanSpace ℝ (Fin d))
    {t : ℝ} (ht : 0 ≤ t) : 0 ≤ mixture a c x t := by
  unfold mixture
  positivity

lemma mixture_eq {d : ℕ} (a c : ℝ) (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    mixture a c x t = t^(a-1)*Real.exp (-((1+c*‖x‖^2)*t)) := by
  unfold mixture
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma mixture_integrable_right {d : ℕ} {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (x : EuclideanSpace ℝ (Fin d)) : IntegrableOn (mixture a c x) (Ioi 0) := by
  change IntegrableOn (fun t : ℝ => mixture a c x t) (Ioi 0)
  simp_rw [mixture_eq]
  exact gamma_laplace_integrable ha (by positivity)

lemma mixture_integral_right {d : ℕ} {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (x : EuclideanSpace ℝ (Fin d)) :
    (∫ t in Ioi (0:ℝ), mixture a c x t) = (1+c*‖x‖^2)^(-a)*Real.Gamma a := by
  simp_rw [mixture_eq]
  exact gamma_laplace ha (by positivity)

lemma mixture_integrable (d : ℕ) {a c : ℝ} (ha : (d:ℝ)/2 < a) (hc : 0 < c) :
    Integrable (Function.uncurry (mixture (d := d) a c))
      (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
  have ha0 : 0 < a := lt_of_le_of_lt (by positivity) ha
  apply (integrable_prod_iff (mixture_measurable d a c).aestronglyMeasurable).mpr
  constructor
  · exact ae_of_all _ (fun x => mixture_integrable_right ha0 hc x)
  · have he (x : EuclideanSpace ℝ (Fin d)) :
        (∫ t in Ioi (0:ℝ), ‖mixture a c x t‖) = (1+c*‖x‖^2)^(-a)*Real.Gamma a := by
      calc
        _ = ∫ t in Ioi (0:ℝ), mixture a c x t := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          rw [Real.norm_eq_abs, abs_of_nonneg (mixture_nonneg a c x ht.le)]
        _ = _ := mixture_integral_right ha0 hc x
    change Integrable (fun x : EuclideanSpace ℝ (Fin d) => ∫ t in Ioi (0:ℝ), ‖mixture a c x t‖)
    simp_rw [he]
    exact (student_integrable d ha hc).mul_const (Real.Gamma a)

lemma oscillatory_mixture_integrable (d : ℕ) {a c : ℝ}
    (ha : (d:ℝ)/2 < a) (hc : 0 < c) (w : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun p : EuclideanSpace ℝ (Fin d) × ℝ => phase w p.1 * (mixture a c p.1 p.2:ℂ))
      (volume.prod (volume.restrict (Ioi (0:ℝ)))) := by
  apply (mixture_integrable d ha hc).norm.mono'
    (((phase_measurable w).comp measurable_fst).mul
      (Complex.measurable_ofReal.comp (mixture_measurable d a c))).aestronglyMeasurable
  exact ae_of_all _ (fun p => by
    change ‖phase w p.1 * (mixture a c p.1 p.2:ℂ)‖ ≤ ‖mixture a c p.1 p.2‖
    rw [norm_mul, phase_norm, one_mul, Complex.norm_real])

#print axioms oscillatory_mixture_integrable
end DGRHS.Gaussian.D11Imported.StudentIntegral
