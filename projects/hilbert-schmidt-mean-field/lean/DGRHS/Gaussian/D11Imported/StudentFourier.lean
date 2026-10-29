/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.StudentSubordination

/-! Gamma/Gaussian subordination for the actual Euclidean Fourier integral.
All exchanges are justified by absolute integrability of the mixture. -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace DGRHS.Gaussian.D11Imported.StudentIntegral
set_option backward.isDefEq.respectTransparency false

lemma mixture_fourier_left (d : ℕ) (a : ℝ) {c t : ℝ} (hc : 0 < c) (ht : 0 < t)
    (w : EuclideanSpace ℝ (Fin d)) :
    (∫ x : EuclideanSpace ℝ (Fin d), phase w x * (mixture a c x t:ℂ)) =
      (((Real.pi/c)^((d:ℝ)/2)*t^(a-(d:ℝ)/2-1)*
        Real.exp (-t-Real.pi^2*‖w‖^2/(c*t))):ℝ) := by
  have he (x : EuclideanSpace ℝ (Fin d)) :
      phase w x*(mixture a c x t:ℂ) =
        ((t^(a-1)*Real.exp (-t):ℝ):ℂ) * (phase w x*(Real.exp (-(c*t)*‖x‖^2):ℂ)) := by
    unfold mixture
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul, gaussian_fourier d (mul_pos hc ht), ← Complex.ofReal_mul]
  congr 1
  rw [show -t-Real.pi^2*‖w‖^2/(c*t) = -t+(-Real.pi^2*‖w‖^2/(c*t)) by ring, Real.exp_add]
  calc
    _ = (t^(a-1)*(Real.pi/(c*t))^((d:ℝ)/2))*Real.exp (-t)*
        Real.exp (-Real.pi^2*‖w‖^2/(c*t)) := by ring
    _ = _ := by rw [powers d hc ht]; ring

lemma student_fourier_subordination (d : ℕ) {a c : ℝ}
    (ha : (d:ℝ)/2 < a) (hc : 0 < c) (w : EuclideanSpace ℝ (Fin d)) :
    (∫ x : EuclideanSpace ℝ (Fin d), phase w x*((1+c*‖x‖^2)^(-a):ℝ)) *
      (Real.Gamma a:ℂ) =
    (((Real.pi/c)^((d:ℝ)/2):ℝ):ℂ) *
      ((∫ t in Ioi (0:ℝ), t^(a-(d:ℝ)/2-1)*Real.exp (-t-Real.pi^2*‖w‖^2/(c*t))):ℝ) := by
  have ha0 : 0 < a := lt_of_le_of_lt (by positivity) ha
  calc
    _ = ∫ x : EuclideanSpace ℝ (Fin d),
        phase w x * (((1+c*‖x‖^2)^(-a)*Real.Gamma a:ℝ):ℂ) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by push_cast; ring)
    _ = ∫ x : EuclideanSpace ℝ (Fin d),
        phase w x * ((∫ t in Ioi (0:ℝ), mixture a c x t):ℝ) := by
      simp_rw [mixture_integral_right ha0 hc]
    _ = ∫ x : EuclideanSpace ℝ (Fin d), ∫ t in Ioi (0:ℝ),
        phase w x * (mixture a c x t:ℂ) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by
        dsimp only
        rw [integral_const_mul, integral_complex_ofReal])
    _ = ∫ t in Ioi (0:ℝ), ∫ x : EuclideanSpace ℝ (Fin d),
        phase w x * (mixture a c x t:ℂ) :=
      integral_integral_swap (oscillatory_mixture_integrable d ha hc w)
    _ = ∫ t in Ioi (0:ℝ),
        ((((Real.pi/c)^((d:ℝ)/2)*t^(a-(d:ℝ)/2-1)*
          Real.exp (-t-Real.pi^2*‖w‖^2/(c*t))):ℝ):ℂ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mixture_fourier_left d a hc ht w
    _ = _ := by
      simp_rw [mul_assoc, Complex.ofReal_mul]
      rw [integral_const_mul]
      simp_rw [← Complex.ofReal_mul]
      rw [integral_complex_ofReal]
      push_cast
      rfl

#print axioms student_fourier_subordination
end DGRHS.Gaussian.D11Imported.StudentIntegral
