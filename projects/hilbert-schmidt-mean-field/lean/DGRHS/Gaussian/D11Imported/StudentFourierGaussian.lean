/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.StudentIntegral

/-! The Gaussian Fourier step in the Gamma-subordination proof of the
Student profile's Fourier transform. -/
noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace DGRHS.Gaussian.D11Imported.StudentIntegral

def phase {d : ℕ} (w x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  Complex.exp (-((2*Real.pi*⟪w,x⟫):ℝ)*Complex.I)

lemma phase_norm {d : ℕ} (w x : EuclideanSpace ℝ (Fin d)) : ‖phase w x‖ = 1 := by
  simp [phase, Complex.norm_exp]

lemma phase_measurable {d : ℕ} (w : EuclideanSpace ℝ (Fin d)) : Measurable (phase w) := by
  unfold phase
  fun_prop

lemma gaussian_fourier (d : ℕ) {b : ℝ} (hb : 0 < b) (w : EuclideanSpace ℝ (Fin d)) :
    (∫ x : EuclideanSpace ℝ (Fin d), phase w x * (Real.exp (-b*‖x‖^2):ℂ)) =
      (((Real.pi/b)^((d:ℝ)/2)*Real.exp (-Real.pi^2*‖w‖^2/b)):ℝ) := by
  have h := GaussianFourier.integral_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    (show 0 < (b:ℂ).re from hb) (-2*Real.pi*Complex.I) w
  have he (x : EuclideanSpace ℝ (Fin d)) :
      phase w x * (Real.exp (-b*‖x‖^2):ℂ) =
      Complex.exp (-(b:ℂ)*(‖x‖:ℂ)^2+(-2*Real.pi*Complex.I)*(⟪w,x⟫:ℂ)) := by
    unfold phase
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [h]
  have he2 : (-2*(Real.pi:ℂ)*Complex.I)^2*(‖w‖:ℂ)^2/(4*(b:ℂ)) =
      ((-Real.pi^2*‖w‖^2/b:ℝ):ℂ) := by
    push_cast
    rw [mul_pow, mul_pow, Complex.I_sq]
    ring
  rw [he2]
  have hp : ((Real.pi:ℂ)/(b:ℂ))^((Fintype.card (Fin d):ℂ)/2) =
      ((Real.pi/b)^((d:ℝ)/2):ℝ) := by
    rw [← Complex.ofReal_div]
    have hc := Complex.ofReal_cpow (show 0 ≤ Real.pi/b by positivity) ((d:ℝ)/2)
    simpa using hc.symm
  rw [hp]
  push_cast
  rfl

#print axioms gaussian_fourier
end DGRHS.Gaussian.D11Imported.StudentIntegral
