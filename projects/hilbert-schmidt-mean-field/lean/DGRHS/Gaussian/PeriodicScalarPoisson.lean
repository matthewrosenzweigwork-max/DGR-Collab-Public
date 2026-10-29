import DGRHS.Gaussian.PeriodicGaussianImageRemainder
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-! Native Mathlib Poisson summation specialized at every spatial point to the
actual Gaussian. The primary Gaussian and Poisson declarations are reused
without any unproved heat-kernel or Fourier coefficient identification. -/
noncomputable section
open MeasureTheory Set Filter Asymptotics
open scoped Classical BigOperators FourierTransform
namespace DGRHS.Periodic

lemma periodicScalarGaussian_poisson (a : ℝ) (ha : 0<a) (x : ℝ) :
    (∑' n : ℤ,Complex.exp (-(Real.pi:ℂ)*a*(x+n)^2)) =
      (1/(a:ℂ)^(1/2:ℂ)) *
        ∑' n : ℤ,Complex.exp (-(Real.pi:ℂ)/a*(n:ℂ)^2)*fourier n (x : UnitAddCircle) := by
  let f : ℝ → ℂ := fun y => Complex.exp (-(Real.pi:ℂ)*a*y^2)
  have ha' : 0<(a:ℂ).re := ha
  have hF : 𝓕 f = fun y : ℝ =>
      (1/(a:ℂ)^(1/2:ℂ))*Complex.exp (-(Real.pi:ℂ)/a*y^2) := fourier_gaussian_pi ha'
  have hf : f =O[cocompact ℝ] (fun y : ℝ => |y|^(-2:ℝ)) := by
    convert (isLittleO_exp_neg_mul_sq_cocompact
      (a := (Real.pi:ℂ)*a) (by simpa using mul_pos Real.pi_pos ha) (-2)).isBigO using 1
    simp only [f,neg_mul]
  have hFf : (𝓕 f) =O[cocompact ℝ] (fun y : ℝ => |y|^(-2:ℝ)) := by
    rw [hF]
    have hc : 0<((Real.pi:ℂ)/a).re := by simpa using div_pos Real.pi_pos ha
    convert ((isLittleO_exp_neg_mul_sq_cocompact hc (-2)).isBigO.const_mul_left
      (1/(a:ℂ)^(1/2:ℂ))) using 1
    simp only [neg_div]
  have h := Real.tsum_eq_tsum_fourier_of_rpow_decay (f := f) (by fun_prop)
    (by norm_num : (1:ℝ)<2) hf hFf x
  rw [hF] at h
  simpa only [f,Complex.ofReal_add,Complex.ofReal_intCast,mul_assoc,tsum_mul_left] using h

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicScalarGaussian_poisson
#check @DGRHS.Periodic.periodicScalarGaussian_poisson
