/- UNCHECKED outside frozen proof. Exact scalar linear/quadratic Gaussian
integrability and transform for the static shared-process tilt. Reuses pinned
Gaussian density, Gaussian integral and Haar translation; no desired MGF law
or convergence assumption. StatLean square-MGF adaptation/license retained.
Primary source searches/captures: research/reuse/pinned-tilted-gaussian.
Density-collapse/withDensity proof pattern adapted under Apache-2.0 from
StatLean/Stat-Lean86b3823f77fc2b0f5a9923f85b588a4f8a65f94c,
StatLean/MultipleTesting/ForMathlib/GaussianSquareMGF.lean; original SHA
9195855af41b9e16c48cdaae4130f8fc724ec26c426bf09e74be6dd7f12418ed.
Original/license retained in Gaussian/Imported and worker upstream-originals.
The adapted proof is new and uncompiled; no upstream verdict transferred. -/
import DGRHS.Gaussian.FiniteLaplace
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Group.Integral
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace DGRHS.Gaussian

lemma gaussianPDF_mul_linear_quadratic (β a t x : ℝ) (hm : 0 < 1+β*a) :
    gaussianPDFReal 0 1 x * Real.exp (t*x-(β*a/2)*x^2) =
      ((Real.sqrt (2*Real.pi))⁻¹ * Real.exp (t^2/(2*(1+β*a)))) *
        Real.exp (-((1+β*a)/2)*(x-t/(1+β*a))^2) := by
  have hpdf : gaussianPDFReal 0 1 x =
      (Real.sqrt (2*Real.pi))⁻¹ * Real.exp (-x^2/2) := by
    rw [gaussianPDFReal]
    simp only [NNReal.coe_one,mul_one,sub_zero]
  calc
    _ = (Real.sqrt (2*Real.pi))⁻¹ *
        Real.exp (-x^2/2+(t*x-(β*a/2)*x^2)) := by
      rw [hpdf,mul_assoc,← Real.exp_add]
    _ = (Real.sqrt (2*Real.pi))⁻¹ *
        Real.exp (t^2/(2*(1+β*a)) + -((1+β*a)/2)*(x-t/(1+β*a))^2) := by
      congr 1
      congr 1
      field_simp [hm.ne']
      <;> ring
    _ = _ := by rw [Real.exp_add]; ring

lemma standardGaussian_tilted_quadratic_integrable (β a t : ℝ)
    (hm : 0 < 1+β*a) :
    Integrable (fun x : ℝ => Real.exp (t*x-(β*a/2)*x^2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
      (ae_of_all _ (fun _ => gaussianPDF_lt_top))]
  simp only [toReal_gaussianPDF,smul_eq_mul]
  have he : (fun x : ℝ => gaussianPDFReal 0 1 x * Real.exp (t*x-(β*a/2)*x^2)) =
      fun x => ((Real.sqrt (2*Real.pi))⁻¹ * Real.exp (t^2/(2*(1+β*a)))) *
        Real.exp (-((1+β*a)/2)*(x-t/(1+β*a))^2) :=
    funext (fun x => gaussianPDF_mul_linear_quadratic β a t x hm)
  rw [he]
  exact ((measurePreserving_sub_right (volume : Measure ℝ) (t/(1+β*a))).integrable_comp_of_integrable
    (integrable_exp_neg_mul_sq (div_pos hm (by norm_num)))).const_mul _

lemma standardGaussian_tilted_quadratic_integral (β a t : ℝ)
    (hm : 0 < 1+β*a) :
    (∫ x : ℝ, Real.exp (t*x-(β*a/2)*x^2) ∂gaussianReal 0 1) =
      Real.exp (t^2/(2*(1+β*a))) * (Real.sqrt (1+β*a))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  simp_rw [smul_eq_mul,gaussianPDF_mul_linear_quadratic β a t _ hm]
  rw [integral_const_mul,
    integral_sub_right_eq_self (fun x : ℝ => Real.exp (-((1+β*a)/2)*x^2))
      (t/(1+β*a)),integral_gaussian ((1+β*a)/2)]
  have hs : (Real.sqrt (2*Real.pi))⁻¹ * Real.sqrt (Real.pi/((1+β*a)/2)) =
      (Real.sqrt (1+β*a))⁻¹ := by
    have hp : (0 : ℝ) ≤ (2*Real.pi)⁻¹ := by positivity
    rw [← Real.sqrt_inv,← Real.sqrt_mul hp]
    have hc : (2*Real.pi)⁻¹ * (Real.pi/((1+β*a)/2)) = (1+β*a)⁻¹ := by
      field_simp [Real.pi_ne_zero,hm.ne']
    rw [hc,Real.sqrt_inv]
  calc
    _ = ((Real.sqrt (2*Real.pi))⁻¹ * Real.sqrt (Real.pi/((1+β*a)/2))) *
        Real.exp (t^2/(2*(1+β*a))) := by ring
    _ = _ := by rw [hs]; ring

/-- The scalar centered factor needed by actual finite joint products. -/
lemma standardGaussian_centered_tilted_quadratic (β a t : ℝ)
    (hm : 0 < 1+β*a) :
    Integrable (fun x : ℝ => Real.exp (t*x+(β*a/2)*(1-x^2))) (gaussianReal 0 1) ∧
    (∫ x : ℝ, Real.exp (t*x+(β*a/2)*(1-x^2)) ∂gaussianReal 0 1) =
      Real.exp (β*a/2+t^2/(2*(1+β*a))) * (Real.sqrt (1+β*a))⁻¹ := by
  have he : (fun x : ℝ => Real.exp (t*x+(β*a/2)*(1-x^2))) =
      fun x => Real.exp (β*a/2) * Real.exp (t*x-(β*a/2)*x^2) := by
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  refine ⟨(standardGaussian_tilted_quadratic_integrable β a t hm).const_mul _,?_⟩
  rw [integral_const_mul,standardGaussian_tilted_quadratic_integral β a t hm,
    ← mul_assoc,← Real.exp_add]
end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.standardGaussian_tilted_quadratic_integrable
#print axioms DGRHS.Gaussian.standardGaussian_tilted_quadratic_integral
#print axioms DGRHS.Gaussian.standardGaussian_centered_tilted_quadratic
#check DGRHS.Gaussian.standardGaussian_centered_tilted_quadratic
