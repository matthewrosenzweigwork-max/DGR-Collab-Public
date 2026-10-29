import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Actual two-dimensional half-variance Gaussian law needed for the source
first-shell polar identity. Native Mathlib Gaussian.Real and WithDensity,
Apache2; pinned declarations/hashes read in UID1006 request20b480685e6948baa35ba6591f1a11fb.
The probability measure and its normalized density are constructed, not
supplied as a favorable Gaussian-field or polar-integral hypothesis. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace DGRHS.Periodic

lemma periodic_halfGaussian_pdf (x : ℝ) :
    gaussianPDFReal 0 (1/2) x = (Real.sqrt Real.pi)⁻¹*Real.exp (-x^2) := by
  have htwo : (2:ℝ)*((1/2:NNReal):ℝ)=1 := by norm_num
  have hpi : (2:ℝ)*Real.pi*((1/2:NNReal):ℝ)=Real.pi := by
    norm_num
    ring
  rw [gaussianPDFReal,hpi,htwo,sub_zero,div_one]

lemma periodic_halfGaussian_pair_pdf (a b : ℝ) :
    gaussianPDFReal 0 (1/2) a * gaussianPDFReal 0 (1/2) b =
      Real.pi⁻¹*Real.exp (-(a^2+b^2)) := by
  rw [periodic_halfGaussian_pdf,periodic_halfGaussian_pdf]
  calc
    _ = (Real.sqrt Real.pi)⁻¹^2*Real.exp (-(a^2)-b^2) := by
      rw [show -(a^2)-b^2=-(a^2)+(-(b^2)) from by ring,Real.exp_add]
      ring
    _ = _ := by
      rw [inv_pow,Real.sq_sqrt Real.pi_pos.le]
      congr 1
      congr 1
      ring

/-- The actual Gaussian pair has the exact normalized planar density. -/
theorem periodic_halfGaussian_pair_law :
    (gaussianReal 0 (1/2)).prod (gaussianReal 0 (1/2)) =
      (volume : Measure (ℝ × ℝ)).withDensity
        (fun p => ENNReal.ofReal (Real.pi⁻¹*Real.exp (-(p.1^2+p.2^2)))) := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1/2:NNReal)≠0),
    prod_withDensity (measurable_gaussianPDF 0 (1/2)) (measurable_gaussianPDF 0 (1/2))]
  congr 1
  funext p
  change ENNReal.ofReal (gaussianPDFReal 0 (1/2) p.1) *
    ENNReal.ofReal (gaussianPDFReal 0 (1/2) p.2) = _
  rw [←ENNReal.ofReal_mul (gaussianPDFReal_nonneg 0 (1/2) p.1),
    periodic_halfGaussian_pair_pdf]

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodic_halfGaussian_pdf
#print axioms DGRHS.Periodic.periodic_halfGaussian_pair_pdf
#print axioms DGRHS.Periodic.periodic_halfGaussian_pair_law
#check @DGRHS.Periodic.periodic_halfGaussian_pair_law
