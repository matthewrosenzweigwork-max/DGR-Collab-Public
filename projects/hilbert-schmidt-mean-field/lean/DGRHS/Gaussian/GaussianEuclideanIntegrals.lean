import DGRHS.Gaussian.RieszGaussianEuclidean
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-! Actual Lebesgue Gaussian integrals used in the short-range L2 comparison.
Pinned Mathlib's Euclidean Gaussian integral is instantiated at the actual scale. -/
noncomputable section
open MeasureTheory Real GaussianFourier
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma integrable_gaussianEuclidean_neg_norm_sq (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (-b * ‖x‖ ^ 2)) := by
  have hi := integrable_cexp_neg_mul_sq_norm_add_of_euclideanSpace
    (b := (b : ℂ)) (by simpa using hb) (0 : ℂ) (0 : EuclideanSpace ℝ ι)
  convert hi.re using 1
  funext x
  simp [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg, ← Complex.ofReal_exp]

lemma integral_gaussianEuclidean_neg_norm_sq (b : ℝ) (hb : 0 < b) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (-b * ‖x‖ ^ 2)) =
      (Real.pi / b) ^ ((Fintype.card ι : ℝ) / 2) := by
  simpa using integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ ι) hb

lemma integrable_gaussianEuclidean_scale_sq (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : EuclideanSpace ℝ ι =>
      (Real.exp (-‖x‖ ^ 2 / (2 * t ^ 2))) ^ 2) := by
  have hi := integrable_gaussianEuclidean_neg_norm_sq (ι := ι) (1 / t ^ 2) (by positivity)
  apply hi.congr
  filter_upwards with x
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma integral_gaussianEuclidean_scale_sq (t : ℝ) (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ ι, (Real.exp (-‖x‖ ^ 2 / (2 * t ^ 2))) ^ 2) =
      Real.pi ^ ((Fintype.card ι : ℝ) / 2) * t ^ (Fintype.card ι : ℝ) := by
  have he : (fun x : EuclideanSpace ℝ ι => (Real.exp (-‖x‖ ^ 2 / (2 * t ^ 2))) ^ 2) =
      (fun x => Real.exp (-(1 / t ^ 2) * ‖x‖ ^ 2)) := by
    funext x
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [he, integral_gaussianEuclidean_neg_norm_sq _ (by positivity), one_div, div_inv_eq_mul,
    Real.mul_rpow Real.pi_pos.le (sq_nonneg t), ← Real.rpow_two,
    ← Real.rpow_mul ht.le, show (2 : ℝ) * ((Fintype.card ι : ℝ) / 2) = (Fintype.card ι : ℝ) by ring]

end DGRHS.Gaussian
#check DGRHS.Gaussian.integrable_gaussianEuclidean_neg_norm_sq
#print axioms DGRHS.Gaussian.integrable_gaussianEuclidean_neg_norm_sq
#check DGRHS.Gaussian.integral_gaussianEuclidean_neg_norm_sq
#print axioms DGRHS.Gaussian.integral_gaussianEuclidean_neg_norm_sq
#check DGRHS.Gaussian.integrable_gaussianEuclidean_scale_sq
#print axioms DGRHS.Gaussian.integrable_gaussianEuclidean_scale_sq
#check DGRHS.Gaussian.integral_gaussianEuclidean_scale_sq
#print axioms DGRHS.Gaussian.integral_gaussianEuclidean_scale_sq
