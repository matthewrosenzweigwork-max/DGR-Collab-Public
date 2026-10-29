import DGRHS.Gaussian.RieszGaussianEuclidean
import Mathlib.MeasureTheory.Integral.Gamma

/-! Actual full-scale Gaussian Riesz formula away from the origin.
The reciprocal substitution uses pinned Mathlib's change-of-variables and
integrability equivalence, not a formal calculation or supplied kernel identity. -/
noncomputable section
open MeasureTheory Set Real
open scoped ENNReal
namespace DGRHS.Gaussian

lemma gaussianRiesz_inverse_scale_integrand (s b t : ℝ) (ht : 0 < t) :
    (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) *
      ((t ^ (-1 : ℝ)) ^ (s - 1) * Real.exp (-b * (t ^ (-1 : ℝ)) ^ 2)) =
        t ^ (-s - 1) * Real.exp (-b / t ^ 2) := by
  norm_num only [abs_neg, abs_one, neg_sub, one_add_one_eq_two, one_mul]
  rw [Real.rpow_neg_one, ← Real.rpow_neg_eq_inv_rpow]
  have hp : t ^ (-2 : ℝ) * t ^ (-(s - 1)) = t ^ (-s - 1) := by
    rw [← Real.rpow_add ht]
    congr 1
    ring
  rw [← mul_assoc, hp, inv_pow]
  congr 2

lemma integrableOn_gaussianRiesz_full_scale (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t ^ (-s - 1) * Real.exp (-b / t ^ 2)) (Ioi 0) := by
  have hi : IntegrableOn (fun u : ℝ => u ^ (s - 1) * Real.exp (-b * u ^ 2)) (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq hb (by linarith)
  have hj := (integrableOn_Ioi_comp_rpow_iff _ (show (-1 : ℝ) ≠ 0 by norm_num)).mpr hi
  exact hj.congr_fun (fun t ht => by
    simpa only [smul_eq_mul] using gaussianRiesz_inverse_scale_integrand s b t ht) measurableSet_Ioi

lemma integral_gaussianRiesz_full_scale (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    (∫ t : ℝ in Ioi 0, t ^ (-s - 1) * Real.exp (-b / t ^ 2)) =
      b ^ (-s / 2) * (1 / 2) * Real.Gamma (s / 2) := by
  calc
    _ = ∫ t : ℝ in Ioi 0, (|(-1 : ℝ)| * t ^ ((-1 : ℝ) - 1)) •
        ((t ^ (-1 : ℝ)) ^ (s - 1) * Real.exp (-b * (t ^ (-1 : ℝ)) ^ 2)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      simpa only [smul_eq_mul] using (gaussianRiesz_inverse_scale_integrand s b t ht).symm
    _ = ∫ u : ℝ in Ioi 0, u ^ (s - 1) * Real.exp (-b * u ^ 2) :=
      integral_comp_rpow_Ioi (fun u : ℝ => u ^ (s - 1) * Real.exp (-b * u ^ 2))
        (p := (-1 : ℝ)) (by norm_num)
    _ = _ := by
      simp_rw [← Real.rpow_two]
      simpa only [show -(s - 1 + 1) / 2 = -s / 2 by ring,
        show (s - 1 + 1) / 2 = s / 2 by ring] using
        integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0 : ℝ) < 2)
          (by linarith : (-1 : ℝ) < s - 1) hb

lemma gaussianRiesz_full_scale_norm_power (s r : ℝ) (hr : 0 < r) :
    (r ^ 2 / 2) ^ (-s / 2) = r ^ (-s) * (2 : ℝ) ^ (s / 2) := by
  rw [Real.div_rpow (sq_nonneg r) (by norm_num), ← Real.rpow_two,
    ← Real.rpow_mul hr.le, show (2 : ℝ) * (-s / 2) = -s by ring,
    show -s / 2 = -(s / 2) by ring,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [div_inv_eq_mul]

lemma gaussianRiesz_normalized_full_scale (s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    gaussianRieszSourceCoefficient s *
      (∫ t : ℝ in Ioi 0, t ^ (-s - 1) * Real.exp (-r ^ 2 / (2 * t ^ 2))) =
        r ^ (-s) / s := by
  have hg : Real.Gamma (s / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity : 0 < s / 2)).ne'
  have htwo : (2 : ℝ) ^ (s / 2) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne'
  have he : (fun t : ℝ => t ^ (-s - 1) * Real.exp (-r ^ 2 / (2 * t ^ 2))) =
      (fun t => t ^ (-s - 1) * Real.exp (-(r ^ 2 / 2) / t ^ 2)) := by
    funext t
    congr 2
    ring
  rw [he, integral_gaussianRiesz_full_scale s (r ^ 2 / 2) hs (by positivity),
    gaussianRiesz_full_scale_norm_power s r hr, gaussianRieszSourceCoefficient_eq_gamma s hs]
  field_simp [hs.ne', hg, htwo]
  <;> ring

lemma gaussianRieszEuclidean_full_scale {ι : Type*} [Fintype ι]
    (s : ℝ) (hs : 0 < s) (x : EuclideanSpace ℝ ι) (hx : x ≠ 0) :
    gaussianRieszSourceCoefficient s *
      (∫ t : ℝ in Ioi 0, t ^ (-s - 1) * Real.exp (-‖x‖ ^ 2 / (2 * t ^ 2))) =
        ‖x‖ ^ (-s) / s :=
  gaussianRiesz_normalized_full_scale s ‖x‖ hs (norm_pos_iff.mpr hx)

end DGRHS.Gaussian
#check DGRHS.Gaussian.gaussianRiesz_inverse_scale_integrand
#print axioms DGRHS.Gaussian.gaussianRiesz_inverse_scale_integrand
#check DGRHS.Gaussian.integrableOn_gaussianRiesz_full_scale
#print axioms DGRHS.Gaussian.integrableOn_gaussianRiesz_full_scale
#check DGRHS.Gaussian.integral_gaussianRiesz_full_scale
#print axioms DGRHS.Gaussian.integral_gaussianRiesz_full_scale
#check DGRHS.Gaussian.gaussianRiesz_full_scale_norm_power
#print axioms DGRHS.Gaussian.gaussianRiesz_full_scale_norm_power
#check DGRHS.Gaussian.gaussianRiesz_normalized_full_scale
#print axioms DGRHS.Gaussian.gaussianRiesz_normalized_full_scale
#check DGRHS.Gaussian.gaussianRieszEuclidean_full_scale
#print axioms DGRHS.Gaussian.gaussianRieszEuclidean_full_scale
