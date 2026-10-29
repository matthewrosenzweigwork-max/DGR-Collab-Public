import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Gaussian-profile source normalization for arxiv2609.02743v1,
lem:HCRStruncations (preserved source SHA256
6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c).
The Gamma evaluation uses the pinned Mathlib substitution/Gamma integral APIs;
its square substitution follows Mathlib's Real.Gamma_one_half_eq argument,
Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean, Apache-2.0.
-/
noncomputable section
open MeasureTheory Set
namespace DGRHS.Gaussian

def gaussianRieszRadialProfile (r : ℝ) : ℝ := Real.exp (-r ^ 2 / 2)

def gaussianRieszProfileDensity (s r : ℝ) : ℝ :=
  r ^ (s - 1) * gaussianRieszRadialProfile r

def gaussianRieszSourceCoefficient (s : ℝ) : ℝ :=
  (s * ∫ r in Ioi 0, gaussianRieszProfileDensity s r)⁻¹

lemma integrable_gaussianRieszProfileDensity (s : ℝ) (hs : 0 < s) :
    IntegrableOn (gaussianRieszProfileDensity s) (Ioi 0) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
    (s := s - 1) (by linarith)
  apply hi.congr_fun _ measurableSet_Ioi
  intro r hr
  unfold gaussianRieszProfileDensity gaussianRieszRadialProfile
  congr 2
  ring

lemma integral_gaussianRieszProfileDensity (s : ℝ) (hs : 0 < s) :
    (∫ r in Ioi 0, gaussianRieszProfileDensity s r) =
      (2 : ℝ) ^ (s / 2) * Real.Gamma (s / 2) / 2 := by
  have hsub := integral_comp_rpow_Ioi_of_pos
    (g := fun u : ℝ => u ^ (s / 2 - 1) * Real.exp (-((1 / 2 : ℝ) * u)))
    (p := (2 : ℝ)) (by norm_num)
  have hleft : (∫ r : ℝ in Ioi 0,
      ((2 : ℝ) * r ^ ((2 : ℝ) - 1)) •
        ((r ^ (2 : ℝ)) ^ (s / 2 - 1) * Real.exp (-((1 / 2 : ℝ) * r ^ (2 : ℝ))))) =
      2 * ∫ r in Ioi 0, gaussianRieszProfileDensity s r := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    unfold gaussianRieszProfileDensity gaussianRieszRadialProfile
    simp only [smul_eq_mul, show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one]
    rw [← Real.rpow_mul hr.le, show (2 : ℝ) * (s / 2 - 1) = s - 2 by ring,
      Real.rpow_two, show -((1 / 2 : ℝ) * r ^ 2) = -r ^ 2 / 2 by ring]
    have hp : r * r ^ (s - 2) = r ^ (s - 1) := by
      rw [mul_comm, ← Real.rpow_add_one hr.ne']
      congr 1
      ring
    calc
      (2 * r) * (r ^ (s - 2) * Real.exp (-r ^ 2 / 2)) =
          2 * (r * r ^ (s - 2)) * Real.exp (-r ^ 2 / 2) := by ring
      _ = 2 * (r ^ (s - 1) * Real.exp (-r ^ 2 / 2)) := by rw [hp]; ring
  rw [hleft, Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith : 0 < s / 2)
    (by norm_num : (0 : ℝ) < 1 / 2)] at hsub
  norm_num only [one_div_div, mul_one] at hsub
  linarith

lemma integral_gaussianRieszProfileDensity_pos (s : ℝ) (hs : 0 < s) :
    0 < ∫ r in Ioi 0, gaussianRieszProfileDensity s r := by
  rw [integral_gaussianRieszProfileDensity s hs]
  exact div_pos (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
    (Real.Gamma_pos_of_pos (by linarith))) (by norm_num)

lemma gaussianRieszSourceCoefficient_pos (s : ℝ) (hs : 0 < s) :
    0 < gaussianRieszSourceCoefficient s :=
  inv_pos.mpr (mul_pos hs (integral_gaussianRieszProfileDensity_pos s hs))

lemma gaussianRieszSourceCoefficient_eq_gamma (s : ℝ) (hs : 0 < s) :
    gaussianRieszSourceCoefficient s =
      (s * ((2 : ℝ) ^ (s / 2) * Real.Gamma (s / 2) / 2))⁻¹ := by
  unfold gaussianRieszSourceCoefficient
  rw [integral_gaussianRieszProfileDensity s hs]

lemma gaussianRieszProfileDensity_source_formula (s r : ℝ) (hr : 0 < r) :
    gaussianRieszProfileDensity s r = r ^ s * gaussianRieszRadialProfile r / r := by
  unfold gaussianRieszProfileDensity
  rw [Real.rpow_sub_one hr.ne']
  ring

lemma gaussianRieszSourceCoefficient_inverse (s : ℝ) :
    (gaussianRieszSourceCoefficient s)⁻¹ =
      s * ∫ r in Ioi 0, r ^ s * gaussianRieszRadialProfile r / r := by
  unfold gaussianRieszSourceCoefficient
  rw [inv_inv]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  exact fun r hr => gaussianRieszProfileDensity_source_formula s r hr

end DGRHS.Gaussian
#check DGRHS.Gaussian.gaussianRieszRadialProfile
#check DGRHS.Gaussian.gaussianRieszProfileDensity
#check DGRHS.Gaussian.gaussianRieszSourceCoefficient
#check DGRHS.Gaussian.integrable_gaussianRieszProfileDensity
#check DGRHS.Gaussian.integral_gaussianRieszProfileDensity
#check DGRHS.Gaussian.integral_gaussianRieszProfileDensity_pos
#check DGRHS.Gaussian.gaussianRieszSourceCoefficient_pos
#check DGRHS.Gaussian.gaussianRieszSourceCoefficient_eq_gamma
#check DGRHS.Gaussian.gaussianRieszProfileDensity_source_formula
#check DGRHS.Gaussian.gaussianRieszSourceCoefficient_inverse
#print axioms DGRHS.Gaussian.gaussianRieszRadialProfile
#print axioms DGRHS.Gaussian.gaussianRieszProfileDensity
#print axioms DGRHS.Gaussian.gaussianRieszSourceCoefficient
#print axioms DGRHS.Gaussian.integrable_gaussianRieszProfileDensity
#print axioms DGRHS.Gaussian.integral_gaussianRieszProfileDensity
#print axioms DGRHS.Gaussian.integral_gaussianRieszProfileDensity_pos
#print axioms DGRHS.Gaussian.gaussianRieszSourceCoefficient_pos
#print axioms DGRHS.Gaussian.gaussianRieszSourceCoefficient_eq_gamma
#print axioms DGRHS.Gaussian.gaussianRieszProfileDensity_source_formula
#print axioms DGRHS.Gaussian.gaussianRieszSourceCoefficient_inverse
