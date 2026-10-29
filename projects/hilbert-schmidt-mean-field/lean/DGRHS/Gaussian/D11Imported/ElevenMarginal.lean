import DGRHS.Gaussian.D11Imported.ElevenEuclideanMass

/-! The actual first-coordinate marginal in Section 4, by integrating the
remaining ten coordinates using the beta integral. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma euclideanProfile_marginal (t : ℝ) :
    (∫ x : Fin 10 → ℝ, euclideanProfile (Fin.cons t x)) =
      1280/(63*Real.pi) * (1+25*t^2)^(-6 : ℤ) := by
  let q : ℝ := 1+25*t^2
  have hq : 0 < q := by dsimp [q]; positivity
  have hp : Real.pi ≠ 0 := Real.pi_pos.ne'
  have he (x : Fin 10 → ℝ) : euclideanProfile (Fin.cons t x) =
      ((5:ℝ)^11 * (122880/Real.pi^6) * q^(-11:ℤ)) *
        (1+(25/q)*∑ i, (x i)^2)^(-(11:ℝ)) := by
    unfold euclideanProfile
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    have hb : 1+25*(t^2+∑ i, (x i)^2) = q*(1+(25/q)*∑ i, (x i)^2) := by
      dsimp [q] at hq ⊢
      field_simp
      <;> ring
    rw [hb, mul_zpow]
    rw [show -(11:ℝ) = ((-11:ℤ):ℝ) by norm_num, Real.rpow_intCast]
    ring
  simp_rw [he]
  rw [integral_const_mul, StudentIntegral.student_integral_pi 10 (by norm_num) (div_pos (by norm_num) hq)]
  norm_num only [Nat.cast_ofNat, show (10:ℝ)/2 = 5 by norm_num,
    show (11:ℝ)-5 = 6 by norm_num]
  rw [show (5:ℝ) = ((5:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have h6 : Real.Gamma (6:ℝ) = 120 := by
    convert Real.Gamma_nat_eq_factorial 5 using 1 <;> norm_num
  have h11 : Real.Gamma (11:ℝ) = 3628800 := by
    convert Real.Gamma_nat_eq_factorial 10 using 1 <;> norm_num
  rw [h6, h11]
  change (48828125:ℝ) * (122880/Real.pi^6) * q^(-11:ℤ) *
    ((Real.pi/(25/q))^(5:ℕ) * 120/3628800) = 1280/(63*Real.pi) * q^(-6:ℤ)
  simp only [zpow_neg, zpow_ofNat]
  field_simp [hq.ne', hp]
  <;> ring

lemma euclideanProfile_marginal_integrable (t : ℝ) :
    Integrable (fun x : Fin 10 → ℝ => euclideanProfile (Fin.cons t x)) := by
  apply Integrable.of_integral_ne_zero
  rw [euclideanProfile_marginal]
  positivity

#print axioms euclideanProfile_marginal
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
