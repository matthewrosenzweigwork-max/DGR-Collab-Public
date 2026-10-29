/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import DGRHS.Gaussian.D11Imported.StudentIntegral
import DGRHS.Gaussian.D11Imported.ElevenConstants

/-! The exact Euclidean normalization in Section 4, before periodization. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma euclideanProfile_pos (x : Fin 11 → ℝ) : 0 < euclideanProfile x := by
  unfold euclideanProfile
  positivity

lemma euclideanProfile_continuous : Continuous euclideanProfile := by
  unfold euclideanProfile
  fun_prop (disch := intro x; left; positivity)

lemma euclideanProfile_integral : (∫ x : Fin 11 → ℝ, euclideanProfile x) = 1 := by
  have hi := StudentIntegral.student_integral_pi 11 (by norm_num : (11:ℝ)/2 < 11)
    (by norm_num : (0:ℝ)<25)
  have hg : Real.Gamma (11/2) = 945 * Real.sqrt Real.pi / 32 := by
    convert Real.Gamma_nat_add_half 5 using 1 <;> norm_num
  have hg11 : Real.Gamma 11 = 3628800 := by
    convert Real.Gamma_nat_eq_factorial 10 using 1 <;> norm_num
  have hp : (Real.pi/25)^((11:ℝ)/2) = (Real.pi^5 * Real.sqrt Real.pi) / 5^11 := by
    rw [show (11:ℝ)/2 = (5:ℕ)+(1/2:ℝ) by norm_num,
      Real.rpow_add (by positivity), Real.rpow_natCast, ← Real.sqrt_eq_rpow,
      Real.sqrt_div Real.pi_pos.le, show Real.sqrt 25 = 5 by norm_num]
    ring
  norm_num only [Nat.cast_ofNat, show (11:ℝ)-11/2 = 11/2 by norm_num] at hi
  rw [hg, hg11, hp] at hi
  have hz : (fun x : Fin 11 → ℝ => (1+25*∑ i, (x i)^2)^(-11:ℤ)) =
      (fun x => (1+25*∑ i, (x i)^2)^(-(11:ℝ))) := by
    funext x
    have h := Real.rpow_intCast (1+25*∑ i, (x i)^2) (-11)
    simpa only [Int.cast_neg, Int.cast_ofNat] using h.symm
  unfold euclideanProfile
  rw [integral_const_mul, hz, hi]
  have hs := Real.sq_sqrt Real.pi_pos.le
  have hp0 : Real.pi ≠ 0 := Real.pi_pos.ne'
  field_simp
  nlinarith [hs]

lemma euclideanProfile_integrable : Integrable euclideanProfile := by
  apply Integrable.of_integral_ne_zero
  rw [euclideanProfile_integral]
  norm_num

#print axioms euclideanProfile_integral
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
