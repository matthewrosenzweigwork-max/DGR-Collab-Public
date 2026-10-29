import DGRHS.Gaussian.D11Imported.ElevenStudentDerivative
import DGRHS.Gaussian.D11Imported.ElevenLogGamma

/-! Exact Euclidean entropy of the specified scaled profile, obtained by
differentiating its true beta integral. -/
noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators Topology
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma studentMass_pos {a : ℝ} (ha : 11/2 < a) : 0 < studentMass a := by
  rw [studentFamily_integral ha]
  have h1 : 0 < a-11/2 := by linarith
  have h2 : 0 < a := by linarith
  positivity

lemma studentMass_log_derivative :
    HasDerivAt (fun a => Real.log (studentMass a))
      ((1627:ℝ)/2520-2*Real.log 2) 11 := by
  have hh : HasDerivAt (fun x => Real.log (Real.Gamma x))
      (-Real.eulerMascheroniConstant-2*Real.log 2+1126/315) ((11:ℝ)-11/2) := by
    norm_num only [show (11:ℝ)-11/2 = 11/2 by norm_num]
    exact logGamma_eleven_half_derivative
  have hshift := hh.comp 11 ((hasDerivAt_id (11:ℝ)).sub_const (11/2))
  have h := ((hasDerivAt_const (11:ℝ) (Real.log ((Real.pi/25)^((11:ℝ)/2)))).add hshift).sub
    logGamma_eleven_derivative
  have h' : HasDerivAt (fun a => Real.log ((Real.pi/25)^((11:ℝ)/2)) +
      Real.log (Real.Gamma (a-11/2)) - Real.log (Real.Gamma a))
        ((1627:ℝ)/2520-2*Real.log 2) 11 := by
    convert h using 1 <;> try simp only [Function.comp_apply, Pi.add_apply, Pi.sub_apply]
    all_goals first | rfl | (funext a; rfl) | ring
  apply h'.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds (show (11/2:ℝ)<11 by norm_num)] with a ha
  change (11/2:ℝ)<a at ha
  have h1 : 0 < a-11/2 := by linarith
  have h2 : 0 < a := by linarith
  rw [studentFamily_integral ha, Real.log_div (by positivity) (Real.Gamma_pos_of_pos h2).ne',
    Real.log_mul (by positivity) (Real.Gamma_pos_of_pos h1).ne']

lemma student_log_integrable :
    Integrable (fun x : Fin 11 → ℝ => Real.log (radialBase x)*studentFamily 11 x) := by
  have h := studentMass_hasDerivAt.1.neg
  change Integrable (fun x : Fin 11 → ℝ => -(-Real.log (radialBase x)*studentFamily 11 x)) at h
  simpa only [neg_mul, neg_neg] using h

lemma student_log_integral :
    (∫ x : Fin 11 → ℝ, Real.log (radialBase x)*studentFamily 11 x) =
      studentMass 11 * (2*Real.log 2 - 1627/2520) := by
  have h := studentMass_hasDerivAt.2.log (studentMass_pos (by norm_num : (11/2:ℝ)<11)).ne'
  have he := h.unique studentMass_log_derivative
  simp only [neg_mul, integral_neg] at he
  have he' := (div_eq_iff (studentMass_pos (by norm_num : (11/2:ℝ)<11)).ne').mp he
  linarith

lemma profile_student (x : Fin 11 → ℝ) :
    euclideanProfile x = ((5:ℝ)^11 * (122880 / Real.pi^6)) * studentFamily 11 x := by
  unfold euclideanProfile studentFamily radialBase
  rw [show -(11:ℝ) = ((-11:ℤ):ℝ) by norm_num, Real.rpow_intCast]

lemma profile_coefficient_mass :
    ((5:ℝ)^11 * (122880 / Real.pi^6)) * studentMass 11 = 1 := by
  have h := euclideanProfile_integral
  simp_rw [profile_student] at h
  rwa [integral_const_mul] at h

lemma euclideanProfile_entropy_integrable :
    Integrable (fun x : Fin 11 → ℝ => euclideanProfile x * Real.log (euclideanProfile x)) := by
  let C : ℝ := (5:ℝ)^11 * (122880 / Real.pi^6)
  have hC : 0 < C := by dsimp [C]; positivity
  have he (x : Fin 11 → ℝ) : euclideanProfile x * Real.log (euclideanProfile x) =
      C*Real.log C*studentFamily 11 x - (11*C)*(Real.log (radialBase x)*studentFamily 11 x) := by
    rw [profile_student]
    change C*studentFamily 11 x * Real.log (C*studentFamily 11 x) = _
    rw [Real.log_mul hC.ne' (show studentFamily 11 x ≠ 0 from (Real.rpow_pos_of_pos (radialBase_pos x) _).ne')]
    change C*studentFamily 11 x * (Real.log C+Real.log (radialBase x^(-(11:ℝ)))) = _
    rw [Real.log_rpow (radialBase_pos x)]
    ring
  simp_rw [he]
  exact ((studentFamily_integrable (by norm_num : (11/2:ℝ)<11)).const_mul _).sub
    (student_log_integrable.const_mul _)

lemma euclideanProfile_entropy_intermediate :
    (∫ x : Fin 11 → ℝ, euclideanProfile x * Real.log (euclideanProfile x)) =
      Real.log ((5:ℝ)^11 * (122880 / Real.pi^6)) - 22*Real.log 2 + 17897/2520 := by
  let C : ℝ := (5:ℝ)^11 * (122880 / Real.pi^6)
  have hC : 0 < C := by dsimp [C]; positivity
  have he (x : Fin 11 → ℝ) : euclideanProfile x * Real.log (euclideanProfile x) =
      C*Real.log C*studentFamily 11 x - (11*C)*(Real.log (radialBase x)*studentFamily 11 x) := by
    rw [profile_student]
    change C*studentFamily 11 x * Real.log (C*studentFamily 11 x) = _
    rw [Real.log_mul hC.ne' (show studentFamily 11 x ≠ 0 from (Real.rpow_pos_of_pos (radialBase_pos x) _).ne')]
    change C*studentFamily 11 x * (Real.log C+Real.log (radialBase x^(-(11:ℝ)))) = _
    rw [Real.log_rpow (radialBase_pos x)]
    ring
  simp_rw [he]
  rw [integral_sub ((studentFamily_integrable (by norm_num : (11/2:ℝ)<11)).const_mul _)
    (student_log_integrable.const_mul _), integral_const_mul, integral_const_mul, student_log_integral]
  change C*Real.log C*studentMass 11 - 11*C*(studentMass 11*(2*Real.log 2-1627/2520)) = _
  have hM := profile_coefficient_mass
  change C*studentMass 11 = 1 at hM
  calc
    _ = C*studentMass 11 * (Real.log C - 22*Real.log 2 + 17897/2520) := by ring
    _ = _ := by rw [hM, one_mul]

lemma euclideanProfile_entropy_exact :
    (∫ x : Fin 11 → ℝ, euclideanProfile x * Real.log (euclideanProfile x)) =
      Real.log (3*5^12/(2^9*Real.pi^6)) + 17897/2520 := by
  rw [euclideanProfile_entropy_intermediate]
  congr 1
  have hC : (5:ℝ)^11 * (122880 / Real.pi^6) ≠ 0 := by positivity
  calc
    _ = Real.log ((5:ℝ)^11 * (122880 / Real.pi^6)) - Real.log ((2:ℝ)^22) := by
      rw [Real.log_pow]
      norm_num
    _ = Real.log (((5:ℝ)^11 * (122880 / Real.pi^6)) / 2^22) :=
      (Real.log_div hC (by norm_num)).symm
    _ = _ := by
      congr 1
      norm_num
      ring

lemma euclideanProfile_entropy_lt :
    (∫ x : Fin 11 → ℝ, euclideanProfile x * Real.log (euclideanProfile x)) < 721/50 := by
  rw [euclideanProfile_entropy_exact]
  exact euclidean_entropy_expression_lt

lemma euclideanProfile_entropy_fine :
    (∫ x : Fin 11 → ℝ, euclideanProfile x * Real.log (euclideanProfile x)) <
      7305164/10^6 + 17897/2520 := by
  rw [euclideanProfile_entropy_exact]
  linarith [euclidean_entropy_expression_fine]

#print axioms euclideanProfile_entropy_exact

#print axioms euclideanProfile_entropy_intermediate
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
