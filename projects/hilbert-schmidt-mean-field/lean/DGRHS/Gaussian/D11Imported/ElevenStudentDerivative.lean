import DGRHS.Gaussian.D11Imported.ElevenEuclideanMass
import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Differentiation of the actual eleven-dimensional beta integral. A
strictly integrable power majorant controls the logarithmic derivative. -/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

def radialBase (x : Fin 11 → ℝ) : ℝ := 1+25*∑ i, (x i)^2

def studentFamily (a : ℝ) (x : Fin 11 → ℝ) : ℝ := radialBase x ^ (-a)

def studentMass (a : ℝ) : ℝ := ∫ x : Fin 11 → ℝ, studentFamily a x

lemma radialBase_ge_one (x : Fin 11 → ℝ) : 1 ≤ radialBase x := by
  unfold radialBase
  have hs := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin 11))) => sq_nonneg (x i))
  linarith

lemma radialBase_pos (x : Fin 11 → ℝ) : 0 < radialBase x := zero_lt_one.trans_le (radialBase_ge_one x)

lemma studentFamily_integral {a : ℝ} (ha : 11/2 < a) :
    studentMass a = (Real.pi/25)^((11:ℝ)/2) * Real.Gamma (a-11/2) / Real.Gamma a := by
  exact StudentIntegral.student_integral_pi 11 (by norm_num; exact ha) (by norm_num)

lemma studentFamily_integrable {a : ℝ} (ha : 11/2 < a) : Integrable (studentFamily a) := by
  apply Integrable.of_integral_ne_zero
  change studentMass a ≠ 0
  rw [studentFamily_integral ha]
  have ha0 : 0 < a := by linarith
  have hs : 0 < a-11/2 := by linarith
  positivity

lemma studentFamily_measurable (a : ℝ) : Measurable (studentFamily a) := by
  unfold studentFamily radialBase
  fun_prop

lemma student_derivative_bound (a : ℝ) (ha : 10 < a) (x : Fin 11 → ℝ) :
    ‖-Real.log (radialBase x) * studentFamily a x‖ ≤ studentFamily 9 x := by
  have hq := radialBase_pos x
  have hq1 := radialBase_ge_one x
  have hl : 0 ≤ Real.log (radialBase x) := Real.log_nonneg hq1
  have hll : Real.log (radialBase x) ≤ radialBase x := (Real.log_le_sub_one_of_pos hq).trans (by linarith)
  unfold studentFamily
  rw [norm_mul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hl,
    Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hq _)]
  change Real.log (radialBase x) * radialBase x^(-a) ≤ radialBase x^(-(9:ℝ))
  calc
    _ ≤ radialBase x * radialBase x^(-a) := mul_le_mul_of_nonneg_right hll (by positivity)
    _ = radialBase x^(1-a) := by
      calc
        _ = radialBase x^(1:ℝ) * radialBase x^(-a) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hq]; congr 1 <;> ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq1 (by linarith)

lemma studentFamily_hasDerivAt (a : ℝ) (x : Fin 11 → ℝ) :
    HasDerivAt (fun a => studentFamily a x)
      (-Real.log (radialBase x)*studentFamily a x) a := by
  have h := ((hasDerivAt_id a).neg.const_rpow (radialBase_pos x))
  convert h using 1 <;> dsimp [studentFamily] <;> ring

lemma studentMass_hasDerivAt :
    Integrable (fun x : Fin 11 → ℝ => -Real.log (radialBase x)*studentFamily 11 x) ∧
    HasDerivAt studentMass
      (∫ x : Fin 11 → ℝ, -Real.log (radialBase x)*studentFamily 11 x) 11 := by
  apply hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Ioi (10:ℝ)) (bound := studentFamily 9) (F := studentFamily)
    (F' := fun a x => -Real.log (radialBase x)*studentFamily a x) (μ := volume) (x₀ := (11:ℝ))
  · exact isOpen_Ioi.mem_nhds (by norm_num : (10:ℝ)<11)
  · exact Eventually.of_forall (fun a => (studentFamily_measurable a).aestronglyMeasurable)
  · exact studentFamily_integrable (by norm_num)
  · apply Measurable.aestronglyMeasurable
    unfold studentFamily radialBase
    fun_prop
  · exact ae_of_all _ (fun x a ha => student_derivative_bound a ha x)
  · exact studentFamily_integrable (by norm_num)
  · exact ae_of_all _ (fun x a _ => studentFamily_hasDerivAt a x)

#print axioms studentMass_hasDerivAt
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
