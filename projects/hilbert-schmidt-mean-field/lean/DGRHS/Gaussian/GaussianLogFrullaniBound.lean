import DGRHS.Gaussian.GaussianLogMellinLimit

/-! Actual global integrable domination for the zero-exponent Gaussian profile.
The same positive-s=1 majorant controls all 0<=s<=1. No assumed limit or
uniform integrability premise is used. Source SHA256
6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c. -/
noncomputable section
open MeasureTheory Set Real
namespace DGRHS.Gaussian

lemma gaussianLog_profile_deficit (v : ℝ) (hv : 0 ≤ v) :
    0 ≤ 1 - Real.exp (-v) ∧ 1 - Real.exp (-v) ≤ v := by
  constructor
  · have h := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hv)
    linarith
  · have h := Real.add_one_le_exp (-v)
    linarith

def gaussianLogFrullaniMajorant (r t : ℝ) : ℝ :=
  (1 + ((r ^ 2 + 1) / 2) * Real.exp (1 / 2)) *
    (t ^ (-2 : ℝ) * Real.exp (-r ^ 2 / (2 * t ^ 2)) +
      t ^ (-2 : ℝ) * Real.exp (-1 / (2 * t ^ 2)))

lemma integrableOn_gaussianLogFrullaniMajorant (r : ℝ) (hr : 0 < r) :
    IntegrableOn (gaussianLogFrullaniMajorant r) (Ioi 0) := by
  have hR := integrableOn_gaussianRiesz_full_scale 1 (r ^ 2 / 2)
    (by norm_num) (by positivity : 0 < r ^ 2 / 2)
  have hOne := integrableOn_gaussianRiesz_full_scale 1 (1 / 2)
    (by norm_num) (by norm_num : (0 : ℝ) < 1 / 2)
  have he : gaussianLogFrullaniMajorant r = fun t : ℝ =>
      (1 + ((r ^ 2 + 1) / 2) * Real.exp (1 / 2)) *
        (t ^ (-(1 : ℝ) - 1) * Real.exp (-(r ^ 2 / 2) / t ^ 2) +
          t ^ (-(1 : ℝ) - 1) * Real.exp (-(1 / 2) / t ^ 2)) := by
    funext t
    dsimp [gaussianLogFrullaniMajorant]
    norm_num only
    congr 1
    congr 1 <;> congr 2 <;> ring
  rw [he]
  exact (hR.add hOne).const_mul _

lemma gaussianLogMellinDifference_norm_le (s r t : ℝ)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht : 0 < t) :
    ‖gaussianLogMellinDifference s r t‖ ≤ gaussianLogFrullaniMajorant r t := by
  let A : ℝ := (r ^ 2 + 1) / 2
  let ER : ℝ := Real.exp (-r ^ 2 / (2 * t ^ 2))
  let E1 : ℝ := Real.exp (-1 / (2 * t ^ 2))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hER : 0 ≤ ER := (Real.exp_pos _).le
  have hE1 : 0 ≤ E1 := (Real.exp_pos _).le
  have hPow : 0 ≤ t ^ (-s - 1) := Real.rpow_nonneg ht.le _
  have hP2 : 0 ≤ t ^ (-2 : ℝ) := Real.rpow_nonneg ht.le _
  have hK : 1 ≤ 1 + A * Real.exp (1 / 2) := by
    linarith [mul_nonneg hA (Real.exp_pos (1 / 2)).le]
  have hNorm : ‖gaussianLogMellinDifference s r t‖ =
      t ^ (-s - 1) * |ER - E1| := by
    simp only [gaussianLogMellinDifference, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg hPow, ER, E1]
  change _ ≤ (1 + A * Real.exp (1 / 2)) * (t ^ (-2 : ℝ) * ER + t ^ (-2 : ℝ) * E1)
  rw [hNorm]
  by_cases ht1 : t ≤ 1
  · have hPower : t ^ (-s - 1) ≤ t ^ (-2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
    have hDiff : |ER - E1| ≤ ER + E1 := by
      apply abs_le.mpr
      constructor <;> linarith
    calc
      _ ≤ t ^ (-2 : ℝ) * (ER + E1) :=
        mul_le_mul hPower hDiff (abs_nonneg _) hP2
      _ = t ^ (-2 : ℝ) * ER + t ^ (-2 : ℝ) * E1 := by ring
      _ ≤ _ := by
        nth_rw 1 [← one_mul (t ^ (-2 : ℝ) * ER + t ^ (-2 : ℝ) * E1)]
        exact mul_le_mul_of_nonneg_right hK (by positivity)
  · have htOne : 1 ≤ t := (lt_of_not_ge ht1).le
    have hPower : t ^ (-s - 1) ≤ 1 := by
      rw [Real.rpow_def_of_pos ht, Real.exp_le_one_iff]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.log_nonneg htOne) (by linarith)
    have hR := gaussianLog_profile_deficit (r ^ 2 / (2 * t ^ 2)) (by positivity)
    have h1 := gaussianLog_profile_deficit (1 / (2 * t ^ 2)) (by positivity)
    have hDiff : |ER - E1| ≤ A / t ^ 2 := by
      have h : |ER - E1| ≤ r ^ 2 / (2 * t ^ 2) + 1 / (2 * t ^ 2) := by
        apply abs_le.mpr
        dsimp [ER, E1]
        simp only [neg_div]
        constructor <;> linarith [hR.1, hR.2, h1.1, h1.2]
      calc _ ≤ _ := h
           _ = _ := by dsimp [A]; ring
    have hComp : 1 ≤ Real.exp (1 / 2) * E1 := by
      dsimp [E1]
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have htSq : 1 ≤ t ^ 2 := by nlinarith
      have hDiv : (1 : ℝ) / (2 * t ^ 2) ≤ 1 / 2 := by
        apply (div_le_div_iff₀ (by positivity : 0 < 2 * t ^ 2) (by norm_num : (0 : ℝ) < 2)).mpr
        nlinarith
      simp only [neg_div]
      linarith
    have hP2eq : t ^ (-2 : ℝ) = (t ^ 2)⁻¹ := by
      rw [Real.rpow_neg ht.le, Real.rpow_two]
    calc
      _ ≤ 1 * (A / t ^ 2) := mul_le_mul hPower hDiff (abs_nonneg _) (by norm_num)
      _ = A * t ^ (-2 : ℝ) := by rw [hP2eq]; ring
      _ ≤ A * t ^ (-2 : ℝ) * (Real.exp (1 / 2) * E1) :=
        le_mul_of_one_le_right (by positivity) hComp
      _ = (A * Real.exp (1 / 2)) * (t ^ (-2 : ℝ) * E1) := by ring
      _ ≤ (A * Real.exp (1 / 2)) * (t ^ (-2 : ℝ) * ER + t ^ (-2 : ℝ) * E1) := by
        apply mul_le_mul_of_nonneg_left
        · linarith [mul_nonneg hP2 hER]
        · positivity
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_right
        · linarith
        · positivity

lemma integrableOn_gaussianLogFrullani (r : ℝ) (hr : 0 < r) :
    IntegrableOn (gaussianLogMellinDifference 0 r) (Ioi 0) := by
  have hm : Measurable (gaussianLogMellinDifference 0 r) := by
    unfold gaussianLogMellinDifference
    fun_prop
  apply (integrableOn_gaussianLogFrullaniMajorant r hr).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact gaussianLogMellinDifference_norm_le 0 r t (by norm_num) (by norm_num) ht

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianLog_profile_deficit
#print axioms DGRHS.Gaussian.gaussianLog_profile_deficit

#check DGRHS.Gaussian.gaussianLogFrullaniMajorant
#print axioms DGRHS.Gaussian.gaussianLogFrullaniMajorant

#check DGRHS.Gaussian.integrableOn_gaussianLogFrullaniMajorant
#print axioms DGRHS.Gaussian.integrableOn_gaussianLogFrullaniMajorant

#check DGRHS.Gaussian.gaussianLogMellinDifference_norm_le
#print axioms DGRHS.Gaussian.gaussianLogMellinDifference_norm_le

#check DGRHS.Gaussian.integrableOn_gaussianLogFrullani
#print axioms DGRHS.Gaussian.integrableOn_gaussianLogFrullani
