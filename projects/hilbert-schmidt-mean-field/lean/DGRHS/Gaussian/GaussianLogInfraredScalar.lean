import DGRHS.Gaussian.GaussianLogFrullaniBound
import DGRHS.Gaussian.GaussianLogBand
import DGRHS.Gaussian.RieszGaussianScale

/-! Actual anchored counterterm and its infrared cancellation.
The finite counterterm here is an alternate approximation, not the printed C_phi,T.
Source SHA256 6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c. -/
noncomputable section
open MeasureTheory Set Real
namespace DGRHS.Gaussian

def gaussianLogCounterterm (T : ℝ) : ℝ :=
  ∫ t : ℝ in Ioc 0 T, t⁻¹ * Real.exp (-1 / (2 * t^2))

lemma integrableOn_gaussianLog_profile_short (T r : ℝ) (hT : 0 < T) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t⁻¹ * Real.exp (-r^2 / (2*t^2))) (Ioc 0 T) := by
  have hi0 := integrableOn_gaussianRiesz_full_scale 1 (r^2/2) (by norm_num) (by positivity)
  have hi := (hi0.mono_set (show Ioc 0 T ⊆ Ioi (0 : ℝ) from fun t ht => ht.1)).const_mul T
  apply hi.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : 0 < t := ht.1
  have hi : t⁻¹ ≤ T * t ^ (-(1 : ℝ)-1) := by
    rw [show -(1 : ℝ)-1 = -2 by norm_num, Real.rpow_neg ht0.le, Real.rpow_two]
    field_simp [ne_of_gt ht0]
    nlinarith [ht.2]
  have he : -r^2/(2*t^2) = -(r^2/2 : ℝ)/t^2 := by ring
  rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr ht0.le) (Real.exp_pos _).le), he]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hi (Real.exp_pos (-(r^2/2 : ℝ)/t^2)).le

lemma integrableOn_gaussianLogCounterterm (T : ℝ) (hT : 0 < T) :
    IntegrableOn (fun t : ℝ => t⁻¹ * Real.exp (-1 / (2*t^2))) (Ioc 0 T) := by
  simpa only [one_pow] using integrableOn_gaussianLog_profile_short T 1 hT (by norm_num)

lemma gaussianLogCounterterm_nonneg (T : ℝ) : 0 ≤ gaussianLogCounterterm T := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  exact mul_nonneg (inv_nonneg.mpr ht.1.le) (Real.exp_pos _).le

lemma gaussianLogCounterterm_split (T : ℝ) (hT : 1 ≤ T) :
    gaussianLogCounterterm T = gaussianLogCounterterm 1 +
      ∫ t : ℝ in Ioc 1 T, t⁻¹ * Real.exp (-1/(2*t^2)) := by
  have hi := integrableOn_gaussianLogCounterterm T (by linarith)
  have he := integral_add_compl (s := Iic (1 : ℝ)) measurableSet_Iic hi
  rw [compl_Iic, Measure.restrict_restrict measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Ioi] at he
  have hA : Iic (1 : ℝ) ∩ Ioc 0 T = Ioc 0 1 := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioc]
    constructor
    · intro ht; exact ⟨ht.2.1, ht.1⟩
    · intro ht; exact ⟨ht.2, ht.1, ht.2.trans hT⟩
  have hB : Ioi (1 : ℝ) ∩ Ioc 0 T = Ioc 1 T := by
    ext t
    simp only [mem_inter_iff, mem_Ioi, mem_Ioc]
    constructor
    · intro ht; exact ⟨ht.1, ht.2.2⟩
    · intro ht; exact ⟨ht.1, by linarith [ht.1], ht.2⟩
  rw [hA, hB] at he
  exact he.symm

lemma gaussianLog_profile_deficit_tail_le (t : ℝ) (ht : 1 < t) :
    t⁻¹ * (1 - Real.exp (-1/(2*t^2))) ≤ rieszGaussianScaleWeight (1/2) 2 t := by
  have hp := gaussianLog_profile_deficit (1/(2*t^2)) (by positivity)
  have h := mul_le_mul_of_nonneg_left hp.2 (inv_nonneg.mpr (by linarith : (0 : ℝ) ≤ t))
  have he : t⁻¹ * (1/(2*t^2)) = rieszGaussianScaleWeight (1/2) 2 t := by
    unfold rieszGaussianScaleWeight
    rw [show -(2 : ℝ)-1 = -3 by norm_num]
    calc
      _ = (1/2 : ℝ)*(t^(-1 : ℝ)*t^(-2 : ℝ)) := by
        rw [Real.rpow_neg_one,Real.rpow_neg (by linarith : (0 : ℝ) ≤ t),Real.rpow_two]
        ring
      _ = _ := by
        rw [← Real.rpow_add (show 0 < t by linarith)]
        norm_num
  simpa only [neg_div] using h.trans_eq he

lemma gaussianLogCounterterm_log_bound (T : ℝ) (hT : 1 ≤ T) :
    Real.log T - gaussianLogCounterterm T ≤ 1/4 := by
  let P : ℝ → ℝ := fun t => t⁻¹ * Real.exp (-1/(2*t^2))
  let D : ℝ → ℝ := fun t => t⁻¹ * (1 - Real.exp (-1/(2*t^2)))
  let R := rieszGaussianScaleWeight (1/2) 2
  have hiP : IntegrableOn P (Ioc 1 T) :=
    (integrableOn_gaussianLogCounterterm T (by linarith)).mono_set
      (fun t ht => ⟨by linarith [ht.1], ht.2⟩)
  have hiInv := integrable_gaussianLogBandWeight 1 T (by norm_num)
  have hiD : IntegrableOn D (Ioc 1 T) := by
    have he : D = (fun t => t⁻¹ - P t) := by funext t; dsimp [D, P]; ring
    rw [he]
    exact hiInv.sub hiP
  have hiR : IntegrableOn R (Ioi 1) :=
    integrable_rieszGaussianScaleWeight (1/2) 2 1 (by norm_num) (by norm_num)
  have hsub : Ioc (1 : ℝ) T ⊆ Ioi 1 := fun t ht => ht.1
  have hb : (∫ t in Ioc 1 T, D t) ≤ ∫ t in Ioc 1 T, R t := by
    apply integral_mono_ae hiD (hiR.mono_set hsub)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact gaussianLog_profile_deficit_tail_le t ht.1
  have hr : (∫ t in Ioc 1 T, R t) ≤ ∫ t in Ioi 1, R t := by
    have hx : Iic T ∩ Ioi (1 : ℝ) = Ioc 1 T := by ext t; simp [and_comm]
    rw [← hx, ← Measure.restrict_restrict measurableSet_Iic]
    apply integral_mono_measure Measure.restrict_le_self
      (ae_nonneg_rieszGaussianScaleWeight (1/2) 2 1 (by norm_num) (by norm_num)) hiR
  have hrval : (∫ t in Ioi 1, R t) = 1/4 := by
    rw [integral_rieszGaussianScaleWeight (1/2) 2 1 (by norm_num) (by norm_num)]
    norm_num
  have hlog : (∫ t : ℝ in Ioc 1 T, t⁻¹) = Real.log T := by
    rw [← intervalIntegral.integral_of_le hT]
    simpa using integral_inv_of_pos (by norm_num : (0 : ℝ) < 1) (by linarith : 0 < T)
  have he : (∫ t in Ioc 1 T, D t) = Real.log T - ∫ t in Ioc 1 T, P t := by
    have he' : D = (fun t => t⁻¹ - P t) := by funext t; dsimp [D, P]; ring
    rw [he', integral_sub hiInv hiP, hlog]
  have hs := gaussianLogCounterterm_split T hT
  have hn := gaussianLogCounterterm_nonneg 1
  rw [hrval] at hr
  rw [he] at hb
  dsimp only [P] at hb
  linarith

lemma gaussianLogCounterterm_low_scale_bound (δ T : ℝ) (hδ : 0 < δ) (hT : 1 ≤ T) :
    Real.log (T/δ) - gaussianLogCounterterm T ≤ -Real.log δ + 1/4 := by
  rw [Real.log_div (by linarith : T ≠ 0) hδ.ne']
  linarith [gaussianLogCounterterm_log_bound T hT]

end DGRHS.Gaussian

#check @DGRHS.Gaussian.gaussianLogCounterterm
#print axioms DGRHS.Gaussian.gaussianLogCounterterm

#check @DGRHS.Gaussian.integrableOn_gaussianLog_profile_short
#print axioms DGRHS.Gaussian.integrableOn_gaussianLog_profile_short

#check @DGRHS.Gaussian.integrableOn_gaussianLogCounterterm
#print axioms DGRHS.Gaussian.integrableOn_gaussianLogCounterterm

#check @DGRHS.Gaussian.gaussianLogCounterterm_nonneg
#print axioms DGRHS.Gaussian.gaussianLogCounterterm_nonneg

#check @DGRHS.Gaussian.gaussianLogCounterterm_split
#print axioms DGRHS.Gaussian.gaussianLogCounterterm_split

#check @DGRHS.Gaussian.gaussianLog_profile_deficit_tail_le
#print axioms DGRHS.Gaussian.gaussianLog_profile_deficit_tail_le

#check @DGRHS.Gaussian.gaussianLogCounterterm_log_bound
#print axioms DGRHS.Gaussian.gaussianLogCounterterm_log_bound

#check @DGRHS.Gaussian.gaussianLogCounterterm_low_scale_bound
#print axioms DGRHS.Gaussian.gaussianLogCounterterm_low_scale_bound

