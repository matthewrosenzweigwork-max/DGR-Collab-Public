import DGRHS.Gaussian.PeriodicHeatScaleNormalization

/-! Proper Mellin integral with the exact coefficient prescribed by the
source periodic logarithmic Green function. -/
noncomputable section
open MeasureTheory Set Real
open scoped Classical BigOperators
namespace DGRHS.Periodic
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicHeat_full_scale_integrable (b : ℝ) (hb : 0<b) :
    IntegrableOn (fun t : ℝ => t^(Fintype.card ι-1)*Real.exp (-b*t^2)) (Ioi 0) := by
  have he : (-1:ℝ)<((Fintype.card ι-1:ℕ):ℝ) :=
    lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg _)
  simpa only [Real.rpow_natCast] using integrableOn_rpow_mul_exp_neg_mul_sq hb he

lemma periodicHeat_full_scale_integral (b : ℝ) (hb : 0<b) :
    (∫ t : ℝ in Ioi 0,t^(Fintype.card ι-1)*Real.exp (-b*t^2)) =
      b^(-(Fintype.card ι:ℝ)/2)*(1/2)*Real.Gamma ((Fintype.card ι:ℝ)/2) := by
  have hd : 1≤Fintype.card ι := Fintype.card_pos
  have he : ((Fintype.card ι-1:ℕ):ℝ)+1=(Fintype.card ι:ℝ) := by
    rw [Nat.cast_sub hd,Nat.cast_one]
    ring
  have h := integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0:ℝ)<2)
    (lt_of_lt_of_le (by norm_num : (-1:ℝ)<0) (Nat.cast_nonneg (Fintype.card ι-1))) hb
  simpa only [Real.rpow_natCast,Real.rpow_two,he] using h

lemma periodic_rpow_half_nat (b : ℝ) (hb : 0≤b) (d : ℕ) :
    b^((d:ℝ)/2)=(Real.sqrt b)^d := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_natCast,← Real.rpow_mul hb]
  congr 1
  ring

lemma periodic_rpow_neg_half_nat (b : ℝ) (hb : 0≤b) (d : ℕ) :
    b^(-(d:ℝ)/2)=((Real.sqrt b)⁻¹)^d := by
  rw [show -(d:ℝ)/2= -((d:ℝ)/2) by ring,Real.rpow_neg hb,
    periodic_rpow_half_nat b hb,inv_pow]

lemma periodicHeat_mellin_scalar (r : ℝ) (hr : 0<r) :
    periodicHeatScaleFactor ι*(2*Real.pi^2*r^2)^(-(Fintype.card ι:ℝ)/2) =
      (4*Real.pi)^((Fintype.card ι:ℝ)/2)/(2*Real.pi)^(Fintype.card ι)*(r⁻¹)^(Fintype.card ι) := by
  rw [periodic_rpow_neg_half_nat _ (by positivity),periodic_rpow_half_nat _ (by positivity)]
  unfold periodicHeatScaleFactor
  rw [← mul_pow,← div_pow,← mul_pow]
  congr 1
  have hp : 0<Real.pi := Real.pi_pos
  have hs : Real.sqrt (2*Real.pi^2*r^2) = Real.sqrt 2*Real.pi*r := by
    rw [Real.sqrt_mul (by positivity : (0:ℝ)≤2*Real.pi^2),
      Real.sqrt_mul (by norm_num : (0:ℝ)≤2),Real.sqrt_sq_eq_abs,
      Real.sqrt_sq_eq_abs,abs_of_pos hr,abs_of_pos Real.pi_pos]
  have hs2 : Real.sqrt (2*Real.pi)=Real.sqrt 2*Real.sqrt Real.pi := Real.sqrt_mul (by norm_num) _
  have hs4 : Real.sqrt (4*Real.pi)=2*Real.sqrt Real.pi := by
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
    norm_num
  rw [hs,hs2,hs4]
  have hs2n : Real.sqrt 2≠0 := (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)).ne'
  field_simp

/-- Exact nonzero Fourier coefficient from the full proper heat-scale integral. -/
theorem periodicHeat_full_coefficient (k : PeriodicFrequency ι) (hk : k≠0) :
    ((periodicHeatScaleFactor ι*
      (∫ t : ℝ in Ioi 0,t^(Fintype.card ι-1)*
        Real.exp (-2*Real.pi^2*t^2*‖periodicFrequencyVector k‖^2)):ℝ):ℂ) =
      periodicLogFourierCoeff k := by
  have hn := periodicFrequency_norm_pos hk
  have he : (fun t : ℝ => t^(Fintype.card ι-1)*Real.exp (-2*Real.pi^2*t^2*‖periodicFrequencyVector k‖^2)) =
      (fun t : ℝ => t^(Fintype.card ι-1)*Real.exp (-(2*Real.pi^2*‖periodicFrequencyVector k‖^2)*t^2)) := by
    funext t
    congr 2
    ring
  rw [he,periodicHeat_full_scale_integral _ (by positivity),periodicLogFourierCoeff,if_neg hk]
  congr 1
  rw [← mul_assoc,← mul_assoc,periodicHeat_mellin_scalar _ hn]
  unfold periodicLogConstant
  ring

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicHeat_full_scale_integral
#print axioms DGRHS.Periodic.periodicHeat_mellin_scalar
#print axioms DGRHS.Periodic.periodicHeat_full_coefficient
#check @DGRHS.Periodic.periodicHeat_full_coefficient
