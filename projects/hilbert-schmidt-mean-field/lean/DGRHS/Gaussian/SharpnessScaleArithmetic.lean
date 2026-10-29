import DGRHS.Gaussian.SharpnessGeometricSelector
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
open Filter
open scoped Topology
namespace DGRHS.Gaussian

lemma sharpness_dyadic_inverse_power (L s : ℝ) (hL : 0 < L) (m : ℕ) :
    (L/(2:ℝ)^m)^(-s) = L^(-s)*((2:ℝ)^s)^m := by
  rw [Real.div_rpow hL.le (by positivity),←Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2),
    Real.rpow_neg (by norm_num : (0:ℝ)≤2),inv_pow,div_inv_eq_mul]

lemma sharpness_feature_error_absorb (β D : ℝ) (hβ : 0 ≤ β) (hD : 0 ≤ D) :
    (26*β^2+12*β^3)*(Real.exp (β*D/2)*(1+D^4))^2 ≤
      625*(26*β^2+12*β^3)*Real.exp ((β+2)*D) := by
  have h4 := Real.pow_div_factorial_le_exp D hD 4
  norm_num at h4
  have hp : 1+D^4 ≤ 25*Real.exp D := by nlinarith [Real.one_le_exp hD]
  have hm := mul_le_mul_of_nonneg_left hp (Real.exp_nonneg (β*D/2))
  have hs := pow_le_pow_left₀ (by positivity : 0 ≤ Real.exp (β*D/2)*(1+D^4)) hm 2
  have he : (Real.exp (β*D/2)*(25*Real.exp D))^2 = 625*Real.exp ((β+2)*D) := by
    rw [mul_pow,mul_pow,←Real.exp_nat_mul _ 2,←Real.exp_nat_mul _ 2]
    norm_num only [show (25:ℝ)^2 = 625 by norm_num]
    rw [show (β+2)*D = (2:ℝ)*(β*D/2)+(2:ℝ)*D by ring,Real.exp_add]
    ring
  rw [he] at hs
  have hc : 0 ≤ 26*β^2+12*β^3 := by positivity
  convert mul_le_mul_of_nonneg_left hs hc using 1 <;> ring

/-- Logarithmic scale choice with a genuine vanishing finite-particle error.
All constants are fixed before N. The native geometric selector constructs m. -/
theorem sharpness_exists_small_error_scale (b v d0 d1 β : ℝ)
    (hb : 1 < b) (hv : 0 < v) (hd0 : 0 ≤ d0) (hd1 : 0 ≤ d1) (hβ : 0 ≤ β)
    (m0 : ℕ) :
    ∃ t : ℝ,0 < t ∧ ∀ᶠ N : ℕ in atTop,∃ m : ℕ,m0 ≤ m ∧
      v*b^m ≤ t*Real.log (N:ℝ) ∧ t*Real.log (N:ℝ) < b*(v*b^m) ∧
      (26*β^2+12*β^3)*(Real.exp (β*(d0+d1*(v*b^m))/2)*(1+(d0+d1*(v*b^m))^4))^2/(N:ℝ) ≤ 1/2 := by
  let t := (2*((β+2)*(d1+1)))⁻¹
  have ht : 0 < t := by dsimp [t]; positivity
  have hcoef : (β+2)*d1*t ≤ 1/2 := by
    dsimp [t]
    rw [←div_eq_mul_inv]
    apply (div_le_iff₀ (by positivity : 0 < 2*((β+2)*(d1+1)))).mpr
    nlinarith
  let C := 625*(26*β^2+12*β^3)*Real.exp ((β+2)*d0)
  have hlog : Tendsto (fun N : ℕ => t*Real.log (N:ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop ht (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hErr : Tendsto (fun N : ℕ => C*(N:ℝ)^(-(1/2:ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero,Function.comp_apply] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/2)).comp tendsto_natCast_atTop_atTop).const_mul C
  refine ⟨t,ht,?_⟩
  filter_upwards [hlog.eventually (eventually_ge_atTop (v*b^m0)),eventually_ge_atTop 1,
    hErr.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2))] with N hscale hN herr
  obtain ⟨m,hm,hlo,hhi⟩ := sharpness_geometric_scale_select b v (t*Real.log (N:ℝ)) hb hv m0 hscale
  refine ⟨m,hm,hlo,hhi,?_⟩
  have hNpos : 0 < (N:ℝ) := by exact_mod_cast (show 0<N by omega)
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hN1
  have hD : 0 ≤ d0+d1*(v*b^m) := by positivity
  have hDlog : (β+2)*(d0+d1*(v*b^m)) ≤ (β+2)*d0+Real.log (N:ℝ)/2 := by
    have hh := mul_le_mul_of_nonneg_left hlo (mul_nonneg (by positivity : 0 ≤ β+2) hd1)
    have hh' := mul_le_mul_of_nonneg_right hcoef hlog0
    nlinarith
  have hexp := Real.exp_le_exp.mpr hDlog
  have heN : Real.exp (Real.log (N:ℝ)/2) = (N:ℝ)^(1/2:ℝ) := by
    rw [Real.rpow_def_of_pos hNpos]
    congr 1
    ring
  have hpow : (N:ℝ)^(1/2:ℝ)/(N:ℝ) = (N:ℝ)^(-(1/2:ℝ)) := by
    calc
      _ = (N:ℝ)^(1/2:ℝ)/(N:ℝ)^(1:ℝ) := by rw [Real.rpow_one]
      _ = (N:ℝ)^((1/2:ℝ)-1) := (Real.rpow_sub hNpos _ _).symm
      _ = _ := by congr 1; norm_num
  have hc : 0 ≤ 625*(26*β^2+12*β^3) := by positivity
  calc
    _ ≤ (625*(26*β^2+12*β^3)*Real.exp ((β+2)*(d0+d1*(v*b^m))))/(N:ℝ) :=
      div_le_div_of_nonneg_right (sharpness_feature_error_absorb β _ hβ hD) hNpos.le
    _ ≤ (625*(26*β^2+12*β^3)*Real.exp ((β+2)*d0+Real.log (N:ℝ)/2))/(N:ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hc) hNpos.le
    _ = C*(N:ℝ)^(-(1/2:ℝ)) := by
      rw [Real.exp_add,heN]
      dsimp [C]
      rw [show 625*(26*β^2+12*β^3)*(Real.exp ((β+2)*d0)*(N:ℝ)^(1/2:ℝ))/(N:ℝ) =
        (625*(26*β^2+12*β^3)*Real.exp ((β+2)*d0))*((N:ℝ)^(1/2:ℝ)/(N:ℝ)) by ring]
      rw [hpow]
    _ ≤ _ := herr.le

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_exists_small_error_scale
#check @DGRHS.Gaussian.sharpness_exists_small_error_scale
