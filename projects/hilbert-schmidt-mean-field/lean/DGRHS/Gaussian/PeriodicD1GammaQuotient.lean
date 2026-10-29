import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

/-! Scalar Gamma quotient in DGR source (DysonDeterminantLimit), lines 3032--3037.
The native Gamma derivative and slope limit are used directly. This file does
not assume or assert the circular integral formula or operator determinant.
Native primary sources and exact Apache license are retained in the D1 records. -/
noncomputable section
open Filter Set
open scoped Topology
namespace DGRHS.Periodic

lemma periodicD1_logGamma_hasDerivAt (β : ℝ) :
    HasDerivAt (fun t : ℝ => Real.log (Real.Gamma (1-β/2*t)))
      (β*Real.eulerMascheroniConstant/2) 0 := by
  have hG : HasDerivAt Real.Gamma (-Real.eulerMascheroniConstant) (1-β/2*0) := by
    simpa using Real.hasDerivAt_Gamma_one
  have hlin : HasDerivAt (fun t : ℝ => 1-β/2*t) (-(β/2)) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul (β/2)).const_sub 1
  have h := (hG.comp 0 hlin).log (by simp)
  convert h using 1 <;> norm_num <;> ring

lemma periodicD1_logGamma_scaled_tendsto (β : ℝ) :
    Tendsto (fun N : ℕ => (N:ℝ)*Real.log (Real.Gamma (1-β/(2*N))))
      atTop (𝓝 (β*Real.eulerMascheroniConstant/2)) := by
  have hseq : Tendsto (fun N : ℕ => (N:ℝ)⁻¹) atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [one_div] using
        (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
          Tendsto (fun N : ℕ => (1:ℝ)/(N:ℝ)) atTop (𝓝 0))
    · filter_upwards [eventually_gt_atTop 0] with N hN
      change (0:ℝ)<(N:ℝ)⁻¹
      exact inv_pos.mpr (Nat.cast_pos.mpr hN)
  have h := (periodicD1_logGamma_hasDerivAt β).tendsto_slope_zero_right.comp hseq
  apply h.congr'
  filter_upwards [] with N
  simp [Function.comp_def,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]

lemma periodicD1_Gamma_argument_pos {β : ℝ} (hβ : β<2) {N : ℕ} (hN : 1≤N) :
    0<1-β/(2*(N:ℝ)) := by
  have hn : (1:ℝ)≤N := by exact_mod_cast hN
  apply sub_pos.mpr
  apply (div_lt_one (by positivity : 0<2*(N:ℝ))).mpr
  linarith

lemma periodicD1_Gamma_power_tendsto {β : ℝ} (hβ : β<2) :
    Tendsto (fun N : ℕ => Real.Gamma (1-β/(2*N))^N)
      atTop (𝓝 (Real.exp (β*Real.eulerMascheroniConstant/2))) := by
  have h := Real.continuous_exp.continuousAt.tendsto.comp
    (periodicD1_logGamma_scaled_tendsto β)
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  change Real.exp ((N:ℝ)*Real.log (Real.Gamma (1-β/(2*N))))=_
  rw [Real.exp_nat_mul,Real.exp_log
    (Real.Gamma_pos_of_pos (periodicD1_Gamma_argument_pos hβ hN))]

/-- The exact scalar quotient limit appearing in the source. Identifying the
quotient with the actual particle integral remains a separate obligation. -/
theorem periodicD1_Gamma_quotient_tendsto (β : ℝ) (hβ0 : 0≤β) (hβ : β<2) :
    Tendsto (fun N : ℕ => Real.Gamma (1-β/2)/Real.Gamma (1-β/(2*N))^N)
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant*β/2)*Real.Gamma (1-β/2))) := by
  have hconst : Tendsto (fun _ : ℕ => Real.Gamma (1-β/2)) atTop
      (𝓝 (Real.Gamma (1-β/2))) := tendsto_const_nhds
  have h := hconst.div (periodicD1_Gamma_power_tendsto hβ)
    (Real.exp_ne_zero (β*Real.eulerMascheroniConstant/2))
  change Tendsto (fun N : ℕ => Real.Gamma (1-β/2)/Real.Gamma (1-β/(2*N))^N)
    atTop (𝓝 (Real.Gamma (1-β/2)/Real.exp (β*Real.eulerMascheroniConstant/2))) at h
  have he : Real.Gamma (1-β/2)/Real.exp (β*Real.eulerMascheroniConstant/2)=
      Real.exp (-Real.eulerMascheroniConstant*β/2)*Real.Gamma (1-β/2) := by
    rw [div_eq_mul_inv,←Real.exp_neg,mul_comm]
    congr 1
    congr 1
    ring
  simpa only [he] using h

end DGRHS.Periodic
