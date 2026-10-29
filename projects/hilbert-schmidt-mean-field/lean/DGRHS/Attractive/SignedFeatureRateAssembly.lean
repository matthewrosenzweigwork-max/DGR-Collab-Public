import DGRHS.Concentration.PartitionRate
import DGRHS.Attractive.LogRateOptimization

/- Scalar passage from the actual fixed-cutoff square-root rate to its limit,
followed by the actual two-limit finite-particle comparison. No determinant
continuity, operator spectral comparison or desired full rate is assumed. -/
noncomputable section
open Filter
open scoped Topology
namespace DGRHS.Attractive

lemma partition_tendsto_of_sqrt_error (Y : ℕ→ℝ) (y A : ℝ)
    (h : ∀ n,1≤n→|Y n-y|≤A/Real.sqrt (n:ℝ)) : Tendsto Y atTop (𝓝 y) := by
  have hi : Tendsto (fun n : ℕ=>(n:ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using
      (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ=>(1:ℝ)/(n:ℝ)) atTop (𝓝 0))
  have hs := ((Real.continuous_sqrt.tendsto 0).comp hi).const_mul A
  have hlim : Tendsto (fun n : ℕ=>A/Real.sqrt (n:ℝ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_inv,Real.sqrt_zero,mul_zero,div_eq_mul_inv] using hs
  apply tendsto_iff_norm_sub_tendsto_zero.2
  apply squeeze_zero' (Eventually.of_forall fun n=>norm_nonneg (Y n-y))
    ((eventually_ge_atTop 1).mono fun n hn=>?_) hlim
  simpa only [Real.norm_eq_abs] using h n hn

lemma power_cutoff_le_exponential_envelope (B q C η : ℝ)
    (hB : 0≤B) (hBC : B≤C) (hqC : q≤C) (hη : 0<η) (hη1 : η≤1) :
    B*η^(-q)≤C*Real.exp (C*(1+Real.log (1/η))) := by
  have hC : 0≤C := hB.trans hBC
  have hlog : 0≤Real.log (1/η) := Real.log_nonneg (by
    exact (le_div_iff₀ hη).2 (by simpa using hη1))
  have hp : η^(-q)≤Real.exp (C*(1+Real.log (1/η))) := by
    rw [Real.rpow_def_of_pos hη]
    apply Real.exp_le_exp.mpr
    have he : Real.log (1/η) = -Real.log η := by rw [one_div,Real.log_inv]
    have hm := mul_le_mul_of_nonneg_right hqC hlog
    rw [he] at hm
    rw [he]
    nlinarith
  exact mul_le_mul hBC hp (by positivity) hC

lemma partition_error_of_sqrt_cutoff_rate (Z Y : ℕ→ℝ) (z y A B q r η : ℝ)
    (hZ : Tendsto Z atTop (𝓝 z))
    (hY : ∀ n,1≤n→|Y n-y|≤B*η^(-q)/Real.sqrt (n:ℝ))
    (hComp : ∀ n,1≤n→|Z n-Y n|≤A*η^r) (n : ℕ) (hn : 1≤n) :
    |Z n-z|≤2*A*η^r+B*η^(-q)/Real.sqrt (n:ℝ) := by
  have hy := partition_tendsto_of_sqrt_error Y y (B*η^(-q)) hY
  have he := DGRHS.Concentration.partition_error_assembly Z Y z y (A*η^r) hZ hy hComp n hn
  have hh := (hY n hn)
  nlinarith

end DGRHS.Attractive
#check @DGRHS.Attractive.partition_tendsto_of_sqrt_error
#check @DGRHS.Attractive.power_cutoff_le_exponential_envelope
#check @DGRHS.Attractive.partition_error_of_sqrt_cutoff_rate
#print axioms DGRHS.Attractive.partition_tendsto_of_sqrt_error
#print axioms DGRHS.Attractive.power_cutoff_le_exponential_envelope
#print axioms DGRHS.Attractive.partition_error_of_sqrt_cutoff_rate
