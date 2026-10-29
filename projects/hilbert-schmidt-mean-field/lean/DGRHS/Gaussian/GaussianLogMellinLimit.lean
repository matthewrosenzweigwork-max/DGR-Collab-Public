import DGRHS.Gaussian.RieszGaussianFullScale
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! Genuine Mellin difference formula and scalar zero-exponent limit.
Gamma recurrence removes the pole before taking the limit; the quotient limit
comes from the actual exponential derivative. No Frullani or improper-limit
identity is assumed. Source SHA256
6f52778d92aa534e2b5851ca0f6b0712dc56470259cb3efcb7146ac2384dac0c. -/
noncomputable section
open MeasureTheory Set Real Filter
open scoped Topology
namespace DGRHS.Gaussian

def gaussianLogMellinDifference (s r t : ℝ) : ℝ :=
  t ^ (-s - 1) * (Real.exp (-r ^ 2 / (2 * t ^ 2)) -
    Real.exp (-1 / (2 * t ^ 2)))

lemma integrableOn_gaussianLogMellinDifference (s r : ℝ)
    (hs : 0 < s) (hr : 0 < r) :
    IntegrableOn (gaussianLogMellinDifference s r) (Ioi 0) := by
  have hR := integrableOn_gaussianRiesz_full_scale s (r ^ 2 / 2) hs
    (by positivity : 0 < r ^ 2 / 2)
  have hOne := integrableOn_gaussianRiesz_full_scale s (1 / 2) hs
    (by norm_num : (0 : ℝ) < 1 / 2)
  convert hR.sub hOne using 1
  funext t
  dsimp [gaussianLogMellinDifference]
  rw [mul_sub]
  congr 1 <;> congr 2 <;> ring

lemma integral_gaussianLogMellinDifference (s r : ℝ)
    (hs : 0 < s) (hr : 0 < r) :
    (∫ t : ℝ in Ioi 0, gaussianLogMellinDifference s r t) =
      (2 : ℝ) ^ (s / 2) * Real.Gamma (s / 2 + 1) *
        (r ^ (-s) - 1) / s := by
  have hR := integrableOn_gaussianRiesz_full_scale s (r ^ 2 / 2) hs
    (by positivity : 0 < r ^ 2 / 2)
  have hOne := integrableOn_gaussianRiesz_full_scale s (1 / 2) hs
    (by norm_num : (0 : ℝ) < 1 / 2)
  have he : gaussianLogMellinDifference s r =
      fun t : ℝ => t ^ (-s - 1) * Real.exp (-(r ^ 2 / 2) / t ^ 2) -
        t ^ (-s - 1) * Real.exp (-(1 / 2) / t ^ 2) := by
    funext t
    dsimp [gaussianLogMellinDifference]
    rw [mul_sub]
    congr 1 <;> congr 2 <;> ring
  rw [he, integral_sub hR hOne,
    integral_gaussianRiesz_full_scale s (r ^ 2 / 2) hs (by positivity),
    integral_gaussianRiesz_full_scale s (1 / 2) hs (by norm_num),
    gaussianRiesz_full_scale_norm_power s r hr]
  have hOnePow : (1 / 2 : ℝ) ^ (-s / 2) = (2 : ℝ) ^ (s / 2) := by
    simpa using gaussianRiesz_full_scale_norm_power s 1 (by norm_num)
  rw [hOnePow, Real.Gamma_add_one (by positivity : s / 2 ≠ 0)]
  field_simp [hs.ne']

lemma continuousAt_realGamma_one : ContinuousAt Real.Gamma (1 : ℝ) := by
  exact (Real.differentiableAt_Gamma (by
    intro m
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith)).continuousAt

lemma tendsto_gaussianLogMellin_quotient (r : ℝ) (hr : 0 < r) :
    Tendsto (fun s : ℝ => (r ^ (-s) - 1) / s) (𝓝[>] 0)
      (𝓝 (-Real.log r)) := by
  have hd : HasDerivAt (fun s : ℝ => Real.exp (-Real.log r * s))
      (-Real.log r) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_mul (-Real.log r)).exp)
  convert hd.tendsto_slope_zero_right using 1
  funext s
  simp only [zero_add, mul_zero, Real.exp_zero, smul_eq_mul]
  rw [Real.rpow_def_of_pos hr]
  have he : Real.log r * (-s) = -Real.log r * s := by ring
  rw [he]
  ring

lemma tendsto_gaussianLogMellin_value (r : ℝ) (hr : 0 < r) :
    Tendsto (fun s : ℝ => (2 : ℝ) ^ (s / 2) *
      Real.Gamma (s / 2 + 1) * ((r ^ (-s) - 1) / s))
      (𝓝[>] 0) (𝓝 (-Real.log r)) := by
  have hS : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hPow : Tendsto (fun s : ℝ => (2 : ℝ) ^ (s / 2))
      (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    have hArg : Tendsto (fun s : ℝ => Real.log 2 * (s / 2))
        (𝓝[>] 0) (𝓝 0) := by
      simpa using (hS.div_const 2).const_mul (Real.log 2)
    have he := (Real.continuous_exp.tendsto (0 : ℝ)).comp hArg
    simpa only [Function.comp_def, Real.exp_zero, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] using he
  have hGamma : Tendsto (fun s : ℝ => Real.Gamma (s / 2 + 1))
      (𝓝[>] 0) (𝓝 (1 : ℝ)) := by
    have hArg : Tendsto (fun s : ℝ => s / 2 + 1) (𝓝[>] 0) (𝓝 1) := by
      simpa using (hS.div_const 2).add_const 1
    simpa only [Function.comp_def, Real.Gamma_one] using continuousAt_realGamma_one.tendsto.comp hArg
  simpa only [one_mul] using
    (hPow.mul hGamma).mul (tendsto_gaussianLogMellin_quotient r hr)

end DGRHS.Gaussian
#check DGRHS.Gaussian.gaussianLogMellinDifference
#print axioms DGRHS.Gaussian.gaussianLogMellinDifference
#check DGRHS.Gaussian.integrableOn_gaussianLogMellinDifference
#print axioms DGRHS.Gaussian.integrableOn_gaussianLogMellinDifference
#check DGRHS.Gaussian.integral_gaussianLogMellinDifference
#print axioms DGRHS.Gaussian.integral_gaussianLogMellinDifference
#check DGRHS.Gaussian.continuousAt_realGamma_one
#print axioms DGRHS.Gaussian.continuousAt_realGamma_one
#check DGRHS.Gaussian.tendsto_gaussianLogMellin_quotient
#print axioms DGRHS.Gaussian.tendsto_gaussianLogMellin_quotient
#check DGRHS.Gaussian.tendsto_gaussianLogMellin_value
#print axioms DGRHS.Gaussian.tendsto_gaussianLogMellin_value
