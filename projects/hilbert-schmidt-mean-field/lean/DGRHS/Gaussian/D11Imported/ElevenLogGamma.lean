import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic

/-! Exact integer and half-integer logarithmic Gamma derivatives needed for
the Euclidean entropy in Section 4. -/
noncomputable section
open Filter Set
open scoped Topology
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

lemma logGamma_next {s g : ℝ} (hs : 0 < s)
    (h : HasDerivAt (fun x => Real.log (Real.Gamma x)) g s) :
    HasDerivAt (fun x => Real.log (Real.Gamma x)) (g+1/s) (s+1) := by
  have hshift : HasDerivAt (fun x : ℝ => x-1) 1 (s+1) := by
    simpa using (hasDerivAt_id (s+1)).sub_const 1
  have h0 : HasDerivAt (fun x => Real.log (Real.Gamma x)) g ((s+1)-1) := by simpa using h
  have hl : HasDerivAt Real.log s⁻¹ ((s+1)-1) := by simpa using Real.hasDerivAt_log hs.ne'
  have hg := (h0.comp (s+1) hshift).add (hl.comp (s+1) hshift)
  norm_num only [mul_one, one_div] at hg ⊢
  apply hg.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds (show 1 < s+1 by linarith)] with x hx
  change 1 < x at hx
  have hx0 : 0 < x-1 := by linarith
  have hγ : Real.Gamma x = (x-1)*Real.Gamma (x-1) := by
    simpa only [sub_add_cancel] using Real.Gamma_add_one hx0.ne'
  rw [hγ, Real.log_mul hx0.ne' (Real.Gamma_pos_of_pos hx0).ne']
  dsimp only [Function.comp_apply, Pi.add_apply]
  ring

lemma logGamma_half_derivative :
    HasDerivAt (fun x => Real.log (Real.Gamma x))
      (-Real.eulerMascheroniConstant-2*Real.log 2) (1/2) := by
  have h := Real.hasDerivAt_Gamma_one_half.log (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<1/2)).ne'
  rw [Real.Gamma_one_half_eq] at h
  convert h using 1
  field_simp [(Real.sqrt_pos.mpr Real.pi_pos).ne']
  ring

lemma logGamma_eleven_half_derivative :
    HasDerivAt (fun x => Real.log (Real.Gamma x))
      (-Real.eulerMascheroniConstant-2*Real.log 2+1126/315) (11/2) := by
  have h1 := logGamma_next (by norm_num : (0:ℝ)<1/2) logGamma_half_derivative
  norm_num only at h1
  have h2 := logGamma_next (by norm_num : (0:ℝ)<3/2) h1
  norm_num only at h2
  have h3 := logGamma_next (by norm_num : (0:ℝ)<5/2) h2
  norm_num only at h3
  have h4 := logGamma_next (by norm_num : (0:ℝ)<7/2) h3
  norm_num only at h4
  have h5 := logGamma_next (by norm_num : (0:ℝ)<9/2) h4
  convert h5 using 1 <;> ring

lemma logGamma_eleven_derivative :
    HasDerivAt (fun x => Real.log (Real.Gamma x))
      ((7381:ℝ)/2520-Real.eulerMascheroniConstant) 11 := by
  have h := (Real.hasDerivAt_Gamma_nat 10).log (Real.Gamma_pos_of_pos (by norm_num : (0:ℝ)<10+1)).ne'
  have hg : Real.Gamma 11 = 3628800 := by
    convert Real.Gamma_nat_eq_factorial 10 using 1 <;> norm_num
  norm_num [harmonic, Finset.sum_range_succ, hg] at h
  convert h using 1 <;> ring

#print axioms logGamma_eleven_half_derivative
#print axioms logGamma_eleven_derivative
end DGRHS.Gaussian.D11Imported.HighDim.Eleven
