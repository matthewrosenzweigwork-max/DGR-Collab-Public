import DGRHS.Kernel.SpectralHilbertSchmidt
import DGRHS.Gaussian.SharpnessOperatorBound

noncomputable section
open MeasureTheory
open scoped Classical
namespace DGRHS.Gaussian

lemma sharpness_log_defect_lower {x L : ℝ} (hx : 0 ≤ x) (hxL : x ≤ L) :
    x^2/(4*(1+L)) ≤ x-Real.log (1+x) := by
  have hp : 0 < 1+x := by linarith
  let t := Real.sqrt (1+x)
  have ht : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t^2 = 1+x := Real.sq_sqrt hp.le
  have hl := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hp)
  rw [Real.log_sqrt hp.le] at hl
  have hq : (t-1)^2 ≤ x-Real.log (1+x) := by dsimp [t] at *; nlinarith
  have hden : (t+1)^2 ≤ 4*(1+L) := by nlinarith [sq_nonneg (t-1)]
  have he : x^2 = (t-1)^2*(t+1)^2 := by nlinarith [sq_nonneg (t^2-(1+x))]
  have hh := mul_le_mul_of_nonneg_left hden (sq_nonneg (t-1))
  have hL : 0 < 4*(1+L) := by linarith
  apply (div_le_iff₀ hL).mpr
  have hh2 := mul_le_mul_of_nonneg_right hq hL.le
  nlinarith

/-- Uniform spectral square lower bound, including zero eigenvalues. -/
theorem sharpness_inv_sqrt_det_lower {j : Type*} (eig : j → ℝ)
    (hs : Summable (fun i => eig i^2)) (hpos : ∀ i,0 ≤ eig i)
    (L : ℝ) (hL : 0 ≤ L) (heL : ∀ i,eig i ≤ L)
    (β : ℝ) (hβ : 0 ≤ β) :
    Real.exp (β^2/(8*(1+β*L))*(∑' i,eig i^2)) ≤
      (Real.sqrt (DGRHS.Kernel.regularizedDet (fun i => β*eig i)))⁻¹ := by
  have hsβ := DGRHS.Kernel.summable_scaled_eigenvalue_sq eig hs β
  have hp : ∀ i,0 < 1+β*eig i := fun i => by have hi := hpos i; positivity
  have hl := DGRHS.Kernel.summable_regularizedLog hsβ
  have hd : 0 < 4*(1+β*L) := by positivity
  have hi : ∀ i,(β*eig i)^2/(4*(1+β*L)) ≤
      -DGRHS.Kernel.regularizedLog (β*eig i) := by
    intro i
    simpa only [DGRHS.Kernel.regularizedLog,neg_sub] using
      sharpness_log_defect_lower (mul_nonneg hβ (hpos i)) (mul_le_mul_of_nonneg_left (heL i) hβ)
  have ht := (hsβ.div_const (4*(1+β*L))).tsum_le_tsum hi hl.neg
  rw [tsum_div_const,tsum_neg] at ht
  have hsq : (∑' i,(β*eig i)^2) = β^2*(∑' i,eig i^2) := by
    simp only [mul_pow,tsum_mul_left]
  rw [hsq] at ht
  rw [DGRHS.Kernel.regularizedDet_eq_exp hsβ hp]
  have hsqrt : Real.sqrt (Real.exp (∑' i,DGRHS.Kernel.regularizedLog (β*eig i))) =
      Real.exp ((∑' i,DGRHS.Kernel.regularizedLog (β*eig i))/2) := by
    calc
      _ = Real.exp (Real.log (Real.sqrt (Real.exp (∑' i,DGRHS.Kernel.regularizedLog (β*eig i))))) :=
        (Real.exp_log (Real.sqrt_pos.mpr (Real.exp_pos _))).symm
      _ = _ := by rw [Real.log_sqrt (Real.exp_pos _).le,Real.log_exp]
  rw [hsqrt,←Real.exp_neg]
  apply Real.exp_le_exp.mpr
  have hh := div_le_div_of_nonneg_right ht (by norm_num : (0:ℝ) ≤ 2)
  convert hh using 1 <;> field_simp <;> ring

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_log_defect_lower
#print axioms DGRHS.Gaussian.sharpness_inv_sqrt_det_lower
#check @DGRHS.Gaussian.sharpness_inv_sqrt_det_lower
