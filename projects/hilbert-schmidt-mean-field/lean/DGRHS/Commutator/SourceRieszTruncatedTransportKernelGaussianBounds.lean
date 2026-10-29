import DGRHS.Commutator.SourceRieszTruncatedTransportKernelScale
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

/-! Native all-order composition bounds for the actual Gaussian. Coarse
polynomial factors are acceptable because subsequent Gaussian widening absorbs them. -/
noncomputable section
open scoped RealInnerProductSpace
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma sourceRiesz_norm_iteratedFDeriv_id_le (n : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (id : E→E) z‖≤max 1 ‖z‖ := by
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero,id_eq] using le_max_right (1:ℝ) ‖z‖
  | succ k =>
    cases k with
    | zero =>
      rw [norm_iteratedFDeriv_one,fderiv_id]
      exact ContinuousLinearMap.norm_id_le.trans (le_max_left _ _)
    | succ k =>
      rw [←norm_iteratedFDeriv_fderiv]
      have hF : fderiv ℝ (id : E→E)=(fun _ : E=>ContinuousLinearMap.id ℝ E) := by funext x;exact fderiv_id
      rw [hF,iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k)]
      simp only [Pi.zero_apply,norm_zero]
      exact (norm_nonneg z).trans (le_max_right _ _)

lemma sourceRiesz_norm_iteratedFDeriv_norm_sq_le (n : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (fun y : E=>‖y‖^2) z‖≤(2:ℝ)^n*(max 1 ‖z‖)^2 := by
  have h := (innerSL ℝ (E:=E)).norm_iteratedFDeriv_le_of_bilinear_of_le_one
    (f:=id) (g:=id) (contDiff_id : ContDiff ℝ n (id : E→E)) (contDiff_id : ContDiff ℝ n (id : E→E)) z le_rfl (norm_innerSL_le ℝ)
  have he : (fun y : E=>(innerSL ℝ) y y)=(fun y=>‖y‖^2) := by ext y;simp
  simp only [id_eq] at h
  rw [he] at h
  calc
    _ ≤ ∑ i∈Finset.range (n+1),(n.choose i:ℝ)*‖iteratedFDeriv ℝ i (id : E→E) z‖*‖iteratedFDeriv ℝ (n-i) (id : E→E) z‖ := h
    _ ≤ ∑ i∈Finset.range (n+1),(n.choose i:ℝ)*(max 1 ‖z‖)^2 := by
      apply Finset.sum_le_sum
      intro i hi
      have h1 := sourceRiesz_norm_iteratedFDeriv_id_le i z
      have h2 := sourceRiesz_norm_iteratedFDeriv_id_le (n-i) z
      simpa only [sq,mul_assoc] using
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (n.choose i))) h2
          (norm_nonneg _) (by positivity : 0≤(n.choose i:ℝ)*max 1 ‖z‖)
    _ = _ := by
      rw [←Finset.sum_mul,←Nat.cast_sum,Nat.sum_range_choose]
      simp

lemma sourceRiesz_norm_iteratedFDeriv_exp_eq (n : ℕ) (a : ℝ) :
    ‖iteratedFDeriv ℝ n Real.exp a‖=Real.exp a := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have he : iteratedDeriv n Real.exp = Real.exp := by
    simpa only [one_mul,one_pow] using iteratedDeriv_exp_const_mul n 1
  rw [he,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]

lemma sourceRieszGaussian_iteratedFDeriv_polynomial_bound (n : ℕ) (z : E) :
    ‖iteratedFDeriv ℝ n (sourceRieszGaussianScale (1:ℝ)) z‖ ≤
      (n.factorial:ℝ)*Real.exp (-‖z‖^2/2)*(2*(max 1 ‖z‖)^2)^n := by
  let f : E→ℝ := fun y=>-(1/2:ℝ)*‖y‖^2
  have hnorm : ContDiff ℝ n (fun y : E=>‖y‖^2) := by
    simpa only [id_eq] using (contDiff_id : ContDiff ℝ n (id : E→E)).norm_sq ℝ
  have hf : ContDiff ℝ n f := contDiff_const.mul hnorm
  have hD : ∀ i : ℕ,1 ≤ i → i ≤ n →‖iteratedFDeriv ℝ i f z‖≤(2*(max 1 ‖z‖)^2)^i := by
    intro i hi hin
    have h := sourceRiesz_norm_iteratedFDeriv_norm_sq_le i z
    have hc : ContDiffAt ℝ i (fun y : E=>‖y‖^2) z := by
      simpa only [id_eq] using (contDiff_id : ContDiff ℝ i (id : E→E)).norm_sq ℝ |>.contDiffAt
    have hF : f=(-(1/2:ℝ)) • (fun y : E=>‖y‖^2) := rfl
    rw [hF,iteratedFDeriv_const_smul_apply hc,norm_smul,Real.norm_eq_abs]
    norm_num
    have hT : 1≤(max 1 ‖z‖)^2 := by nlinarith [le_max_left (1:ℝ) ‖z‖]
    have hP : (max 1 ‖z‖)^2≤((max 1 ‖z‖)^2)^i := by
      have hpow : 1≤((max 1 ‖z‖)^2)^(i-1) := one_le_pow₀ hT
      calc
        _ = 1*(max 1 ‖z‖)^2 := by ring
        _ ≤ ((max 1 ‖z‖)^2)^(i-1)*(max 1 ‖z‖)^2 := mul_le_mul_of_nonneg_right hpow (sq_nonneg _)
        _ = _ := by rw [←pow_succ];congr 1;omega
    calc
      _ ≤ (2:ℝ)^i*(max 1 ‖z‖)^2 := by linarith [norm_nonneg (iteratedFDeriv ℝ i (fun y : E=>‖y‖^2) z)]
      _ ≤ (2:ℝ)^i*((max 1 ‖z‖)^2)^i := mul_le_mul_of_nonneg_left hP (by positivity)
      _ = _ := (mul_pow _ _ _).symm
  have h := norm_iteratedFDeriv_comp_le (𝕜:=ℝ) (g:=Real.exp) (f:=f)
    (Real.contDiff_exp : ContDiff ℝ n Real.exp) hf le_rfl z
    (C:=Real.exp (f z)) (D:=2*(max 1 ‖z‖)^2)
    (fun i _=>le_of_eq (sourceRiesz_norm_iteratedFDeriv_exp_eq i (f z))) hD
  have he : sourceRieszGaussianScale (1:ℝ)=(Real.exp ∘ f) := by
    funext y
    dsimp [sourceRieszGaussianScale,f]
    congr 1
    ring
  rw [he]
  convert h using 1
  dsimp [f]
  congr 2
  ring

end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRiesz_norm_iteratedFDeriv_id_le
#print axioms DGRHS.Commutator.sourceRiesz_norm_iteratedFDeriv_id_le
#check @DGRHS.Commutator.sourceRiesz_norm_iteratedFDeriv_norm_sq_le
#print axioms DGRHS.Commutator.sourceRiesz_norm_iteratedFDeriv_norm_sq_le
#check DGRHS.Commutator.sourceRiesz_norm_iteratedFDeriv_exp_eq
#print axioms DGRHS.Commutator.sourceRiesz_norm_iteratedFDeriv_exp_eq
#check @DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_polynomial_bound
#print axioms DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_polynomial_bound
