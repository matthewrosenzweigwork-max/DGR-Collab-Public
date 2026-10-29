import DGRHS.Commutator.SourceRieszTruncatedTransportKernelGaussianBounds
import Mathlib.Analysis.Complex.Exponential

/-! Polynomial absorption for the actual Gaussian derivatives. Constants depend
only on the derivative order; no dimension or short-scale parameter enters. -/
noncomputable section
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sourceRieszGaussianDerivativeConstant (n : ℕ) : ℝ :=
  (n.factorial:ℝ)*2^n*8^(3*n)*((3*n).factorial:ℝ)*Real.exp (1/8)

lemma sourceRieszGaussianDerivativeConstant_pos (n : ℕ) :
    0 < sourceRieszGaussianDerivativeConstant n := by
  unfold sourceRieszGaussianDerivativeConstant
  positivity

lemma sourceRieszGaussian_polynomial_widening (n : ℕ) (r : ℝ) (hr : 0≤r) :
    (max 1 r)^n*((n.factorial:ℝ)*Real.exp (-r^2/2)*(2*(max 1 r)^2)^n) ≤
      sourceRieszGaussianDerivativeConstant n*Real.exp (-r^2/8) := by
  have hT : max 1 r ≤ 1+r^2 := by
    apply max_le
    · nlinarith [sq_nonneg r]
    · nlinarith [sq_nonneg (r-1/2)]
  have hpower : (max 1 r)^(3*n) ≤ (1+r^2)^(3*n) := by gcongr
  have hseries := Real.pow_div_factorial_le_exp ((1+r^2)/8) (by positivity) (3*n)
  have hfac : 0 < ((3*n).factorial:ℝ) := by positivity
  have hpoly : (1+r^2)^(3*n) ≤ 8^(3*n)*((3*n).factorial:ℝ)*Real.exp ((1+r^2)/8) := by
    have h := (div_le_iff₀ hfac).mp hseries
    have hp : 0 < (8:ℝ)^(3*n) := by positivity
    have h' := mul_le_mul_of_nonneg_left h hp.le
    rw [←mul_pow] at h'
    have he : (8:ℝ)*((1+r^2)/8)=1+r^2 := by ring
    rw [he] at h'
    nlinarith
  have hexp : Real.exp ((1+r^2)/8)*Real.exp (-r^2/2) ≤
      Real.exp (1/8)*Real.exp (-r^2/8) := by
    rw [←Real.exp_add,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg r]
  calc
    _ = (n.factorial:ℝ)*2^n*(max 1 r)^(3*n)*Real.exp (-r^2/2) := by
      rw [mul_pow,←pow_mul]
      ring
    _ ≤ (n.factorial:ℝ)*2^n*(1+r^2)^(3*n)*Real.exp (-r^2/2) := by gcongr
    _ ≤ (n.factorial:ℝ)*2^n*(8^(3*n)*((3*n).factorial:ℝ)*Real.exp ((1+r^2)/8))*Real.exp (-r^2/2) := by gcongr
    _ = ((n.factorial:ℝ)*2^n*8^(3*n)*((3*n).factorial:ℝ))*(Real.exp ((1+r^2)/8)*Real.exp (-r^2/2)) := by ring
    _ ≤ ((n.factorial:ℝ)*2^n*8^(3*n)*((3*n).factorial:ℝ))*(Real.exp (1/8)*Real.exp (-r^2/8)) := by gcongr
    _ = _ := by unfold sourceRieszGaussianDerivativeConstant;ring

lemma sourceRieszGaussian_iteratedFDeriv_widened_bound (n : ℕ) (z : E) :
    (max 1 ‖z‖)^n*‖iteratedFDeriv ℝ n (sourceRieszGaussianScale 1) z‖ ≤
      sourceRieszGaussianDerivativeConstant n*Real.exp (-‖z‖^2/8) := by
  exact (mul_le_mul_of_nonneg_left
    (sourceRieszGaussian_iteratedFDeriv_polynomial_bound n z) (by positivity)).trans
    (sourceRieszGaussian_polynomial_widening n ‖z‖ (norm_nonneg _))

end DGRHS.Commutator
#check DGRHS.Commutator.sourceRieszGaussianDerivativeConstant
#print axioms DGRHS.Commutator.sourceRieszGaussianDerivativeConstant
#check DGRHS.Commutator.sourceRieszGaussianDerivativeConstant_pos
#print axioms DGRHS.Commutator.sourceRieszGaussianDerivativeConstant_pos
#check DGRHS.Commutator.sourceRieszGaussian_polynomial_widening
#print axioms DGRHS.Commutator.sourceRieszGaussian_polynomial_widening
#check @DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_widened_bound
#print axioms DGRHS.Commutator.sourceRieszGaussian_iteratedFDeriv_widened_bound
