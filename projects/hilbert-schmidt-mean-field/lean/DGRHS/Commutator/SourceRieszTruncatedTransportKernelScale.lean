import DGRHS.Commutator.SourceRieszTransportKernel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Actual first derivative of the Gaussian scale integrand and its widened
Gaussian domination. No derivative/profile estimate is assumed. -/
noncomputable section
open scoped RealInnerProductSpace NNReal
namespace DGRHS.Commutator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def sourceRieszGaussianScale (t : ℝ) (z : E) : ℝ :=
  Real.exp (-‖z‖^2/(2*t^2))

def sourceRieszGaussianScaleDerivative (t : ℝ) (z : E) : E→L[ℝ] ℝ :=
  (-sourceRieszGaussianScale t z / t^2) • innerSL ℝ z

lemma hasFDerivAt_sourceRieszGaussianScale (t : ℝ) (ht : t≠0) (z : E) :
    HasFDerivAt (sourceRieszGaussianScale t) (sourceRieszGaussianScaleDerivative t z) z := by
  have h := ((((hasStrictFDerivAt_norm_sq z).hasFDerivAt.neg).const_smul ((2*t^2)⁻¹))).exp
  convert h using 1
  · ext q
    simp only [sourceRieszGaussianScale,Pi.smul_apply,Pi.neg_apply,smul_eq_mul]
    congr 1
    ring
  · ext w
    simp only [sourceRieszGaussianScaleDerivative,sourceRieszGaussianScale,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.neg_apply,Pi.smul_apply,Pi.neg_apply,smul_eq_mul]
    ring

lemma sourceRieszGaussianScaleDerivative_apply (t : ℝ) (z w : E) :
    sourceRieszGaussianScaleDerivative t z w =
      -(sourceRieszGaussianScale t z / t^2)*⟪z,w⟫ := by
  simp [sourceRieszGaussianScaleDerivative,neg_div]

lemma sourceRieszGaussianScale_polynomial_bound (r t : ℝ) (ht : 0<t) :
    (r^2/t^2)*Real.exp (-r^2/(2*t^2)) ≤
      4*Real.exp (-r^2/(4*t^2)) := by
  let a := r^2/(4*t^2)
  have ha : 0≤a := by dsimp [a];positivity
  have h := Real.mul_exp_neg_le_exp_neg_one a
  have he : Real.exp (-1)≤1 := Real.exp_le_one_iff.mpr (by norm_num)
  have h' : a*Real.exp (-a)≤1 := h.trans he
  have heq : Real.exp (-r^2/(2*t^2))=Real.exp (-a)*Real.exp (-a) := by
    rw [←Real.exp_add];congr 1;dsimp [a];ring
  rw [heq]
  have heq2 : r^2/t^2=4*a := by dsimp [a];ring
  rw [heq2]
  have hea : -r^2/(4*t^2) = -a := by dsimp [a];ring
  rw [hea]
  nlinarith [mul_le_mul_of_nonneg_right h' (Real.exp_pos (-a)).le]

lemma sourceRieszGaussianScale_transport_bound (t : ℝ) (ht : 0<t)
    {K : ℝ≥0} {v : E→E} (hv : LipschitzWith K v) (x y : E) :
    |sourceRieszGaussianScaleDerivative t (x-y) (v x-v y)| ≤
      4*(K:ℝ)*Real.exp (-‖x-y‖^2/(4*t^2)) := by
  rw [sourceRieszGaussianScaleDerivative_apply,sourceRieszGaussianScale,abs_mul,abs_neg,
    abs_div,abs_of_pos (Real.exp_pos _),abs_of_nonneg (sq_nonneg t)]
  have hi := norm_inner_le_norm (𝕜:=ℝ) (x-y) (v x-v y)
  rw [Real.norm_eq_abs] at hi
  have hv' : ‖v x-v y‖≤(K:ℝ)*‖x-y‖ := by simpa only [dist_eq_norm] using hv.dist_le_mul x y
  have hb := sourceRieszGaussianScale_polynomial_bound ‖x-y‖ t ht
  calc
    _ ≤ (Real.exp (-‖x-y‖^2/(2*t^2))/t^2)*(‖x-y‖*((K:ℝ)*‖x-y‖)) := by
      exact mul_le_mul_of_nonneg_left (hi.trans (mul_le_mul_of_nonneg_left hv' (norm_nonneg _))) (by positivity)
    _ = (K:ℝ)*((‖x-y‖^2/t^2)*Real.exp (-‖x-y‖^2/(2*t^2))) := by ring
    _ ≤ (K:ℝ)*(4*Real.exp (-‖x-y‖^2/(4*t^2))) := mul_le_mul_of_nonneg_left hb K.coe_nonneg
    _ = _ := by ring
end DGRHS.Commutator
#check @DGRHS.Commutator.sourceRieszGaussianScale
#print axioms DGRHS.Commutator.sourceRieszGaussianScale
#check @DGRHS.Commutator.sourceRieszGaussianScaleDerivative
#print axioms DGRHS.Commutator.sourceRieszGaussianScaleDerivative
#check @DGRHS.Commutator.hasFDerivAt_sourceRieszGaussianScale
#print axioms DGRHS.Commutator.hasFDerivAt_sourceRieszGaussianScale
#check @DGRHS.Commutator.sourceRieszGaussianScaleDerivative_apply
#print axioms DGRHS.Commutator.sourceRieszGaussianScaleDerivative_apply
#check @DGRHS.Commutator.sourceRieszGaussianScale_polynomial_bound
#print axioms DGRHS.Commutator.sourceRieszGaussianScale_polynomial_bound
#check @DGRHS.Commutator.sourceRieszGaussianScale_transport_bound
#print axioms DGRHS.Commutator.sourceRieszGaussianScale_transport_bound
