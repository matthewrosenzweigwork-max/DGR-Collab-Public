import DGRHS.Gaussian.SharpnessGramMatrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open MeasureTheory Set Matrix
open scoped ENNReal Classical MatrixOrder InnerProductSpace
namespace DGRHS.Gaussian
variable {α X ι : Type*} [Fintype α] [DecidableEq α] [MeasurableSpace X] [Fintype ι]

/-- Actual finite Gram vectors: columns of the native positive matrix square
root. No favorable Gaussian feature is selected. -/
def sharpnessMatrixFeature (B : Matrix α α ℝ) (i : α) : EuclideanSpace ℝ α :=
  WithLp.toLp 2 (fun j => CFC.sqrt B j i)

lemma inner_sharpnessMatrixFeature (B : Matrix α α ℝ) (hB : B.PosSemidef) (i j : α) :
    inner ℝ (sharpnessMatrixFeature B i) (sharpnessMatrixFeature B j) = B i j := by
  have hS : (CFC.sqrt B).IsHermitian := by
    simpa only [sub_zero] using (CFC.sqrt_nonneg B).isHermitian
  have hsq : CFC.sqrt B*CFC.sqrt B = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  have hentry := congrArg (fun A : Matrix α α ℝ => A i j) hsq
  rw [Matrix.mul_apply] at hentry
  have hs (k : α) : CFC.sqrt B k i = CFC.sqrt B i k := by
    have he := congrArg (fun A : Matrix α α ℝ => A i k) hS.eq
    simpa only [Matrix.conjTranspose_apply,star_trivial] using he
  unfold sharpnessMatrixFeature
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [star_trivial,dotProduct]
  calc
    _ = ∑ k, CFC.sqrt B i k*CFC.sqrt B k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hs k]
      ring
    _ = _ := hentry

lemma norm_sq_sharpnessMatrixFeature (B : Matrix α α ℝ) (hB : B.PosSemidef) (i : α) :
    ‖sharpnessMatrixFeature B i‖^2 = B i i := by
  rw [← real_inner_self_eq_norm_sq,inner_sharpnessMatrixFeature B hB]

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.inner_sharpnessMatrixFeature
#print axioms DGRHS.Gaussian.norm_sq_sharpnessMatrixFeature
#check @DGRHS.Gaussian.inner_sharpnessMatrixFeature
