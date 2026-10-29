import DGRHS.Gaussian.SharpnessCompression
import Mathlib.LinearAlgebra.Matrix.PosDef

noncomputable section
open MeasureTheory Set Matrix
open scoped ENNReal Classical
namespace DGRHS.Gaussian
variable {X α ι : Type*} [MeasurableSpace X] [Fintype α] [Fintype ι]

lemma sharpness_atom_integral_symmetric (μ : Measure X) [IsFiniteMeasure μ]
    (H : X × X → ℝ) (hH : ∀ p, H p.swap = H p) (A B : Set X) :
    sharpnessAtomIntegral μ H A B = sharpnessAtomIntegral μ H B A := by
  unfold sharpnessAtomIntegral
  calc
    _ = ∫ p,H p.swap ∂(μ.restrict B).prod (μ.restrict A) :=
      (integral_prod_swap H).symm
    _ = _ := by congr 1; funext p; exact hH p

lemma sharpness_atom_average_symmetric (μ : Measure X) [IsFiniteMeasure μ]
    (H : X × X → ℝ) (hH : ∀ p, H p.swap = H p) (A B : Set X) :
    sharpnessAtomAverage μ H A B = sharpnessAtomAverage μ H B A := by
  unfold sharpnessAtomAverage
  rw [sharpness_atom_integral_symmetric μ H hH A B,mul_comm (μ A).toReal (μ B).toReal]

/-- The actual unweighted block-average matrix is positive semidefinite. Its
normalization is proved from the physical bounded-test form; no positive
matrix or favorable feature map is supplied. -/
theorem sharpness_riesz_average_matrix_posSemidef (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (A : α → Set (EuclideanSpace ℝ ι))
    (hA : ∀ i, MeasurableSet (A i)) :
    Matrix.PosSemidef (fun (i j : α) => sharpnessAtomAverage (gaussianRieszDensityMeasure ρ)
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s)) (A i) (A j)) := by
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let B : Matrix α α ℝ := fun i j => sharpnessAtomAverage μ H (A i) (A j)
  have hHs : ∀ p, H p.swap = H p := by
    rintro ⟨x,y⟩
    exact DGRHS.centeredKernel_symmetric μ (fun u v => gaussianRieszPhysicalPair s (u,v))
      (sharpness_riesz_pair_symmetric s) y x
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change B.conjTranspose = B
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial]
    exact sharpness_atom_average_symmetric μ H hHs (A j) (A i)
  · intro x
    have hn := sharpness_finite_atom_form_nonneg s hs ha ρ M hM hρ A hA
      (fun i => x i/(μ (A i)).toReal)
    have he (i j : α) :
        (x i/(μ (A i)).toReal)*(x j/(μ (A j)).toReal)*sharpnessAtomIntegral μ H (A i) (A j) =
        x i*(B i j*x j) := by
      dsimp [B,sharpnessAtomAverage]
      simp only [div_eq_mul_inv,_root_.mul_inv_rev]
      ring
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum]
    exact hn.trans_eq (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => he i j)))

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_atom_average_symmetric
#print axioms DGRHS.Gaussian.sharpness_riesz_average_matrix_posSemidef
#check @DGRHS.Gaussian.sharpness_riesz_average_matrix_posSemidef
