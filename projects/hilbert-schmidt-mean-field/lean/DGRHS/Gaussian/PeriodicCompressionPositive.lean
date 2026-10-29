import DGRHS.Gaussian.PeriodicBoundedFourierForm
import DGRHS.Gaussian.SharpnessGramMatrix

/-! Actual positive finite compression of the original periodic Fourier
kernel. Native Parseval supplies the bounded-test positivity; unchanged
proper atom form and matrix-root infrastructure is reused. No favorable
matrix, Gaussian field, derivative or partition comparison is a premise. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ENNReal Classical BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicLog_finite_atom_form_nonneg {α : Type*} [Fintype α]
    (A : α → Set (PeriodicTorus ι)) (hA : ∀ i,MeasurableSet (A i)) (z : α → ℝ) :
    0 ≤ ∑ i,∑ j,z i*z j*sharpnessAtomIntegral (periodicHaar ι)
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1-p.2)) (A i) (A j) := by
  let F := sharpnessAtomStep A z
  let K := ∑ i,|z i|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hF := stronglyMeasurable_sharpnessAtomStep A hA z
  have hb : ∀ x,‖F x‖ ≤ K := norm_sharpnessAtomStep_le A z
  have hn := periodicLog_bounded_form_nonneg F hF.aestronglyMeasurable K hb
  have hw : AEStronglyMeasurable (fun p : PeriodicTorus ι × PeriodicTorus ι => F p.1*F p.2)
      ((periodicHaar ι).prod (periodicHaar ι)) :=
    ((hF.comp_measurable measurable_fst).mul (hF.comp_measurable measurable_snd)).aestronglyMeasurable
  have hiW := periodicLogPair_integrable.bdd_mul hw
    (Eventually.of_forall fun p : PeriodicTorus ι × PeriodicTorus ι => by
      rw [norm_mul]
      exact mul_le_mul (hb p.1) (hb p.2) (norm_nonneg _) hK)
  have hi : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicLogKernel (p.1-p.2)*F p.1*F p.2) ((periodicHaar ι).prod (periodicHaar ι)) :=
    hiW.congr (Eventually.of_forall fun p => by dsimp; ring)
  have he : (∫ p : PeriodicTorus ι × PeriodicTorus ι,
      periodicLogKernel (p.1-p.2)*F p.1*F p.2 ∂(periodicHaar ι).prod (periodicHaar ι)) =
      ∫ x,F x*(∫ y,F y*periodicLogKernel (x-y) ∂periodicHaar ι) ∂periodicHaar ι := by
    rw [integral_prod _ hi]
    calc
      _ = ∫ x,∫ y,F x*(F y*periodicLogKernel (x-y)) ∂periodicHaar ι ∂periodicHaar ι := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => integral_congr_ae
          (Eventually.of_forall fun y => by dsimp; ring)
      _ = _ := by simp_rw [integral_const_mul]
  have hprod : 0 ≤ ∫ p : PeriodicTorus ι × PeriodicTorus ι,
      periodicLogKernel (p.1-p.2)*F p.1*F p.2 ∂(periodicHaar ι).prod (periodicHaar ι) := he.symm ▸ hn
  exact hprod.trans_eq (sharpness_atom_form_identity (periodicHaar ι)
    (fun p => periodicLogKernel (p.1-p.2)) periodicLogPair_integrable A hA z)

/-- The exact atom-average matrix of the original logarithmic Fourier kernel
is positive semidefinite, including null atoms with totalized averages. -/
theorem periodicLog_average_matrix_posSemidef {α : Type*} [Fintype α]
    (A : α → Set (PeriodicTorus ι)) (hA : ∀ i,MeasurableSet (A i)) :
    Matrix.PosSemidef (fun i j => sharpnessAtomAverage (periodicHaar ι)
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1-p.2)) (A i) (A j)) := by
  let μ := periodicHaar ι
  let H := fun p : PeriodicTorus ι × PeriodicTorus ι => periodicLogKernel (p.1-p.2)
  let B : Matrix α α ℝ := fun i j => sharpnessAtomAverage μ H (A i) (A j)
  have hHs : ∀ p,H p.swap=H p := by
    rintro ⟨x,y⟩
    simpa only [H,Prod.swap,neg_sub] using periodicLogKernel_even (x-y)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change B.conjTranspose=B
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial]
    exact sharpness_atom_average_symmetric μ H hHs (A j) (A i)
  · intro x
    have hn := periodicLog_finite_atom_form_nonneg A hA (fun i => x i/(μ (A i)).toReal)
    have he (i j : α) :
        (x i/(μ (A i)).toReal)*(x j/(μ (A j)).toReal)*sharpnessAtomIntegral μ H (A i) (A j) =
        x i*(B i j*x j) := by
      dsimp [B,sharpnessAtomAverage]
      simp only [div_eq_mul_inv,_root_.mul_inv_rev]
      ring
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum]
    exact hn.trans_eq (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => he i j)))

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicLog_finite_atom_form_nonneg
#print axioms DGRHS.Periodic.periodicLog_average_matrix_posSemidef
#check @DGRHS.Periodic.periodicLog_average_matrix_posSemidef
