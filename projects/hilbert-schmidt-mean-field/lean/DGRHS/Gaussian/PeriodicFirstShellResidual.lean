import DGRHS.Gaussian.PeriodicFirstShellKernel
import DGRHS.Gaussian.PeriodicCompressionPositive

/-! The actual full logarithmic kernel minus its actual cosine-sine first
shell has a nonnegative bounded-test form and positive finite compressions.
This is derived, not a residual covariance/PSD hypothesis. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped Classical BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

attribute [local fun_prop] periodicFirstShellMode_continuous

lemma periodicFirstShellPair_continuous :
    Continuous (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicFirstShellKernel p.1 p.2) := by
  unfold periodicFirstShellKernel
  fun_prop

lemma periodicFirstShellPair_integrable :
    Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicFirstShellKernel p.1 p.2)
      ((periodicHaar ι).prod (periodicHaar ι)) :=
  periodicFirstShellPair_continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma periodicFirstShellKernel_symmetric (x y : PeriodicTorus ι) :
    periodicFirstShellKernel y x=periodicFirstShellKernel x y := by
  unfold periodicFirstShellKernel
  congr 1
  apply Finset.sum_congr rfl
  intro q _
  ring

def periodicFirstShellResidualPair (p : PeriodicTorus ι × PeriodicTorus ι) : ℝ :=
  periodicLogKernel (p.1-p.2)-periodicFirstShellKernel p.1 p.2

lemma periodicFirstShellResidualPair_integrable :
    Integrable (periodicFirstShellResidualPair (ι := ι)) ((periodicHaar ι).prod (periodicHaar ι)) :=
  periodicLogPair_integrable.sub periodicFirstShellPair_integrable

lemma periodic_bounded_pair_test_integrable
    (H : PeriodicTorus ι × PeriodicTorus ι → ℝ)
    (hH : Integrable H ((periodicHaar ι).prod (periodicHaar ι)))
    (F : PeriodicTorus ι → ℝ) (hF : AEStronglyMeasurable F (periodicHaar ι))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x,‖F x‖ ≤ B) :
    Integrable (fun p => H p*F p.1*F p.2) ((periodicHaar ι).prod (periodicHaar ι)) := by
  have hw : AEStronglyMeasurable (fun p : PeriodicTorus ι × PeriodicTorus ι => F p.1*F p.2)
      ((periodicHaar ι).prod (periodicHaar ι)) := (hF.comp_measurePreserving (measurePreserving_fst (μ := periodicHaar ι) (ν := periodicHaar ι))).mul
    (hF.comp_measurePreserving (measurePreserving_snd (μ := periodicHaar ι) (ν := periodicHaar ι)))
  have hi := hH.bdd_mul (c := B*B) hw
    (Eventually.of_forall fun p => by
      rw [norm_mul]
      exact mul_le_mul (hb p.1) (hb p.2) (norm_nonneg _) hB)
  exact hi.congr (Eventually.of_forall fun p => by dsimp;ring)

lemma periodic_bounded_pair_form_identity
    (H : PeriodicTorus ι × PeriodicTorus ι → ℝ)
    (hH : Integrable H ((periodicHaar ι).prod (periodicHaar ι)))
    (F : PeriodicTorus ι → ℝ) (hF : AEStronglyMeasurable F (periodicHaar ι))
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ x,‖F x‖ ≤ B) :
    (∫ p,H p*F p.1*F p.2 ∂(periodicHaar ι).prod (periodicHaar ι)) =
      ∫ x,F x*(∫ y,F y*H (x,y) ∂periodicHaar ι) ∂periodicHaar ι := by
  rw [integral_prod _ (periodic_bounded_pair_test_integrable H hH F hF B hB hb)]
  calc
    _ = ∫ x,∫ y,F x*(F y*H (x,y)) ∂periodicHaar ι ∂periodicHaar ι := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => integral_congr_ae
        (Eventually.of_forall fun y => by dsimp;ring)
    _ = _ := by simp_rw [integral_const_mul]

/-- Actual first-shell removal is nonnegative on every bounded real test. -/
theorem periodicFirstShellResidual_bounded_form_nonneg (F : PeriodicTorus ι → ℝ)
    (hF : AEStronglyMeasurable F (periodicHaar ι))
    (B : ℝ) (hb : ∀ x,‖F x‖≤B) :
    0 ≤ ∫ p,periodicFirstShellResidualPair p*F p.1*F p.2
      ∂(periodicHaar ι).prod (periodicHaar ι) := by
  have hB : 0 ≤ B := (norm_nonneg (F 0)).trans (hb 0)
  have hiF : Integrable F (periodicHaar ι) :=
    (integrable_const B).mono' hF (Eventually.of_forall hb)
  have hiG := periodic_bounded_pair_test_integrable
    (fun p => periodicLogKernel (p.1-p.2)) periodicLogPair_integrable F hF B hB hb
  have hiS := periodic_bounded_pair_test_integrable
    (fun p => periodicFirstShellKernel p.1 p.2) periodicFirstShellPair_integrable F hF B hB hb
  have he : (∫ p,periodicFirstShellResidualPair p*F p.1*F p.2
      ∂(periodicHaar ι).prod (periodicHaar ι)) =
      (∫ p,periodicLogKernel (p.1-p.2)*F p.1*F p.2 ∂(periodicHaar ι).prod (periodicHaar ι))-
      (∫ p,periodicFirstShellKernel p.1 p.2*F p.1*F p.2 ∂(periodicHaar ι).prod (periodicHaar ι)) := by
    rw [←integral_sub hiG hiS]
    apply integral_congr_ae
    exact Eventually.of_forall fun p => by dsimp [periodicFirstShellResidualPair];ring
  rw [he,
    periodic_bounded_pair_form_identity _ periodicLogPair_integrable F hF B hB hb,
    periodic_bounded_pair_form_identity _ periodicFirstShellPair_integrable F hF B hB hb,
    periodicFirstShell_form_identity F hiF]
  exact sub_nonneg.mpr (periodicLog_coordinate_firstShell_form_lower F hF B hb)

lemma periodicFirstShellResidual_atom_form_nonneg {α : Type*} [Fintype α]
    (A : α → Set (PeriodicTorus ι)) (hA : ∀ i,MeasurableSet (A i)) (z : α → ℝ) :
    0 ≤ ∑ i,∑ j,z i*z j*sharpnessAtomIntegral (periodicHaar ι)
      periodicFirstShellResidualPair (A i) (A j) := by
  let F := sharpnessAtomStep A z
  let B := ∑ i,|z i|
  have hn := periodicFirstShellResidual_bounded_form_nonneg F
    (stronglyMeasurable_sharpnessAtomStep A hA z).aestronglyMeasurable B
    (norm_sharpnessAtomStep_le A z)
  exact hn.trans_eq (sharpness_atom_form_identity (periodicHaar ι)
    periodicFirstShellResidualPair periodicFirstShellResidualPair_integrable A hA z)

/-- Every actual finite atom compression of the full-minus-first-shell
kernel is PSD, without any favorable residual matrix premise. -/
theorem periodicFirstShellResidual_average_matrix_posSemidef {α : Type*} [Fintype α]
    (A : α → Set (PeriodicTorus ι)) (hA : ∀ i,MeasurableSet (A i)) :
    Matrix.PosSemidef (fun i j => sharpnessAtomAverage (periodicHaar ι)
      periodicFirstShellResidualPair (A i) (A j)) := by
  let μ := periodicHaar ι
  let H := periodicFirstShellResidualPair (ι := ι)
  let B : Matrix α α ℝ := fun i j => sharpnessAtomAverage μ H (A i) (A j)
  have hHs : ∀ p,H p.swap=H p := by
    rintro ⟨x,y⟩
    dsimp [H,periodicFirstShellResidualPair]
    rw [show y-x=-(x-y) by abel,periodicLogKernel_even,periodicFirstShellKernel_symmetric]
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change B.conjTranspose=B
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial]
    exact sharpness_atom_average_symmetric μ H hHs (A j) (A i)
  · intro x
    have hn := periodicFirstShellResidual_atom_form_nonneg A hA (fun i => x i/(μ (A i)).toReal)
    have he (i j : α) :
        (x i/(μ (A i)).toReal)*(x j/(μ (A j)).toReal)*sharpnessAtomIntegral μ H (A i) (A j) =
        x i*(B i j*x j) := by
      dsimp [B,sharpnessAtomAverage]
      simp only [div_eq_mul_inv,_root_.mul_inv_rev]
      ring
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum]
    exact hn.trans_eq (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => he i j)))

end DGRHS.Periodic
#print axioms DGRHS.Periodic.periodicFirstShellPair_continuous
#print axioms DGRHS.Periodic.periodicFirstShellPair_integrable
#print axioms DGRHS.Periodic.periodicFirstShellKernel_symmetric
#print axioms DGRHS.Periodic.periodicFirstShellResidualPair_integrable
#print axioms DGRHS.Periodic.periodic_bounded_pair_test_integrable
#print axioms DGRHS.Periodic.periodic_bounded_pair_form_identity
#print axioms DGRHS.Periodic.periodicFirstShellResidual_bounded_form_nonneg
#print axioms DGRHS.Periodic.periodicFirstShellResidual_atom_form_nonneg
#print axioms DGRHS.Periodic.periodicFirstShellResidual_average_matrix_posSemidef
#check @DGRHS.Periodic.periodicFirstShellResidual_bounded_form_nonneg
#check @DGRHS.Periodic.periodicFirstShellResidual_average_matrix_posSemidef
