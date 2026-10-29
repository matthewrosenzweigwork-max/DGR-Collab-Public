import DGRHS.Gaussian.PeriodicRieszL2Fourier
import DGRHS.Gaussian.PeriodicCompressionPositive

/-! Compiled in the DGRHS development build (imported by the P9c periodic release root, checked 2026-10-06); development check only, not protected acceptance, not independently reviewed. Genuine positivity of the constructed Riesz
spectral kernel and its exact Haar atom-average matrices. Adapts the checked
PeriodicBoundedFourierForm/PeriodicCompressionPositive route, using the actual
A68 coefficients rather than assuming favorable matrices or positivity.
All source-positive exponents satisfy 0 < s and 2*s < d. Proper product
integration precedes the atom identity. This does not identify periodic
local singularities or transfer positivity to an arbitrary background. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ENNReal Classical BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicRieszFourierCoeff_real (s : ℝ) (k : PeriodicFrequency ι) :
    ((periodicRieszFourierCoeff s k).re : ℂ) = periodicRieszFourierCoeff s k := by
  unfold periodicRieszFourierCoeff
  split_ifs <;> simp

lemma periodicRieszKernel_fourierCoeff (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (k : PeriodicFrequency ι) :
    UnitAddTorus.mFourierCoeff (fun x => (periodicRieszKernel s hs x : ℂ)) k =
      periodicRieszFourierCoeff s k :=
  (periodic_mFourierCoeff_congr (periodicRieszKernel_coe_ae s hs) k).trans
    (periodicRieszL2_fourierCoeff s hs k)

lemma periodicRieszFourierCoeff_re_nonneg (s : ℝ) (hs0 : 0 < s)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (k : PeriodicFrequency ι) :
    0 ≤ (periodicRieszFourierCoeff s k).re := by
  by_cases hk : k = 0
  · subst k
    simp
  · exact (periodicRieszFourierCoeff_re_pos s hs0 (by linarith) k hk).le

lemma periodicRiesz_bounded_form_hasSum (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (F : PeriodicTorus ι → ℝ)
    (hF : AEStronglyMeasurable F (periodicHaar ι))
    (B : ℝ) (hb : ∀ x, ‖F x‖ ≤ B) :
    HasSum (fun k : PeriodicFrequency ι => (periodicRieszFourierCoeff s k).re *
      ((UnitAddTorus.mFourierCoeff (fun x => (F x : ℂ)) k).re ^ 2 +
       (UnitAddTorus.mFourierCoeff (fun x => (F x : ℂ)) k).im ^ 2))
      (∫ x, F x * (∫ y, F y * periodicRieszKernel s hs (x-y)
        ∂periodicHaar ι) ∂periodicHaar ι) := by
  apply periodic_bounded_fourier_form_hasSum (periodicRieszKernel s hs) F
    (periodicRieszKernel_integrable s hs) hF B hb
    (fun k => (periodicRieszFourierCoeff s k).re)
  intro k
  exact (periodicRieszKernel_fourierCoeff s hs k).trans
    (periodicRieszFourierCoeff_real s k).symm

lemma periodicRiesz_bounded_form_nonneg (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (hs0 : 0 < s)
    (F : PeriodicTorus ι → ℝ) (hF : AEStronglyMeasurable F (periodicHaar ι))
    (B : ℝ) (hb : ∀ x, ‖F x‖ ≤ B) :
    0 ≤ ∫ x, F x * (∫ y, F y * periodicRieszKernel s hs (x-y)
      ∂periodicHaar ι) ∂periodicHaar ι := by
  have h := periodicRiesz_bounded_form_hasSum s hs F hF B hb
  rw [← h.tsum_eq]
  exact tsum_nonneg fun k => mul_nonneg
    (periodicRieszFourierCoeff_re_nonneg s hs0 hs k)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))

lemma periodicRieszPair_memLp (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    MemLp (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs (p.1-p.2))
      2 ((periodicHaar ι).prod (periodicHaar ι)) :=
  (periodicRieszKernel_memLp s hs).comp_measurePreserving periodicHaar_preserving_difference

lemma periodicRieszPair_integrable (s : ℝ) (hs : 2 * s < (Fintype.card ι : ℝ)) :
    Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs (p.1-p.2))
      ((periodicHaar ι).prod (periodicHaar ι)) :=
  (periodicRieszPair_memLp s hs).integrable (by norm_num)

lemma periodicRiesz_finite_atom_form_nonneg (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (hs0 : 0 < s) {α : Type*} [Fintype α]
    (A : α → Set (PeriodicTorus ι)) (hA : ∀ i,MeasurableSet (A i)) (z : α → ℝ) :
    0 ≤ ∑ i,∑ j,z i*z j*sharpnessAtomIntegral (periodicHaar ι)
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs (p.1-p.2)) (A i) (A j) := by
  let F := sharpnessAtomStep A z
  let K := ∑ i,|z i|
  have hK : 0 ≤ K := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hF := stronglyMeasurable_sharpnessAtomStep A hA z
  have hb : ∀ x,‖F x‖ ≤ K := norm_sharpnessAtomStep_le A z
  have hn := periodicRiesz_bounded_form_nonneg s hs hs0 F hF.aestronglyMeasurable K hb
  have hw : AEStronglyMeasurable (fun p : PeriodicTorus ι × PeriodicTorus ι => F p.1*F p.2)
      ((periodicHaar ι).prod (periodicHaar ι)) :=
    ((hF.comp_measurable measurable_fst).mul (hF.comp_measurable measurable_snd)).aestronglyMeasurable
  have hiW := (periodicRieszPair_integrable s hs).bdd_mul hw
    (Eventually.of_forall fun p : PeriodicTorus ι × PeriodicTorus ι => by
      rw [norm_mul]
      exact mul_le_mul (hb p.1) (hb p.2) (norm_nonneg _) hK)
  have hi : Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι =>
      periodicRieszKernel s hs (p.1-p.2)*F p.1*F p.2) ((periodicHaar ι).prod (periodicHaar ι)) :=
    hiW.congr (Eventually.of_forall fun p => by dsimp; ring)
  have he : (∫ p : PeriodicTorus ι × PeriodicTorus ι,
      periodicRieszKernel s hs (p.1-p.2)*F p.1*F p.2 ∂(periodicHaar ι).prod (periodicHaar ι)) =
      ∫ x,F x*(∫ y,F y*periodicRieszKernel s hs (x-y) ∂periodicHaar ι) ∂periodicHaar ι := by
    rw [integral_prod _ hi]
    calc
      _ = ∫ x,∫ y,F x*(F y*periodicRieszKernel s hs (x-y)) ∂periodicHaar ι ∂periodicHaar ι := by
        apply integral_congr_ae
        exact Eventually.of_forall fun x => integral_congr_ae
          (Eventually.of_forall fun y => by dsimp; ring)
      _ = _ := by simp_rw [integral_const_mul]
  have hprod : 0 ≤ ∫ p : PeriodicTorus ι × PeriodicTorus ι,
      periodicRieszKernel s hs (p.1-p.2)*F p.1*F p.2 ∂(periodicHaar ι).prod (periodicHaar ι) := he.symm ▸ hn
  exact hprod.trans_eq (sharpness_atom_form_identity (periodicHaar ι)
    (fun p => periodicRieszKernel s hs (p.1-p.2)) (periodicRieszPair_integrable s hs) A hA z)

/-- The exact atom-average matrix of the constructed Riesz spectral kernel
is positive semidefinite, including null atoms with totalized averages. -/
theorem periodicRiesz_average_matrix_posSemidef (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (hs0 : 0 < s) {α : Type*} [Fintype α]
    (A : α → Set (PeriodicTorus ι)) (hA : ∀ i,MeasurableSet (A i)) :
    Matrix.PosSemidef (fun i j => sharpnessAtomAverage (periodicHaar ι)
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs (p.1-p.2)) (A i) (A j)) := by
  let μ := periodicHaar ι
  let H := fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs (p.1-p.2)
  let B : Matrix α α ℝ := fun i j => sharpnessAtomAverage μ H (A i) (A j)
  have hHs : ∀ p,H p.swap=H p := by
    rintro ⟨x,y⟩
    simpa only [H,Prod.swap,neg_sub] using periodicRieszKernel_even s hs (x-y)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change B.conjTranspose=B
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial]
    exact sharpness_atom_average_symmetric μ H hHs (A j) (A i)
  · intro x
    have hn := periodicRiesz_finite_atom_form_nonneg s hs hs0 A hA (fun i => x i/(μ (A i)).toReal)
    have he (i j : α) :
        (x i/(μ (A i)).toReal)*(x j/(μ (A j)).toReal)*sharpnessAtomIntegral μ H (A i) (A j) =
        x i*(B i j*x j) := by
      dsimp [B,sharpnessAtomAverage]
      simp only [div_eq_mul_inv,_root_.mul_inv_rev]
      ring
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum]
    exact hn.trans_eq (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => he i j)))


end DGRHS.Periodic
