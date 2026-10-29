import DGRHS.Gaussian.PeriodicRieszCompressionPositive
import DGRHS.Gaussian.PeriodicBoundedBackgroundL2
import DGRHS.Gaussian.PeriodicFirstShellResidual
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! RECORDS-ONLY / UNCOMPILED. Actual positive-Riesz atom matrices under
measurable nonnegative essentially bounded probability densities. The
withDensity product is transported to a Haar quadratic form with the actual
weighted test. An explicit clipped representative handles the AE density cap;
no pointwise cap is silently inferred. This is not a source partition theorem. -/
noncomputable section
open MeasureTheory Set Filter Matrix
open scoped ENNReal Classical BigOperators
namespace DGRHS.Periodic
open DGRHS.Gaussian
universe u
variable {ι : Type u} [Fintype ι] [Nonempty ι]

lemma periodicCappedDensityPair_integral_eq (ρ : PeriodicTorus ι → ℝ)
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (f : PeriodicTorus ι × PeriodicTorus ι → ℝ) :
    (∫ p, f p ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) =
      ∫ p, ρ p.1 * ρ p.2 * f p ∂(periodicHaar ι).prod (periodicHaar ι) := by
  unfold periodicCappedDensityMeasure
  rw [prod_withDensity hρm.ennreal_ofReal hρm.ennreal_ofReal]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall (fun p => by finiteness))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by
    simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hρ0 p.1),
      ENNReal.toReal_ofReal (hρ0 p.2), smul_eq_mul])

lemma periodicRiesz_density_bounded_form_nonneg_pointwise (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (hs0 : 0 < s)
    (ρ : PeriodicTorus ι → ℝ) (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (M : ℝ) (hM : 0 ≤ M) (hρM : ∀ x, ρ x ≤ M)
    (F : PeriodicTorus ι → ℝ) (hF : StronglyMeasurable F)
    (B : ℝ) (hb : ∀ x, ‖F x‖ ≤ B) :
    0 ≤ ∫ p : PeriodicTorus ι × PeriodicTorus ι,
      periodicRieszKernel s hs (p.1-p.2) * F p.1 * F p.2
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ) := by
  have hB : 0 ≤ B := (norm_nonneg (F 0)).trans (hb 0)
  have hW : StronglyMeasurable (fun x => ρ x * F x) := hρm.stronglyMeasurable.mul hF
  have hbound : ∀ x, ‖ρ x * F x‖ ≤ M*B := by
    intro x
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hρ0 x)]
    exact mul_le_mul (hρM x) (hb x) (norm_nonneg _) hM
  have hn := periodicRiesz_bounded_form_nonneg s hs hs0 (fun x => ρ x * F x)
    hW.aestronglyMeasurable (M*B) hbound
  have he := periodic_bounded_pair_form_identity
    (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs (p.1-p.2))
    (periodicRieszPair_integrable s hs) (fun x => ρ x * F x)
    hW.aestronglyMeasurable (M*B) (mul_nonneg hM hB) hbound
  rw [periodicCappedDensityPair_integral_eq ρ hρm hρ0]
  have hnorm : (∫ p : PeriodicTorus ι × PeriodicTorus ι,
      ρ p.1 * ρ p.2 * (periodicRieszKernel s hs (p.1-p.2) * F p.1 * F p.2)
      ∂(periodicHaar ι).prod (periodicHaar ι)) =
      ∫ p : PeriodicTorus ι × PeriodicTorus ι,
        periodicRieszKernel s hs (p.1-p.2) * (ρ p.1 * F p.1) * (ρ p.2 * F p.2)
        ∂(periodicHaar ι).prod (periodicHaar ι) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun p => by ring)
  rw [hnorm, he]
  exact hn

lemma periodicRiesz_density_bounded_form_nonneg (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (hs0 : 0 < s)
    (ρ : PeriodicTorus ι → ℝ) (hρm : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂periodicHaar ι, 0 ≤ ρ x)
    (M : ℝ) (hM : 0 ≤ M) (hρM : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    (F : PeriodicTorus ι → ℝ) (hF : StronglyMeasurable F)
    (B : ℝ) (hb : ∀ x, ‖F x‖ ≤ B) :
    0 ≤ ∫ p : PeriodicTorus ι × PeriodicTorus ι,
      periodicRieszKernel s hs (p.1-p.2) * F p.1 * F p.2
      ∂(periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ) := by
  let ρc : PeriodicTorus ι → ℝ := fun x => min (max (ρ x) 0) M
  have hρcm : Measurable ρc := (hρm.max measurable_const).min measurable_const
  have hc0 : ∀ x, 0 ≤ ρc x := fun x => le_min (le_max_right _ _) hM
  have hcM : ∀ x, ρc x ≤ M := fun x => min_le_right _ _
  have hc : ρc =ᵐ[periodicHaar ι] ρ := by
    filter_upwards [hρ0,hρM] with x hx hy
    simp only [ρc, max_eq_left hx, min_eq_left hy]
  have hmeasure : periodicCappedDensityMeasure ρc = periodicCappedDensityMeasure ρ := by
    apply withDensity_congr_ae
    exact hc.mono (fun x hx => congrArg ENNReal.ofReal hx)
  have hn := periodicRiesz_density_bounded_form_nonneg_pointwise s hs hs0
    ρc hρcm hc0 M hM hcM F hF B hb
  rw [hmeasure] at hn
  exact hn

lemma periodicRiesz_density_pair_integrable (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (ρ : PeriodicTorus ι → ℝ)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hρM : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M) :
    Integrable (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs (p.1-p.2))
      ((periodicCappedDensityMeasure ρ).prod (periodicCappedDensityMeasure ρ)) :=
  (periodicPair_memLp_of_density_cap ρ M hρM (periodicRieszKernel s hs)
    (periodicRieszKernel_memLp s hs)).integrable (by norm_num)

lemma periodicRiesz_density_finite_atom_form_nonneg (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (hs0 : 0 < s)
    (ρ : PeriodicTorus ι → ℝ) (hρm : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂periodicHaar ι, 0 ≤ ρ x)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρM : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    {α : Type*} [Fintype α] (A : α → Set (PeriodicTorus ι))
    (hA : ∀ i, MeasurableSet (A i)) (z : α → ℝ) :
    0 ≤ ∑ i, ∑ j, z i * z j * sharpnessAtomIntegral (periodicCappedDensityMeasure ρ)
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs (p.1-p.2))
      (A i) (A j) := by
  have hn := periodicRiesz_density_bounded_form_nonneg s hs hs0 ρ hρm hρ0 M hM hρM
    (sharpnessAtomStep A z) (stronglyMeasurable_sharpnessAtomStep A hA z)
    (∑ i, |z i|) (norm_sharpnessAtomStep_le A z)
  exact hn.trans_eq (sharpness_atom_form_identity (periodicCappedDensityMeasure ρ)
    (fun p => periodicRieszKernel s hs (p.1-p.2))
    (periodicRiesz_density_pair_integrable s hs ρ M hρM) A hA z)

theorem periodicRiesz_density_average_matrix_posSemidef (s : ℝ)
    (hs : 2 * s < (Fintype.card ι : ℝ)) (hs0 : 0 < s)
    (ρ : PeriodicTorus ι → ℝ) (hρm : Measurable ρ)
    (hρ0 : ∀ᵐ x ∂periodicHaar ι, 0 ≤ ρ x)
    [IsProbabilityMeasure (periodicCappedDensityMeasure ρ)]
    (M : ℝ) (hM : 0 ≤ M) (hρM : ∀ᵐ x ∂periodicHaar ι, ρ x ≤ M)
    {α : Type*} [Fintype α] (A : α → Set (PeriodicTorus ι))
    (hA : ∀ i, MeasurableSet (A i)) :
    Matrix.PosSemidef (fun i j => sharpnessAtomAverage (periodicCappedDensityMeasure ρ)
      (fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs (p.1-p.2))
      (A i) (A j)) := by
  let μ := periodicCappedDensityMeasure ρ
  let H := fun p : PeriodicTorus ι × PeriodicTorus ι => periodicRieszKernel s hs (p.1-p.2)
  let Q : Matrix α α ℝ := fun i j => sharpnessAtomAverage μ H (A i) (A j)
  have hHs : ∀ p, H p.swap = H p := by
    rintro ⟨x,y⟩
    simpa only [H,Prod.swap,neg_sub] using periodicRieszKernel_even s hs (x-y)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · change Q.conjTranspose = Q
    ext i j
    simp only [Matrix.conjTranspose_apply,star_trivial]
    exact sharpness_atom_average_symmetric μ H hHs (A j) (A i)
  · intro x
    have hn := periodicRiesz_density_finite_atom_form_nonneg s hs hs0 ρ hρm hρ0 M hM hρM
      A hA (fun i => x i / (μ (A i)).toReal)
    have he (i j : α) :
        (x i / (μ (A i)).toReal) * (x j / (μ (A j)).toReal) * sharpnessAtomIntegral μ H (A i) (A j) =
          x i * (Q i j * x j) := by
      dsimp [Q,sharpnessAtomAverage]
      simp only [div_eq_mul_inv,_root_.mul_inv_rev]
      ring
    simp only [dotProduct,Matrix.mulVec,Pi.star_apply,star_trivial,Finset.mul_sum]
    exact hn.trans_eq (Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => he i j)))

end DGRHS.Periodic
