import DGRHS.Gaussian.SharpnessAtomDiagonal
import DGRHS.Gaussian.SharpnessPositiveForm

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

/-- Proper pair averages over actual atoms. The bound uses the actual atom
mass, not a supplied favorable compression-diagonal estimate. -/
theorem sharpness_centered_atom_pair_bound (s δ : ℝ) (hs : 0 < s) (hδ : 0 < δ)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (A : Set (EuclideanSpace ℝ ι)) :
    Integrable (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s))
      (((gaussianRieszDensityMeasure ρ).restrict A).prod ((gaussianRieszDensityMeasure ρ).restrict A)) ∧
    (∫ p, hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) p
      ∂((gaussianRieszDensityMeasure ρ).restrict A).prod ((gaussianRieszDensityMeasure ρ).restrict A)) ≤
      (gaussianRieszDensityMeasure ρ A).toReal *
        (M * (gaussianRieszSourceCoefficient s * (2*Real.pi)^((Fintype.card ι : ℝ)/2) /
          ((Fintype.card ι : ℝ)-s) * δ^((Fintype.card ι : ℝ)-s))) +
      (gaussianRieszSourceCoefficient s/s * δ^(-s) + gaussianRieszPhysicalPotentialConstant s M ι) *
        (gaussianRieszDensityMeasure ρ A).toReal^2 := by
  let μ := gaussianRieszDensityMeasure ρ
  let ν := μ.restrict A
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let B := gaussianRieszPhysicalPotentialConstant s M ι
  let S := M * (gaussianRieszSourceCoefficient s * (2*Real.pi)^((Fintype.card ι : ℝ)/2) /
    ((Fintype.card ι : ℝ)-s) * δ^((Fintype.card ι : ℝ)-s))
  let D := gaussianRieszSourceCoefficient s/s * δ^(-s)
  have hiH : Integrable H (ν.prod ν) := by
    rw [show ν.prod ν = (μ.prod μ).restrict (A ×ˢ A) from Measure.prod_restrict A A]
    exact (sharpness_centered_riesz_integrable s hs ha ρ M hM hρ).restrict
  have hiW : Integrable (gaussianRieszPhysicalPair s) (ν.prod ν) := by
    rw [show ν.prod ν = (μ.prod μ).restrict (A ×ˢ A) from Measure.prod_restrict A A]
    exact (sharpness_riesz_pair_integrable s hs ha ρ M hM hρ).restrict
  refine ⟨hiH, ?_⟩
  have hm := sharpness_riesz_pair_mean_bound s hs ha ρ M hM hρ
  have hp : ∀ p, H p ≤ gaussianRieszPhysicalPair s p + B := by
    intro p
    have h1 := (sharpness_riesz_potential_bound s hs ha ρ M hM hρ p.1).2.1
    have h2 := (sharpness_riesz_potential_bound s hs ha ρ M hM hρ p.2).2.1
    change gaussianRieszPhysicalPair s p - DGRHS.potential μ _ p.1 -
      DGRHS.secondPotential μ _ p.2 + _ ≤ _
    rw [DGRHS.secondPotential_eq_potential μ _ (sharpness_riesz_pair_symmetric s)]
    dsimp [DGRHS.potential, μ, B] at *
    linarith [hm.2]
  have hW : (∫ p, gaussianRieszPhysicalPair s p ∂ν.prod ν) ≤ (μ A).toReal*(S+D*(μ A).toReal) := by
    rw [integral_prod _ hiW]
    calc
      _ ≤ ∫ _ : EuclideanSpace ℝ ι, S+D*(μ A).toReal ∂ν :=
        integral_mono_ae hiW.integral_prod_left (integrable_const _)
          (Eventually.of_forall fun x => (sharpness_riesz_atom_row_bound s δ hs hδ ha ρ M hM hρ A x).2)
      _ = _ := by simp [ν, Measure.real]
  calc
    _ ≤ ∫ p, gaussianRieszPhysicalPair s p+B ∂ν.prod ν :=
      integral_mono_ae hiH (hiW.add (integrable_const _)) (Eventually.of_forall hp)
    _ = (∫ p, gaussianRieszPhysicalPair s p ∂ν.prod ν)+B*(μ A).toReal^2 := by
      rw [integral_add hiW (integrable_const _)]
      have hmass : (ν.prod ν) univ = μ A * μ A := by
        rw [← Set.univ_prod_univ, Measure.prod_prod]
        simp [ν]
      rw [integral_const, show (ν.prod ν).real univ = (μ A).toReal * (μ A).toReal by
        rw [Measure.real, hmass, ENNReal.toReal_mul]]
      simp only [smul_eq_mul, pow_two]
      ring
    _ ≤ _ := by dsimp [S, D, B] at *; nlinarith [hW]

/-- Positivity of each actual compression diagonal is inherited from the
proved full singular form on the indicator of the atom. -/
theorem sharpness_centered_atom_pair_nonneg (s : ℝ) (hs : 0 < s)
    (ha : 0 < (Fintype.card ι : ℝ)-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) (A : Set (EuclideanSpace ℝ ι)) (hA : MeasurableSet A) :
    0 ≤ (∫ p, hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszPhysicalPair s) p
      ∂((gaussianRieszDensityMeasure ρ).restrict A).prod ((gaussianRieszDensityMeasure ρ).restrict A)) := by
  let μ := gaussianRieszDensityMeasure ρ
  let H := hoeffdingCentered μ (gaussianRieszPhysicalPair s)
  let f := A.indicator (fun _ => (1 : ℝ))
  have hf : StronglyMeasurable f := stronglyMeasurable_const.indicator hA
  have hb (x : EuclideanSpace ℝ ι) : ‖f x‖ ≤ 1 := by
    dsimp [f]
    by_cases hx : x ∈ A <;> simp [hx]
  have hn := (sharpness_centered_riesz_bounded_form_nonneg s hs ha ρ M hM hρ f hf 1 (by norm_num) hb).2
  rw [Measure.prod_restrict, ← integral_indicator (hA.prod hA)]
  convert hn using 1
  congr 1
  funext p
  dsimp [f]
  by_cases h1 : p.1 ∈ A <;> by_cases h2 : p.2 ∈ A <;> simp [h1, h2]

end DGRHS.Gaussian
#print axioms DGRHS.Gaussian.sharpness_centered_atom_pair_bound
#print axioms DGRHS.Gaussian.sharpness_centered_atom_pair_nonneg
#check @DGRHS.Gaussian.sharpness_centered_atom_pair_bound
