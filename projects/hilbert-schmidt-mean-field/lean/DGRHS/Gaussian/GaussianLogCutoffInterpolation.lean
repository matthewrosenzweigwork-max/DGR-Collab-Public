import DGRHS.Gaussian.GaussianLogCutoffCanonicalMoment
import DGRHS.Gaussian.GaussianRieszInterpolatedMoment

/-! Supporting development. Actual logarithmic cutoff-plus-short interpolation;
uniform proper canonical moments from the two derived physical endpoints. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration

variable {ι : Type*} [Fintype ι]

def gaussianLogInterpolatedPair (η t : ℝ) : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ :=
  gaussianLogTruncatedPair η+t • gaussianLogShortPair η

lemma ae_gaussianLogInterpolated_exponent (η β t : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) (n : ℕ) :
    (fun ω => β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
      (gaussianLogInterpolatedPair η t)) ω) =ᵐ[Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)]
      (fun ω => (1-t)*(β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (gaussianLogTruncatedPair η)) ω) +
        t*(β*iidNegativeStatistic n (hoeffdingCentered (gaussianRieszDensityMeasure ρ)
        (logPhysicalPair)) ω)) := by
  let μ := gaussianRieszDensityMeasure ρ
  let W := gaussianLogTruncatedPair (ι := ι) η
  let V := logPhysicalPair (E := EuclideanSpace ℝ ι)
  have hW : Integrable W (μ.prod μ) := integrable_gaussianLogTruncatedPair_source η hη hd ρ M hM hρ hpair
  have hV : Integrable V (μ.prod μ) := hpair
  have he : gaussianLogInterpolatedPair η t =ᵐ[μ.prod μ] (1-t) • W+t • V := by
    exact Filter.Eventually.of_forall (fun p => by
      simp only [gaussianLogInterpolatedPair,gaussianLogTruncatedPair,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      dsimp only [W,V,gaussianLogTruncatedPair]
      ring)
  have hc := ae_hoeffdingCentered_congr μ _ _ he
  have haC := ae_hoeffdingCentered_add μ ((1-t) • W) (t • V) (hW.smul (1-t)) (hV.smul t)
  have hcenter : hoeffdingCentered μ (gaussianLogInterpolatedPair η t) =ᵐ[μ.prod μ]
      (1-t) • hoeffdingCentered μ W+t • hoeffdingCentered μ V := by
    filter_upwards [hc,haC] with p hp1 hp2
    rw [hp1,hp2,hoeffdingCentered_const_smul,hoeffdingCentered_const_smul]
  have hstat := ae_physical_iidNegativeStatistic_congr μ n _ _ hcenter
  filter_upwards [hstat] with ω hω
  rw [hω,physical_iidNegativeStatistic_add,physical_iidNegativeStatistic_const_smul,
    physical_iidNegativeStatistic_const_smul]
  ring

theorem gaussianLogInterpolated_uniform_exponential (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hpair : Integrable logPhysicalPair ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (htail : Integrable (fun x => Real.exp (-2*β*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) :
    ∃ C : ℝ, ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ n : ℕ, 1 ≤ n → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      Integrable (fun ω => Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogInterpolatedPair η t)) ω))
          (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogInterpolatedPair η t)) ω)
          ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ≤ C := by
  let μ := gaussianRieszDensityMeasure ρ
  obtain ⟨C₀,hC₀⟩ := gaussianLogCutoffCanonical_uniform_exponential β hβ hd ρ M hM hρ hpair htail
  obtain ⟨C₁,hC₁⟩ := logPhysicalCanonical_uniform_exponential β hβ hd ρ M hM hρ hpair htail
  refine ⟨max C₀ C₁,?_⟩
  intro η hη hη1 n hn t ht
  let X := fun ω => β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogTruncatedPair η)) ω
  let Y := fun ω => β*iidNegativeStatistic n (hoeffdingCentered μ (logPhysicalPair)) ω
  have hX : AEMeasurable X (Measure.pi (fun _ : Fin n => μ)) :=
    ((measurable_physical_iidNegativeStatistic n _ (stronglyMeasurable_hoeffdingCentered μ _
      (stronglyMeasurable_logPhysicalPair.sub (stronglyMeasurable_gaussianLogShortPair η hη hd))).measurable).const_mul β).aemeasurable
  have hY : AEMeasurable Y (Measure.pi (fun _ : Fin n => μ)) :=
    ((measurable_physical_iidNegativeStatistic n _ (stronglyMeasurable_hoeffdingCentered μ _
      (stronglyMeasurable_logPhysicalPair)).measurable).const_mul β).aemeasurable
  obtain ⟨hi,hb⟩ := interpolated_exp_integral (Measure.pi (fun _ : Fin n => μ)) X Y hX hY
    (hC₀ η hη hη1 n hn).1 (hC₁ n hn).1 t ht.1 ht.2
  have he : (fun ω => Real.exp (β*iidNegativeStatistic n (hoeffdingCentered μ
      (gaussianLogInterpolatedPair η t)) ω)) =ᵐ[Measure.pi (fun _ : Fin n => μ)]
      (fun ω => Real.exp ((1-t)*X ω+t*Y ω)) := (ae_gaussianLogInterpolated_exponent η β t hη hd ρ M hM hρ hpair n).mono
    (fun ω h => congrArg Real.exp h)
  refine ⟨hi.congr he.symm,?_⟩
  rw [integral_congr_ae he]
  refine hb.trans ?_
  calc
    _ ≤ (1-t)*max C₀ C₁+t*max C₀ C₁ :=
      add_le_add (mul_le_mul_of_nonneg_left ((hC₀ η hη hη1 n hn).2.trans (le_max_left _ _)) (by linarith [ht.2]))
        (mul_le_mul_of_nonneg_left ((hC₁ n hn).2.trans (le_max_right _ _)) ht.1)
    _ = _ := by ring

end DGRHS.Gaussian
#check @DGRHS.Gaussian.gaussianLogInterpolatedPair
#print axioms DGRHS.Gaussian.gaussianLogInterpolatedPair
#check @DGRHS.Gaussian.ae_gaussianLogInterpolated_exponent
#print axioms DGRHS.Gaussian.ae_gaussianLogInterpolated_exponent
#check @DGRHS.Gaussian.gaussianLogInterpolated_uniform_exponential
#print axioms DGRHS.Gaussian.gaussianLogInterpolated_uniform_exponential
