import DGRHS.Gaussian.GaussianRieszCutoffMoment

/-! The actual uniform cutoff moment extends to every positive regularization:
above the small scale, the SAME Fourier Gram feature gives a deterministic
particle cap. No extra scale restriction is imposed on the final endpoint. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma gaussianRieszCutoff_large_scale_exponential (s η δ β : ℝ) (hs : 0 < s)
    (hδ : 0 < δ) (hδη : δ ≤ η) (hβ : 0 ≤ β)
    (μ : Measure (EuclideanSpace ℝ ι)) [IsProbabilityMeasure μ] (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun ω => Real.exp (β*iidNegativeStatistic n
      (hoeffdingCentered μ (gaussianRieszTruncatedPair s η)) ω)) (Measure.pi (fun _ : Fin n => μ)) ∧
    (∫ ω,Real.exp (β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianRieszTruncatedPair s η)) ω)
      ∂Measure.pi (fun _ : Fin n => μ)) ≤ Real.exp (2*β*(gaussianRieszSourceCoefficient s/s*δ^(-s))) := by
  let particleLaw := Measure.pi (fun _ : Fin n => μ)
  let C := Real.exp (2*β*(gaussianRieszSourceCoefficient s/s*δ^(-s)))
  have hη := lt_of_lt_of_le hδ hδη
  have hc : 0 ≤ gaussianRieszSourceCoefficient s/s := div_nonneg (gaussianRieszSourceCoefficient_pos s hs).le hs.le
  have hp := Real.rpow_le_rpow_of_nonpos hδ hδη (by linarith : -s ≤ 0)
  have hb (ω : Fin n → EuclideanSpace ℝ ι) :
      β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianRieszTruncatedPair s η)) ω ≤
      2*β*(gaussianRieszSourceCoefficient s/s*δ^(-s)) := by
    have h1 := mul_le_mul_of_nonneg_left (gaussianRieszCenteredTruncated_particle_cap s η hs hη μ n hn ω) hβ
    have h2 := mul_le_mul_of_nonneg_left hp (mul_nonneg (by positivity : 0 ≤ 2*β) hc)
    nlinarith only [h1,h2]
  have he (ω : Fin n → EuclideanSpace ℝ ι) :
      Real.exp (β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianRieszTruncatedPair s η)) ω) ≤ C :=
    Real.exp_le_exp.mpr (hb ω)
  have hi : Integrable (fun ω => Real.exp (β*iidNegativeStatistic n
      (hoeffdingCentered μ (gaussianRieszTruncatedPair s η)) ω)) particleLaw := by
    apply (integrable_const C).mono'
      ((measurable_gaussianRieszCutoff_exponent s η β hs hη μ n).exp.aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun ω => by rw [Real.norm_of_nonneg (Real.exp_pos _).le];exact he ω)
  refine ⟨hi,?_⟩
  have hh := integral_mono hi (integrable_const C) he
  simpa only [integral_const,probReal_univ,one_smul] using hh

theorem gaussianRieszCutoff_uniform_exponential (s β : ℝ) (hs : 0 < s) (hβ : 0 ≤ β)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M) :
    ∃ C : ℝ, ∀ η : ℝ, 0 < η → ∀ n : ℕ, 1 ≤ n →
      Integrable (fun ω => Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszTruncatedPair s η)) ω))
          (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω, Real.exp (β*iidNegativeStatistic n
        (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianRieszTruncatedPair s η)) ω)
          ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ≤ C := by
  obtain ⟨δ,hδ,hδ1,C,hC⟩ := gaussianRieszCutoff_uniform_small_scale_exponential s β hs hβ ha ρ M hM hρ
  refine ⟨max C (Real.exp (2*β*(gaussianRieszSourceCoefficient s/s*δ^(-s)))),?_⟩
  intro η hη n hn
  by_cases hηδ : η ≤ δ
  · obtain ⟨hi,hb⟩ := hC η hη hηδ n hn
    exact ⟨hi,hb.trans (le_max_left _ _)⟩
  · obtain ⟨hi,hb⟩ := gaussianRieszCutoff_large_scale_exponential s η δ β hs hδ (le_of_not_ge hηδ) hβ
      (gaussianRieszDensityMeasure ρ) n hn
    exact ⟨hi,hb.trans (le_max_right _ _)⟩

end DGRHS.Gaussian

#check DGRHS.Gaussian.gaussianRieszCutoff_large_scale_exponential
#print axioms DGRHS.Gaussian.gaussianRieszCutoff_large_scale_exponential

#check DGRHS.Gaussian.gaussianRieszCutoff_uniform_exponential
#print axioms DGRHS.Gaussian.gaussianRieszCutoff_uniform_exponential
