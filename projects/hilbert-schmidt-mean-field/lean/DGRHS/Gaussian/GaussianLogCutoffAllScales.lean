import DGRHS.Gaussian.GaussianLogCutoffSourceMoment

/-! Supporting development. Exact finite Gram cancellation covers larger cutoffs;
the actual master factory covers smaller ones, with one common proper source moment. -/
noncomputable section
open MeasureTheory Real
open scoped BigOperators
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma gaussianLogCutoffApproxExponent_gram_cap (μ : Measure (EuclideanSpace ℝ ι))
    [IsProbabilityMeasure μ] (β η T : ℝ) (hβ : 0 ≤ β) (hη : 0 < η)
    (hηT : η ≤ T) (hT : 1 ≤ T) (n : ℕ) (hn : 1 ≤ n) (ω : Fin n → EuclideanSpace ℝ ι) :
    gaussianLogCutoffApproxExponent μ β η T n ω ≤ β/2*(-Real.log η+1/4) := by
  classical
  have hn' : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hcap := gaussianLogCenteredBand_particle_diagonal_cap η T hη hηT μ n hn ω
  have hcap' := (le_div_iff₀ (by positivity : 0 < 2*(n : ℝ))).mp hcap
  have hs : (∑ i : Fin n,‖centeredGaussianLogBandFeature η T hη μ (ω i)‖^2) =
      (n : ℝ)*Real.log (T/η)-2*(∑ i : Fin n,∫ y,gaussianLogBandPair η T (ω i,y) ∂μ) +
      (n : ℝ)*(∫ p,gaussianLogBandPair η T p ∂μ.prod μ) := by
    simp_rw [norm_sq_centeredGaussianLogBandFeature_eq η T hη hηT μ,
      Finset.sum_add_distrib,Finset.sum_sub_distrib,← Finset.mul_sum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  rw [hs] at hcap'
  have hb := mul_le_mul_of_nonneg_left hcap' hβ
  have hc := mul_le_mul_of_nonneg_left (gaussianLogCounterterm_low_scale_bound η T hη hT)
    (show 0 ≤ (n : ℝ)*β by positivity)
  have he : (n : ℝ)*gaussianLogCutoffApproxExponent μ β η T n ω =
      (n : ℝ)*β*iidNegativeStatistic n (hoeffdingCentered μ (gaussianLogBandPair η T)) ω +
      β*(∑ i : Fin n,∫ y,gaussianLogBandPair η T (ω i,y) ∂μ) -
      (n : ℝ)*β/2*(∫ p,gaussianLogBandPair η T p ∂μ.prod μ) -
      (n : ℝ)*β/2*gaussianLogCounterterm T := by
    unfold gaussianLogCutoffApproxExponent
    field_simp
  have hh : (n : ℝ)*gaussianLogCutoffApproxExponent μ β η T n ω ≤
      (n : ℝ)*(β/2*(-Real.log η+1/4)) := by
    rw [he]
    nlinarith only [hb,hc]
  exact (mul_le_mul_iff_right₀ hn').mp (by simpa only [mul_comm] using hh)

theorem gaussianLogCutoffSource_all_finiteIR_uniform_exponential (β : ℝ) (hβ : 0 ≤ β)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] :
    ∃ C : ℝ,∀ η : ℝ,0 < η → η ≤ 1 → ∀ T : ℝ,1 ≤ T → ∀ n : ℕ,1 ≤ n →
      Integrable (fun ω => Real.exp (gaussianLogCutoffApproxExponent (gaussianRieszDensityMeasure ρ) β η T n ω))
        (Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ∧
      (∫ ω,Real.exp (gaussianLogCutoffApproxExponent (gaussianRieszDensityMeasure ρ) β η T n ω)
        ∂Measure.pi (fun _ : Fin n => gaussianRieszDensityMeasure ρ)) ≤ C := by
  let μ := gaussianRieszDensityMeasure ρ
  obtain ⟨δ,hδ,hδ1,C,hC⟩ := gaussianLogCutoffSource_finiteIR_uniform_exponential β hβ hd ρ M hM hρ
  let K := Real.exp (β/2*(-Real.log δ+1/4))
  refine ⟨max C K,?_⟩
  intro η hη hη1 T hT n hn
  by_cases hsmall : η ≤ δ
  · obtain ⟨hi,hb⟩ := hC η hη hsmall T hT n hn
    exact ⟨hi,hb.trans (le_max_left _ _)⟩
  · have hδeta : δ ≤ η := (le_of_not_ge hsmall)
    have hlog : Real.log δ ≤ Real.log η := Real.log_le_log hδ hδeta
    have hb (ω : Fin n → EuclideanSpace ℝ ι) : Real.exp (gaussianLogCutoffApproxExponent μ β η T n ω) ≤ K := by
      apply Real.exp_le_exp.mpr
      exact (gaussianLogCutoffApproxExponent_gram_cap μ β η T hβ hη (hη1.trans hT) hT n hn ω).trans
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity : 0 ≤ β/2))
    have hi : Integrable (fun ω : Fin n → EuclideanSpace ℝ ι =>
        Real.exp (gaussianLogCutoffApproxExponent μ β η T n ω)) (Measure.pi (fun _ : Fin n => μ)) := by
      apply (integrable_const K).mono'
        (Real.measurable_exp.comp (measurable_gaussianLogCutoffApproxExponent μ β η T hη n)).aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun ω => by
        dsimp only [Function.comp_def]
        rw [Real.norm_of_nonneg (Real.exp_pos _).le];exact hb ω)
    refine ⟨hi,?_⟩
    have hz := integral_mono hi (integrable_const K) hb
    have hK : (∫ _ : Fin n → EuclideanSpace ℝ ι,K ∂Measure.pi (fun _ : Fin n => μ)) = K := by simp
    exact (hz.trans_eq hK).trans (le_max_right _ _)

end DGRHS.Gaussian
#check @DGRHS.Gaussian.gaussianLogCutoffApproxExponent_gram_cap
#print axioms DGRHS.Gaussian.gaussianLogCutoffApproxExponent_gram_cap
#check @DGRHS.Gaussian.gaussianLogCutoffSource_all_finiteIR_uniform_exponential
#print axioms DGRHS.Gaussian.gaussianLogCutoffSource_all_finiteIR_uniform_exponential
