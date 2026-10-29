import DGRHS.Gaussian.GaussianLogCutoffIdentification
import DGRHS.Gaussian.GaussianLogCanonicalMoment

/-! Supporting development. Every-x SAME-cutoff potential lower bound and proper exponential
one-body tail, uniformly for eta<=1 under the original full potential tail. -/
noncomputable section
open MeasureTheory Real Filter
namespace DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma gaussianLogShort_potential_le_one (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    (x : EuclideanSpace ℝ ι) :
    (∫ y,gaussianLogShortPair η (x,y) ∂gaussianRieszDensityMeasure ρ) ≤ gaussianLogShortConstant M ι := by
  have hs := gaussianLogShortRange_convolution_le η hη hd ρ M hM hρ x
  change (∫ y,gaussianLogShortPair η (x,y) ∂gaussianRieszDensityMeasure ρ) ≤ _ at hs
  have hp : η^(Fintype.card ι : ℝ) ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hη.le hη1 hd.le
  have hC : 0 ≤ M*((2*Real.pi)^((Fintype.card ι : ℝ)/2)/(Fintype.card ι : ℝ)) := by positivity
  have hb := mul_le_mul_of_nonneg_left hp hC
  unfold gaussianLogShortConstant
  exact hs.trans (by nlinarith only [hb])

lemma gaussianLogCutoff_pairMean_le_full (η : ℝ) (hη : 0 < η)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))) :
    (∫ p,gaussianLogTruncatedPair η p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ≤
    (∫ p,logPhysicalPair p ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  rw [gaussianLogTruncated_pairMean_eq η hη hd ρ M hM hρ hpair]
  have hn : 0 ≤ ∫ p,gaussianLogShortPair η p
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ) :=
    integral_nonneg (fun p => gaussianLogShortRange_nonneg η _)
  linarith

lemma gaussianLogCutoff_potential_uniform_exponential_tail (c : ℝ) (hc : 0 ≤ c)
    (hd : 0 < (Fintype.card ι : ℝ)) (ρ : EuclideanSpace ℝ ι → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hρ : ∀ᵐ x ∂volume,ρ x ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hpair : Integrable logPhysicalPair
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)))
    (he : Integrable (fun x => Real.exp (-c*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x))
      (gaussianRieszDensityMeasure ρ)) (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    Integrable (fun x => Real.exp (-c*(∫ y,gaussianLogTruncatedPair η (x,y) ∂gaussianRieszDensityMeasure ρ)))
      (gaussianRieszDensityMeasure ρ) ∧
    (∫ x,Real.exp (-c*(∫ y,gaussianLogTruncatedPair η (x,y) ∂gaussianRieszDensityMeasure ρ))
      ∂gaussianRieszDensityMeasure ρ) ≤
      Real.exp (c*gaussianLogShortConstant M ι)*
        (∫ x,Real.exp (-c*logPhysicalPotential (gaussianRieszDensityMeasure ρ) x) ∂gaussianRieszDensityMeasure ρ) := by
  let μ := gaussianRieszDensityMeasure ρ
  let F := fun x => ∫ y,gaussianLogTruncatedPair η (x,y) ∂μ
  let G := fun x => Real.exp (c*gaussianLogShortConstant M ι)*Real.exp (-c*logPhysicalPotential μ x)
  have hF : Integrable F μ := (integrable_gaussianLogTruncatedPair_source η hη hd ρ M hM hρ hpair).integral_prod_left
  have hG : Integrable G μ := he.const_mul _
  have hb (x : EuclideanSpace ℝ ι) : Real.exp (-c*F x) ≤ G x := by
    dsimp only [G]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    dsimp [F]
    rw [gaussianLogTruncated_potential_eq η hη hd ρ M hM hρ hpair x]
    have hs := gaussianLogShort_potential_le_one η hη hη1 hd ρ M hM hρ x
    have hh := mul_le_mul_of_nonneg_left hs hc
    nlinarith only [hh]
  have hi : Integrable (fun x => Real.exp (-c*F x)) μ := by
    apply hG.mono' (Real.continuous_exp.comp_aestronglyMeasurable (hF.aestronglyMeasurable.const_mul (-c)))
    exact Eventually.of_forall (fun x => by
      change ‖Real.exp (-c*F x)‖ ≤ G x
      rw [Real.norm_of_nonneg (Real.exp_pos _).le];exact hb x)
  refine ⟨hi,?_⟩
  exact (integral_mono hi hG hb).trans_eq (integral_const_mul _ _)

end DGRHS.Gaussian

#check @DGRHS.Gaussian.gaussianLogShort_potential_le_one
#print axioms DGRHS.Gaussian.gaussianLogShort_potential_le_one
#check @DGRHS.Gaussian.gaussianLogCutoff_pairMean_le_full
#print axioms DGRHS.Gaussian.gaussianLogCutoff_pairMean_le_full
#check @DGRHS.Gaussian.gaussianLogCutoff_potential_uniform_exponential_tail
#print axioms DGRHS.Gaussian.gaussianLogCutoff_potential_uniform_exponential_tail
