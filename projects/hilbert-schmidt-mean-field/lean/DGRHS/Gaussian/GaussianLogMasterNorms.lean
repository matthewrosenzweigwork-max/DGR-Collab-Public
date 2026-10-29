import DGRHS.Gaussian.GaussianLogMasterBand
import DGRHS.Concentration.MasterExponential

/-! One fixed actual physical band scale supplies all three master norm fields,
uniformly in the lower cutoff. No concentration or moment bound is assumed. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma exists_gaussianLogMaster_scale (β M : ℝ) (hM : 0 ≤ M)
    (hd : 0 < (Fintype.card ι : ℝ)) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      16*(2*β)^2*gaussianLogBandRowControl δ M ι < 1/glzUniversalTailConstant ∧
      4*|2*β| *Real.sqrt (gaussianLogBandRowControl δ M ι) < 1/glzUniversalTailConstant := by
  exact exists_gaussianLogBand_small_scale (2*β) M (1/glzUniversalTailConstant)
    hM hd (by positivity [glzUniversalTailConstant_pos])

lemma gaussianLogMasterBand_norm_fields (α δ β : ℝ)
    (hα : 0 < α) (hαδ : α ≤ δ) (hd : 0 < (Fintype.card ι : ℝ))
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hrow : 16*(2*β)^2*gaussianLogBandRowControl δ M ι ≤ 1/glzUniversalTailConstant)
    (hop : 4*|2*β| *Real.sqrt (gaussianLogBandRowControl δ M ι) ≤ 1/glzUniversalTailConstant) :
    (∀ᵐ x ∂gaussianRieszDensityMeasure ρ,
      (∫ y, (gaussianLogMasterBand α δ (2*β) (gaussianRieszDensityMeasure ρ) (x,y))^2
        ∂gaussianRieszDensityMeasure ρ) ≤ 1/glzUniversalTailConstant) ∧
    ((∫ p, (gaussianLogMasterBand α δ (2*β) (gaussianRieszDensityMeasure ρ) p)^2
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ≤ 1/glzUniversalTailConstant) ∧
    ‖DGRHS.Kernel.integralOperator (gaussianLogMasterBand α δ (2*β) (gaussianRieszDensityMeasure ρ))
      ((memLp_infty_gaussianLogMasterBand α δ (2*β) hα hαδ (gaussianRieszDensityMeasure ρ)).mono_exponent
        (show (2 : ℝ≥0∞) ≤ ∞ from le_top))‖ ≤ 1/glzUniversalTailConstant := by
  obtain ⟨hr,hj⟩ := gaussianLogScaledCenteredBand_square_controls α δ (2*β) hα hαδ hd ρ M hM hρ
  refine ⟨?_,hj.trans hrow,?_⟩
  · filter_upwards [hr] with x hx
    exact hx.trans hrow
  · exact (norm_gaussianLogScaledCenteredBand_operator_le α δ (2*β) hα hαδ hd ρ M hM hρ).trans hop

end DGRHS.Gaussian

#check DGRHS.Gaussian.exists_gaussianLogMaster_scale
#print axioms DGRHS.Gaussian.exists_gaussianLogMaster_scale
#check DGRHS.Gaussian.gaussianLogMasterBand_norm_fields
#print axioms DGRHS.Gaussian.gaussianLogMasterBand_norm_fields
