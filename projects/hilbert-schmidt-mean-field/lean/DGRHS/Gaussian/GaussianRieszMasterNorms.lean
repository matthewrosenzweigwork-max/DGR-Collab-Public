import DGRHS.Gaussian.GaussianRieszMasterBand
import DGRHS.Concentration.MasterExponential

/-! One fixed actual physical band scale supplies all three master norm fields,
uniformly in the lower cutoff. No concentration or moment bound is assumed. -/
noncomputable section
open MeasureTheory Real
open scoped ENNReal
namespace DGRHS.Gaussian
open DGRHS.Concentration
variable {ι : Type*} [Fintype ι]

lemma exists_gaussianRieszMaster_scale (s β M : ℝ) (hM : 0 ≤ M)
    (ha : 0 < (Fintype.card ι : ℝ)/2-s) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      16*(2*β)^2*gaussianRieszBandRowControl s δ M ι < 1/glzUniversalTailConstant ∧
      4*|2*β| *Real.sqrt (gaussianRieszBandRowControl s δ M ι) < 1/glzUniversalTailConstant := by
  exact exists_gaussianRieszBand_small_scale s (2*β) M (1/glzUniversalTailConstant)
    hM ha (by positivity [glzUniversalTailConstant_pos])

lemma gaussianRieszMasterBand_norm_fields (s α δ β : ℝ) (hs : 0 < s)
    (hα : 0 < α) (hαδ : α ≤ δ) (ha : 0 < (Fintype.card ι : ℝ)/2-s)
    (ρ : EuclideanSpace ℝ ι → ℝ) (M : ℝ) (hM : 0 ≤ M)
    [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)] (hρ : ∀ᵐ x ∂volume, ρ x ≤ M)
    (hrow : 16*(2*β)^2*gaussianRieszBandRowControl s δ M ι ≤ 1/glzUniversalTailConstant)
    (hop : 4*|2*β| *Real.sqrt (gaussianRieszBandRowControl s δ M ι) ≤ 1/glzUniversalTailConstant) :
    (∀ᵐ x ∂gaussianRieszDensityMeasure ρ,
      (∫ y, (gaussianRieszMasterBand s α δ (2*β) ρ (x,y))^2
        ∂gaussianRieszDensityMeasure ρ) ≤ 1/glzUniversalTailConstant) ∧
    ((∫ p, (gaussianRieszMasterBand s α δ (2*β) ρ p)^2
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) ≤ 1/glzUniversalTailConstant) ∧
    ‖DGRHS.Kernel.integralOperator (gaussianRieszMasterBand s α δ (2*β) ρ)
      ((memLp_infty_gaussianRieszMasterBand s α δ (2*β) hs hα hαδ ha ρ M hM hρ).mono_exponent
        (show (2 : ℝ≥0∞) ≤ ∞ from le_top))‖ ≤ 1/glzUniversalTailConstant := by
  obtain ⟨hr,hj⟩ := gaussianRieszScaledCenteredBand_square_controls s α δ (2*β) hs hα hαδ ha ρ M hM hρ
  refine ⟨?_,hj.trans hrow,?_⟩
  · filter_upwards [hr] with x hx
    exact hx.trans hrow
  · exact (norm_gaussianRieszScaledCenteredBand_operator_le s α δ (2*β) hs hα hαδ ha ρ M hM hρ).trans hop

end DGRHS.Gaussian

#check DGRHS.Gaussian.exists_gaussianRieszMaster_scale
#print axioms DGRHS.Gaussian.exists_gaussianRieszMaster_scale
#check DGRHS.Gaussian.gaussianRieszMasterBand_norm_fields
#print axioms DGRHS.Gaussian.gaussianRieszMasterBand_norm_fields
