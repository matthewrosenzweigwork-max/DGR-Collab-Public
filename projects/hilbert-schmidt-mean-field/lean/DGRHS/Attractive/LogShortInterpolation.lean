/- Actual logarithmic short-range interpolation, source 2774--2835.
Every-row factorial bounds use the algebraic representative, retaining the
proper every-row quantifier rather than transferring product-AE linearity. -/
import DGRHS.Gaussian.SingularLogIntegrability
import DGRHS.Gaussian.GaussianLogShortRangeFactorial
import DGRHS.Gaussian.GaussianLogShortRangeSource
import DGRHS.Attractive.CenteredRowFactorial
import DGRHS.Attractive.SourceOperatorBound
import DGRHS.Attractive.SourceMomentThreshold
noncomputable section
open MeasureTheory
namespace DGRHS.Attractive
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι]

lemma RowFactorialMoments.neg {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {h : Ω×Ω→ℝ} {C : ℝ}
    (hC : RowFactorialMoments μ h C) : RowFactorialMoments μ (-h) C := by
  refine ⟨hC.nonneg,?_,?_⟩
  · intro p hp y
    simpa only [Pi.neg_apply,abs_neg] using hC.proper p hp y
  · intro p hp y
    simpa only [Pi.neg_apply,abs_neg] using hC.bound p hp y

lemma gaussianLogShortPair_symmetric (η : ℝ) (x y : EuclideanSpace ℝ ι) :
    gaussianLogShortPair η (x,y)=gaussianLogShortPair η (y,x) := by
  unfold gaussianLogShortPair gaussianLogShortRange
  rw [norm_sub_rev]

theorem gaussianLogShort_centered_factorial_rows (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M) :
    RowFactorialMoments (gaussianRieszDensityMeasure ρ)
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) (gaussianLogShortPair η))
      (12*gaussianLogShortFactorialConstant M (Fintype.card ι:ℝ)) := by
  exact nonneg_centered_rowFactorial _ _
    (stronglyMeasurable_gaussianLogShortPair η hη hd).measurable
    (fun z=>gaussianLogShortRange_nonneg η (z.1-z.2))
    (gaussianLogShortPair_symmetric η) _
    (gaussianLogShortRange_factorial_rows η hη hη1 hd ρ M hM hρ)

def gaussianLogInterpolationRowConstant (C M d : ℝ) : ℝ :=
  4*(C+12*gaussianLogShortFactorialConstant M d)

def gaussianLogAlgebraicInterpolation (μ : Measure (EuclideanSpace ℝ ι))
    (η t : ℝ) (z : EuclideanSpace ℝ ι×EuclideanSpace ℝ ι) : ℝ :=
  hoeffdingCentered μ logPhysicalPair z-(1-t)*hoeffdingCentered μ (gaussianLogShortPair η) z

theorem gaussianLog_interpolated_factorial_rows (η t : ℝ)
    (hη : 0<η) (hη1 : η≤1) (ht : 0≤t) (ht1 : t≤1)
    (hd : 0<(Fintype.card ι:ℝ)) (ρ : EuclideanSpace ℝ ι→ℝ)
    (M C : ℝ) (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ x ∂volume,ρ x≤M)
    (hC : RowFactorialMoments (gaussianRieszDensityMeasure ρ)
      (hoeffdingCentered (gaussianRieszDensityMeasure ρ) logPhysicalPair) C) :
    RowFactorialMoments (gaussianRieszDensityMeasure ρ)
      (gaussianLogAlgebraicInterpolation (gaussianRieszDensityMeasure ρ) η t)
      (gaussianLogInterpolationRowConstant C M (Fintype.card ι:ℝ)) := by
  have hshort := gaussianLogShort_centered_factorial_rows η hη hη1 hd ρ M hM hρ
  have hf := (stronglyMeasurable_hoeffdingCentered (gaussianRieszDensityMeasure ρ) _
    (measurable_logPhysicalPair (E:=EuclideanSpace ℝ ι)).stronglyMeasurable).measurable
  have hs := (stronglyMeasurable_hoeffdingCentered (gaussianRieszDensityMeasure ρ) _
    (stronglyMeasurable_gaussianLogShortPair η hη hd)).measurable
  exact RowFactorialMoments.sub_scaled (gaussianRieszDensityMeasure ρ) _ _ hf hs C _ (1-t) hC hshort
    (by rw [abs_of_nonneg (by linarith : 0≤1-t)];linarith)

/- A concrete positive threshold, with a positive admissible original witness.
It depends only on C,M,d and is at most half the original beta0. -/
def gaussianLogQuantitativeThreshold (C M d : ℝ) : ℝ :=
  min (attractiveBetaThreshold C/2)
    ((2*attractiveMomentConstant*(1+gaussianLogInterpolationRowConstant C M d))⁻¹)

lemma gaussianLogQuantitativeThreshold_pos (C M d : ℝ)
    (hC : 0<C) (hM : 0≤M) (hd : 0<d) :
    0<gaussianLogQuantitativeThreshold C M d := by
  have hrow : 0≤gaussianLogInterpolationRowConstant C M d := by
    unfold gaussianLogInterpolationRowConstant gaussianLogShortFactorialConstant
    positivity
  exact lt_min (by positivity [attractiveBetaThreshold_pos hC])
    (inv_pos.mpr (by positivity [attractiveMomentConstant_pos]))

lemma gaussianLogQuantitativeThreshold_half (C M d : ℝ) :
    gaussianLogQuantitativeThreshold C M d≤attractiveBetaThreshold C/2 := min_le_left _ _

lemma gaussianLogQuantitativeThreshold_row_small (C M d β : ℝ)
    (hC : 0<C) (hM : 0≤M) (hd : 0<d) (hβ : 0≤β)
    (hsmall : β<gaussianLogQuantitativeThreshold C M d) :
    β*(attractiveMomentConstant*gaussianLogInterpolationRowConstant C M d)<1 := by
  have hrow : 0≤gaussianLogInterpolationRowConstant C M d := by
    unfold gaussianLogInterpolationRowConstant gaussianLogShortFactorialConstant
    positivity
  have hp : 0<2*attractiveMomentConstant*(1+gaussianLogInterpolationRowConstant C M d) :=
    by positivity [attractiveMomentConstant_pos]
  have hb := hsmall.trans_le (min_le_right _ _)
  change β<(2*attractiveMomentConstant*(1+gaussianLogInterpolationRowConstant C M d))⁻¹ at hb
  rw [←one_div,lt_div_iff₀ hp] at hb
  have hle : attractiveMomentConstant*gaussianLogInterpolationRowConstant C M d≤
      2*attractiveMomentConstant*(1+gaussianLogInterpolationRowConstant C M d) := by
    nlinarith [attractiveMomentConstant_pos]
  exact (mul_le_mul_of_nonneg_left hle hβ).trans_lt hb
end DGRHS.Attractive
#check @DGRHS.Attractive.gaussianLog_interpolated_factorial_rows
#print axioms DGRHS.Attractive.RowFactorialMoments.neg
#print axioms DGRHS.Attractive.gaussianLogShort_centered_factorial_rows
#print axioms DGRHS.Attractive.gaussianLog_interpolated_factorial_rows
#print axioms DGRHS.Attractive.gaussianLogQuantitativeThreshold_pos
#print axioms DGRHS.Attractive.gaussianLogQuantitativeThreshold_half
#print axioms DGRHS.Attractive.gaussianLogQuantitativeThreshold_row_small
