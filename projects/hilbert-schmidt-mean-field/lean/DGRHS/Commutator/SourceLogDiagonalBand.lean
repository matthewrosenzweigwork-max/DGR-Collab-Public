import DGRHS.Gaussian.GaussianShortRangeSourceL2
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! RECORDS-ONLY UNCHECKED. Instantiate the already checked square-density
transfer with the actual indicator of a finite Euclidean ball. The resulting
diagonal-band mass has one density-bound factor M, with the outer probability
factor of mass one. No joint time-density representative or pair-force L1 is
used here. Positive dimension is explicit. Compiler HOLD. -/
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal
namespace DGRHS.Commutator
open DGRHS.Gaussian
variable {ι : Type*} [Fintype ι] [Nonempty ι]
local notation "E" => EuclideanSpace ℝ ι

def sourceLogBallIndicator (ε : ℝ) (z : E) : ℝ :=
  (ball (0:E) ε).indicator (fun _=>1) z

lemma sourceLogBallIndicator_sq (ε : ℝ) (z : E) :
    sourceLogBallIndicator ε z^2=sourceLogBallIndicator ε z := by
  classical
  by_cases hz:z∈ball (0:E) ε
  · simp [sourceLogBallIndicator,Set.indicator,hz]
  · simp [sourceLogBallIndicator,Set.indicator,hz]

lemma sourceLog_ball_volume_ne_top (ε : ℝ) :
    volume (ball (0:E) ε)≠∞ := by
  rw [EuclideanSpace.volume_ball]
  finiteness

lemma stronglyMeasurable_sourceLogBallIndicator (ε : ℝ) :
    StronglyMeasurable (sourceLogBallIndicator (ι:=ι) ε) :=
  stronglyMeasurable_const.indicator measurableSet_ball

lemma integrable_sourceLogBallIndicator_sq (ε : ℝ) :
    Integrable (fun z:E=>sourceLogBallIndicator ε z^2) volume := by
  have h : Integrable (sourceLogBallIndicator (ι:=ι) ε) volume :=
    (integrableOn_const (C:=(1:ℝ)) (s:=ball (0:E) ε)
      (hs:=sourceLog_ball_volume_ne_top ε)).integrable_indicator measurableSet_ball
  simpa only [sourceLogBallIndicator_sq] using h

lemma integrable_sourceLogDiagonalBand (ε : ℝ) (ρ : E→ℝ) (M : ℝ)
    (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ z ∂volume,ρ z≤M) :
    Integrable (fun p:E×E=>sourceLogBallIndicator ε (p.1-p.2))
      ((gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ)) := by
  simpa only [sourceLogBallIndicator_sq] using
    integrable_sq_sub_density_product ρ M hM hρ (sourceLogBallIndicator ε)
      (stronglyMeasurable_sourceLogBallIndicator ε) (integrable_sourceLogBallIndicator_sq ε)

lemma integral_sourceLogDiagonalBand_le (ε : ℝ) (ρ : E→ℝ) (M : ℝ)
    (hM : 0≤M) [IsProbabilityMeasure (gaussianRieszDensityMeasure ρ)]
    (hρ : ∀ᵐ z ∂volume,ρ z≤M) :
    (∫ p:E×E,sourceLogBallIndicator ε (p.1-p.2)
      ∂(gaussianRieszDensityMeasure ρ).prod (gaussianRieszDensityMeasure ρ))≤
      M*volume.real (ball (0:E) ε) := by
  have hi : (∫ z:E,sourceLogBallIndicator ε z)=volume.real (ball (0:E) ε) := by
    change (∫ z:E,(ball (0:E) ε).indicator (fun _=> (1:ℝ)) z)=_
    rw [integral_indicator_const (1:ℝ) measurableSet_ball]
    simp only [smul_eq_mul,mul_one]
  simpa only [sourceLogBallIndicator_sq,hi] using
    integral_sq_sub_density_product_le ρ M hM hρ (sourceLogBallIndicator ε)
      (stronglyMeasurable_sourceLogBallIndicator ε) (integrable_sourceLogBallIndicator_sq ε)

end DGRHS.Commutator
set_option pp.maxSteps 1000000
set_option pp.deepTerms true
#check @DGRHS.Commutator.sourceLogBallIndicator
#print axioms DGRHS.Commutator.sourceLogBallIndicator
#check @DGRHS.Commutator.sourceLogBallIndicator_sq
#print axioms DGRHS.Commutator.sourceLogBallIndicator_sq
#check @DGRHS.Commutator.sourceLog_ball_volume_ne_top
#print axioms DGRHS.Commutator.sourceLog_ball_volume_ne_top
#check @DGRHS.Commutator.stronglyMeasurable_sourceLogBallIndicator
#print axioms DGRHS.Commutator.stronglyMeasurable_sourceLogBallIndicator
#check @DGRHS.Commutator.integrable_sourceLogBallIndicator_sq
#print axioms DGRHS.Commutator.integrable_sourceLogBallIndicator_sq
#check @DGRHS.Commutator.integrable_sourceLogDiagonalBand
#print axioms DGRHS.Commutator.integrable_sourceLogDiagonalBand
#check @DGRHS.Commutator.integral_sourceLogDiagonalBand_le
#print axioms DGRHS.Commutator.integral_sourceLogDiagonalBand_le
