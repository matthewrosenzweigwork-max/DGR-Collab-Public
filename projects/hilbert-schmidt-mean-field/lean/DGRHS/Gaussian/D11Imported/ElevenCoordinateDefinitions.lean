import DGRHS.Gaussian.D11Imported.ElevenLabelDefinitions

noncomputable section
open MeasureTheory Set
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

/-- The explicit one-coordinate marginal from Section 4. -/
def coordinateProfile (t : ℝ) : ℝ :=
  1280/(63*Real.pi) * (1+25*t^2)^(-6 : ℤ)

/-- The law of the rounded coordinate, using the manuscript's half-open cells. -/
def coordinateLabelProbability (n : ℤ) : ℝ :=
  ∫ t in Ico ((n:ℝ)-1/2) ((n:ℝ)+1/2), coordinateProfile t

def coordinateLabelMoment : ℝ :=
  ∑' n : ℤ, coordinateLabelProbability n * (n.natAbs:ℝ)

end DGRHS.Gaussian.D11Imported.HighDim.Eleven
