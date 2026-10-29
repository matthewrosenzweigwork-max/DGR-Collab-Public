import DGRHS.Gaussian.D11Imported.ElevenDefinitions

/-! Literal conditional lattice-label probabilities and Shannon entropy from
Section 4. The entropy is defined by its integral, not by the identity to be proved. -/
noncomputable section
open MeasureTheory Set
namespace DGRHS.Gaussian.D11Imported.HighDim.Eleven

def labelCube : Set (Fin 11 → ℝ) :=
  univ.pi (fun _ => Ico (-(1/2 : ℝ)) (1/2))

def conditionalLabel (y : Fin 11 → ℝ) (n : Frequency 11) : ℝ :=
  euclideanProfile (fun i => y i+(n i:ℝ)) /
    periodizedProfile (fun i => (y i : UnitAddCircle))

def conditionalLabelEntropy : ℝ :=
  -(∫ y in labelCube, periodizedProfile (fun i => (y i : UnitAddCircle)) *
    ∑' n : Frequency 11, conditionalLabel y n * Real.log (conditionalLabel y n))

def labelProbability (n : Frequency 11) : ℝ :=
  ∫ y in labelCube, euclideanProfile (fun i => y i+(n i:ℝ))

def labelEntropy : ℝ :=
  -(∑' n : Frequency 11, labelProbability n * Real.log (labelProbability n))

end DGRHS.Gaussian.D11Imported.HighDim.Eleven
