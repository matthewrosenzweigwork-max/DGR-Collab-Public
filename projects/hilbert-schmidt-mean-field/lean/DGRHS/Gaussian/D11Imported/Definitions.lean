/- Adapted locally from the owner-supplied September 27 BecknerOnofri archive.
See D11Imported/PROVENANCE.md and SOURCE_ADAPTATIONS.json for exact member hashes. -/
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLog
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
Trusted analytic definitions for the high-dimensional endpoint.

The measure is actual normalized Haar measure on (R/Z)^d. Frequencies use
the Euclidean length, not the default maximum norm on a function type.
Infinite spectral energies use ENNReal; a divergent series is never silently
replaced by the default real `tsum` value. No analytic bound is a field of
the probability-density or Sobolev-domain definitions.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal

namespace DGRHS.Gaussian.D11Imported.HighDim

abbrev Torus (d : ℕ) := UnitAddTorus (Fin d)
abbrev Frequency (d : ℕ) := Fin d → ℤ
abbrev NonzeroFrequency (d : ℕ) := {k : Frequency d // k ≠ 0}

def torusMeasure (d : ℕ) : Measure (Torus d) :=
  Measure.pi (fun _ : Fin d => AddCircle.haarAddCircle)

instance (d : ℕ) : IsProbabilityMeasure (torusMeasure d) := by
  unfold torusMeasure
  infer_instance

def fourierCoeff {d : ℕ} (f : Torus d → ℝ) (k : Frequency d) : ℂ :=
  ∫ x, UnitAddTorus.mFourier (-k) x * (f x : ℂ) ∂torusMeasure d

def frequencyLength {d : ℕ} (k : Frequency d) : ℝ :=
  Real.sqrt (∑ i : Fin d, (k i : ℝ) ^ 2)

structure ProbabilityDensity (d : ℕ) where
  value : Torus d → ℝ
  nonneg : ∀ᵐ x ∂torusMeasure d, 0 ≤ value x
  integrable : Integrable value (torusMeasure d)
  mass : (∫ x, value x ∂torusMeasure d) = 1

def uniformDensity (d : ℕ) : ProbabilityDensity d where
  value := fun _ => 1
  nonneg := Filter.Eventually.of_forall (fun _ => zero_le_one)
  integrable := integrable_const 1
  mass := by simp

def ProbabilityDensity.FiniteEntropy {d : ℕ} (ρ : ProbabilityDensity d) : Prop :=
  Integrable (fun x => ρ.value x * Real.log (ρ.value x)) (torusMeasure d)

def entropy {d : ℕ} (ρ : ProbabilityDensity d) : ℝ :=
  ∫ x, ρ.value x * Real.log (ρ.value x) ∂torusMeasure d

def spectralTerm {d : ℕ} (ρ : ProbabilityDensity d)
    (k : NonzeroFrequency d) : ℝ :=
  (frequencyLength k.val ^ d)⁻¹ * ‖fourierCoeff ρ.value k.val‖ ^ 2

def spectralEnergy {d : ℕ} (ρ : ProbabilityDensity d) : ℝ≥0∞ :=
  ∑' k : NonzeroFrequency d, ENNReal.ofReal (spectralTerm ρ k)

def spectralThreshold (d : ℕ) : ℝ :=
  2 * Real.pi ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2)

end DGRHS.Gaussian.D11Imported.HighDim
