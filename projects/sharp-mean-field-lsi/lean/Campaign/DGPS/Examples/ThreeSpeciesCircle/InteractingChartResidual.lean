import DGPS.Examples.ThreeSpeciesCircle.InteractingChartNative
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarWeakEuler

/-! Exact native residual dictionary for the actual rank-three chart.
This unconditional identity retains the scalar deficit term; it is not
discarded before actual minimality supplies its zero value. -/

noncomputable section
open MeasureTheory Filter
open DGPS.Frontier.STR029 DGPS.Circle.AngularNormalization

namespace DGPS.Examples.ThreeSpeciesCircle

def elementaryChartLogConstant (h : ℝ) (u : PeriodicC2_STR02969) : ℝ :=
  -Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s) + u.val s))) +
    Real.log (meanT_STR02901 (fun s => Real.exp (h * Real.cos (3 * s))))

def elementaryAngularLogResidual (h γ ε : ℝ) (u : PeriodicC2_STR02969)
    (ρ : AbsoluteDensity 1) (t : ℝ) : ℝ :=
  -2 * a0 * deriv (deriv u.val) t +
    6 * a0 * h * Real.sin (3 * t) * deriv u.val t - a0 * (deriv u.val t) ^ 2 -
      2 * (a0 * (1 + γ)) * (u.val t + elementaryChartLogConstant h u) +
        elementaryEulerCorrection h ε (a0 * (1 + γ)) ρ (angEquiv.symm (t : AngCircle)) -
          elementaryEulerMultiplier h ε (a0 * (1 + γ)) ρ

/-- The actual native gradient equals the physical logarithmic residual minus
the full actual deficit, with the exact physical a0 normalization. No zero
deficit, stationarity, optimizer or Euler premise is imposed in this identity. -/
theorem interactingChartGradient_logResidual {h : ℝ} (hh : 0 < h)
    (u : PeriodicC2_STR02969) (ρ : AbsoluteDensity 1)
    (hρ : ∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) = rhoT_STR02901 h u.val (angSec θ))
    (γ ε t : ℝ) :
    a0 * (interactingChartGradient h (ε, γ, u)).val t =
      rhoT_STR02901 h u.val t *
        (elementaryAngularLogResidual h γ ε u ρ t -
          ((ordinaryFisher h ρ).toReal - 2 * (a0 * (1 + γ)) * (ordinaryEntropy h ρ).toReal +
            ε * elementaryC h (a0 * (1 + γ)) ρ + ε ^ 2 * elementaryJ h ρ)) := by
  obtain ⟨hH, hI⟩ := interactingChart_native_ordinary_terms h u ρ hρ
  rw [interactingChartGradient_native hh u ρ hρ γ ε t, hH, hI]
  unfold elementaryAngularLogResidual elementaryChartLogConstant
    elementaryEulerCorrection elementaryEulerMultiplier gradG_STR02950
    entropyChart_STR02949 fisherChart_STR02949
  have ha : a0 ≠ 0 := by unfold a0; positivity
  field_simp [ha]
  <;> ring

end DGPS.Examples.ThreeSpeciesCircle
