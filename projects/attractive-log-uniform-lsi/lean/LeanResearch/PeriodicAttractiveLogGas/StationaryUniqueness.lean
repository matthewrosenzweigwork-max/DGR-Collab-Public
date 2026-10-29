import LeanResearch.PeriodicAttractiveLogGas.StationarySharpIsoperimetry
import LeanResearch.PeriodicAttractiveLogGas.OccupationFarImbalance

/-! Stationary uniqueness and far occupation imbalance with the geometric
premise discharged. The original Green kernel, the critical stationary
endpoint, and the resolution-independent coupling range are unchanged. -/
set_option autoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace PeriodicAttractiveLogGas.StationaryUniqueness
open StationarySharpIsoperimetry ConditionalLawEstimates

theorem stationary_constant {u : Torus → ℝ} {ρ : ℝ}
    (hu : ContDiff ℝ ∞ (fun x : PlanarSpace ↦ u (torusQuotient x)))
    (hpde : ∀ x : PlanarSpace,
      Laplacian.laplacian (fun y : PlanarSpace ↦ u (torusQuotient y)) x +
        ρ * (Real.exp (u (torusQuotient x)) / (∫ z, Real.exp (u z) ∂torusMeasure) - 1) = 0)
    (hρ : 0 ≤ ρ) (hρmax : ρ ≤ 8 * Real.pi) :
    ∀ z, u z = Real.log (∫ x, Real.exp (u x) ∂torusMeasure) := by
  exact OccupationFarImbalance.stationary_constant hu hpde hρ hρmax
    (sharp_physical_superlevel_isoperimetry (OccupationFarImbalance.normalizedStationary_contDiff hu))

theorem original_fixedPoint_eq_one {f : Torus → ℝ} (hf : MemLp f 4 torusMeasure)
    (hmass : (∫ x, f x ∂torusMeasure) = 1) {β : ℝ} (hβ : 0 ≤ β) (hβ4 : β ≤ 4)
    (hfix : f =ᵐ[torusMeasure] fun x ↦
      Real.exp (β * ∫ y, greenRealRepresentative (x - y) * f y ∂torusMeasure) /
        (∫ z, Real.exp (β * ∫ y, greenRealRepresentative (z - y) * f y ∂torusMeasure)
          ∂torusMeasure)) :
    f =ᵐ[torusMeasure] (fun _ ↦ (1 : ℝ)) :=
  OccupationFarImbalance.original_fixedPoint_eq_one
    (fun _ hv ↦ sharp_physical_superlevel_isoperimetry hv) hf hmass hβ hβ4 hfix

/-- A single positive constant and a single particle threshold, uniform in
the original coupling interval. No isoperimetric or stationary-uniqueness
premise remains in the complete type. -/
theorem exists_FarImbalance {J : ℕ} {β₀ t : ℝ} (hsub : β₀ < 4)
    (ht : 0 < t) (htC : t ≤ occupationBound β₀)
    (hmesh : 8 * (radius β₀ + 4) ≤ J) :
    ∃ cFar : ℝ, 0 < cFar ∧ ∃ NFar : ℕ, 2 ≤ NFar ∧
      ∀ N : ℕ, NFar ≤ N → 4 ≤ t * N ∧
        ∀ β : ℝ, 0 ≤ β → β ≤ β₀ →
          OccupationCoercivity.FarImbalance (N := N) (t := t)
            (ConditionalLawEstimates.mesh_pos hmesh) β β₀ cFar := by
  exact OccupationFarImbalance.exists_FarImbalance
    (fun _ hv ↦ sharp_physical_superlevel_isoperimetry hv) hsub ht htC hmesh

end PeriodicAttractiveLogGas.StationaryUniqueness
