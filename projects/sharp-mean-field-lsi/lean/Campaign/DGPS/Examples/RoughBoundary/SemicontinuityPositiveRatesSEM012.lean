import DGPS.Examples.RoughBoundary.SemicontinuityCountersequence
import DGPS.Examples.RoughBoundary.FeatureRough
import DGPS.Examples.RoughBoundary.LandscapeSelection
import DGPS.Examples.RoughBoundary.FreeEnergy
import DGPS.Examples.RoughBoundary.NonlinearRate
import DGPS.Examples.RoughBoundary.NonlinearSpeciesRate

/-!
# SEM012: every small nonzero amplitude has exact positive rates

For the common finite parameter selection `ε₀, L₀` of RUF026 and every `L ≥ L₀`:
* for `0 < |ε| ≤ ε₀` the feature `U_{L,ε}` has all directional local `L²` obstructions (RUF007),
  Haar measure is the unique global minimizer of the free energy (RUF027), and the scalar and the
  multi-species rates equal `a0 = 4π²` for every absolute drift (RUF033, RUF036);
* at `ε = 0` the feature is smooth and its Haar potential has a critical point with positive gap,
  so the smooth remote Gibbs competitor (SEM010) forces both rates to zero for every drift.
-/

open MeasureTheory Set
open scoped Real ENNReal NNReal

namespace DGPS.Examples.RoughBoundary.Semicontinuity

open DGPS.Examples.RoughBoundary.Feature (dtheta Ureal Jrot Ufeat norm_Ufeat
  every_nonzero_direction_is_rough)
open DGPS.Examples.RoughBoundary.Model (modelData)
open DGPS.Examples.RoughBoundary.FreeEnergy (FreeEnergyDecomposition
  freeEnergyDecomposition_of_certificate)
open DGPS.Examples.RoughBoundary.Landscape (common_finite_parameter_selection)
open DGPS.Examples.RoughBoundary.Nonlinear (exact_scalar_rate_of_the_rough_example
  exact_arbitrary_finite_species_rate)

/-- **SEM012.** Every small nonzero amplitude has exact positive rates. There are `ε₀ > 0` and
`L₀ ≥ max {1, 1/ε₀}` such that for every `L ≥ L₀` (`L > 0`):
* for every `0 < |ε| ≤ ε₀`, every nonempty open `J ⊂ ℝ` and every nonzero direction `a ∈ ℝ²`, the
  functions `θ'`, `U' = 2π θ' J U` and `a · U'` are not in `L²(J)`; Haar measure is the unique
  global minimizer of the free energy; and for every absolute drift both the scalar rate `r_*` and
  the multi-species rate `r_ms` equal `a0 = 4π²`;
* at `ε = 0` the smooth model has both rates zero for every absolute drift. -/
theorem every_small_nonzero_amplitude_has_exact_positive_rates :
    ∃ ε₀ L₀ : ℝ, 0 < ε₀ ∧ 1 ≤ L₀ ∧ 1 / ε₀ ≤ L₀ ∧
      ∀ L : ℝ, L₀ ≤ L → ∀ hL : 0 < L,
        (∀ ε : ℝ, 0 < |ε| → |ε| ≤ ε₀ →
          (∀ J : Set ℝ, IsOpen J → J.Nonempty → ∀ a : EuclideanSpace ℝ (Fin 2), a ≠ 0 →
            ¬ MemLp (dtheta L ε) 2 (volume.restrict J) ∧
            ¬ MemLp (fun x => (2 * π * dtheta L ε x) • Jrot (Ureal L ε x)) 2
              (volume.restrict J) ∧
            ¬ MemLp (fun x => inner ℝ a ((2 * π * dtheta L ε x) • Jrot (Ureal L ε x))) 2
              (volume.restrict J)) ∧
          (∀ μ : ProbabilityMeasure (Torus 1),
            freeEnergy (modelData hL ε) μ = freeEnergyMinimum (modelData hL ε) →
              μ = haarProbability 1) ∧
          (∀ b : AbsoluteDrift (modelData hL ε),
            scalarRate (modelData hL ε) b = ENNReal.ofReal (4 * π ^ 2) ∧
              speciesRate (modelData hL ε) b = ENNReal.ofReal (4 * π ^ 2))) ∧
        (∀ b : AbsoluteDrift (modelData hL 0),
          scalarRate (modelData hL 0) b = 0 ∧ speciesRate (modelData hL 0) b = 0) := by
  obtain ⟨ε₀, L₀, h1, h2, h3, h4, -⟩ := common_finite_parameter_selection
  refine ⟨ε₀, L₀, h1, h2, h3, fun L hL hLpos => ⟨fun ε hε0 hεε => ?_, ?_⟩⟩
  · have hne : ε ≠ 0 := abs_pos.mp hε0
    have hdec : FreeEnergyDecomposition L ε :=
      freeEnergyDecomposition_of_certificate ε (h4 L hL ε hεε)
    obtain ⟨-, -, -, -, huniq, -⟩ := hdec hLpos
    exact ⟨fun J hJ hJne a ha => every_nonzero_direction_is_rough hLpos hne hJ hJne ha,
      fun μ hμ => huniq μ hμ,
      fun b => ⟨(exact_scalar_rate_of_the_rough_example hLpos hne hdec b).1,
        (exact_arbitrary_finite_species_rate hLpos hne hdec b).1⟩⟩
  · have hz : IsSmoothPeriodic (fun _ : Torus 1 => (0 : ℝ)) := by
      unfold IsSmoothPeriodic
      exact contDiff_const
    have hUeq : ∀ y, Ufeat L 0 y = UfeatF L 0 (fun _ => 0) y := by
      intro y
      simp [Ufeat, UfeatF, Ureal, UrealF, DGPS.Examples.RoughBoundary.Feature.theta, thetaF]
    have hs : ∀ j : Fin 2, IsSmoothPeriodic fun y => Ufeat L 0 y j := by
      intro j
      have hfun : (fun y => Ufeat L 0 y j) = fun y => UfeatF L 0 (fun _ => 0) y j :=
        funext fun y => by rw [hUeq y]
      rw [hfun]
      exact isSmoothPeriodic_UfeatF_SEM011 hLpos 0 hz j
    have hU := h4 L hL 0 (by rw [abs_zero]; exact h1.le)
    obtain ⟨-, -, -, -, -, -, Δ, B, aM, aS, hΔ, hΔB, -, -, -, hcS, -, -, -, -, -, -, hgM, hgS⟩ := id hU
    have hcrit : fderiv ℝ (featurePotential Landscape.kappa0 (Ufeat L 0)) (aS 0) = 0 := hcS 0
    have hpos : 0 < featurePotential Landscape.kappa0 (Ufeat L 0) (aS 0) := by
      have h5 := hgM 0
      have h6 := hgS 0 0
      linarith
    intro b
    obtain ⟨-, -, -, hsR, hsP, -⟩ :=
      smooth_positive_gap_gibbs_competitor_forces_both_rates_zero hs (norm_Ufeat L 0) hU hcrit
        hpos b
    exact ⟨hsR, hsP⟩

end DGPS.Examples.RoughBoundary.Semicontinuity
