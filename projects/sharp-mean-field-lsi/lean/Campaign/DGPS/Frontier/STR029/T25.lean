import DGPS.Frontier.STR029.T63

/-!
# STR029.25: Uniform neighborhood entry of all global optimizers

Task id: STR029.25. Title: Uniform neighborhood entry of all global optimizers.

Prerequisites: STR029.61 (recovery of the scaled rate from the value equation), STR029.62 (a
global optimizer in a positive chart is fully critical) and STR029.63 (sequential localization
gives uniform neighborhood entry). STR029.63 is the direct input; its conclusion is taken as given
and strengthened by the variational range equation `Rpar = 0`.

Statement. Let `N₀, N₁, N₂ ⊆ ℝ × ℝ × ℝ` be open sets that contain the three limit points
`(2, 0, -16/15)`, `(-1, √3, -16/15)` and `(-1, -√3, -16/15)`. Then there are a graph neighbourhood
`(U, V, ψ)` of the value-equation range map and a radius `η₁ > 0` such that for every `h ≠ 0` with
`|h| < η₁` and every absolute density `ρ` with positive entropy at `h` that is a global optimizer
of the normalized Fisher quotient at `h`, there are chart data `(a, b, w)` representing `ρ` with
`(a, b, h, r) ∈ U`, an element `wE` of `E` representing `w` with `wE = ψ (a, b, h, r)` and
`Rpar (a, b, h, r) wE = 0`, and `(a / h, b / h, r / h ^ 2) ∈ N₀ ∪ N₁ ∪ N₂`, where
`r = rateSTR02963 h ρ` is the physical rate minus one.

Proof route. Apply STR029.63 to obtain `(U, V, ψ)`, the radius `η₁`, and the entry conclusion.
The graph characterization `Rpar p w = 0 ↔ w = ψ p` for `p ∈ U` and `w ∈ V` turns the equality
`wE = ψ (a, b, h, r)` into `Rpar (a, b, h, r) wE = 0`. The membership `wE ∈ V` follows from
`ψ p ∈ V` for `p ∈ U`.

Provides:
* `DGPS.Frontier.STR029.str029_25_uniform_neighborhood_entry_global_optimizers`: the main
  statement above.

R5 notes:
* Open sets. As in STR029.63, `N₀`, `N₁`, `N₂` are arbitrary open sets for the product metric on
  `ℝ × ℝ × ℝ`, each containing its limit point. One radius `η₁` serves all three sets and does not
  depend on `h` or `ρ`.
* Added conjunct. The only change relative to the STR029.63 conclusion is the conjunct
  `Rpar_STR02916 (a, b, h, rateSTR02963 h ρ) wE = 0`. It is derived from the graph
  characterization, not assumed.
* Redundancy. Node .25 and node .63 state the same conclusion. This module is a thin wrapper over
  the STR029.63 theorem and adds no analytic content.
* Other readings. The rate coordinate is `rateSTR02963`, the physical rate minus one. The chart
  witnesses are `C^{2,1/2}` and represent `ρ` almost everywhere for the angular Haar measure.
  Global optimality compares the normalized Fisher quotient with densities of positive entropy at
  the same `h`. The domain is `h ≠ 0` with `|h| < η₁`.
-/

open scoped ContDiff
open Filter Topology
open DGPS.Analysis.PeriodicHolder
open MeasureTheory Set
open DGPS.Circle.AngularNormalization
open scoped ENNReal
open DGPS DGPS.Examples.ThreeSpeciesCircle

namespace DGPS.Frontier.STR029

/-- Uniform neighborhood entry of all global optimizers. Given open neighbourhoods `N₀`, `N₁`,
`N₂` of the three limit points, there is a graph neighbourhood `(U, V, ψ)` and a radius `η₁ > 0`
such that every positive-entropy global optimizer at `0 < |h| < η₁` has a chart representative
with `wE = ψ (a, b, h, r)`, `Rpar (a, b, h, r) wE = 0`, and scaled point in `N₀ ∪ N₁ ∪ N₂`. -/
theorem str029_25_uniform_neighborhood_entry_global_optimizers
    (N₀ N₁ N₂ : Set (ℝ × ℝ × ℝ)) (hN₀ : IsOpen N₀) (hN₁ : IsOpen N₁) (hN₂ : IsOpen N₂)
    (hp₀ : ((2 : ℝ), (0 : ℝ), (-16 / 15 : ℝ)) ∈ N₀)
    (hp₁ : ((-1 : ℝ), Real.sqrt 3, (-16 / 15 : ℝ)) ∈ N₁)
    (hp₂ : ((-1 : ℝ), -Real.sqrt 3, (-16 / 15 : ℝ)) ∈ N₂) :
    ∃ (U : Set Par_STR02916) (V : Set E_STR02969) (ψ : Par_STR02916 → E_STR02969),
      IsOpen U ∧ (0 : Par_STR02916) ∈ U ∧ IsOpen V ∧ (0 : E_STR02969) ∈ V ∧
      ContDiffOn ℝ ∞ ψ U ∧ ψ 0 = 0 ∧ (∀ p ∈ U, ψ p ∈ V) ∧
      (∀ p ∈ U, ∀ w ∈ V, Rpar_STR02916 p w = 0 ↔ w = ψ p) ∧
      ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ h : ℝ, h ≠ 0 → |h| < η₁ → ∀ ρ : AbsoluteDensity 1,
        0 < ordinaryEntropy h ρ →
        (∀ ρ' : AbsoluteDensity 1, 0 < ordinaryEntropy h ρ' →
          ordinaryFisher h ρ / (2 * ordinaryEntropy h ρ) ≤
            ordinaryFisher h ρ' / (2 * ordinaryEntropy h ρ')) →
        ∃ (a b : ℝ) (w : ℝ → ℝ),
          (∀ᵐ θ ∂angHaar, ρ.density (angEquiv.symm θ) =
            rhoT_STR02901 h (uT_STR02901 a b w) (angSec θ)) ∧
          IsC2Alpha_STR02901 (1 / 2) w ∧ InE_STR02901 w ∧
          ∃ wE : E_STR02969, (wE : PeriodicC2_STR02969).val = w ∧
            (a, b, h, rateSTR02963 h ρ) ∈ U ∧ wE = ψ (a, b, h, rateSTR02963 h ρ) ∧
            Rpar_STR02916 (a, b, h, rateSTR02963 h ρ) wE = 0 ∧
            (a / h, b / h, rateSTR02963 h ρ / h ^ 2) ∈ N₀ ∪ N₁ ∪ N₂ := by
  obtain ⟨U, V, ψ, hU, h0U, hV, h0V, hdiff, hψ0, hψV, hiff, η₁, hη₁, hmain⟩ :=
    str029_63_sequential_localization_gives_uniform_neighborhood_entry N₀ N₁ N₂ hN₀ hN₁ hN₂
      hp₀ hp₁ hp₂
  refine ⟨U, V, ψ, hU, h0U, hV, h0V, hdiff, hψ0, hψV, hiff, η₁, hη₁, ?_⟩
  intro h hh hhη ρ hpos hopt
  obtain ⟨a, b, w, hae, hC2, hE, wE, hval, hpU, hψeq, hN⟩ :=
    hmain h hh hhη ρ hpos hopt
  have hwV : wE ∈ V := by
    rw [hψeq]
    exact hψV _ hpU
  exact ⟨a, b, w, hae, hC2, hE, wE, hval, hpU, hψeq, (hiff _ hpU wE hwV).2 hψeq, hN⟩

end DGPS.Frontier.STR029
