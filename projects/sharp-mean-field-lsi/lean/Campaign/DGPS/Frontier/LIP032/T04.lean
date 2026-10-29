import DGPS.Frontier.LIP032.T23
import DGPS.Frontier.LIP032.T25

/-!
# LIP032.04: Interpolation density and L2 initial class

Task id and title: LIP032.04, "Interpolation density and L2 initial class" (node LIP032,
contractibility of the minimizer set; pure density task, no positive-rate or flow hypothesis is
used by this unit).

## Provides
* `DGPS.Frontier.LIP032.lip032_04_interpolation_density_l2_initial_class` : for minimizers
  `ν ∈ S` and `s ∈ [0,1]` (with the fixed base point `μ ∈ S`, `q = p_μ`), the density
  `f_{ν,s} = (1 - s) p_ν + s q` is continuous, has integral one and satisfies
  `e^{-2(M_V+M_W)} ≤ f_{ν,s} ≤ e^{2(M_V+M_W)}`; it defines the real `L²(m)` class `[f_{ν,s}]`
  whose coercion is an a.e. representative of `f_{ν,s}`, with the a.e. transport clauses and the
  clause that a.e.-equal continuous inputs give the same class; for every `η ∈ S` and `t ∈ [0,1]`,
  `‖f_{ν,s} - f_{η,t}‖_1 ≤ ‖p_ν - p_η‖_∞ + 2|s - t|`; and the parameter map `(η, t) ↦ f_{η,t}` is
  continuous for the real `L¹` distance at every point of `S × [0,1]`.

The proof assembles LIP032.22 (bounded density), LIP032.23 (canonical `L²` class and
representative transport) and LIP032.25 (exact interpolation `L¹` estimate and its continuity).
No helper declaration is introduced.

## R5 notes
* Hypotheses: exactly those of LIP032.22, LIP032.23 and LIP032.25. `A : InteractionData d`; reals
  `M_V`, `M_W` with `|A.V| ≤ M_V` and `|A.W| ≤ M_W` (no nonnegativity assumed, none needed); the
  fixed base point `μ` and the minimizer `ν` with memberships `_hμ`, `_hν` in `S` (the bounds hold
  for every probability measure, so these memberships are not used by the proof); and `s ∈ [0,1]`.
  The memberships `η ∈ S` and `t ∈ [0,1]` of the `L¹` clause are universally quantified premises of
  that clause. No hypothesis was added.
* Positive-rate hypotheses. The header of LIP031,
  `DGPS.Lipschitz.positive_rate_flow_tails_and_limiting_minimizer` (in
  `DGPS/Lipschitz/MinimizerRetraction.lean`), inherits the mean-field data, the weak-gradient
  hypotheses, `0 < r` and `ENNReal.ofReal r < scalarRate A drift`. This unit does not invoke LIP031
  and none of these hypotheses is used or added: the statement is a pure density, integration and
  approximation statement, as the specification states for this branch.
* The `c` and `C` bounds are written inline as `Real.exp (-(2 * (M_V + M_W)))` and
  `Real.exp (2 * (M_V + M_W))`, with `B_0 = M_V + M_W`.
* `‖f‖_1` is the real integral `∫ |f| dm` with `m = haar d`. `‖p_ν - p_η‖_∞` is read as the real
  supremum `⨆ x, |p_ν x - p_η x|`; it is the true supremum because the Gibbs densities are continuous
  on the compact torus.
* `L²(m; ℝ)` is typed as `DGPS.Lipschitz.L2s d` (an abbreviation for `Lp ℝ 2 (haar d)`), through
  `l2Class_LIP03223`. The campaign alias binding of Task 29 is a separate task and is not claimed by
  this unit.
* The representative clauses are the full conclusion of LIP032.23: membership in `L²(m)`, the a.e.
  equality `⇑[f] =ᵐ f`, a.e. nonnegativity, integral one of the representative, the a.e. bound by
  `C`, and equality of classes for every continuous `g` with `g =ᵐ f`. They are transported along the
  a.e. equality, so the continuous representative used for the density measure is the one used for
  the `L²` class.
* The continuity clause is the one of LIP032.25. Its domain is `S × [0,1]`, with `S` carrying the
  subspace topology of the weak topology (the subtype `minimizerSet_LIP03225`) and `[0,1]` its
  subspace topology. A real `L¹` distance is not a topology on functions, so continuity is read as:
  at every point `(ν₀, s₀)`, the distance `∫ |f_{ν,s} - f_{ν₀,s₀}| dm` tends to `0` along the
  neighbourhood filter. This is the reading fixed by LIP032.25.
* Nothing in the statement is strengthened or weakened relative to the three prerequisite
  statements.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- **LIP032.04.** For minimizers `μ, ν ∈ S` (`μ` the base point, `q = p_μ`) and `s ∈ [0,1]`, the
density `f_{ν,s}` is continuous, has integral one and satisfies `c ≤ f_{ν,s} ≤ C`; the class
`[f_{ν,s}]` in `L²(m)` has a coercion that agrees a.e. with `f_{ν,s}`, and the transported
representative is a.e. nonnegative, has integral one and is a.e. bounded by `C`; a.e.-equal continuous
inputs give the same class. For every `η ∈ S` and `t ∈ [0,1]`,
`‖f_{ν,s} - f_{η,t}‖_1 ≤ ‖p_ν - p_η‖_∞ + 2|s - t|`, and the parameter map `(η, t) ↦ f_{η,t}` is
continuous for the real `L¹` distance at every point of `S × [0,1]`. -/
theorem lip032_04_interpolation_density_l2_initial_class
    (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W)
    (μ : ProbabilityMeasure (Torus d)) (_hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν : ProbabilityMeasure (Torus d)) (_hν : freeEnergy A ν = freeEnergyMinimum A)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (Continuous (interpolDensity_LIP03222 A μ ν s) ∧
      ∫ x, interpolDensity_LIP03222 A μ ν s x ∂haar d = 1 ∧
      ∀ x, Real.exp (-(2 * (M_V + M_W))) ≤ interpolDensity_LIP03222 A μ ν s x ∧
        interpolDensity_LIP03222 A μ ν s x ≤ Real.exp (2 * (M_V + M_W))) ∧
    (MemLp (interpolDensity_LIP03222 A μ ν s) 2 (haar d) ∧
      (⇑(l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) : Torus d → ℝ)
        =ᵐ[haar d] interpolDensity_LIP03222 A μ ν s ∧
      (0 ≤ᵐ[haar d] (⇑(l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) : Torus d → ℝ)) ∧
      ∫ x, (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) x ∂haar d = 1 ∧
      (∀ᵐ x ∂haar d, |(l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) x| ≤
        Real.exp (2 * (M_V + M_W))) ∧
      (∀ g : Torus d → ℝ, Continuous g → g =ᵐ[haar d] interpolDensity_LIP03222 A μ ν s →
        l2Class_LIP03223 g = l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) ∧
    (∀ (η : ProbabilityMeasure (Torus d)), freeEnergy A η = freeEnergyMinimum A →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ∫ x, |interpolDensity_LIP03222 A μ ν s x - interpolDensity_LIP03222 A μ η t x| ∂haar d ≤
          (⨆ x, |DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) x -
            DGPS.Lipschitz.gibbsDensity A (η : Measure (Torus d)) x|) + 2 * |s - t|) ∧
    (∀ (ν₀ : minimizerSet_LIP03225 A) (s₀ : Set.Icc (0 : ℝ) 1),
      Tendsto (fun z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 =>
        ∫ x, |interpolDensity_LIP03222 A μ z.1.1 z.2 x -
          interpolDensity_LIP03222 A μ ν₀.1 s₀ x| ∂haar d)
        (𝓝 (ν₀, s₀)) (𝓝 0)) := by
  obtain ⟨hcont, hint, hbnd, -⟩ :=
    lip032_22_interpolation_bounded_density A M_V M_W hV hW μ _hμ ν _hν s hs0 hs1
  have h23 := lip032_23_canonical_l2_class_representative_transport A M_V M_W hV hW μ _hμ ν _hν
    s hs0 hs1
  refine ⟨⟨hcont, hint, hbnd⟩, h23, ?_, ?_⟩
  · intro η hη t ht0 ht1
    exact lip032_25_exact_interpolation_l1_estimate A M_V M_W hV hW μ _hμ ν _hν η hη s t hs0 hs1
      ht0 ht1
  · intro ν₀ s₀
    exact lip032_25_exact_interpolation_l1_estimate_continuous A M_V M_W hV hW μ _hμ ν₀ s₀

end DGPS.Frontier.LIP032
