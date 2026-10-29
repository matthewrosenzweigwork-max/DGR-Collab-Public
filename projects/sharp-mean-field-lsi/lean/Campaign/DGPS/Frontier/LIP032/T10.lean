import DGPS.Frontier.LIP032.T40

/-!
# LIP032.10: Zero-gap data are fixed

Task id and title: LIP032.10, "Zero-gap data are fixed" (node LIP032, contractibility of the
minimizer set; leaf formalization, conditional on Task 29 and on the positive-rate flow context
of LIP031).

## Provides
* `DGPS.Frontier.LIP032.lip032_10_zero_gap_data_fixed` : MAIN. For a choice `u` of flows and a
  choice `R` of limiting probabilities with the LIP032.30 property `hch`, every free-energy
  minimizer `ν` satisfies `R [p_ν] = ν`, where `[p_ν]` is the `L²(m)` class of the Gibbs density
  `p_ν = gibbsDensity A ν`.
* `DGPS.Frontier.LIP032.lip032_10_zero_gap_data_fixed_nonvacuous` : non-vacuity: choices `u`, `R`
  with the property `hch` exist (LIP032.30), and for them `R [p_ν] = ν` for every minimizer.

## R5 notes
* Proof route. The proof is the LIP032.40 argument, taken from `lip032_40_zero_initial_gap_fixes_measure`
  and its non-vacuity variant. The zero initial gap, the time-zero LIP031 tail bound and the
  measure-determination step are all inside that proof. No new analytic step is introduced here.
  The uniform bound `G_0` is not used for the zero gap.
* Hypotheses. The positive-rate context of LIP031 is inherited exactly as in LIP032.30 and
  LIP032.40: `A`, `drift : AbsoluteDrift A`, `G`, `B`, `g`, `β`, `hMF`, `hV : IsWeakGradient A.V G`,
  `hWB`, a real `r` with `hr : 0 < r` and `hrate : ENNReal.ofReal r < scalarRate A drift`. Beyond
  them the only hypotheses are the fixed minimizer `μ` with `hμ`, the choices `u` and `R`, and the
  choice property `hch`. No hypothesis is added, and no bound is assumed.
* Choices. The specification's limiting probability `R` is read as the output of LIP032.30: a
  choice of flows `u` and of limits `R`, both indexed by the initial `L²` class. The hypothesis
  `hch` is the LIP032.30 property, quantified over all minimizers and all `s ∈ [0,1]`. Only its
  `s = 0` instance is used. The main theorem therefore applies to every choice with that property,
  and `lip032_10_zero_gap_data_fixed_nonvacuous` shows the property is satisfiable.
* Non-literal reading. The specification writes `p_ν` for the initial density. Here it is the class
  `l2Class_LIP03223 (gibbsDensity A ν)`. The interpolation density at `s = 0` is identified with
  `gibbsDensity A ν` as a function, not only almost everywhere (LIP032.40).
* Frozen statement. Nothing here proves or strengthens the unconditional frozen contractibility
  sentence of the node (FD-001). The conclusion depends on `hr`, `hrate` and `hch`.
* Dimension. `d` is arbitrary; positivity of `d` is not used.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- Zero-gap data are fixed: for a choice `u` of flows and `R` of limiting probabilities with the
LIP032.30 property, every free-energy minimizer `ν` satisfies `R [p_ν] = ν`. -/
theorem lip032_10_zero_gap_data_fixed (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (u : DGPS.Lipschitz.L2s d → ℝ → DGPS.Lipschitz.L2s d)
    (R : DGPS.Lipschitz.L2s d → ProbabilityMeasure (Torus d))
    (hch : ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A ν = freeEnergyMinimum A →
      ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
        DGPS.Lipschitz.IsGlobalProbFlow hMF
            (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))
            (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) ∧
          freeEnergy A (R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) =
            freeEnergyMinimum A ∧
          ∀ φ : Torus d → ℝ, Continuous φ →
            Tendsto (fun t : ℝ =>
                ∫ x, u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) t x * φ x ∂haar d)
              atTop
              (𝓝 (∫ x, φ x
                ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) :
                  Measure (Torus d))))) :
    ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A ν = freeEnergyMinimum A →
      R (l2Class_LIP03223 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)))) = ν :=
  lip032_40_zero_initial_gap_fixes_measure A drift hMF hV hWB hr hrate μ hμ u R hch

/-- Non-vacuity of the zero-gap statement: choices `u`, `R` with the LIP032.30 property exist,
and for every such choice `R [p_ν] = ν` for every free-energy minimizer `ν`. -/
theorem lip032_10_zero_gap_data_fixed_nonvacuous (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A) :
    ∃ (u : DGPS.Lipschitz.L2s d → ℝ → DGPS.Lipschitz.L2s d)
      (R : DGPS.Lipschitz.L2s d → ProbabilityMeasure (Torus d)),
      (∀ ν : ProbabilityMeasure (Torus d), freeEnergy A ν = freeEnergyMinimum A →
        ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
          DGPS.Lipschitz.IsGlobalProbFlow hMF
              (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))
              (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) ∧
            freeEnergy A (R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) =
              freeEnergyMinimum A ∧
            ∀ φ : Torus d → ℝ, Continuous φ →
              Tendsto (fun t : ℝ =>
                  ∫ x, u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) t x * φ x ∂haar d)
                atTop
                (𝓝 (∫ x, φ x
                  ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) :
                    Measure (Torus d))))) ∧
      ∀ ν : ProbabilityMeasure (Torus d), freeEnergy A ν = freeEnergyMinimum A →
        R (l2Class_LIP03223 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)))) = ν :=
  lip032_40_zero_initial_gap_fixes_measure_exists A drift hMF hV hWB hr hrate μ hμ

end DGPS.Frontier.LIP032
