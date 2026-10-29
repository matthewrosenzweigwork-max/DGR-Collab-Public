import DGPS.Frontier.LIP032.T38

/-!
# LIP032.09: Weak continuity of the limit map

Task id and title: LIP032.09, "Weak continuity of the limit map" (node LIP032, contractibility of the
minimizer set; conditional on the Task 29 bindings and on the positive-rate flow context of LIP031,
inherited through LIP032.38).

## Provides
* `DGPS.Frontier.LIP032.lip032_09_weak_continuity_limit_map` : MAIN. Under the exact positive-rate
  context of LIP032.38, there is a limit map `R` on the `L²(m)` classes such that the map
  `(ν, s) ↦ R [f_{ν,s}]` from `S × [0,1]` into the probability measures on the torus, with the weak
  topology, is continuous.

## R5 notes
* Inherited hypotheses. The binders `A`, `drift`, `G`, `B`, `g`, `β`, `hMF`, `hV`, `hWB`, `r`, `hr`,
  `hrate`, `μ`, `hμ`, `M_V`, `M_W`, `hVb`, `hWb` are exactly those of LIP032.38 (and hence of
  LIP032.37). Nothing is added and nothing is removed. In particular the positive-rate data `hr` and
  `hrate` are inherited, so the unit is not stated in the unconditional reading, which is false as
  recorded in the node preamble (FD-001). No strengthening is made.
* Choice function. The specification speaks of "the" map `R(f)`. As in LIP032.37 and LIP032.38 the
  limit map is available only existentially, so the conclusion is existential over `R` on the classes
  `l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)`.
* Parameter space. `S × [0,1]` is `minimizerSet_LIP03225 A × Set.Icc 0 1` with the product of the weak
  subspace topology and the subspace topology, as in LIP032.25 and LIP032.38.
* Weak topology. The continuity is into `ProbabilityMeasure (Torus d)` with its weak topology. No
  stronger convergence mode is introduced: the proof is the second conjunct of LIP032.38, which
  reduces the weak statement to continuity of all continuous real test integrals through the
  characterization of the weak topology by bounded continuous tests (LIB05).
* Proof. The unit is a projection of LIP032.38: the first conjunct, about continuous real tests, is
  discarded, and the second conjunct is the claimed continuity. No new analysis is performed here.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- **LIP032.09.** Weak continuity of the limit map. Under the positive-rate context of LIP032.38,
there is a limit map `R` on the `L²(m)` classes such that `(ν, s) ↦ R [f_{ν,s}]` is continuous from
`S × [0,1]` into the probability measures on the torus with the weak topology. -/
theorem lip032_09_weak_continuity_limit_map (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (M_V M_W : ℝ) (hVb : ∀ x, |A.V x| ≤ M_V) (hWb : ∀ x y, |A.W x y| ≤ M_W) :
    ∃ (R : DGPS.Lipschitz.L2s d → ProbabilityMeasure (Torus d)),
      Continuous (fun z : minimizerSet_LIP03225 A × Set.Icc (0 : ℝ) 1 =>
        R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ z.1.1 z.2))) := by
  obtain ⟨R, -, hc⟩ :=
    lip032_38_continuous_test_continuity_weak_continuity A drift hMF hV hWB hr hrate μ hμ M_V M_W
      hVb hWb
  exact ⟨R, hc⟩

end DGPS.Frontier.LIP032
