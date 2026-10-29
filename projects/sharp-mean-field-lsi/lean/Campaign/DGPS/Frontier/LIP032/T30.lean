import DGPS.Frontier.LIP032.T23
import DGPS.Frontier.LIP032.T29
import DGPS.Lipschitz.MinimizerRetraction

/-!
# LIP032.30: Choose one flow and one limiting probability

Task id and title: LIP032.30, "Choose one flow and one limiting probability" (node LIP032,
contractibility of the minimizer set; conditional on the interface binding of LIP032.29 and on the
positive-rate flow context of LIP031).

## Provides
* `DGPS.Frontier.LIP032.lip032_30_choose_one_flow_one_limiting_probability` : MAIN. For a fixed
  minimizer `μ` and the exact flow context of LIP031, there are two functions `u` and `R` on the
  `L²(m)` classes such that, for every minimizer `ν` and `s ∈ [0,1]`, with `c = [f_{ν,s}]`:
  `u c` is a global probability flow started from `c`, `R c` is a free-energy minimizer, and
  `∫ (u c t) φ dm → ∫ φ d(R c)` as `t → +∞` for every continuous `φ`.
* `DGPS.Frontier.LIP032.choose_flow_limit_LIP03230` (helper) : for one initial class with some
  global probability flow, a flow and a limiting minimizer with the displayed convergence exist.

## R5 notes
* Hypotheses. The statement of the unit says to apply LIP031 "with the exact fixed inputs in
  Section 2.1" of the node, so the positive-rate context is inherited by the unit itself and is
  taken as binders, exactly as in LIP031: `A`, `drift : AbsoluteDrift A`, `G`, `B`, `g`, `β`,
  `h_MF : MeanFieldData G B g β`, `h_V : IsWeakGradient A.V G`, `h_WB` (the a.e. `IsWeakGradientLp ∞`
  hypothesis), a real `r`, `h_r : 0 < r` and `h_rate : ENNReal.ofReal r < scalarRate A drift`.
  The unconditional reading of the frozen contractibility sentence (FD-001) is not claimed and not
  strengthened; the present theorem is only the conditional existence-of-choices statement.
* Omitted binders. `LipschitzData A` and `0 < d` appear in Section 2.1 but are not needed by any
  declaration used here (LIP032.22 and LIP032.27 obtain the density bounds without them). They are
  not added as unused hypotheses; the theorem is therefore a formal generalization of the spec'd
  version, never a strengthening of any listed hypothesis.
* Bounds `M_V`, `M_W` are not binders: they come from LIP032.27 (`..._bounds_exists`), as in
  LIP032.29. The membership `ν ∈ S` is the extended-real equation `freeEnergy A ν =
  freeEnergyMinimum A`, as in LIP032.22, .23, .28, .29. The fixed `μ ∈ S` is likewise a binder.
* Indexing by class. The choices are functions `u : L2s d → ℝ → L2s d` and
  `R : L2s d → ProbabilityMeasure (Torus d)` of the initial class `c : L2s d` (not of a pair
  `(ν, s)` and not of a representative), so equal classes automatically receive the same choice.
  The conclusion quantifies over all `(ν, s)` with `ν ∈ S`, `s ∈ [0,1]` and speaks about
  `c = l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)`. Values of the choice functions off the
  family `I` are junk (chosen arbitrarily) and unused.
* The choice is made for classes that have some global probability flow for `h_MF`
  (a class not in `I` may have none; then a default value is used). For every class in `I` the
  existence is LIP028 applied through LIP032.23, as in `..._flow_exists` of LIP032.29.
* `R c ∈ S` is read as `freeEnergy A (R c) = freeEnergyMinimum A`, the conclusion of LIP031.
  Convergence is `Tendsto (fun t => ∫ x, u c t x * φ x ∂haar d) atTop (𝓝 (∫ x, φ x ∂(R c)))` for
  every continuous `φ : Torus d → ℝ`, exactly as in LIP031; the integral `∫ u(t) φ dm` of the
  statement is the pairing of the `L²` class with `φ`. No continuity or measurability of
  `c ↦ (u c, R c)` is claimed (Task 31 and Task 38).
* The auxiliary dissipation function of LIP031 is discarded.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- Helper: for one initial class `c` that has a global probability flow, choose a flow from
`c` and a limiting free-energy minimizer with the displayed convergence. -/
theorem choose_flow_limit_LIP03230 (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d,
      IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    (c : DGPS.Lipschitz.L2s d)
    (hex : ∃ u : ℝ → DGPS.Lipschitz.L2s d, DGPS.Lipschitz.IsGlobalProbFlow hMF c u) :
    ∃ (u : ℝ → DGPS.Lipschitz.L2s d) (R : ProbabilityMeasure (Torus d)),
      DGPS.Lipschitz.IsGlobalProbFlow hMF c u ∧
      freeEnergy A R = freeEnergyMinimum A ∧
      ∀ φ : Torus d → ℝ, Continuous φ →
        Tendsto (fun t : ℝ => ∫ x, u t x * φ x ∂haar d) atTop
          (𝓝 (∫ x, φ x ∂(R : Measure (Torus d)))) := by
  obtain ⟨u, hu⟩ := hex
  obtain ⟨-, R, -, -, -, -, -, -, -, hRmin, hRlim, -⟩ :=
    DGPS.Lipschitz.positive_rate_flow_tails_and_limiting_minimizer A drift hMF hV hWB hr hrate hu
  exact ⟨u, R, hu, hRmin, hRlim⟩

/-- **LIP032.30.** Choose one flow and one limiting probability for every initial class
`[f_{ν,s}]`, `ν ∈ S`, `s ∈ [0,1]`, as functions of the class: a global probability flow `u c`
started from `c`, and a minimizer `R c` with `∫ (u c t) φ dm → ∫ φ d(R c)` for continuous `φ`. -/
theorem lip032_30_choose_one_flow_one_limiting_probability (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d,
      IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A) :
    ∃ (u : DGPS.Lipschitz.L2s d → ℝ → DGPS.Lipschitz.L2s d)
      (R : DGPS.Lipschitz.L2s d → ProbabilityMeasure (Torus d)),
      ∀ (ν : ProbabilityMeasure (Torus d)), freeEnergy A ν = freeEnergyMinimum A →
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
                ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) : Measure (Torus d)))) := by
  classical
  have key : ∀ c : DGPS.Lipschitz.L2s d,
      ∃ (u : ℝ → DGPS.Lipschitz.L2s d) (R : ProbabilityMeasure (Torus d)),
        (∃ u' : ℝ → DGPS.Lipschitz.L2s d, DGPS.Lipschitz.IsGlobalProbFlow hMF c u') →
        DGPS.Lipschitz.IsGlobalProbFlow hMF c u ∧
        freeEnergy A R = freeEnergyMinimum A ∧
        ∀ φ : Torus d → ℝ, Continuous φ →
          Tendsto (fun t : ℝ => ∫ x, u t x * φ x ∂haar d) atTop
            (𝓝 (∫ x, φ x ∂(R : Measure (Torus d)))) := by
    intro c
    by_cases hex : ∃ u' : ℝ → DGPS.Lipschitz.L2s d, DGPS.Lipschitz.IsGlobalProbFlow hMF c u'
    · obtain ⟨u, R, h⟩ := choose_flow_limit_LIP03230 A drift hMF hV hWB hr hrate c hex
      exact ⟨u, R, fun _ => h⟩
    · exact ⟨fun _ => 0, μ, fun h => absurd h hex⟩
  choose u R hch using key
  refine ⟨u, R, fun ν hν s hs0 hs1 => hch _ ?_⟩
  exact gate_lip032_29_initial_value_flowgap_definition_binding_flow_exists A μ hμ ν hν s hs0 hs1
    hMF

end DGPS.Frontier.LIP032
