import DGPS.Frontier.LIP032.T28
import DGPS.Frontier.LIP032.T29
import DGPS.Frontier.LIP032.T30
import DGPS.Lipschitz.MinimizerRetraction

/-!
# LIP032.32: Uniform tail with one constant

Task id and title: LIP032.32, "Uniform tail with one constant" (node LIP032, contractibility of the
minimizer set; conditional on the flow binding of LIP032.29, the choice of Task 30 and the
positive-rate flow context of LIP031).

## Provides
* `DGPS.Frontier.LIP032.lip032_32_uniform_tail_one_constant` : MAIN. Under the exact positive-rate
  context of LIP031, a fixed minimizer `μ`, and bounds `|A.V| ≤ M_V`, `|A.W| ≤ M_W`, there are
  choice functions `u` and `R` on the `L²(m)` classes such that, for every minimizer `ν`, every
  `s ∈ [0,1]` and `c = [f_{ν,s}]`: `u c` is a global probability flow started from `c`, `R c` is a
  free-energy minimizer, `∫ (u c t) φ dm → ∫ φ d(R c)` for continuous `φ`, and for every one-Lipschitz
  `φ` and `t ≥ 0`, `|∫ (u c t) φ dm - ∫ φ d(R c)| ≤ K e^{-rt}` with the single constant
  `K = √(2 G_0 / r)`, `G_0 = log C + 2 M_V + M_W`, `C = exp (2 (M_V + M_W))`.

## R5 notes
* Positive-rate context. The statement of the unit says to apply LIP031 with "the exact fixed
  inputs in Section 2.1" of the node. These are inherited, exactly as in LIP030, and taken as
  binders: `A`, `drift : AbsoluteDrift A`, `G`, `B`, `g`, `β`, `hMF : MeanFieldData G B g β`,
  `hV : IsWeakGradient A.V G`, `hWB` (the a.e. `IsWeakGradientLp ⊤` hypothesis), a real `r`,
  `hr : 0 < r`, and `hrate : ENNReal.ofReal r < scalarRate A drift`. The unconditional reading of
  the frozen contractibility sentence (FD-001) is neither claimed nor strengthened here.
* Omitted binders. `LipschitzData A` and `0 < d` appear in Section 2.1 but no declaration used here
  needs them, as in LIP030; they are not added.
* Bounds `M_V`, `M_W`. The specification says "choose bounds `M_V, M_W ≥ 0` with `|A.V| ≤ M_V`,
  `|A.W| ≤ M_W`" and then defines `G_0` from them. Here they are binders `hVb`, `hWb`, so the
  conclusion holds for every admissible choice, in particular the chosen one. Admissibility is not
  required to be nonnegative (no such sign is used). The existence of such bounds is LIP032.27 and
  is not needed as a hypothesis for the proof.
* The family `I`. Read as the classes `[f_{ν,s}]` with `ν ∈ S` (the extended equation
  `freeEnergy A ν = freeEnergyMinimum A`) and `s ∈ [0,1]`, the parametrization used by LIP030.
  `[·]` is `l2Class_LIP03223` and `f_{ν,s}` is `interpolDensity_LIP03222 A μ ν s`.
* Witnesses. The unit says to apply LIP031 "to the witnesses selected in Task 30". The conclusion
  is therefore existential over the choice functions `(u, R)` and carries the Task 30 properties
  (flow, minimality, convergence) together with the tail bound. The tail is proved by applying
  LIP031 to the flow `u c` with its own limit `R₃₁`; `R₃₁` and `R c` agree on continuous tests
  because both are limits of the same function `t ↦ ∫ u c t φ dm` (uniqueness of limits), and
  one-Lipschitz tests are continuous. So the tail holds for the `R c` of Task 30, and by the same
  argument for any choice that satisfies the Task 30 properties.
* One-Lipschitz tests. "One-Lipschitz real `φ`" is read as `TorusLipschitzWith 1 φ` for the
  Euclidean quotient distance, as in LIP031.
* Pairings. `∫ u(t) φ dm` is `∫ x, u c t x * φ x ∂haar d`, the pairing of the `L²` class with
  `φ`, as in LIP030 and LIP031. `R(f)(φ)` is `∫ x, φ x ∂(R c : Measure (Torus d))`.
* Constant. `K` is written literally as `Real.sqrt (2 * G_0 / r)` with
  `G_0 = Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W`, the same expression as in
  LIP032.28. The constant depends only on `M_V`, `M_W`, `r`; it is uniform over `ν`, `s`, `φ`, `t`.
  The factor `e^{-rt}` is placed on the right of `K`.
* Time. Only `t ≥ 0` is claimed, as in the statement. The flow gap at `t = 0` is the initial
  gap of LIP032.29, bounded by LIP032.28 (`0 ≤ E f - E q ≤ G_0`); the upper bound is the only
  place where `G_0` enters.
* Monotonicity step. `2 * flowGap / r ≤ 2 * G_0 / r` uses `r > 0`, and square-root monotonicity
  gives the bound by `K`. This is the square-root step identified as the main difficulty in the
  specification.
* The auxiliary dissipation function of LIP031 is discarded.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- **LIP032.32.** Uniform tail with one constant: for the choice functions of Task 30 and every
minimizer `ν`, `s ∈ [0,1]` and one-Lipschitz `φ`, the tail `|∫ (u c t) φ dm - ∫ φ d(R c)|` is at most
`K e^{-rt}` for `t ≥ 0`, with `K = √(2 G_0 / r)`, `c = [f_{ν,s}]`. -/
theorem lip032_32_uniform_tail_one_constant (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (M_V M_W : ℝ) (hVb : ∀ x, |A.V x| ≤ M_V) (hWb : ∀ x y, |A.W x y| ≤ M_W) :
    ∃ (u : DGPS.Lipschitz.L2s d → ℝ → DGPS.Lipschitz.L2s d)
      (R : DGPS.Lipschitz.L2s d → ProbabilityMeasure (Torus d)),
      ∀ (ν : ProbabilityMeasure (Torus d)), freeEnergy A ν = freeEnergyMinimum A →
        ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
          DGPS.Lipschitz.IsGlobalProbFlow hMF
              (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))
              (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) ∧
          freeEnergy A (R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) =
            freeEnergyMinimum A ∧
          (∀ φ : Torus d → ℝ, Continuous φ →
            Tendsto (fun t : ℝ =>
                ∫ x, u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) t x * φ x ∂haar d)
              atTop
              (𝓝 (∫ x, φ x
                ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) :
                  Measure (Torus d))))) ∧
          (∀ φ : Torus d → ℝ, TorusLipschitzWith 1 φ → ∀ t : ℝ, 0 ≤ t →
            |∫ x, u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) t x * φ x ∂haar d -
                ∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) :
                  Measure (Torus d))| ≤
              Real.sqrt (2 * (Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W) / r) *
                Real.exp (-(r * t))) := by
  obtain ⟨u, R, hch⟩ :=
    lip032_30_choose_one_flow_one_limiting_probability A drift hMF hV hWB hr hrate μ hμ
  refine ⟨u, R, fun ν hν s hs0 hs1 => ?_⟩
  obtain ⟨hflow, hmin, hconv⟩ := hch ν hν s hs0 hs1
  refine ⟨hflow, hmin, hconv, fun φ hφ t ht => ?_⟩
  have hφc : Continuous φ := DGPS.Lipschitz.torusLipschitz_continuous hφ
  -- the tail inequalities of LIP031 for this flow, with its own limit `R₃₁`
  obtain ⟨-, R₃₁, -, -, -, -, -, -, -, -, hconv₃₁, htail⟩ :=
    DGPS.Lipschitz.positive_rate_flow_tails_and_limiting_minimizer A drift hMF hV hWB hr hrate
      hflow
  -- the limit is determined by the flow: both limits of `t ↦ ∫ u t φ dm` coincide
  have heq : ∫ x, φ x ∂(R₃₁ : Measure (Torus d)) =
      ∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) :
        Measure (Torus d)) :=
    tendsto_nhds_unique (hconv₃₁ φ hφc) (hconv φ hφc)
  -- the initial gap is `E(f_{ν,s}) - E(p_μ)`, which lies in `[0, G_0]`
  have hfg := (gate_lip032_29_initial_value_flowgap_definition_binding A μ hμ ν hν s hs0 hs1 hMF
    _ hflow).2
  obtain ⟨-, -, hlow, hup⟩ :=
    lip032_28_real_free_energy_uniform_gap A M_V M_W hVb hWb μ hμ ν hν s hs0 hs1
  have hgap0 : DGPS.Lipschitz.flowGap A
      (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) 0 ≤
        Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W := by
    rw [hfg]
    linarith
  -- square-root monotonicity with the single constant `K`
  have hsq : Real.sqrt (2 * DGPS.Lipschitz.flowGap A
      (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) 0 / r) ≤
        Real.sqrt (2 * (Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W) / r) := by
    apply Real.sqrt_le_sqrt
    have h2 : 2 * DGPS.Lipschitz.flowGap A
        (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) 0 ≤
          2 * (Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W) := by
      linarith
    exact div_le_div_of_nonneg_right h2 hr.le
  obtain ⟨h1, h2⟩ := htail φ hφ t ht
  have hexp : 0 ≤ Real.exp (-(r * t)) := (Real.exp_pos _).le
  rw [heq] at h1
  calc _ ≤ Real.sqrt (2 * DGPS.Lipschitz.flowGap A
            (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) t / r) := h1
    _ ≤ Real.exp (-(r * t)) * Real.sqrt (2 * DGPS.Lipschitz.flowGap A
            (u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) 0 / r) := h2
    _ ≤ Real.exp (-(r * t)) * Real.sqrt (2 * (Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W)
            / r) := mul_le_mul_of_nonneg_left hsq hexp
    _ = _ := mul_comm _ _

end DGPS.Frontier.LIP032
