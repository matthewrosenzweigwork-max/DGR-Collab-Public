import DGPS.Frontier.LIP032.T31
import DGPS.Frontier.LIP032.T32

/-!
# LIP032.06: Chosen flows and unique minimizing limits

Task id and title: LIP032.06, "Chosen flows and unique minimizing limits" (node LIP032,
contractibility of the minimizer set; conditional on the flow binding of LIP032.29, the choice of
Task 30, the uniqueness of Task 31, the uniform tail of Task 32, and the positive-rate flow context
of LIP031).

## Provides
* `DGPS.Frontier.LIP032.lip032_06_chosen_flows_unique_minimizing_limits` : MAIN. Under the exact
  positive-rate context of LIP031, a fixed minimizer `μ` and bounds `|A.V| ≤ M_V`, `|A.W| ≤ M_W`,
  there are choice functions `u` and `R` on the `L²(m)` classes such that, for every minimizer `ν`,
  every `s ∈ [0,1]` and `c = [f_{ν,s}]`:
  (a) `u c` is a global probability flow of the mean-field model started from `c`;
  (b) `R c` is a free-energy minimizer and `∫ (u c t) φ dm → ∫ φ d(R c)` for every continuous `φ`;
  (c) for every one-Lipschitz `φ` and `t ≥ 0`, `|∫ (u c t) φ dm - ∫ φ d(R c)| ≤ K e^{-rt}` with the
  single constant `K = √(2 G_0 / r)`, `G_0 = log C + 2 M_V + M_W`, `C = exp (2 (M_V + M_W))`;
  (d) any two global probability flows from `c` agree at every `t ≥ 0`;
  (e) any global probability flow `v` from `c` whose weak limit along continuous tests is a
  free-energy minimizer `R'` has `R' = R c`, so the limiting probability is determined by `c`.

## R5 notes
* Positive-rate context. The unit inherits the fixed inputs of Section 2.1 of the node, exactly as
  LIP032.30 and LIP032.32 do, and takes them as binders: `A`, `drift : AbsoluteDrift A`, `G`, `B`,
  `g`, `β`, `hMF : MeanFieldData G B g β`, `hV : IsWeakGradient A.V G`, `hWB` (the a.e.
  `IsWeakGradientLp ⊤` hypothesis), a real `r`, `hr : 0 < r` and `hrate : ENNReal.ofReal r <
  scalarRate A drift`. No positive-rate hypothesis is added beyond these, and none is removed.
* Unconditional reading (FD-001). The unconditional reading of the frozen contractibility sentence
  is neither claimed nor strengthened. The present theorem is the conditional statement on the
  chosen flows and limits; it is not a proof of contractibility.
* Bounds. `M_V`, `M_W` are binders `hVb`, `hWb` (the specification says "choose bounds"), so the
  conclusion holds for every admissible choice, as in LIP032.32. Their existence is LIP032.27 and is
  not needed as a hypothesis here. The constant `K` is written inline with the same expression as in
  LIP032.32 and LIP032.28; it depends only on `M_V`, `M_W`, `r`, and is uniform over `ν`, `s`, `φ`
  and `t`.
* Fixed minimizer. `μ` with `freeEnergy A μ = freeEnergyMinimum A` is a binder, and it defines the
  interpolation family `[f_{ν,s}] = l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)`.
* Family. The minimizers `ν ∈ S` are read as the extended-real equations
  `freeEnergy A ν = freeEnergyMinimum A`, and `s` ranges over `0 ≤ s ≤ 1`, as in LIP032.30.
* Chosen flows and limits. The choices are functions of the class `c : L2s d`, not of a pair
  `(ν, s)`, so equal classes receive equal choices. Values off the family are junk and unused.
  Continuity of `c ↦ (u c, R c)` is not claimed.
* Global probability flow. "Flow" is read as `IsGlobalProbFlow hMF c u`, the LIP028 notion, with
  the same mean-field data for every flow in the statement.
* "Uniquely determined" in clause (e) is read as: every free-energy minimizer that is the weak limit
  along continuous tests of some global probability flow from `c` equals the chosen `R c`. Clause
  (d) is read as: any two global probability flows from `c` agree for every `t ≥ 0`, not only for
  the chosen one. Equality is claimed only for nonnegative times; no value at negative times is
  compared.
* One-Lipschitz tests. "One-Lipschitz real `φ`" is read as `TorusLipschitzWith 1 φ` for the
  Euclidean quotient distance, as in LIP031 and LIP032.32.
* Pairings. `∫ u(t) φ dm` is `∫ x, u c t x * φ x ∂haar d`, the pairing of the `L²` class with `φ`;
  the limit is `∫ φ d(R c)` as in LIP031.
* Witnesses. Clauses (a), (b), (c) are the conclusion of LIP032.32 (which carries the Task 30
  choice and the Task 31 limit identification); clauses (d), (e) are the uniqueness statement of
  LIP032.31 applied to the chosen flow `u c` and to the chosen limit `R c`.
* The auxiliary dissipation function of LIP031 is discarded.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- **LIP032.06.** Chosen flows and unique minimizing limits: for every minimizer `ν`, every
`s ∈ [0,1]` and `c = [f_{ν,s}]`, there are a global probability flow `u c` from `c`, a free-energy
minimizer `R c` that is its weak limit with the tail bound `K e^{-rt}` for one-Lipschitz tests, all
global probability flows from `c` agree for `t ≥ 0`, and `R c` is the only minimizing limit of any
flow from `c`. -/
theorem lip032_06_chosen_flows_unique_minimizing_limits (A : InteractionData d)
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
                Real.exp (-(r * t))) ∧
          (∀ v w : ℝ → DGPS.Lipschitz.L2s d,
            DGPS.Lipschitz.IsGlobalProbFlow hMF
                (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) v →
            DGPS.Lipschitz.IsGlobalProbFlow hMF
                (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) w →
            ∀ t : ℝ, 0 ≤ t → v t = w t) ∧
          (∀ (v : ℝ → DGPS.Lipschitz.L2s d) (R' : ProbabilityMeasure (Torus d)),
            DGPS.Lipschitz.IsGlobalProbFlow hMF
                (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) v →
            freeEnergy A R' = freeEnergyMinimum A →
            (∀ φ : Torus d → ℝ, Continuous φ →
              Tendsto (fun t : ℝ => ∫ x, v t x * φ x ∂haar d) atTop
                (𝓝 (∫ x, φ x ∂(R' : Measure (Torus d))))) →
            R' = R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s))) := by
  obtain ⟨u, R, hall⟩ :=
    lip032_32_uniform_tail_one_constant A drift hMF hV hWB hr hrate μ hμ M_V M_W hVb hWb
  refine ⟨u, R, fun ν hν s hs0 hs1 => ?_⟩
  obtain ⟨hflow, hmin, hconv, htail⟩ := hall ν hν s hs0 hs1
  refine ⟨hflow, hmin, hconv, htail, ?_, ?_⟩
  · intro v w hvf hwf t ht
    exact (lip032_31_nonnegative_time_uniqueness_limit_uniqueness A drift hMF hV hWB hr hrate
      hvf hwf).1 t ht
  · intro v R' hvf hR'min hR'lim
    exact (lip032_31_nonnegative_time_uniqueness_limit_uniqueness A drift hMF hV hWB hr hrate
      hflow hvf).2 _ R' hmin hR'min hconv hR'lim |>.symm

end DGPS.Frontier.LIP032
