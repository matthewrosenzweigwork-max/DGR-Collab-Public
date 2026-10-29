import DGPS.Frontier.LIP032.T37

/-!
# LIP032.08: Difference estimate for limiting tests

Task id and title: LIP032.08, "Difference estimate for limiting tests" (node LIP032, contractibility
of the minimizer set; the difference estimate for the limit map `R` of the interpolation densities,
conditional on the Task 29 bindings and on the positive-rate flow context of LIP031, inherited
through LIP032.37).

## Provides
* `DGPS.Frontier.LIP032.lip032_08_difference_estimate_limiting_tests` : MAIN. Under the exact
  positive-rate context of LIP031, a fixed minimizer `μ`, and bounds `|A.V| ≤ M_V`, `|A.W| ≤ M_W`,
  there is a choice function `R` on the `L²(m)` classes such that, for all minimizers `ν₁, ν₂`, all
  `s₁, s₂ ∈ [0,1]`, every `L ≥ 0`, every `L`-Lipschitz `φ` and every `t ≥ 0`, with
  `c_i = [f_{ν_i,s_i}]` and `f_i = f_{ν_i,s_i}`,
  `|∫ φ d(R c₁) - ∫ φ d(R c₂)| ≤ 2 L K e^{-rt} + ‖φ‖∞ Σ(t) ‖f₁ - f₂‖₁`, where
  `K = √(2 G_0 / r)`, `G_0 = log C + 2 M_V + M_W`, `C = exp (2 (M_V + M_W))`,
  `Σ(t) = 2 exp (2π d (g+3β)² t)`, `‖φ‖∞ = ⨆ x, |φ x|` and `‖f₁ - f₂‖₁ = ∫ |f₁ - f₂| dm`.

## R5 notes
* Route. The conclusion is exactly the conclusion of LIP032.37, and the proof is the single term
  that applies `lip032_37_difference_limiting_tests` to the same binders. The two tail terms and the
  middle term of the Task 08 proof sketch are supplied by LIP032.37 and its prerequisites
  (LIP032.35 and LIP032.36); nothing is reproved here.
* Inherited hypotheses. The binders `A`, `drift`, `G`, `B`, `g`, `β`, `hMF`, `hV`, `hWB`, `r`,
  `hr`, `hrate`, `μ`, `hμ`, `M_V`, `M_W`, `hVb`, `hWb` are exactly those of LIP032.37 (and hence of
  LIP032.35 and LIP032.32). Nothing is added and nothing is removed. The unconditional reading of the
  frozen contractibility sentence is neither claimed nor strengthened here (FD-001): the positive-rate
  hypotheses `hr` and `hrate` are present, as in LIP031.
* Interpolation densities. The Task 08 sentence "for interpolation densities `f, f̃`" is read as
  `f = f_{ν₁,s₁}` and `f̃ = f_{ν₂,s₂}` with `ν₁, ν₂` minimizers (the equation
  `freeEnergy A ν = freeEnergyMinimum A`) and `s₁, s₂ ∈ [0,1]`, as in LIP032.37. The classes are
  `l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)`.
* Choice function. The conclusion is existential over `R` only, as in LIP032.37. The Task 08
  sentence mentions the limit map `R(f)` alone, and the flow `u` of LIP032.32 does not appear in the
  statement, so the existential over `R` is the faithful reading.
* The limit map. `R(f)(φ)` is `∫ x, φ x ∂(R c : Measure (Torus d))`, as in LIP032.37.
* Tests. "`L`-Lipschitz" is `TorusLipschitzWith L` for the Euclidean quotient distance, with only
  `0 ≤ L` assumed. Continuity of `φ` is derived inside LIP032.37.
* Sup norm and norm. `‖φ‖∞` is read as `⨆ x, |φ x|`, and `‖f₁ - f₂‖₁` as the real integral
  `∫ |f₁ x - f₂ x| dm` of the continuous interpolation densities, as in LIP032.37.
* Constant. `K` is written literally as `Real.sqrt (2 * G_0 / r)` with the explicit `G_0`, and the
  middle factor is the LIP028 factor `Σ(t)` with the drift-bound parameter `g` kept distinct from the
  initial density variable, which is the density `f_{ν,s}` and never `g`.
* Case `L = 0`. No separate case is needed; it is covered by LIP032.37.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- **LIP032.08.** Difference estimate for limiting tests: under the positive-rate context of LIP031
and for a fixed minimizer `μ`, there is a limit map `R` such that for every pair of minimizers
`ν₁, ν₂`, every `s₁, s₂ ∈ [0,1]`, every `L ≥ 0`, every `L`-Lipschitz `φ` and every `t ≥ 0`,
`|∫ φ d(R c₁) - ∫ φ d(R c₂)| ≤ 2 L K e^{-rt} + ‖φ‖∞ Σ(t) ‖f₁ - f₂‖₁`, with `c_i = [f_{ν_i,s_i}]`. -/
theorem lip032_08_difference_estimate_limiting_tests (A : InteractionData d)
    (drift : AbsoluteDrift A)
    {G : Torus d → Tangent d} {B : Torus d → Torus d → Tangent d} {g β : ℝ}
    (hMF : DGPS.Lipschitz.MeanFieldData G B g β)
    (hV : IsWeakGradient A.V G)
    (hWB : ∀ᵐ y ∂haar d, IsWeakGradientLp ⊤ (fun x => A.W x y) (fun x => B x y))
    {r : ℝ} (hr : 0 < r) (hrate : ENNReal.ofReal r < scalarRate A drift)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (M_V M_W : ℝ) (hVb : ∀ x, |A.V x| ≤ M_V) (hWb : ∀ x y, |A.W x y| ≤ M_W) :
    ∃ (R : DGPS.Lipschitz.L2s d → ProbabilityMeasure (Torus d)),
      ∀ (ν₁ ν₂ : ProbabilityMeasure (Torus d)), freeEnergy A ν₁ = freeEnergyMinimum A →
        freeEnergy A ν₂ = freeEnergyMinimum A →
        ∀ s₁ s₂ : ℝ, 0 ≤ s₁ → s₁ ≤ 1 → 0 ≤ s₂ → s₂ ≤ 1 →
        ∀ L : ℝ, 0 ≤ L → ∀ φ : Torus d → ℝ, TorusLipschitzWith L φ →
        ∀ t : ℝ, 0 ≤ t →
          |∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₁ s₁)) :
                Measure (Torus d)) -
              ∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν₂ s₂)) :
                Measure (Torus d))| ≤
            2 * L * Real.sqrt (2 * (Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W) / r) *
                Real.exp (-(r * t)) +
              (⨆ x, |φ x|) * (2 * Real.exp (2 * Real.pi * (d : ℝ) * (g + 3 * β) ^ 2 * t)) *
                ∫ x, |interpolDensity_LIP03222 A μ ν₁ s₁ x - interpolDensity_LIP03222 A μ ν₂ s₂ x|
                  ∂haar d :=
  lip032_37_difference_limiting_tests A drift hMF hV hWB hr hrate μ hμ M_V M_W hVb hWb

end DGPS.Frontier.LIP032
