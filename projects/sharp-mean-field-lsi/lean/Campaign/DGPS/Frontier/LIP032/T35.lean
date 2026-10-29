import DGPS.Frontier.LIP032.T32

/-!
# LIP032.35: Scale the tail to every Lipschitz test

Task id and title: LIP032.35, "Scale the tail to every Lipschitz test" (node LIP032, contractibility
of the minimizer set; conditional on the flow binding of LIP032.29, the choice of Task 30, the
uniform tail with one constant of Task 32, and the positive-rate flow context of LIP031).

## Provides
* `DGPS.Frontier.LIP032.lip032_35_scale_tail_lipschitz_test` : MAIN. Under the exact positive-rate
  context of LIP031, a fixed minimizer `μ`, and bounds `|A.V| ≤ M_V`, `|A.W| ≤ M_W`, there are
  choice functions `u` and `R` on the `L²(m)` classes such that, for every minimizer `ν`, every
  `s ∈ [0,1]` and `c = [f_{ν,s}]`, every `L ≥ 0`, every `L`-Lipschitz `φ` and every `t ≥ 0`,
  `|∫ (u c t) φ dm - ∫ φ d(R c)| ≤ L K e^{-rt}` with the single constant
  `K = √(2 G_0 / r)`, `G_0 = log C + 2 M_V + M_W`, `C = exp (2 (M_V + M_W))`.
* `DGPS.Frontier.LIP032.scaled_tail_bound_LIP03235` (helper) : for a function `ρ` and a measure `ν'`,
  a uniform bound `K'` for the tail against one-Lipschitz tests yields the bound `L K'` against
  `L`-Lipschitz tests, for every `L ≥ 0`.

## R5 notes
* Positive-rate context. The unit inherits the context of Task 32, which is inherited from Task 30
  and LIP031. It is taken as binders exactly as in LIP032.32: `A`, `drift : AbsoluteDrift A`, `G`,
  `B`, `g`, `β`, `hMF : MeanFieldData G B g β`, `hV : IsWeakGradient A.V G`, `hWB` (the a.e.
  `IsWeakGradientLp ⊤` hypothesis), a real `r`, `hr : 0 < r`, and
  `hrate : ENNReal.ofReal r < scalarRate A drift`. No positivity or flow hypothesis is added, and
  the unconditional reading of the frozen contractibility sentence (FD-001) is neither claimed nor
  strengthened here.
* Bounds `M_V`, `M_W`. They are binders `hVb`, `hWb`, as in LIP032.32, so the conclusion holds for
  every admissible choice. Admissibility is not required to be nonnegative.
* The family `I`. Read as the classes `[f_{ν,s}]` with `ν` a minimizer (`freeEnergy A ν =
  freeEnergyMinimum A`) and `s ∈ [0,1]`, indexed by the pair `(ν, s)`, as in LIP032.30 and
  LIP032.32. `[·]` is `l2Class_LIP03223` and `f_{ν,s}` is `interpolDensity_LIP03222 A μ ν s`.
* Choice functions. The conclusion is existential over `(u, R)`, as in LIP032.32. The tail is
  obtained from the tail of LIP032.32 for these same `u` and `R`; the flow and minimizer conjuncts
  of LIP032.32 are not repeated in the conclusion, since the unit states only the tail bound.
* One-Lipschitz tests. "One-Lipschitz" is `TorusLipschitzWith 1` for the Euclidean quotient
  distance, and "`L`-Lipschitz" is `TorusLipschitzWith L` for the same distance, as in LIP031 and
  LIP032.32. Only `0 ≤ L` is assumed; this is the range asked for by the unit.
* Constant. `K` is written literally as `Real.sqrt (2 * G_0 / r)` with
  `G_0 = Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W`, as in LIP032.32. The product
  `L * K * e^{-rt}` is written with `L` on the left, and it is uniform over `ν`, `s`, `φ`, `t`.
* Pairings. `∫ u(t) φ dm` is `∫ x, u c t x * φ x ∂haar d`, and `∫ φ d(R c)` is
  `∫ x, φ x ∂(R c : Measure (Torus d))`, as in LIP032.32.
* Case `L > 0`. The test `L⁻¹ • φ` is one-Lipschitz; scaling the tail bound by `L` gives the claim.
* Case `L = 0`. The test `φ` is constant, but this is not used. For every real `c` with
  `|c| · 0 ≤ 1` the test `c • φ` is one-Lipschitz, so `|c| · D ≤ K'` for `D` the left-hand side
  and `K' = K e^{-rt}`. If `D > 0`, the choice `c = (K' + 1) / D` gives `K' + 1 ≤ K'`, a
  contradiction. Hence `D ≤ 0`, which is the claim for `L = 0`. No unverified mass clause for the
  flow is used.
* Integrability. None is needed: `integral_const_mul` is unconditional, and the scaled integrals
  are handled by linearity alone.
-/

open MeasureTheory Filter Topology

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- Helper for LIP032.35: a uniform tail bound `K'` against one-Lipschitz tests yields the bound
`L * K'` against `L`-Lipschitz tests, for every `L ≥ 0`. The case `L = 0` uses the rescaling by an
arbitrary real constant and a contradiction; the case `L > 0` rescales by `L⁻¹`. -/
theorem scaled_tail_bound_LIP03235 (ρ : Torus d → ℝ) (ν' : Measure (Torus d)) {K' : ℝ}
    (hK : 0 ≤ K')
    (htail : ∀ ψ : Torus d → ℝ, TorusLipschitzWith 1 ψ →
      |∫ x, ρ x * ψ x ∂haar d - ∫ x, ψ x ∂ν'| ≤ K')
    {L : ℝ} (hL : 0 ≤ L) (φ : Torus d → ℝ) (hφ : TorusLipschitzWith L φ) :
    |∫ x, ρ x * φ x ∂haar d - ∫ x, φ x ∂ν'| ≤ L * K' := by
  have hscale : ∀ c : ℝ, |c| * L ≤ 1 →
      |c| * |∫ x, ρ x * φ x ∂haar d - ∫ x, φ x ∂ν'| ≤ K' := by
    intro c hc
    have h1 : TorusLipschitzWith 1 (fun x => c * φ x) := by
      intro x y
      have hd : 0 ≤ torusDist x y := Real.sqrt_nonneg _
      calc |c * φ x - c * φ y| = |c| * |φ x - φ y| := by
            rw [← mul_sub, abs_mul]
        _ ≤ |c| * (L * torusDist x y) := mul_le_mul_of_nonneg_left (hφ x y) (abs_nonneg _)
        _ = (|c| * L) * torusDist x y := by ring
        _ ≤ 1 * torusDist x y := mul_le_mul_of_nonneg_right hc hd
    have h2 : |∫ x, ρ x * (c * φ x) ∂haar d - ∫ x, c * φ x ∂ν'| ≤ K' :=
      htail (fun x => c * φ x) h1
    have e1 : ∫ x, ρ x * (c * φ x) ∂haar d = c * ∫ x, ρ x * φ x ∂haar d := by
      rw [← integral_const_mul]
      congr 1
      funext x
      ring
    have e2 : ∫ x, c * φ x ∂ν' = c * ∫ x, φ x ∂ν' := integral_const_mul _ _
    rw [e1, e2, ← mul_sub, abs_mul] at h2
    exact h2
  rcases hL.eq_or_lt with h0 | hpos
  · subst h0
    have fact : ∀ D : ℝ, 0 ≤ D → (∀ c : ℝ, |c| * D ≤ K') → D ≤ 0 := by
      intro D hD hall
      by_contra hneg
      have hDpos : 0 < D := not_le.mp hneg
      have hpos' : 0 < (K' + 1) / D := div_pos (by linarith) hDpos
      have h4 := hall ((K' + 1) / D)
      rw [abs_of_pos hpos', div_mul_cancel₀ _ hDpos.ne'] at h4
      linarith
    rw [zero_mul]
    exact fact _ (abs_nonneg _) (fun c => hscale c (by simp))
  · have hc : |L⁻¹| * L ≤ 1 := by
      rw [abs_inv, abs_of_pos hpos]
      exact (inv_mul_cancel₀ hpos.ne').le
    have h5 := hscale L⁻¹ hc
    rw [abs_inv, abs_of_pos hpos] at h5
    have h6 := mul_le_mul_of_nonneg_left h5 hpos.le
    rw [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul] at h6
    exact h6

/-- **LIP032.35.** Scale the tail to every Lipschitz test: for the choice functions of Task 32, every
minimizer `ν`, `s ∈ [0,1]`, `L ≥ 0`, every `L`-Lipschitz `φ` and every `t ≥ 0`, the tail
`|∫ (u c t) φ dm - ∫ φ d(R c)|` is at most `L K e^{-rt}` with `K = √(2 G_0 / r)` and `c = [f_{ν,s}]`. -/
theorem lip032_35_scale_tail_lipschitz_test (A : InteractionData d)
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
          ∀ L : ℝ, 0 ≤ L → ∀ φ : Torus d → ℝ, TorusLipschitzWith L φ →
            ∀ t : ℝ, 0 ≤ t →
              |∫ x, u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) t x * φ x ∂haar d -
                  ∫ x, φ x ∂(R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) :
                    Measure (Torus d))| ≤
                L * Real.sqrt (2 * (Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W) / r) *
                  Real.exp (-(r * t)) := by
  obtain ⟨u, R, h32⟩ :=
    lip032_32_uniform_tail_one_constant A drift hMF hV hWB hr hrate μ hμ M_V M_W hVb hWb
  refine ⟨u, R, fun ν hν s hs0 hs1 L hL φ hφ t ht => ?_⟩
  obtain ⟨-, -, -, htail⟩ := h32 ν hν s hs0 hs1
  refine le_of_le_of_eq
    (scaled_tail_bound_LIP03235
      (fun x => u (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) t x)
      (R (l2Class_LIP03223 (interpolDensity_LIP03222 A μ ν s)) : Measure (Torus d))
      (by positivity) (fun ψ hψ => htail ψ hψ t ht) hL φ hφ) (by ring)

end DGPS.Frontier.LIP032
