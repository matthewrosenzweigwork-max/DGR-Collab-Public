import DGPS.Frontier.LIP032.T18

/-!
# LIP032.01: Uniform Gibbs bounds

Task id and title: LIP032.01, "Uniform Gibbs bounds" (node LIP032, contractibility of the minimizer
set; leaf formalization, verification level V1). This is a pure density statement: no positive-rate
hypothesis is used.

## Provides
* `DGPS.Frontier.LIP032.lip032_01_uniform_gibbs_bounds_exists` : for every interaction data `A`
  there are reals `M_V, M_W ≥ 0` with `|A.V x| ≤ M_V` and `|A.W x y| ≤ M_W` for all `x, y`.
* `DGPS.Frontier.LIP032.lip032_01_uniform_gibbs_bounds` : for bounds `M_V, M_W` of `A.V` and `A.W`,
  with `B_0 = M_V + M_W`, `c = e^{-2 B_0}` and `C = e^{2 B_0}`: (i) every probability `ν` on `𝕋^d`
  has a continuous Gibbs density `p_ν = gibbsDensity A ν` with `∫ p_ν dm = 1` and
  `0 < c ≤ p_ν x ≤ C` for every `x`; (ii) every free-energy minimizer `ν` satisfies
  `μ_{p_ν} = ν`, where `μ_f = m.withDensity (ofReal ∘ f)`.

## R5 notes
* Hypotheses of the main statement: `A : InteractionData d` and reals `M_V`, `M_W` with the two
  pointwise bounds `hV`, `hW`. The specification says "choose bounds `M_V, M_W ≥ 0`"; the bounds are
  taken as universally quantified data, and their nonnegativity is not assumed (it follows from the
  bound at any point of the torus). The existence of such bounds is the separate lemma
  `..._exists`, which supplies them with nonnegativity.
* The bounds are chosen before `ν`, so the constants `c`, `C` are independent of `ν`.
* `p_ν` is the packet's `DGPS.Lipschitz.gibbsDensity A ν`, which unfolds to
  `e^{-(V + W*ν)} / ∫ e^{-(V + W*ν)} dm` with `(W*ν)(x) = ∫ A.W x y dν(y)`. This is the density of
  the specification with `U_ν = A.V + ∫ A.W(·,y) dν(y)`. Continuity, mass one and the two-sided bound
  are taken from LIP032.17 applied to `U_ν`, with bound `B_0 = M_V + M_W` from LIP032.16.
* `ν` in part (i) is a `Measure (Torus d)` with `[IsProbabilityMeasure ν]`, as in LIP032.16 and
  LIP032.18. The free-energy minimizer set `S` in part (ii) is formalized as
  `ν : ProbabilityMeasure (Torus d)` with `freeEnergy A ν = freeEnergyMinimum A`, exactly as in
  LIP017. Part (ii) is the LIP032.18 Gibbs bridge verbatim and uses no bound hypothesis.
* `c = Real.exp (-(2 * (M_V + M_W)))` and `C = Real.exp (2 * (M_V + M_W))` are written out in the
  statement, not abbreviated. The conjunct `0 < c` is stated explicitly, although it is immediate.
* `μ_{p_ν}` is `densityMeasure_LIP03218 (p_ν)` from LIP032.18, i.e.
  `(haar d).withDensity (fun x => ENNReal.ofReal (p_ν x))`.
* No statement of the specification has been strengthened or weakened. The positive-rate
  hypothesis of the flow branch (see the LIP032 statement issue) is not part of this unit.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- Existence of bounds `M_V, M_W ≥ 0` with `|A.V| ≤ M_V` and `|A.W| ≤ M_W`, by compactness. -/
theorem lip032_01_uniform_gibbs_bounds_exists (A : InteractionData d) :
    ∃ M_V M_W : ℝ, 0 ≤ M_V ∧ 0 ≤ M_W ∧ (∀ x, |A.V x| ≤ M_V) ∧ (∀ x y, |A.W x y| ≤ M_W) := by
  obtain ⟨MV, hMV⟩ := A.V_bounded
  obtain ⟨MW, -, hMW⟩ := lip032_16_continuous_kernel_integrals_common_bounds_exists_bound A
  exact ⟨max MV 0, max MW 0, le_max_right _ _, le_max_right _ _,
    fun x => (hMV x).trans (le_max_left _ _), fun x y => (hMW x y).trans (le_max_left _ _)⟩

/-- **LIP032.01.** Uniform Gibbs bounds. For bounds `|A.V| ≤ M_V` and `|A.W| ≤ M_W`, with
`B_0 = M_V + M_W`, `c = e^{-2B_0}` and `C = e^{2B_0}`: every probability `ν` on `𝕋^d` has a
continuous Gibbs density `p_ν` with `∫ p_ν dm = 1` and `0 < c ≤ p_ν ≤ C` everywhere; and every
free-energy minimizer `ν` satisfies `μ_{p_ν} = ν`. -/
theorem lip032_01_uniform_gibbs_bounds (A : InteractionData d) (M_V M_W : ℝ)
    (hV : ∀ x, |A.V x| ≤ M_V) (hW : ∀ x y, |A.W x y| ≤ M_W) :
    (∀ (ν : Measure (Torus d)) [IsProbabilityMeasure ν],
      Continuous (DGPS.Lipschitz.gibbsDensity A ν) ∧
      ∫ x, DGPS.Lipschitz.gibbsDensity A ν x ∂haar d = 1 ∧
      0 < Real.exp (-(2 * (M_V + M_W))) ∧
      ∀ x, Real.exp (-(2 * (M_V + M_W))) ≤ DGPS.Lipschitz.gibbsDensity A ν x ∧
        DGPS.Lipschitz.gibbsDensity A ν x ≤ Real.exp (2 * (M_V + M_W))) ∧
    (∀ ν : ProbabilityMeasure (Torus d), freeEnergy A ν = freeEnergyMinimum A →
      densityMeasure_LIP03218 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d))) =
        (ν : Measure (Torus d))) := by
  refine ⟨fun ν _ => ?_,
    fun ν hν => (lip032_18_density_probability_test_integral_bridge_gibbs A ν hν).2.2.2⟩
  obtain ⟨-, -, -, hbd, hint, hcont⟩ :=
    lip032_17_positive_normalized_exponential_interaction A M_V M_W hV hW ν
  exact ⟨hcont, hint, Real.exp_pos _, hbd⟩

end DGPS.Frontier.LIP032
