import DGPS.Frontier.LIP032.T28

/-!
# LIP032.05: Uniform finite initial energy gap

Task id and title: LIP032.05, "Uniform finite initial energy gap" (node LIP032, contractibility of
the minimizer set; leaf formalization, pure energy task; no positive-rate, flow or Lipschitz
hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.lip032_05_uniform_finite_initial_energy_gap` : for minimizers `μ, ν ∈ S`
  and `s ∈ [0,1]`, the probability `P` whose measure is `μ_f`, with `f = f_{ν,s}`, has finite free
  energy; `F_* = E(q)` for `q = p_μ`; the extended difference `F(μ_f) - F_*` equals the real
  difference `E(f) - E(q)`; and `0 ≤ E(f) - E(q) ≤ G_0`, where
  `G_0 = log C + 2 M_V + M_W` and `C = exp (2 (M_V + M_W))`.

## R5 notes
* Hypotheses are exactly those of the specification's statement, read through the frozen context:
  the interaction data `A`, pointwise bounds `|A.V| ≤ M_V` and `|A.W| ≤ M_W` (the "choose bounds"
  step, not assumed nonnegative), the minimizers `μ` and `ν` (as `freeEnergy = freeEnergyMinimum`),
  and `s ∈ [0,1]`. No positive-rate hypothesis `r > 0` or `ofReal r < scalarRate` is added: this
  statement concerns only initial energies, so the LIP031 rate is not used and the FD-001 gap does
  not arise here.
* "Each interpolation density" is read as universal quantification over `ν ∈ S` and `s ∈ [0,1]`,
  realized by the binders `ν`, `hν`, `s`, `hs0`, `hs1`.
* "Finite free energy" is recorded twice: as `FiniteFreeEnergy A P` (there is a real `r` with
  `freeEnergy A P = r`) and implicitly by the explicit `EReal` identity for `freeEnergy A P`.
  The probability `P` is the one whose underlying measure is `μ_f`; it is unique, since
  probability measures are determined by their measure.
* `E(f)` and `E(q)` are the real free energies `realFreeEnergy_LIP03228` of LIP032.28, with
  `q = gibbsDensity A μ`; `μ_q = μ` is part of LIP032.28 and is not restated.
* `F(μ_f) - F_*` is written as an `EReal` subtraction, and `F_* = E(q)` is recorded as an equation
  in `EReal` with a finite real coercion. The conversion `EReal.coe_sub` is applied only after both
  extended values have been identified with finite reals.
* `G_0` is written inline as `Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W`, the literal
  `log C + 2 M_V + M_W` with `C = exp (2 B_0)` and `B_0 = M_V + M_W`; it is not simplified.
* The proof is a repackaging of LIP032.28 (`lip032_28_real_free_energy_uniform_gap`) and adds no
  new analytic content. No statement was weakened and no hypothesis was strengthened.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- **LIP032.05.** Uniform finite initial energy gap: for minimizers `μ, ν ∈ S` and `s ∈ [0,1]`,
the density `f_{ν,s}` gives a probability `P` with finite free energy, `F_* = E(q)`,
`F(μ_f) - F_* = E(f) - E(q)`, and `0 ≤ E(f) - E(q) ≤ G_0`. -/
theorem lip032_05_uniform_finite_initial_energy_gap
    (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W)
    (μ : ProbabilityMeasure (Torus d)) (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν : ProbabilityMeasure (Torus d)) (hν : freeEnergy A ν = freeEnergyMinimum A)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∃ P : ProbabilityMeasure (Torus d),
      (P : Measure (Torus d)) = densityMeasure_LIP03218 (interpolDensity_LIP03222 A μ ν s) ∧
      FiniteFreeEnergy A P ∧
      freeEnergyMinimum A
        = ((realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d))) : ℝ)
          : EReal) ∧
      freeEnergy A P - freeEnergyMinimum A
        = ((realFreeEnergy_LIP03228 A (interpolDensity_LIP03222 A μ ν s)
            - realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d)))
            : ℝ) : EReal) ∧
      0 ≤ realFreeEnergy_LIP03228 A (interpolDensity_LIP03222 A μ ν s)
          - realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d))) ∧
      realFreeEnergy_LIP03228 A (interpolDensity_LIP03222 A μ ν s)
          - realFreeEnergy_LIP03228 A (DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d)))
        ≤ Real.log (Real.exp (2 * (M_V + M_W))) + 2 * M_V + M_W := by
  obtain ⟨⟨P, hPμ, hPf⟩, ⟨-, -, hFmin⟩, hlow, hup⟩ :=
    lip032_28_real_free_energy_uniform_gap A M_V M_W hV hW μ hμ ν hν s hs0 hs1
  refine ⟨P, hPμ, ⟨_, hPf⟩, hFmin, ?_, hlow, hup⟩
  rw [hPf, hFmin, EReal.coe_sub]

end DGPS.Frontier.LIP032
