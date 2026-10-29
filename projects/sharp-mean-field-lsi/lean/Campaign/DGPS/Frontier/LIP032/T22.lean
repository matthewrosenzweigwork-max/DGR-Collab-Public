import DGPS.Frontier.LIP032.T18

/-!
# LIP032.22: Interpolation is a bounded density

Task id and title: LIP032.22, "Interpolation is a bounded density" (node LIP032, contractibility of
the minimizer set; pure density task, no positive-rate hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.interpolDensity_LIP03222` : the interpolated density
  `f_{ν,s} = (1 - s) p_ν + s q` with `p_ν = gibbsDensity A ν` and `q = p_μ = gibbsDensity A μ`
  for the fixed minimizer `μ`.
* `DGPS.Frontier.LIP032.gibbs_bounds_LIP03222` : for a probability `ν` and bounds `|A.V| ≤ M_V`,
  `|A.W| ≤ M_W`, the Gibbs density `p_ν` satisfies `e^{-2(M_V+M_W)} ≤ p_ν ≤ e^{2(M_V+M_W)}`,
  is continuous, and has integral one (a specialization of LIP032.17 to `U = equilibriumPotential`).
* `DGPS.Frontier.LIP032.lip032_22_interpolation_bounded_density` : for `ν, μ ∈ S` and `s ∈ [0,1]`,
  `f_{ν,s}` is continuous, has integral one, satisfies `c ≤ f_{ν,s} ≤ C` with
  `c = e^{-2(M_V+M_W)}`, `C = e^{2(M_V+M_W)}`, and `μ_{f_{ν,s}}` is a probability measure.

## R5 notes
* Hypotheses of the main statement, all taken from the specification's context: `A : InteractionData
  d`; reals `M_V`, `M_W` with `|A.V| ≤ M_V` and `|A.W| ≤ M_W` (the bounds `B_0 = M_V + M_W`,
  `c = e^{-2B_0}`, `C = e^{2B_0}` are written out inline); the free-energy minimizers `μ` and `ν`
  as `ProbabilityMeasure (Torus d)` with `freeEnergy A _ = freeEnergyMinimum A` (membership in `S`);
  and `s` with `0 ≤ s ≤ 1`.
* The specification says "choose `M_V, M_W ≥ 0`". Nonnegativity is not assumed: it is not needed for
  the conclusion, and it follows from the bounds at any point of the torus anyway. Omitting it gives
  a statement with no extra hypothesis.
* The minimizer memberships `hμ`, `hν` are part of the specification's set `S` but are not used in the
  proof: the bounds hold for every probability measure. They are kept so that the statement is the
  specified one (`ν ∈ S`, with `μ ∈ S` the fixed base point). Their binder names carry a leading
  underscore (`_hμ`, `_hν`) only to silence the unused-variable linter; the types are unchanged.
* `μ` is the fixed base point of the specification (`q = p_μ`); the statement quantifies over `ν`
  and `s` with `μ` fixed, as in "for `ν ∈ S` and `s ∈ [0,1]`".
* `p_ν` is `DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d))`, the packet's Gibbs density (with
  `ν` coerced to a Borel measure). The bounds come from LIP032.17 applied to
  `U = equilibriumPotential A ν`, using `|equilibriumPotential A ν| ≤ M_V + M_W`, which is
  `abs_add_le` together with `abs_interactionConvolution_le`. The identification
  `gibbsDensity = normExp_LIP03217 (equilibriumPotential _)` is definitional.
* "Continuous", "integral one" and "`c ≤ f ≤ C`" are the three pointwise/integral conclusions of the
  specification; "`μ_f` is a probability" is `IsProbabilityMeasure (densityMeasure_LIP03218 f)`,
  obtained from LIP032.18 (`isProbabilityMeasure_density_LIP03218`). The density `f` is nonnegative
  because `c > 0`.
* The pointwise identities at `s = 0, 1` mentioned in the specification's proof are not part of its
  statement and are not stated here.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- The interpolated density `f_{ν,s} = (1 - s) p_ν + s q` with `q = p_μ`. -/
noncomputable def interpolDensity_LIP03222 (A : InteractionData d) (μ ν : ProbabilityMeasure (Torus d))
    (s : ℝ) (x : Torus d) : ℝ :=
  (1 - s) * DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) x +
    s * DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d)) x

/-- Bounds, continuity and mass one of the Gibbs density `p_ν` for a probability `ν`, with
`|A.V| ≤ M_V` and `|A.W| ≤ M_W`. -/
theorem gibbs_bounds_LIP03222 (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W) (ν : ProbabilityMeasure (Torus d)) :
    Continuous (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d))) ∧
    (∀ x, Real.exp (-(2 * (M_V + M_W))) ≤ DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) x ∧
      DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) x ≤ Real.exp (2 * (M_V + M_W))) ∧
    ∫ x, DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) x ∂haar d = 1 := by
  have hb : ∀ x, |DGPS.Lipschitz.equilibriumPotential A (ν : Measure (Torus d)) x| ≤ M_V + M_W :=
    fun x => (abs_add_le _ _).trans
      (add_le_add (hV x) (DGPS.Lipschitz.abs_interactionConvolution_le A _ hW x))
  obtain ⟨-, -, -, hbd, hint, hcont⟩ :=
    lip032_17_positive_normalized_exponential
      (DGPS.Lipschitz.equilibriumPotential A (ν : Measure (Torus d)))
      (DGPS.Lipschitz.continuous_equilibriumPotential A _) (M_V + M_W) hb
  exact ⟨hcont, hbd, hint⟩

/-- **LIP032.22.** For minimizers `ν, μ ∈ S` and `s ∈ [0,1]`, the interpolated density
`f_{ν,s} = (1 - s) p_ν + s q` (with `q = p_μ`) is continuous, has integral one, satisfies
`e^{-2(M_V+M_W)} ≤ f_{ν,s} ≤ e^{2(M_V+M_W)}`, and `μ_{f_{ν,s}}` is a probability measure. -/
theorem lip032_22_interpolation_bounded_density
    (A : InteractionData d) (M_V M_W : ℝ) (hV : ∀ x, |A.V x| ≤ M_V)
    (hW : ∀ x y, |A.W x y| ≤ M_W)
    (μ : ProbabilityMeasure (Torus d)) (_hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν : ProbabilityMeasure (Torus d)) (_hν : freeEnergy A ν = freeEnergyMinimum A)
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Continuous (interpolDensity_LIP03222 A μ ν s) ∧
    ∫ x, interpolDensity_LIP03222 A μ ν s x ∂haar d = 1 ∧
    (∀ x, Real.exp (-(2 * (M_V + M_W))) ≤ interpolDensity_LIP03222 A μ ν s x ∧
      interpolDensity_LIP03222 A μ ν s x ≤ Real.exp (2 * (M_V + M_W))) ∧
    IsProbabilityMeasure (densityMeasure_LIP03218 (interpolDensity_LIP03222 A μ ν s)) := by
  obtain ⟨hpc, hpb, hpi⟩ := gibbs_bounds_LIP03222 A M_V M_W hV hW ν
  obtain ⟨hqc, hqb, hqi⟩ := gibbs_bounds_LIP03222 A M_V M_W hV hW μ
  have hs1' : (0 : ℝ) ≤ 1 - s := sub_nonneg.mpr hs1
  have hcont : Continuous (interpolDensity_LIP03222 A μ ν s) :=
    (continuous_const.mul hpc).add (continuous_const.mul hqc)
  have hbnd : ∀ x, Real.exp (-(2 * (M_V + M_W))) ≤ interpolDensity_LIP03222 A μ ν s x ∧
      interpolDensity_LIP03222 A μ ν s x ≤ Real.exp (2 * (M_V + M_W)) := by
    intro x
    obtain ⟨hp1, hp2⟩ := hpb x
    obtain ⟨hq1, hq2⟩ := hqb x
    unfold interpolDensity_LIP03222
    constructor
    · nlinarith [mul_le_mul_of_nonneg_left hp1 hs1', mul_le_mul_of_nonneg_left hq1 hs0]
    · nlinarith [mul_le_mul_of_nonneg_left hp2 hs1', mul_le_mul_of_nonneg_left hq2 hs0]
  have hint : ∫ x, interpolDensity_LIP03222 A μ ν s x ∂haar d = 1 := by
    unfold interpolDensity_LIP03222
    rw [integral_add ((integrable_continuous_LIP03218 hpc).const_mul _)
        ((integrable_continuous_LIP03218 hqc).const_mul _),
      integral_const_mul, integral_const_mul, hpi, hqi]
    ring
  have h0 : ∀ x, 0 ≤ interpolDensity_LIP03222 A μ ν s x := fun x =>
    (Real.exp_pos _).le.trans (hbnd x).1
  exact ⟨hcont, hint, hbnd, isProbabilityMeasure_density_LIP03218 hcont h0 hint⟩

end DGPS.Frontier.LIP032
