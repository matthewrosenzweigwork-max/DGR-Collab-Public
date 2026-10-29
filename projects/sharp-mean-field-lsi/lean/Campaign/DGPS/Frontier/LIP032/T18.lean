import DGPS.Frontier.LIP032.T17
import DGPS.Variational.EquilibriumGibbs

/-!
# LIP032.18: Density-to-probability and test-integral bridge

Task id and title: LIP032.18, "Density-to-probability and test-integral bridge" (node LIP032,
contractibility of the minimizer set; leaf formalization, no positive-rate hypothesis is used).

## Provides
* `DGPS.Frontier.LIP032.densityMeasure_LIP03218` : the measure `μ_f = m.withDensity (ofReal ∘ f)`
  attached to a real density `f` on `𝕋^d`.
* `DGPS.Frontier.LIP032.isProbabilityMeasure_density_LIP03218` : `μ_f` is a probability measure
  for continuous `f ≥ 0` with `∫ f dm = 1`.
* `DGPS.Frontier.LIP032.lip032_18_density_probability_test_integral_bridge` : the main statement,
  a conjunction of (a) `μ_f` is a probability and every bounded measurable real `φ` is
  `μ_f`-integrable with `∫ φ dμ_f = ∫ f φ dm`; (b) continuous mass-one nonnegative densities that
  agree `m`-a.e. give equal probabilities; (c) for every free-energy minimizer `ν` the Gibbs density
  `p_ν` is a continuous nonnegative mass-one density and `μ_{p_ν} = ν`.
* `DGPS.Frontier.LIP032.lip032_18_density_probability_test_integral_bridge_integral` : part (a)
  integral identity for one density.
* `DGPS.Frontier.LIP032.lip032_18_density_probability_test_integral_bridge_ae` : part (b), proved
  without any hypothesis on the densities beyond a.e. equality.
* `DGPS.Frontier.LIP032.lip032_18_density_probability_test_integral_bridge_gibbs` : part (c).

## R5 notes
* `m` is `haar d`. The specification's "`ofReal ∘ f`" is the function `x ↦ ENNReal.ofReal (f x)`;
  `μ_f` is `(haar d).withDensity` of it, a `Measure (Torus d)` (the probability-measure subtype is
  not formed; `IsProbabilityMeasure` is proved instead).
* "Bounded measurable real `φ`" is formalized as `Measurable φ` together with `∃ C, ∀ x, |φ x| ≤ C`.
  Besides the identity `∫ φ dμ_f = ∫ f φ dm` the conclusion records `Integrable φ μ_f` (the
  specification's proof remarks that `φ` is integrable under `μ_f`); the right integrand is spelled
  `fun x => f x * φ x`.
* The a.e. statement keeps the hypotheses of the specification (continuity, nonnegativity, mass one
  for both densities) as binders in the statement of the main theorem; the helper `_ae` does not
  need them and is stated without them.
* Part (c): `S` is the set of free-energy minimizers, formalized as
  `ν : ProbabilityMeasure (Torus d)` with `freeEnergy A ν = freeEnergyMinimum A`, exactly as in
  LIP017 (`DGPS.Lipschitz.free_energy_minimum_and_gibbs_identity`). `p_ν` is the packet's
  `DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d))`. The measure identity is the LIP017 third
  conjunct, used verbatim. The side facts that `p_ν` is continuous, nonnegative and has mass one
  come from LIP032.17 applied to `U = equilibriumPotential A ν` with the uniform bound of
  `exists_potential_bound` (the packet's `gibbsDensity` unfolds definitionally to
  `normExp_LIP03217 (equilibriumPotential A ν)`). No `LipschitzData` hypothesis is needed.
* Continuity gives measurability and boundedness of `f` automatically (compact `𝕋^d`); these are
  not separate hypotheses.
-/

open MeasureTheory

namespace DGPS.Frontier.LIP032

variable {d : ℕ}

/-- The measure `μ_f = m.withDensity (ofReal ∘ f)` attached to a real density `f`. -/
noncomputable def densityMeasure_LIP03218 (f : Torus d → ℝ) : Measure (Torus d) :=
  (haar d).withDensity fun x => ENNReal.ofReal (f x)

/-- A continuous function on the torus is integrable against Haar measure. -/
theorem integrable_continuous_LIP03218 {f : Torus d → ℝ} (hf : Continuous f) :
    Integrable f (haar d) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

/-- `μ_f` is a probability measure for continuous `f ≥ 0` with `∫ f dm = 1`. -/
theorem isProbabilityMeasure_density_LIP03218 {f : Torus d → ℝ} (hf : Continuous f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∫ x, f x ∂haar d = 1) :
    IsProbabilityMeasure (densityMeasure_LIP03218 f) := by
  refine ⟨?_⟩
  rw [densityMeasure_LIP03218, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_continuous_LIP03218 hf)
      (Filter.Eventually.of_forall h0), h1]
  simp

/-- For bounded measurable `φ`: `φ` is `μ_f`-integrable and `∫ φ dμ_f = ∫ f φ dm`. -/
theorem lip032_18_density_probability_test_integral_bridge_integral {f : Torus d → ℝ}
    (hf : Continuous f) (h0 : ∀ x, 0 ≤ f x) (h1 : ∫ x, f x ∂haar d = 1)
    {φ : Torus d → ℝ} (hφ : Measurable φ) (hC : ∃ C : ℝ, ∀ x, |φ x| ≤ C) :
    Integrable φ (densityMeasure_LIP03218 f) ∧
      ∫ x, φ x ∂densityMeasure_LIP03218 f = ∫ x, f x * φ x ∂haar d := by
  have := isProbabilityMeasure_density_LIP03218 hf h0 h1
  obtain ⟨C, hC⟩ := hC
  refine ⟨Integrable.of_bound hφ.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hC x), ?_⟩
  rw [densityMeasure_LIP03218, integral_withDensity_eq_integral_toReal_smul
    (hf.measurable.ennreal_ofReal) (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (h0 x)]

/-- Densities that agree `m`-a.e. give equal measures. -/
theorem lip032_18_density_probability_test_integral_bridge_ae {f g : Torus d → ℝ}
    (h : f =ᵐ[haar d] g) : densityMeasure_LIP03218 f = densityMeasure_LIP03218 g :=
  withDensity_congr_ae (h.mono fun x hx => by simp [hx])

/-- For a free-energy minimizer `ν`, `p_ν` is a continuous nonnegative mass-one density with
`μ_{p_ν} = ν`. -/
theorem lip032_18_density_probability_test_integral_bridge_gibbs (A : InteractionData d)
    (ν : ProbabilityMeasure (Torus d)) (hν : freeEnergy A ν = freeEnergyMinimum A) :
    Continuous (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d))) ∧
    (∀ x, 0 ≤ DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) x) ∧
    ∫ x, DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) x ∂haar d = 1 ∧
    densityMeasure_LIP03218 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d))) =
      (ν : Measure (Torus d)) := by
  obtain ⟨B, -, hB⟩ := DGPS.Lipschitz.exists_potential_bound A
  have hc : Continuous (DGPS.Lipschitz.equilibriumPotential A (ν : Measure (Torus d))) :=
    DGPS.Lipschitz.continuous_equilibriumPotential A _
  obtain ⟨-, -, -, hbd, hint, hcont⟩ :=
    lip032_17_positive_normalized_exponential
      (DGPS.Lipschitz.equilibriumPotential A (ν : Measure (Torus d))) hc B
      (hB (ν : Measure (Torus d)))
  refine ⟨hcont, fun x => ?_, hint, ?_⟩
  · exact (Real.exp_pos _).le.trans (hbd x).1
  · exact ((DGPS.Lipschitz.free_energy_minimum_and_gibbs_identity A).2.2.1 ν hν).1.symm

/-- **LIP032.18.** Density-to-probability and test-integral bridge. -/
theorem lip032_18_density_probability_test_integral_bridge (A : InteractionData d) :
    (∀ f : Torus d → ℝ, Continuous f → (∀ x, 0 ≤ f x) → ∫ x, f x ∂haar d = 1 →
      IsProbabilityMeasure (densityMeasure_LIP03218 f) ∧
      ∀ φ : Torus d → ℝ, Measurable φ → (∃ C : ℝ, ∀ x, |φ x| ≤ C) →
        Integrable φ (densityMeasure_LIP03218 f) ∧
          ∫ x, φ x ∂densityMeasure_LIP03218 f = ∫ x, f x * φ x ∂haar d) ∧
    (∀ f g : Torus d → ℝ, Continuous f → (∀ x, 0 ≤ f x) → ∫ x, f x ∂haar d = 1 →
      Continuous g → (∀ x, 0 ≤ g x) → ∫ x, g x ∂haar d = 1 → f =ᵐ[haar d] g →
        densityMeasure_LIP03218 f = densityMeasure_LIP03218 g) ∧
    (∀ ν : ProbabilityMeasure (Torus d), freeEnergy A ν = freeEnergyMinimum A →
      Continuous (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d))) ∧
      (∀ x, 0 ≤ DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) x) ∧
      ∫ x, DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d)) x ∂haar d = 1 ∧
      densityMeasure_LIP03218 (DGPS.Lipschitz.gibbsDensity A (ν : Measure (Torus d))) =
        (ν : Measure (Torus d))) :=
  ⟨fun _ hf h0 h1 => ⟨isProbabilityMeasure_density_LIP03218 hf h0 h1, fun _ hφ hC =>
      lip032_18_density_probability_test_integral_bridge_integral hf h0 h1 hφ hC⟩,
    fun _ _ _ _ _ _ _ _ h => lip032_18_density_probability_test_integral_bridge_ae h,
    fun ν hν => lip032_18_density_probability_test_integral_bridge_gibbs A ν hν⟩

end DGPS.Frontier.LIP032
