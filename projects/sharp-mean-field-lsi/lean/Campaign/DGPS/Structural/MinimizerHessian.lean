import DGPS.Equilibrium.Hessian
import DGPS.Lipschitz.HessianKernel
import DGPS.Model.FreeEnergy
import DGPS.Structural.ZeroDissipationFixedPoint
import DGPS.Variational.EquilibriumGibbs

/-!
# Minimizers are Gibbs densities; nonnegative centered Hessian (STR004)

For direct Lipschitz standing data `A` (with a weak-drift provider `b`, as in STR003):

* `gibbsMinimizer_exists`: the free-energy minimum is a finite real number, it is attained, and
  every minimizer `μ` satisfies `μ = P μ` (`P = frozenGibbs A`), has a positive Lipschitz density,
  and is the measure of an absolute competitor, every such competitor having zero dissipation.
* `minimizer_centeredHessian_nonneg`: at a minimizer, the centered kernel `K` has zero `μ`-mean in
  each variable and `I + T ≥ 0` on `L²_0(μ)`.
* `zeroDissipation_unique_implies_minimizer_unique`: if exactly one absolute density has zero
  dissipation, its measure is the unique global minimizer.

The proof combines DEF008 (existence), LIP017 (Gibbs identity of minimizers, positive Lipschitz
Gibbs density), STR003 (zero dissipation versus frozen fixed points), DEF026 (kernel centering) and
LIP033 (`I + T ≥ 0`, transported from the `Lipschitz` operator to the DEF026 Hessian).
-/

namespace DGPS.Structural

open MeasureTheory

variable {d : ℕ}

/-- The frozen Gibbs density is the Gibbs density `e^{-Φ}/Z` of LIP017. -/
theorem frozenGibbs_density_eq_gibbsDensity (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) :
    (frozenGibbs A μ).density = DGPS.Lipschitz.gibbsDensity A (μ : Measure (Torus d)) := rfl

/-- A minimizer (`freeEnergy = freeEnergyMinimum`) is a global lower bound. -/
theorem minimizer_le (A : InteractionData d) {μ : ProbabilityMeasure (Torus d)}
    (hμ : freeEnergy A μ = freeEnergyMinimum A) (ν : ProbabilityMeasure (Torus d)) :
    freeEnergy A μ ≤ freeEnergy A ν := by
  rw [hμ]; exact iInf_le _ ν

/-- A minimizer is the frozen Gibbs fixed point `μ = P μ`. -/
theorem minimizer_eq_frozenGibbs (A : InteractionData d) {μ : ProbabilityMeasure (Torus d)}
    (hμ : freeEnergy A μ = freeEnergyMinimum A) :
    (μ : Measure (Torus d)) = (frozenGibbs A μ).measure := by
  obtain ⟨-, -, h3, -⟩ := DGPS.Lipschitz.free_energy_minimum_and_gibbs_identity A
  exact (h3 μ hμ).1

/-- **STR004 (existence and Gibbs form).** Under direct Lipschitz data and a weak-drift provider,
the free-energy minimum `F_*` is a finite real number attained by some probability `μ`; every
minimizer satisfies `μ = P μ` with `P = frozenGibbs A`, has a positive Lipschitz density, is the
measure of some absolute-admissible competitor, and every absolute competitor with measure `μ` has
zero dissipation. -/
theorem gibbsMinimizer_exists (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) :
    (∃ r : ℝ, freeEnergyMinimum A = (r : EReal)) ∧
    (∃ μ : ProbabilityMeasure (Torus d), freeEnergy A μ = freeEnergyMinimum A) ∧
    ∀ μ : ProbabilityMeasure (Torus d), freeEnergy A μ = freeEnergyMinimum A →
      (μ : Measure (Torus d)) = (frozenGibbs A μ).measure ∧
      (frozenGibbs A μ).hasPositiveLipschitzDensity ∧
      (∃ ρ : AbsoluteDensity d, densityMeasure ρ = μ) ∧
      ∀ ρ : AbsoluteDensity d, densityMeasure ρ = μ → scalarDissipation A b ρ = 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := DGPS.Lipschitz.free_energy_minimum_and_gibbs_identity A
  refine ⟨h2, h1, fun μ hμ => ?_⟩
  have hfix : (μ : Measure (Torus d)) = (frozenGibbs A μ).measure := (h3 μ hμ).1
  obtain ⟨c, C, L, K, hc, -, hbd⟩ := h4 hLip
  obtain ⟨hb1, hb2, -⟩ := hbd μ hμ
  obtain ⟨-, hfp⟩ := zeroDissipation_iff_frozenFixedPoint A hLip b
  obtain ⟨-, ρ, hρ, -⟩ := hfp μ hfix
  refine ⟨hfix, ⟨L, c, hc, fun x => (hb1 x).1, hb2⟩, ⟨ρ, hρ⟩, fun ρ' hρ' => ?_⟩
  have := (zeroDissipation_iff_frozenFixedPoint A hLip b).1 ρ'
  rw [this, hρ']
  exact hfix

/-- The DEF026 centered kernel is the LIP-side centered kernel. -/
theorem centeredKernel_eq_lipschitz (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    (x y : Torus d) :
    centeredKernel A μ x y = DGPS.Lipschitz.centeredKernel A (μ : Measure (Torus d)) x y := rfl

/-- The DEF026 kernel operator agrees with the LIP033 centered operator. -/
theorem kernelOp_eq_centeredOperator (A : InteractionData d) (μ : ProbabilityMeasure (Torus d))
    (f : Lp ℝ 2 (μ : Measure (Torus d))) :
    kernelOp A μ f = DGPS.Lipschitz.centeredOperator A (μ : Measure (Torus d)) f := by
  refine Lp.ext ?_
  refine (kernelOp_ae A μ f).trans ?_
  unfold DGPS.Lipschitz.centeredOperator
  have h2 := ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) (μ := (μ : Measure (Torus d)))
    (DGPS.Lipschitz.Tcont A (μ : Measure (Torus d)) f)
  filter_upwards [h2] with x hx
  rw [ContinuousLinearMap.comp_apply, hx, DGPS.Lipschitz.Tcont_apply]
  rfl

/-- **STR004 (centered Hessian).** At a minimizer `μ` of the free energy the centered kernel `K` has
zero `μ`-mean in each variable and `I + T ≥ 0` on real `L²_0(μ)`, i.e. `⟨f, (I + T) f⟩ ≥ 0` for
every `f ∈ L²_0(μ)` (`densityHessian = I + T`). -/
theorem minimizer_centeredHessian_nonneg (A : InteractionData d)
    {μ : ProbabilityMeasure (Torus d)} (hμ : freeEnergy A μ = freeEnergyMinimum A) :
    (∀ x : Torus d, ∫ y, centeredKernel A μ x y ∂(μ : Measure (Torus d)) = 0) ∧
    (∀ y : Torus d, ∫ x, centeredKernel A μ x y ∂(μ : Measure (Torus d)) = 0) ∧
    ∀ f : centeredL2 μ, 0 ≤ inner ℝ f (densityHessian A μ f) := by
  refine ⟨integral_centeredKernel_right A μ, integral_centeredKernel_left A μ, fun f => ?_⟩
  have hpsd := (DGPS.Lipschitz.centered_hessian_positive_semidefinite_and_finite_nullspace A μ
    (minimizer_le A hμ)).2.2.1
  have hf : (f : Lp ℝ 2 (μ : Measure (Torus d))) ∈ DGPS.Lipschitz.meanZeroL2 μ :=
    (DGPS.Lipschitz.mem_meanZeroL2 μ _).2 f.2
  have h := hpsd ⟨f, hf⟩
  have e : ((densityHessian A μ f : centeredL2 μ) : Lp ℝ 2 (μ : Measure (Torus d))) =
      (f : Lp ℝ 2 (μ : Measure (Torus d))) +
        DGPS.Lipschitz.centeredOperator A (μ : Measure (Torus d)) f := by
    rw [← kernelOp_eq_centeredOperator]; rfl
  have c1 := Submodule.coe_inner (centeredL2 μ) f (densityHessian A μ f)
  have c2 := Submodule.coe_inner (DGPS.Lipschitz.meanZeroL2 μ)
    (⟨f, hf⟩ + DGPS.Lipschitz.centeredOperator0 A μ ⟨f, hf⟩) ⟨f, hf⟩
  rw [c1, e, real_inner_comm]
  rw [c2] at h
  simpa [DGPS.Lipschitz.coe_centeredOperator0] using h

/-- **STR004 (uniqueness).** If exactly one absolute density has zero dissipation, then its measure
is the unique global minimizer of the free energy. -/
theorem zeroDissipation_unique_implies_minimizer_unique (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A)
    (hu : ∃! ρ : AbsoluteDensity d, scalarDissipation A b ρ = 0) :
    ∃ ρ₀ : AbsoluteDensity d, scalarDissipation A b ρ₀ = 0 ∧
      ∀ μ : ProbabilityMeasure (Torus d),
        freeEnergy A μ = freeEnergyMinimum A ↔ μ = densityMeasure ρ₀ := by
  obtain ⟨ρ₀, hρ₀, huniq⟩ := hu
  obtain ⟨-, ⟨μ₁, hμ₁⟩, hall⟩ := gibbsMinimizer_exists A hLip b
  obtain ⟨-, -, ⟨ρ₁, hρ₁⟩, hz⟩ := hall μ₁ hμ₁
  have hρ : ρ₁ = ρ₀ := huniq ρ₁ (hz ρ₁ hρ₁)
  have hμ : μ₁ = densityMeasure ρ₀ := by rw [← hρ, hρ₁]
  refine ⟨ρ₀, hρ₀, fun μ => ⟨fun hμm => ?_, fun hμm => ?_⟩⟩
  · obtain ⟨-, -, ⟨ρ, hρ'⟩, hz'⟩ := hall μ hμm
    have := huniq ρ (hz' ρ hρ')
    rw [← hρ', this]
  · rw [hμm, ← hμ]; exact hμ₁

end DGPS.Structural
