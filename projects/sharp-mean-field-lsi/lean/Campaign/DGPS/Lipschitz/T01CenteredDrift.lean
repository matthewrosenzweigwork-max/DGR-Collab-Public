import DGPS.Lipschitz.T01SpectralBridge
import DGPS.Structural.FrozenEnergyIdentity

/-!
# The centered conditional drift on the current absolute domain

A slice gradient of the actual centered kernel and a genuine weak gradient of the frozen
reference potential give the force of every absolute competitor. The extra term in the
potential is constant in the spatial coordinate and therefore contributes no derivative.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

open KernelApproximation

/-- The centered convolution plus the reference potential differs from the original
interaction potential by a scalar constant. This is a pointwise identity. -/
theorem centered_reference_potential_identity (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) (ρ : AbsoluteDensity d) (x : Torus d) :
    frozenPotential A (μ : Measure (Torus d)) x +
      (∫ y, centeredKernel A (μ : Measure (Torus d)) x y
        ∂(densityMeasure ρ : Measure (Torus d))) =
      interactionPotential A ρ x + meanInteraction A μ -
        ∫ z, interactionConvolution A (μ : Measure (Torus d)) z
          ∂(densityMeasure ρ : Measure (Torus d)) := by
  have hk := Structural.kernelPotential_eq A μ (densityMeasure ρ) x
  unfold Structural.kernelPotential at hk
  rw [DGPS.integral_centeredKernel_right, sub_zero] at hk
  change frozenPotential A (μ : Measure (Torus d)) x +
      (∫ y, DGPS.centeredKernel A μ x y ∂(densityMeasure ρ : Measure (Torus d))) =
    interactionPotential A ρ x + meanInteraction A μ -
      ∫ z, DGPS.interactionConvolution A μ z ∂(densityMeasure ρ : Measure (Torus d))
  rw [hk]
  dsimp only [frozenPotential, interactionPotential, DGPS.interactionConvolution,
    DGPS.Lipschitz.interactionConvolution]
  ring

/-- A current provider's force equals the reference gradient plus the centered kernel
convolution. The kernel derivative is an actual jointly measurable bounded slice derivative;
no ambient restriction to the diagonal and no semiconvexity premise is used. -/
theorem absoluteDrift_centered_ae (A : InteractionData d) (b : AbsoluteDrift A)
    (μ : ProbabilityMeasure (Torus d)) (D : KData d)
    (hD : D.K = centeredKernel A (μ : Measure (Torus d)))
    {v : Torus d → Tangent d}
    (hv : IsWeakGradient (frozenPotential A (μ : Measure (Torus d))) v)
    (ρ : AbsoluteDensity d) :
    b.force ρ =ᵐ[haar d]
      fun x => v x + ∫ y, ρ.density y • D.G1 x y ∂haar d := by
  have hB : MemLp (Function.uncurry D.G1) ∞ ((haar d).prod (haar d)) :=
    memLp_top_of_bound D.G1m.aestronglyMeasurable D.B
      (Eventually.of_forall fun p => D.G1b p.1 p.2)
  have hWB : ∀ᵐ y ∂haar d,
      IsWeakGradientLp ∞ (fun x => D.K x y) (fun x => D.G1 x y) := by
    apply Eventually.of_forall
    intro y
    obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn (D.slice_cont y).continuousOn
    exact ⟨memLp_top_of_bound (D.slice_cont y).aestronglyMeasurable M
        (Eventually.of_forall fun x => hM x (Set.mem_univ x)),
      memLp_top_of_bound D.G1m.of_uncurry_right.aestronglyMeasurable D.B
        (Eventually.of_forall fun x => D.G1b x y), (D.g1 y).ibp⟩
  have hc := isWeakGradientLp_convolution D.Kc D.G1m hB hWB ρ.integrable_density
  have hc2 : IsWeakGradient (fun x => ∫ y, D.K x y * ρ.density y ∂haar d)
      (fun x => ∫ y, ρ.density y • D.G1 x y ∂haar d) :=
    ⟨hc.memLp.mono_exponent le_top, hc.memLp_grad.mono_exponent le_top, hc.ibp⟩
  let c : ℝ := meanInteraction A μ -
    ∫ z, interactionConvolution A (μ : Measure (Torus d)) z
      ∂(densityMeasure ρ : Measure (Torus d))
  have hpot : (fun x => frozenPotential A (μ : Measure (Torus d)) x +
      (∫ y, D.K x y * ρ.density y ∂haar d) + -c) = interactionPotential A ρ := by
    funext x
    rw [hD]
    have hi : (∫ y, centeredKernel A (μ : Measure (Torus d)) x y * ρ.density y ∂haar d) =
        ∫ y, centeredKernel A (μ : Measure (Torus d)) x y
          ∂(densityMeasure ρ : Measure (Torus d)) := by
      rw [Structural.budget_integral_densityMeasure]
      exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
    rw [hi, centered_reference_potential_identity]
    dsimp [c]
    ring
  have hw := (hv.add hc2).add (isWeakGradient_const (-c))
  rw [hpot] at hw
  have hw1 : IsWeakGradientLp 1 (interactionPotential A ρ)
      (fun x => v x + ∫ y, ρ.density y • D.G1 x y ∂haar d) := by
    refine ⟨hw.memLp.mono_exponent one_le_two, ?_, ?_⟩
    · simpa only [add_zero] using hw.memLp_grad.mono_exponent one_le_two
    · simpa only [add_zero] using hw.ibp
  exact b.ae_eq_of_isWeakGradient ρ hw1

end DGPS.Lipschitz
