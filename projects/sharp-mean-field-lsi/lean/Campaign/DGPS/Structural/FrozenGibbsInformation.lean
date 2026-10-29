import DGPS.Variational.ZeroDissipation
import DGPS.Model.SpeciesRate
import DGPS.Model.Barycenter

/-!
# Direct Lipschitz information identity in the absolute domain (STR002)

For Lipschitz data `A` and every absolute competitor `ρ` (`ρ ≥ 0`, `∫ρ = 1`, `√ρ ∈ H¹`), with
`P = frozenGibbs A (ρ m)` the frozen Gibbs reference:

* `nonlinearDissipation_eq_frozenInformation`: `D(ρ) = I(ρ m | P(ρ m))`, where `I` is
  `ordinaryRelativeFisher` (`4 ∫ |∇ √(ρ/p)|² p dm`, or `⊤`);
* `speciesDissipation_eq_frozenInformation`: `D_θ = ∑ θ_s I(ρ_s m | P(ρ̄ m))` for every finite
  positive-weight family, with the common reference `P(ρ̄ m)`.

Both rest on `frozenInformation_eq_score`: for any absolute `σ`, the information of `ρ m` relative
to `P(σ m)` is `∫⁻ |2∇√ρ + √ρ b_σ|²`.  The score is identified through the `L¹` weak gradient
`∇ log p_σ = -b_σ` (DEF033), so the identity holds in `ℝ≥0∞`, including the value `⊤` and the zero
set of `ρ` (where `√ρ` has vanishing gradient and `∇ log p` is never divided by `ρ`).
-/

open MeasureTheory
open scoped ENNReal

namespace DGPS.Structural

variable {d : ℕ}

/-- Pointwise: `‖2 g - u L‖ₑ² = ofReal ‖2 g + u (-L)‖²`. -/
theorem enorm_sq_eq_ofReal_norm_sq (v : Tangent d) : ‖v‖ₑ ^ 2 = ENNReal.ofReal (‖v‖ ^ 2) := by
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- Multiplication/division by `√p_ν` is an `H¹` isomorphism: for every absolute `ρ`, the relative
square root `√(ρ/p_σ)` lies in the weighted `H¹` of the frozen reference `P(σ m)`. -/
theorem relativeSqrt_mem_weightedH1 (A : InteractionData d) (hLip : LipschitzData A)
    (σ ρ : AbsoluteDensity d) :
    relativeSqrt (densityMeasure ρ : Measure (Torus d)) (frozenGibbs A (densityMeasure σ)) ∈
      WeightedH1 (frozenGibbs A (densityMeasure σ)) := by
  have hP := frozenGibbs_hasPositiveLipschitzDensity A hLip (densityMeasure σ)
  rw [RelativeFisher.relativeSqrt_mem_weightedH1_iff hP]
  have habs : (fun x => Real.sqrt ((densityMeasure ρ : Measure (Torus d)).rnDeriv (haar d) x
      |>.toReal)) =ᵐ[haar d] ρ.sqrt := by
    have h := Measure.rnDeriv_withDensity₀ (haar d)
      (f := fun x => ENNReal.ofReal (ρ.sqrt x ^ 2))
      (by exact (ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal)
    filter_upwards [h, ρ.sqrt_nonneg] with x hx hx0
    rw [densityMeasure_coe, hx, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq hx0]
  obtain ⟨g, hg⟩ := ρ.sqrt_mem
  exact ⟨g, hg.congr_ae habs.symm (Filter.EventuallyEq.refl _ _)⟩

/-- The information of `ρ m` relative to the frozen Gibbs reference of an arbitrary absolute `σ m`
is the lintegral of the dissipation score built from the force `b_σ`. -/
theorem frozenInformation_eq_score (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) (σ ρ : AbsoluteDensity d) :
    ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus d))
        (frozenGibbs A (densityMeasure σ)) =
      ∫⁻ x, ENNReal.ofReal
        (‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • b.force σ x‖ ^ 2)
        ∂haar d := by
  set P := frozenGibbs A (densityMeasure σ) with hPdef
  have hP : P.hasPositiveLipschitzDensity := frozenGibbs_hasPositiveLipschitzDensity A hLip _
  rw [positiveReference_absolute_identity P hP ρ]
  have hforce : (fun x => -(b.force σ x)) =ᵐ[haar d]
      weakGradient (fun x => Real.log (P.density x)) (P.memH1_log hP) :=
    (def033_log_weakGradient A b σ).ae_eq_of_one
      (def033_isWeakGradientLp_one (isWeakGradient_weakGradient (P.memH1_log hP)))
  refine lintegral_congr_ae ?_
  filter_upwards [hforce] with x hx
  rw [← hx, enorm_sq_eq_ofReal_norm_sq]
  simp [sub_eq_add_neg]

/-- **STR002 (scalar).** The nonlinear dissipation is the Fisher information relative to the
frozen Gibbs reference of the competitor itself. -/
theorem nonlinearDissipation_eq_frozenInformation (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (ρ : AbsoluteDensity d) :
    scalarDissipation A b ρ =
      ordinaryRelativeFisher (densityMeasure ρ : Measure (Torus d))
        (frozenGibbs A (densityMeasure ρ)) :=
  (frozenInformation_eq_score A hLip b ρ ρ).symm

/-- **STR002 (species).** `D_θ = ∑ θ_s I(ρ_s m | P(ρ̄ m))` with the common reference
`P(ρ̄ m)`; no lower bound on the positive weights is needed. -/
theorem speciesDissipation_eq_frozenInformation (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (F : SpeciesFamily d) :
    speciesDissipation A b F =
      ∑ s, ENNReal.ofReal (F.weight s) *
        ordinaryRelativeFisher
          (densityMeasure (F.density s) : Measure (Torus d))
          (frozenGibbs A (densityMeasure (barycenter F))) := by
  unfold speciesDissipation
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [frozenInformation_eq_score A hLip b (barycenter F) (F.density s)]
  rfl

end DGPS.Structural
