import DGPS.Particle.ConditionalSubsetScores
import DGPS.Model.SpeciesRate
import DGPS.Model.ScalarRate
import DGPS.Foundations.SobolevCalculus
import DGPS.Structural.SmallRateCircle
import DGPS.Lipschitz.T01EntropyCoercivity

/-!
# The current mean-field rate step for bounded positive conditional densities

The rate is applied to the actual absolute Sobolev family. The score identity below
identifies its canonical square-root dissipation with the classical density-score form.
Bounds on the density belong only to this regular conditional stage.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- A subrate controls every current family, including families of zero gap and infinite
extended dissipation. No regularity or positivity condition beyond the absolute domain is used. -/
theorem two_subrate_speciesGap_le (A : InteractionData d) (b : AbsoluteDrift A)
    {r : ℝ} (hr : 0 ≤ r) (hrr : ENNReal.ofReal r ≤ speciesRate A b)
    (F : SpeciesFamily d) :
    ENNReal.ofReal (2 * r * (speciesGap A F : ℝ)) ≤ speciesDissipation A b F := by
  by_cases hG : speciesGap A F = 0
  · simp [hG]
  have hpos : 0 < speciesGap A F := pos_iff_ne_zero.mpr hG
  have h := hrr.trans (speciesRate_le A b F hpos)
  unfold speciesQuotient at h
  have hg0 : (2 * (speciesGap A F : ℝ≥0∞)) ≠ 0 := by simp [hG]
  have hgt : (2 * (speciesGap A F : ℝ≥0∞)) ≠ ⊤ := ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
  have hh := (ENNReal.le_div_iff_mul_le (Or.inl hg0) (Or.inl hgt)).mp h
  have he : ENNReal.ofReal r * (2 * (speciesGap A F : ℝ≥0∞)) =
      ENNReal.ofReal (2 * r * (speciesGap A F : ℝ)) := by
    rw [ENNReal.ofReal_mul (mul_nonneg zero_le_two hr),
      ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
    ring
  rwa [he] at hh

/-- The scalar subrate has the identical extended-value interpretation on the unchanged
domain; the zero-gap case does not require division by zero. -/
theorem two_subrate_scalarGap_le (A : InteractionData d) (b : AbsoluteDrift A)
    {r : ℝ} (hr : 0 ≤ r) (hrr : ENNReal.ofReal r ≤ scalarRate A b)
    (ρ : AbsoluteDensity d) :
    ENNReal.ofReal (2 * r * (scalarGap A ρ : ℝ)) ≤ scalarDissipation A b ρ := by
  by_cases hG : scalarGap A ρ = 0
  · simp [hG]
  have hpos : 0 < scalarGap A ρ := pos_iff_ne_zero.mpr hG
  have h := hrr.trans (scalarRate_le_quotient A b ρ hpos)
  unfold scalarQuotient at h
  have hg0 : (2 * (scalarGap A ρ : ℝ≥0∞)) ≠ 0 := by simp [hG]
  have hgt : (2 * (scalarGap A ρ : ℝ≥0∞)) ≠ ⊤ := ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top
  have hh := (ENNReal.le_div_iff_mul_le (Or.inl hg0) (Or.inl hgt)).mp h
  have he : ENNReal.ofReal r * (2 * (scalarGap A ρ : ℝ≥0∞)) =
      ENNReal.ofReal (2 * r * (scalarGap A ρ : ℝ)) := by
    rw [ENNReal.ofReal_mul (mul_nonneg zero_le_two hr),
      ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
    ring
  rwa [he] at hh

/-- Every genuine density derivative agrees with the derivative obtained from the canonical
square root. Uniqueness is used in L1, so no boundedness assumption is needed. -/
theorem absolute_density_gradient_identity {d : ℕ} (ρ : AbsoluteDensity d)
    {g : Torus d → Tangent d} (hg : IsWeakGradient ρ.density g) :
    g =ᵐ[haar d] fun x => (2 * ρ.sqrt x) • weakGradient ρ.sqrt ρ.sqrt_mem x := by
  have h1 : IsWeakGradientLp 1 ρ.density g :=
    ⟨hg.memLp.mono_exponent one_le_two, hg.memLp_grad.mono_exponent one_le_two, hg.ibp⟩
  exact h1.ae_eq_of_one (DGPS.density_gradient ρ).1

/-- The absolute dissipation integrand equals the density times the squared density score.
The supplied derivative is genuine; no chosen representative derivative is assumed pointwise. -/
theorem positive_absolute_score_identity {d : ℕ} (ρ : AbsoluteDensity d)
    {g : Torus d → Tangent d} (hg : IsWeakGradient ρ.density g)
    (hpos : ∀ x, 0 < ρ.density x) (v : Torus d → Tangent d) :
    (fun x => ‖(2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • v x‖ ^ 2)
      =ᵐ[haar d] fun x => ρ.density x * ‖(ρ.density x)⁻¹ • g x + v x‖ ^ 2 := by
  filter_upwards [absolute_density_gradient_identity ρ hg] with x hx
  have hu : ρ.sqrt x ≠ 0 := by
    intro h
    have := hpos x
    simp [AbsoluteDensity.density, h] at this
  have he : (2 : ℝ) • weakGradient ρ.sqrt ρ.sqrt_mem x + ρ.sqrt x • v x =
      ρ.sqrt x • ((ρ.density x)⁻¹ • g x + v x) := by
    rw [hx, smul_add, smul_smul, smul_smul]
    congr 1
    congr 1
    dsimp [AbsoluteDensity.density]
    field_simp [hu]
    <;> ring
  rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rfl

/-- The genuine family dissipation in conditional-density score variables. The force is
that of the actual barycenter of the family, including in the nonsymmetric case. -/
theorem positive_speciesDissipation_eq (A : InteractionData d) (b : AbsoluteDrift A)
    (F : SpeciesFamily d) (g : Fin F.count → Torus d → Tangent d)
    (hg : ∀ s, IsWeakGradient (F.density s).density (g s))
    (hpos : ∀ s x, 0 < (F.density s).density x) :
    speciesDissipation A b F =
      ∑ s, ENNReal.ofReal (F.weight s) * ∫⁻ x, ENNReal.ofReal
        ((F.density s).density x *
          ‖((F.density s).density x)⁻¹ • g s x + b.force (barycenter F) x‖ ^ 2) ∂haar d := by
  unfold speciesDissipation
  refine Finset.sum_congr rfl fun s _ => congrArg (fun z => ENNReal.ofReal (F.weight s) * z) ?_
  apply lintegral_congr_ae
  exact (positive_absolute_score_identity (F.density s) (hg s)
    (hpos s) (b.force (barycenter F))).fun_comp ENNReal.ofReal

/-- The current family rate applied in the classical score variables used in conditioning.
No bound on the density score is required. -/
theorem two_subrate_positive_species_score_le (A : InteractionData d) (b : AbsoluteDrift A)
    {r : ℝ} (hr : 0 ≤ r) (hrr : ENNReal.ofReal r ≤ speciesRate A b)
    (F : SpeciesFamily d) (g : Fin F.count → Torus d → Tangent d)
    (hg : ∀ s, IsWeakGradient (F.density s).density (g s))
    (hpos : ∀ s x, 0 < (F.density s).density x) :
    ENNReal.ofReal (2 * r * (speciesGap A F : ℝ)) ≤
      ∑ s, ENNReal.ofReal (F.weight s) * ∫⁻ x, ENNReal.ofReal
        ((F.density s).density x *
          ‖((F.density s).density x)⁻¹ • g s x + b.force (barycenter F) x‖ ^ 2) ∂haar d := by
  rw [← positive_speciesDissipation_eq A b F g hg hpos]
  exact two_subrate_speciesGap_le A b hr hrr F

/-- The species gap relative to an actual minimizing Gibbs law. All species entropies
are finite as a consequence of the absolute domain; there is no extra competitor restriction. -/
theorem speciesGap_eq_reference_entropy_correction (A : InteractionData d)
    {μ : ProbabilityMeasure (Torus d)} (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (F : SpeciesFamily d) :
    (∀ s, relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
      (μ : Measure (Torus d)) ≠ ⊤) ∧
    (speciesGap A F : ℝ) =
      (∑ s, F.weight s * (relativeEntropy
        (densityMeasure (F.density s) : Measure (Torus d)) (μ : Measure (Torus d))).toReal) +
      t01CenteredCorrection A μ (densityMeasure (barycenter F)) := by
  have hfix := Structural.minimizer_eq_frozenGibbs A hμ
  have hs := fun s => Structural.budget_entropy_frozen A μ (F.density s)
  have hb := Structural.budget_entropy_frozen A μ (barycenter F)
  simp only [← hfix] at hs hb
  refine ⟨fun s => (hs s).1, ?_⟩
  have hsum : (∑ s, F.weight s * (relativeEntropy
        (densityMeasure (F.density s) : Measure (Torus d)) (μ : Measure (Torus d))).toReal) =
      (∑ s, F.weight s * (relativeEntropy
        (densityMeasure (F.density s) : Measure (Torus d)) (haar d)).toReal) +
      ∫ x, frozenPotential A (μ : Measure (Torus d)) x
        ∂(densityMeasure (barycenter F) : Measure (Torus d)) +
      Real.log (frozenPartition A (μ : Measure (Torus d))) := by
    simp_rw [(hs _).2, mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      F.weight_sum, one_mul,
      ← Structural.budget_integral_barycenter F
        (frozenPotential_continuous A (μ : Measure (Torus d)))]
  have hfin := (absoluteDensity_entropy_finite (barycenter F)).2.2.1
  have hE := freeEnergy_eq_real A (densityMeasure (barycenter F)) hfin
  have hsub := free_energy_sub_eq A μ
    (minimizer_eq_gibbs A μ (Structural.minimizer_le A hμ))
    (densityMeasure (barycenter F)) hfin
  have hbne : relativeEntropy (densityMeasure (barycenter F) : Measure (Torus d))
      (μ : Measure (Torus d)) ≠ ⊤ := hb.1
  rw [hE, hμ, ← coe_freeEnergyMinimumReal,
    ← EReal.coe_ennreal_toReal hbne, ← EReal.coe_sub, ← EReal.coe_add] at hsub
  have hreal := EReal.coe_injective hsub
  change (relativeEntropy (densityMeasure (barycenter F) : Measure (Torus d))
    (haar d)).toReal + potentialEnergy A (densityMeasure (barycenter F)) +
    (1 / 2 : ℝ) * interactionEnergy A (densityMeasure (barycenter F)) -
    freeEnergyMinimumReal A =
    (relativeEntropy (densityMeasure (barycenter F) : Measure (Torus d))
      (μ : Measure (Torus d))).toReal +
      t01CenteredCorrection A μ (densityMeasure (barycenter F)) at hreal
  rw [coe_speciesGap, speciesRawGap, hsum]
  linarith [hb.2]

/-- The actual multispecies rate supplies the conditional mean-field gap bound relative
to a minimizing Gibbs law. The companion score identity identifies its right side. -/
theorem two_subrate_reference_species_entropy_le (A : InteractionData d) (b : AbsoluteDrift A)
    {μ : ProbabilityMeasure (Torus d)} (hμ : freeEnergy A μ = freeEnergyMinimum A)
    {r : ℝ} (hr : 0 ≤ r) (hrr : ENNReal.ofReal r ≤ speciesRate A b)
    (F : SpeciesFamily d) :
    ENNReal.ofReal (2 * r *
      ((∑ s, F.weight s * (relativeEntropy
        (densityMeasure (F.density s) : Measure (Torus d)) (μ : Measure (Torus d))).toReal) +
      t01CenteredCorrection A μ (densityMeasure (barycenter F)))) ≤
      speciesDissipation A b F := by
  rw [← (speciesGap_eq_reference_entropy_correction A hμ F).2]
  exact two_subrate_speciesGap_le A b hr hrr F

end DGPS.Lipschitz
