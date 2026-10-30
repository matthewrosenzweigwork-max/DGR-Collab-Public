import DGPS.Lipschitz.T01EquilibriumBridge
import DGPS.Structural.FrozenGibbsInformation
import DGPS.Variational.ScoreDecomposition

/-!
# Relative competitors at a positive Lipschitz reference

These domain and fixed-barycenter identities use the actual absolute species domain. The
reference density need only be positive Lipschitz; no smoothness is assumed.
-/

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- Change of measure against the positive Lipschitz reference representative. -/
theorem t01_integral_reference (P : BoundedPositiveReference d)
    (hP : P.hasPositiveLipschitzDensity) (f : Torus d → ℝ) :
    ∫ x, f x ∂P.measure = ∫ x, P.density x * f x ∂haar d := by
  rw [BoundedPositiveReference.measure,
    integral_withDensity_eq_integral_toReal_smul P.measurable_ofReal_density
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (RelativeFisher.density_pos hP x).le]

/-- A normalized nonnegative relative form-domain test gives an absolute competitor. -/
noncomputable def t01RelativeAbsoluteDensity (P : BoundedPositiveReference d)
    (hP : P.hasPositiveLipschitzDensity) (u : Torus d → ℝ)
    (hu : u ∈ WeightedH1 P) (hu0 : ∀ x, 0 ≤ u x)
    (h1 : ∫ x, u x ^ 2 ∂P.measure = 1) : AbsoluteDensity d where
  sqrt := fun x => P.density x ^ (1 / 2 : ℝ) * u x
  sqrt_mem := (RelativeFisher.memWeightedH1_iff_memH1_mul_sqrt hP).mp hu
  sqrt_nonneg := Eventually.of_forall fun x =>
    mul_nonneg (Real.rpow_pos_of_pos (RelativeFisher.density_pos hP x) _).le (hu0 x)
  mass_one := by
    have hs : ∀ x, (P.density x ^ (1 / 2 : ℝ) * u x) ^ 2 = P.density x * u x ^ 2 := by
      intro x
      rw [mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (RelativeFisher.density_pos hP x).le]
    simp_rw [hs]
    rw [← t01_integral_reference P hP (fun x => u x ^ 2)]
    exact h1

theorem t01RelativeAbsoluteDensity_density (P : BoundedPositiveReference d)
    (hP : P.hasPositiveLipschitzDensity) (u : Torus d → ℝ)
    (hu : u ∈ WeightedH1 P) (hu0 : ∀ x, 0 ≤ u x)
    (h1 : ∫ x, u x ^ 2 ∂P.measure = 1) (x : Torus d) :
    (t01RelativeAbsoluteDensity P hP u hu hu0 h1).density x = P.density x * u x ^ 2 := by
  change (P.density x ^ (1 / 2 : ℝ) * u x) ^ 2 = _
  rw [mul_pow, ← Real.sqrt_eq_rpow, Real.sq_sqrt (RelativeFisher.density_pos hP x).le]

/-- The relative-to-absolute construction represents the exact tilted reference measure. -/
theorem t01RelativeAbsoluteDensity_measure (P : BoundedPositiveReference d)
    (hP : P.hasPositiveLipschitzDensity) (u : Torus d → ℝ)
    (hu : u ∈ WeightedH1 P) (hu0 : ∀ x, 0 ≤ u x)
    (h1 : ∫ x, u x ^ 2 ∂P.measure = 1) :
    (densityMeasure (t01RelativeAbsoluteDensity P hP u hu hu0 h1) : Measure (Torus d)) =
      P.measure.withDensity (fun x => ENNReal.ofReal (u x ^ 2)) := by
  have hum : AEMeasurable u (haar d) :=
    ((mem_weightedH1_iff P).mp hu).choose_spec.memLp.aestronglyMeasurable.aemeasurable
  rw [BoundedPositiveReference.measure,
    ← withDensity_mul₀ P.measurable_ofReal_density.aemeasurable (hum.pow_const 2).ennreal_ofReal]
  change (haar d).withDensity (fun x => ENNReal.ofReal
    ((t01RelativeAbsoluteDensity P hP u hu hu0 h1).density x)) = _
  apply withDensity_congr_ae
  exact Eventually.of_forall fun x => by
    change ENNReal.ofReal ((t01RelativeAbsoluteDensity P hP u hu hu0 h1).density x) =
      ENNReal.ofReal (P.density x) * ENNReal.ofReal (u x ^ 2)
    rw [t01RelativeAbsoluteDensity_density]
    exact ENNReal.ofReal_mul (RelativeFisher.density_pos hP x).le

/-- Entropy of the constructed absolute competitor is exactly its relative-test entropy. -/
theorem t01RelativeAbsoluteDensity_entropy (P : BoundedPositiveReference d)
    (hP : P.hasPositiveLipschitzDensity) (u : Torus d → ℝ)
    (hu : u ∈ WeightedH1 P) (hu0 : ∀ x, 0 ≤ u x)
    (h1 : ∫ x, u x ^ 2 ∂P.measure = 1) :
    relativeEntropy (densityMeasure (t01RelativeAbsoluteDensity P hP u hu hu0 h1)) P.measure =
      homogeneousEntropy P.measure (fun x => u x ^ 2) := by
  rw [t01RelativeAbsoluteDensity_measure]
  exact relativeEntropy_withDensity (Eventually.of_forall fun x => sq_nonneg (u x))
    (hu.choose_spec.memLp.aestronglyMeasurable.aemeasurable.pow_const 2)

/-- Information of the constructed absolute competitor is the weighted test energy. -/
theorem t01RelativeAbsoluteDensity_fisher (P : BoundedPositiveReference d)
    (hP : P.hasPositiveLipschitzDensity) (u : Torus d → ℝ)
    (hu : u ∈ WeightedH1 P) (hu0 : ∀ x, 0 ≤ u x)
    (h1 : ∫ x, u x ^ 2 ∂P.measure = 1) :
    ordinaryRelativeFisher (densityMeasure (t01RelativeAbsoluteDensity P hP u hu hu0 h1)) P =
      4 * ∫⁻ x, ‖weightedGradient P u hu x‖ₑ ^ 2 ∂P.measure := by
  rw [t01RelativeAbsoluteDensity_measure]
  have hum : AEMeasurable (fun x => ENNReal.ofReal (u x ^ 2)) P.measure :=
    (hu.choose_spec.memLp.aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  have hrel : relativeSqrt (P.measure.withDensity (fun x => ENNReal.ofReal (u x ^ 2))) P =ᵐ[P.measure] u := by
    filter_upwards [Measure.rnDeriv_withDensity₀ P.measure hum] with x hx
    change Real.sqrt ((P.measure.withDensity (fun x => ENNReal.ofReal (u x ^ 2))).rnDeriv
      P.measure x).toReal = u x
    rw [hx, ENNReal.toReal_ofReal (sq_nonneg _), Real.sqrt_sq (hu0 x)]
  have hrelHaar : relativeSqrt (P.measure.withDensity (fun x => ENNReal.ofReal (u x ^ 2))) P =ᵐ[haar d] u :=
    P.haar_ac_measure.ae_le hrel
  apply ordinaryRelativeFisher_eq (withDensity_absolutelyContinuous _ _)
  exact ((isWeightedWeakGradient_iff P).mp
    (isWeightedWeakGradient_weightedGradient P hu)).congr_ae
    hrelHaar.symm (EventuallyEq.refl _ _)

/-- Two normalized relative tests with exact complementary squared masses have the reference
as their exact barycenter, on the actual absolute-domain species family. -/
theorem t01_relative_twoSpecies_barycenter (P : BoundedPositiveReference d)
    (hP : P.hasPositiveLipschitzDensity) (u v : Torus d → ℝ)
    (hu : u ∈ WeightedH1 P) (hv : v ∈ WeightedH1 P)
    (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x)
    (hu1 : ∫ x, u x ^ 2 ∂P.measure = 1) (hv1 : ∫ x, v x ^ 2 ∂P.measure = 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hmix : ∀ x, ε * u x ^ 2 + (1 - ε) * v x ^ 2 = 1) :
    let F := SpeciesFamily.twoSpecies ε hε0 hε1
      (t01RelativeAbsoluteDensity P hP u hu hu0 hu1)
      (t01RelativeAbsoluteDensity P hP v hv hv0 hv1)
    (densityMeasure (barycenter F) : Measure (Torus d)) = P.measure := by
  intro F
  change (haar d).withDensity (fun x => ENNReal.ofReal ((barycenter F).density x)) = _
  rw [BoundedPositiveReference.measure]
  apply withDensity_congr_ae
  refine Eventually.of_forall fun x => congrArg ENNReal.ofReal ?_
  have hsum : (barycenter F).density x =
      ε * (P.density x * u x ^ 2) + (1 - ε) * (P.density x * v x ^ 2) := by
    rw [F.barycenter_density_eq_sum]
    change (∑ s : Fin 2, (if s.val = 0 then ε else 1 - ε) *
      (if s.val = 0 then t01RelativeAbsoluteDensity P hP u hu hu0 hu1
        else t01RelativeAbsoluteDensity P hP v hv hv0 hv1).density x) = _
    simp [Fin.sum_univ_two, t01RelativeAbsoluteDensity_density]
  rw [hsum]
  linear_combination P.density x * hmix x

/-- At a minimizing barycenter, the species gap is exactly the weighted relative entropy. -/
theorem t01_speciesGap_at_minimizing_barycenter (A : InteractionData d) (F : SpeciesFamily d)
    {μ : ProbabilityMeasure (Torus d)} (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    (hbar : densityMeasure (barycenter F) = μ) :
    (speciesGap A F : ℝ) =
      ∑ s, F.weight s *
        (relativeEntropy (densityMeasure (F.density s)) (μ : Measure (Torus d))).toReal := by
  rw [DGPS.SpeciesFamily.speciesGap_decomposition A F]
  have hgap : scalarGap A (barycenter F) = 0 :=
    (scalarGap_eq_zero_iff_minimizer A (barycenter F)).mpr (by rw [hbar]; exact hμ)
  rw [hgap, NNReal.coe_zero, zero_add, hbar]

/-- At a fixed minimizing barycenter, the common force is exactly the reference information. -/
theorem t01_speciesDissipation_at_minimizing_barycenter (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (F : SpeciesFamily d)
    {μ : ProbabilityMeasure (Torus d)} (hbar : densityMeasure (barycenter F) = μ) :
    speciesDissipation A b F =
      ∑ s, ENNReal.ofReal (F.weight s) * ordinaryRelativeFisher
        (densityMeasure (F.density s)) (frozenGibbs A μ) := by
  rw [DGPS.Structural.speciesDissipation_eq_frozenInformation A hLip b F, hbar]

end DGPS.Lipschitz
