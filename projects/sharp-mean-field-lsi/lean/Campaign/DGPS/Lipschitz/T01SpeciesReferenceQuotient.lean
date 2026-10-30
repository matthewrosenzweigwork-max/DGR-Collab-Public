import DGPS.Lipschitz.T01SpeciesReferenceRate
import DGPS.FiniteN.Tools.Rothaus

/-!
# Exact fixed-reference species quotient bounds
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- At a minimizing barycenter each weighted reference entropy is bounded by the species gap. -/
theorem t01_weighted_entropy_le_speciesGap (A : InteractionData d) (F : SpeciesFamily d)
    {μ : ProbabilityMeasure (Torus d)} (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    (hbar : densityMeasure (barycenter F) = μ) (s : Fin F.count) :
    ENNReal.ofReal (F.weight s) * relativeEntropy (densityMeasure (F.density s))
      (μ : Measure (Torus d)) ≤ (speciesGap A F : ℝ≥0∞) := by
  have hfin : relativeEntropy (densityMeasure (F.density s)) (μ : Measure (Torus d)) ≠ ⊤ := by
    rw [← hbar]
    exact (F.relativeEntropy_species s).2.1
  have hr : F.weight s * (relativeEntropy (densityMeasure (F.density s))
      (μ : Measure (Torus d))).toReal ≤ (speciesGap A F : ℝ) := by
    rw [t01_speciesGap_at_minimizing_barycenter A F hμ hbar]
    exact Finset.single_le_sum
      (f := fun i => F.weight i * (relativeEntropy (densityMeasure (F.density i))
        (μ : Measure (Torus d))).toReal)
      (fun i _ => mul_nonneg (F.weight_nonneg i) ENNReal.toReal_nonneg) (Finset.mem_univ s)
  have h := ENNReal.ofReal_le_ofReal hr
  simpa only [ENNReal.ofReal_mul (F.weight_nonneg s), ENNReal.ofReal_toReal hfin,
    ENNReal.ofReal_coe_nnreal] using h

/-- The relative Fisher information is four times the real weighted Dirichlet energy. -/
theorem t01_relative_fisher_real_energy (P : BoundedPositiveReference d)
    (hP : P.hasPositiveLipschitzDensity) (u : Torus d → ℝ)
    (hu : u ∈ WeightedH1 P) (hu0 : ∀ x, 0 ≤ u x)
    (h1 : ∫ x, u x ^ 2 ∂P.measure = 1) :
    ordinaryRelativeFisher (densityMeasure (t01RelativeAbsoluteDensity P hP u hu hu0 h1)) P =
      ENNReal.ofReal (4 * ∫ x, ‖weightedGradient P u hu x‖ ^ 2 ∂P.measure) := by
  rw [t01RelativeAbsoluteDensity_fisher, ENNReal.ofReal_mul (by norm_num),
    ENNReal.ofReal_ofNat]
  congr 1
  rw [ofReal_integral_eq_lintegral_ofReal
    (isWeightedWeakGradient_weightedGradient P hu).memLp_grad.norm.integrable_sq
    (Eventually.of_forall fun x => sq_nonneg _)]
  apply lintegral_congr
  intro x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/-- An exact complementary pair gives the quantitative species upper bound needed for
binary dilution. The reference is the actual minimizing Gibbs law. -/
theorem t01_relative_pair_rate_bound (A : InteractionData d) (hLip : LipschitzData A)
    (b : AbsoluteDrift A) {μ : ProbabilityMeasure (Torus d)}
    (hμ : DGPS.freeEnergy A μ = DGPS.freeEnergyMinimum A)
    (u v : Torus d → ℝ) (hu : u ∈ WeightedH1 (frozenGibbs A μ))
    (hv : v ∈ WeightedH1 (frozenGibbs A μ))
    (hu0 : ∀ x, 0 ≤ u x) (hv0 : ∀ x, 0 ≤ v x)
    (hu1 : ∫ x, u x ^ 2 ∂(frozenGibbs A μ).measure = 1)
    (hv1 : ∫ x, v x ^ 2 ∂(frozenGibbs A μ).measure = 1)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hmix : ∀ x, ε * u x ^ 2 + (1 - ε) * v x ^ 2 = 1)
    (hent : 0 < homogeneousEntropy (frozenGibbs A μ).measure (fun x => u x ^ 2)) :
    speciesRate A b ≤
      (ENNReal.ofReal ε * ENNReal.ofReal
          (4 * ∫ x, ‖weightedGradient (frozenGibbs A μ) u hu x‖ ^ 2 ∂(frozenGibbs A μ).measure) +
        ENNReal.ofReal (1 - ε) * ENNReal.ofReal
          (4 * ∫ x, ‖weightedGradient (frozenGibbs A μ) v hv x‖ ^ 2 ∂(frozenGibbs A μ).measure)) /
      (2 * (ENNReal.ofReal ε * homogeneousEntropy (frozenGibbs A μ).measure
        (fun x => u x ^ 2))) := by
  let P := frozenGibbs A μ
  have hP := frozenGibbs_hasPositiveLipschitzDensity A hLip μ
  let ρu := t01RelativeAbsoluteDensity P hP u hu hu0 hu1
  let ρv := t01RelativeAbsoluteDensity P hP v hv hv0 hv1
  let F := SpeciesFamily.twoSpecies ε hε0 hε1 ρu ρv
  have hfix : (μ : Measure (Torus d)) = P.measure := DGPS.Structural.minimizer_eq_frozenGibbs A hμ
  have hbar : densityMeasure (barycenter F) = μ := by
    apply Subtype.ext
    exact (t01_relative_twoSpecies_barycenter P hP u v hu hv hu0 hv0 hu1 hv1
      ε hε0 hε1 hmix).trans hfix.symm
  have hEntu : relativeEntropy (densityMeasure ρu) (μ : Measure (Torus d)) =
      homogeneousEntropy P.measure (fun x => u x ^ 2) := by
    rw [hfix]
    exact t01RelativeAbsoluteDensity_entropy P hP u hu hu0 hu1
  have hgap := t01_weighted_entropy_le_speciesGap A F hμ hbar (⟨0, by change 0 < 2; decide⟩)
  change ENNReal.ofReal ε * relativeEntropy (densityMeasure ρu) (μ : Measure (Torus d)) ≤
    (speciesGap A F : ℝ≥0∞) at hgap
  rw [hEntu] at hgap
  have hG : 0 < speciesGap A F := by
    have hz := (ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hε0).ne' hent.ne').trans_le hgap
    exact_mod_cast hz
  have hD : speciesDissipation A b F =
      ENNReal.ofReal ε * ENNReal.ofReal
        (4 * ∫ x, ‖weightedGradient P u hu x‖ ^ 2 ∂P.measure) +
      ENNReal.ofReal (1 - ε) * ENNReal.ofReal
        (4 * ∫ x, ‖weightedGradient P v hv x‖ ^ 2 ∂P.measure) := by
    rw [t01_speciesDissipation_at_minimizing_barycenter A hLip b F hbar]
    change (∑ s : Fin 2, ENNReal.ofReal (F.weight s) *
      ordinaryRelativeFisher (densityMeasure (F.density s)) P) = _
    simp only [Fin.sum_univ_two]
    change ENNReal.ofReal ε * ordinaryRelativeFisher (densityMeasure ρu) P +
      ENNReal.ofReal (1 - ε) * ordinaryRelativeFisher (densityMeasure ρv) P = _
    rw [t01_relative_fisher_real_energy, t01_relative_fisher_real_energy]
  refine (speciesRate_le A b F hG).trans ?_
  unfold speciesQuotient
  rw [hD]
  have hden : 2 * (ENNReal.ofReal ε * homogeneousEntropy P.measure (fun x => u x ^ 2)) ≤
      2 * (speciesGap A F : ℝ≥0∞) := by gcongr
  exact ENNReal.div_le_div_left hden _

end DGPS.Lipschitz
