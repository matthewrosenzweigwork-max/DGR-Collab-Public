import DGPS.Structural.FrozenGibbsInformation
import DGPS.Structural.FrozenGibbsIdentities
import DGPS.Analysis.BoundedPerturbation
import DGPS.Model.FreeEnergy

/-
STR017: circle frozen entropy budget.

For a finite absolute family with barycenter `ν = ρ̄ m`, set `H_fr = ∑ θ_s H(ρ_s m | P_ν)`,
`G = speciesGap`, `D = speciesDissipation`, `M = osc V + osc W`. Then
`G ≤ H_fr + M` and `D ≥ 2ℓ H_fr ≥ 2ℓ (G - M)`, `ℓ = frozenLSRateInf`.

Route (R5): self-contained, via Mathlib's `integral_llr_tilted_right` and the STR002 identity
`speciesDissipation_eq_frozenInformation`; the per-species frozen LSI is proved locally.
-/

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

namespace DGPS.Structural

variable {d : ℕ}

theorem budget_measure_eq_tilted (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) :
    (frozenGibbs A ν).measure =
      (haar d).tilted (fun x => -frozenPotential A (ν : Measure (Torus d)) x) := rfl

theorem budget_entropy_frozen (A : InteractionData d) (ν : ProbabilityMeasure (Torus d))
    (ρ : AbsoluteDensity d) :
    relativeEntropy (densityMeasure ρ : Measure (Torus d)) (frozenGibbs A ν).measure ≠ ⊤ ∧
    (relativeEntropy (densityMeasure ρ : Measure (Torus d)) (frozenGibbs A ν).measure).toReal =
      (relativeEntropy (densityMeasure ρ : Measure (Torus d)) (haar d)).toReal +
        ∫ x, frozenPotential A (ν : Measure (Torus d)) x ∂(densityMeasure ρ : Measure (Torus d)) +
          Real.log (frozenPartition A (ν : Measure (Torus d))) := by
  have hfin := (absoluteDensity_entropy_finite ρ).2.2.1
  have hH : (relativeEntropy (densityMeasure ρ : Measure (Torus d)) (haar d)) =
      klDiv (densityMeasure ρ : Measure (Torus d)) (haar d) := Analysis.relativeEntropy_eq_klDiv
  have hP : relativeEntropy (densityMeasure ρ : Measure (Torus d)) (frozenGibbs A ν).measure =
      klDiv (densityMeasure ρ : Measure (Torus d)) (frozenGibbs A ν).measure :=
    Analysis.relativeEntropy_eq_klDiv
  rw [hH] at hfin ⊢
  rw [hP]
  have hμac : (densityMeasure ρ : Measure (Torus d)) ≪ haar d :=
    withDensity_absolutelyContinuous _ _
  have hint := (klDiv_ne_top_iff.1 hfin).2
  have hcont : Continuous (fun x => -frozenPotential A (ν : Measure (Torus d)) x) :=
    (frozenPotential_continuous A (ν : Measure (Torus d))).neg
  have hfμ : Integrable (fun x => -frozenPotential A (ν : Measure (Torus d)) x)
      (densityMeasure ρ : Measure (Torus d)) :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hfν : Integrable (fun x => Real.exp (-frozenPotential A (ν : Measure (Torus d)) x))
      (haar d) := integrable_exp_neg_frozenPotential A (ν : Measure (Torus d))
  have hac : (densityMeasure ρ : Measure (Torus d)) ≪ (frozenGibbs A ν).measure :=
    hμac.trans (frozenGibbs A ν).haar_ac_measure
  have hl := integral_llr_tilted_right hμac hfμ hfν hint
  have hli := integrable_llr_tilted_right hμac hfμ hint hfν
  rw [← budget_measure_eq_tilted] at hl hli
  refine ⟨klDiv_ne_top_iff.2 ⟨hac, hli⟩, ?_⟩
  rw [toReal_klDiv_of_measure_eq hac (by simp), toReal_klDiv_of_measure_eq hμac (by simp), hl,
    integral_neg]
  unfold frozenPartition
  ring


/-- The frozen LSI applied to one species: `2 r_LS(P) H(ν | P) ≤ I(ν | P)`. -/
theorem budget_lsi_fisher (P : BoundedPositiveReference d) (ν : Measure (Torus d))
    (hH : relativeEntropy ν P.measure ≠ ⊤) :
    2 * ordinaryLSRate P * relativeEntropy ν P.measure ≤ ordinaryRelativeFisher ν P := by
  by_cases hac : ν ≪ P.measure
  swap
  · exact absurd (relativeEntropy_of_not_absolutelyContinuous hac) hH
  by_cases hmem : relativeSqrt ν P ∈ WeightedH1 P
  swap
  · rw [ordinaryRelativeFisher_of_not_mem hmem]; exact le_top
  have hE : relativeEntropy ν P.measure =
      homogeneousEntropy P.measure (fun x => relativeSqrt ν P x ^ 2) := by
    rw [relativeEntropy_of_absolutelyContinuous hac]
    congr 1
    funext x
    unfold relativeSqrt
    rw [Real.sq_sqrt ENNReal.toReal_nonneg]
  by_cases h0 : relativeEntropy ν P.measure = 0
  · rw [h0]; simp
  have hpos : 0 < homogeneousEntropy P.measure (fun x => relativeSqrt ν P x ^ 2) := by
    rw [← hE]; exact pos_iff_ne_zero.2 h0
  have hle : ordinaryLSRate P ≤
      2 * (∫⁻ x, ‖weightedGradient P (relativeSqrt ν P) hmem x‖ₑ ^ 2 ∂P.measure) /
        homogeneousEntropy P.measure (fun x => relativeSqrt ν P x ^ 2) := by
    unfold ordinaryLSRate
    exact iInf_le _ (⟨relativeSqrt ν P, hmem, hpos⟩ :
      {f : Torus d → ℝ // f ∈ WeightedH1 P ∧
        0 < homogeneousEntropy P.measure (fun x => f x ^ 2)})
  rw [← hE] at hle
  rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl hH)] at hle
  rw [ordinaryRelativeFisher, dite_eq_left_of_eq_true (eq_true ⟨hac, hmem⟩)]
  calc 2 * ordinaryLSRate P * relativeEntropy ν P.measure
      = 2 * (ordinaryLSRate P * relativeEntropy ν P.measure) := by rw [mul_assoc]
    _ ≤ 2 * (2 * ∫⁻ x, ‖weightedGradient P (relativeSqrt ν P) hmem x‖ₑ ^ 2 ∂P.measure) :=
        by gcongr
    _ = 4 * ∫⁻ x, ‖weightedGradient P (relativeSqrt ν P) hmem x‖ₑ ^ 2 ∂P.measure := by
        rw [← mul_assoc]; norm_num


/-! ### Elementary integral identities -/

theorem budget_aemeasurable_density (ρ : AbsoluteDensity d) :
    AEMeasurable ρ.density (haar d) :=
  ρ.memLp_sqrt.aestronglyMeasurable.aemeasurable.pow_const 2

theorem budget_integral_densityMeasure (ρ : AbsoluteDensity d) (g : Torus d → ℝ) :
    ∫ x, g x ∂(densityMeasure ρ : Measure (Torus d)) = ∫ x, ρ.density x * g x ∂haar d := by
  have h1 : AEMeasurable (fun x => ENNReal.ofReal (ρ.sqrt x ^ 2)) (haar d) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (budget_aemeasurable_density ρ)
  rw [densityMeasure_coe, integral_withDensity_eq_integral_toReal_smul₀ h1
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  rw [AbsoluteDensity.density, ENNReal.toReal_ofReal (sq_nonneg _)]

/-- Linearity of continuous integrals in the species decomposition of the barycenter. -/
theorem budget_integral_barycenter (F : SpeciesFamily d) {g : Torus d → ℝ} (hg : Continuous g) :
    ∫ x, g x ∂(densityMeasure (barycenter F) : Measure (Torus d)) =
      ∑ s, F.weight s * ∫ x, g x ∂(densityMeasure (F.density s) : Measure (Torus d)) := by
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  have hint : ∀ s : Fin F.count, Integrable (fun x => (F.density s).density x * g x) (haar d) :=
    fun s => (F.density s).integrable_density.mul_bdd hg.aestronglyMeasurable (c := C)
      (Filter.Eventually.of_forall fun x => hC x (Set.mem_univ x))
  rw [budget_integral_densityMeasure]
  have e : ∀ x, (barycenter F).density x * g x =
      ∑ s, F.weight s * ((F.density s).density x * g x) := fun x => by
    rw [SpeciesFamily.barycenter_density_apply, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by simp [AbsoluteDensity.density]; ring
  simp_rw [e]
  rw [integral_finsetSum _ fun s _ => (hint s).const_mul _]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_const_mul, budget_integral_densityMeasure]

/-- `∫ (V + W*ν) dν = ∫ V dν + ∬ W dν²`. -/
theorem budget_integral_frozenPotential (A : InteractionData d)
    (μ : ProbabilityMeasure (Torus d)) :
    ∫ x, frozenPotential A (μ : Measure (Torus d)) x ∂(μ : Measure (Torus d)) =
      potentialEnergy A (μ : Measure (Torus d)) + interactionEnergy A (μ : Measure (Torus d)) := by
  have hW : Continuous (fun x => ∫ y, A.W x y ∂(μ : Measure (Torus d))) := by
    have h : Continuous (fun x => ∫ y in (Set.univ : Set (Torus d)), A.W x y
        ∂(μ : Measure (Torus d))) :=
      continuous_parametric_integral_of_continuous (f := A.W) A.W_continuous isCompact_univ
    simpa only [Measure.restrict_univ] using h
  unfold frozenPotential potentialEnergy
  rw [integral_add
    (A.V_continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (hW.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))]
  unfold interactionEnergy
  rw [integral_prod _ (integrable_W_prod A μ)]

/-! ### The three amplitude bounds -/

theorem budget_le_interactionEnergy (A : InteractionData d) (μ : ProbabilityMeasure (Torus d)) :
    sInf (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) ≤
      interactionEnergy A (μ : Measure (Torus d)) := by
  have := integral_mono (integrable_const _) (integrable_W_prod A μ)
    (fun p : Torus d × Torus d => def025_le_W A p.1 p.2)
  simpa [interactionEnergy] using this

theorem budget_frozenPotential_le (A : InteractionData d) (ν : ProbabilityMeasure (Torus d))
    (x : Torus d) :
    frozenPotential A (ν : Measure (Torus d)) x ≤
      sSup (Set.range A.V) + sSup (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) := by
  unfold frozenPotential
  have hi : Integrable (fun y => A.W x y) (ν : Measure (Torus d)) :=
    (A.W_continuous_right x).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h := integral_mono hi (integrable_const _) (fun y => def025_W_le A x y)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  exact add_le_add (def025_V_le A x) h

theorem budget_neg_log_partition_le (A : InteractionData d) (ν : ProbabilityMeasure (Torus d)) :
    -Real.log (frozenPartition A (ν : Measure (Torus d))) ≤
      sSup (Set.range A.V) + sSup (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) := by
  set M := sSup (Set.range A.V) + sSup (Set.range fun p : Torus d × Torus d => A.W p.1 p.2)
  have h := integral_mono (integrable_const (Real.exp (-M)))
    (integrable_exp_neg_frozenPotential A (ν : Measure (Torus d)))
    (fun x => Real.exp_le_exp.2 (neg_le_neg (budget_frozenPotential_le A ν x)))
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
  have hZ := frozenPartition_pos A (ν : Measure (Torus d))
  have h2 := Real.log_le_log (Real.exp_pos _) h
  rw [Real.log_exp] at h2
  unfold frozenPartition at hZ ⊢
  linarith

theorem budget_le_freeEnergyMinimumReal (A : InteractionData d) :
    sInf (Set.range A.V) + (1 / 2 : ℝ) *
        sInf (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) ≤ freeEnergyMinimumReal A := by
  rw [← EReal.coe_le_coe_iff, coe_freeEnergyMinimumReal, freeEnergyMinimum]
  refine le_iInf fun ν => ?_
  have hV : sInf (Set.range A.V) ≤ potentialEnergy A (ν : Measure (Torus d)) := by
    have := integral_mono (integrable_const _)
      (A.V_continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
        (μ := (ν : Measure (Torus d))))
      (fun x => def025_le_V A x)
    simpa [potentialEnergy] using this
  have hW := budget_le_interactionEnergy A ν
  have hreal : sInf (Set.range A.V) + (1 / 2 : ℝ) *
        sInf (Set.range fun p : Torus d × Torus d => A.W p.1 p.2) ≤
      potentialEnergy A (ν : Measure (Torus d)) +
        (1 / 2 : ℝ) * interactionEnergy A (ν : Measure (Torus d)) := by
    nlinarith
  have h0 : (0 : EReal) ≤ ((relativeEntropy (ν : Measure (Torus d)) (haar d) : ℝ≥0∞) : EReal) :=
    EReal.coe_ennreal_nonneg _
  unfold freeEnergy
  calc _ ≤ ((potentialEnergy A (ν : Measure (Torus d)) +
          (1 / 2 : ℝ) * interactionEnergy A (ν : Measure (Torus d)) : ℝ) : EReal) :=
        EReal.coe_le_coe_iff.2 hreal
    _ = (0 : EReal) + ((potentialEnergy A ν : ℝ) : EReal) +
          (((1 / 2 : ℝ) * interactionEnergy A ν : ℝ) : EReal) := by
        rw [zero_add, EReal.coe_add]
    _ ≤ _ := add_le_add (add_le_add h0 le_rfl) le_rfl

/-! ### The frozen entropy budget -/

/-- The frozen entropy `H_fr = ∑ θ_s H(ρ_s m | P_ν)` with `ν = ρ̄ m`, in `ℝ≥0∞`. -/
noncomputable def frozenEntropy (A : InteractionData d) (F : SpeciesFamily d) : ℝ≥0∞ :=
  ∑ s, ENNReal.ofReal (F.weight s) *
    relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
      (frozenGibbs A (densityMeasure (barycenter F))).measure

/-- **STR017.** Circle frozen entropy budget: `H_fr` is finite, `G ≤ H_fr + M`, and
`D ≥ 2 ℓ H_fr ≥ 2 ℓ (G - M)`, where `ℓ = frozenLSRateInf A` and `M = osc V + osc W`. -/
theorem speciesGap_le_frozenEntropy_add_amplitude (A : InteractionData d)
    (hLip : LipschitzData A) (b : AbsoluteDrift A) (F : SpeciesFamily d) :
    frozenEntropy A F ≠ ⊤ ∧
    (speciesGap A F : ℝ) ≤ (frozenEntropy A F).toReal + totalOscillation A ∧
    2 * frozenLSRateInf A * frozenEntropy A F ≤ speciesDissipation A b F ∧
    2 * frozenLSRateInf A * ENNReal.ofReal ((speciesGap A F : ℝ) - totalOscillation A) ≤
      2 * frozenLSRateInf A * frozenEntropy A F := by
  set ν : ProbabilityMeasure (Torus d) := densityMeasure (barycenter F) with hν
  have hfin : ∀ s, relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
      (frozenGibbs A ν).measure ≠ ⊤ := fun s => (budget_entropy_frozen A ν (F.density s)).1
  have hne : frozenEntropy A F ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun s _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin s)
  have hsum : (frozenEntropy A F).toReal =
      ∑ s, F.weight s * ((relativeEntropy (densityMeasure (F.density s)) (haar d)).toReal +
        ∫ x, frozenPotential A (ν : Measure (Torus d)) x
          ∂(densityMeasure (F.density s) : Measure (Torus d)) +
        Real.log (frozenPartition A (ν : Measure (Torus d)))) := by
    unfold frozenEntropy
    rw [ENNReal.toReal_sum fun s _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin s)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (F.weight_nonneg s),
      (budget_entropy_frozen A ν (F.density s)).2]
  have hbary := budget_integral_barycenter F (frozenPotential_continuous A (ν : Measure (Torus d)))
  have hpot := budget_integral_frozenPotential A ν
  have hsum2 : (frozenEntropy A F).toReal =
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar d)).toReal +
        potentialEnergy A (ν : Measure (Torus d)) + interactionEnergy A (ν : Measure (Torus d)) +
        Real.log (frozenPartition A (ν : Measure (Torus d))) := by
    rw [hsum]
    have e : ∀ s, F.weight s * ((relativeEntropy (densityMeasure (F.density s)) (haar d)).toReal +
        ∫ x, frozenPotential A (ν : Measure (Torus d)) x
          ∂(densityMeasure (F.density s) : Measure (Torus d)) +
        Real.log (frozenPartition A (ν : Measure (Torus d)))) =
        F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar d)).toReal +
        F.weight s * ∫ x, frozenPotential A (ν : Measure (Torus d)) x
          ∂(densityMeasure (F.density s) : Measure (Torus d)) +
        F.weight s * Real.log (frozenPartition A (ν : Measure (Torus d))) := fun s => by ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← hbary, hpot, ← Finset.sum_mul,
      F.weight_sum]
    ring
  have hG : (speciesGap A F : ℝ) =
      (frozenEntropy A F).toReal - (1 / 2 : ℝ) * interactionEnergy A (ν : Measure (Torus d)) -
        Real.log (frozenPartition A (ν : Measure (Torus d))) - freeEnergyMinimumReal A := by
    rw [coe_speciesGap, speciesRawGap, hsum2]
    ring
  have h1 := budget_le_interactionEnergy A ν
  have h2 := budget_neg_log_partition_le A ν
  have h3 := budget_le_freeEnergyMinimumReal A
  have hM : (speciesGap A F : ℝ) ≤ (frozenEntropy A F).toReal + totalOscillation A := by
    unfold totalOscillation potentialOscillation interactionOscillation
    rw [hG]
    linarith
  refine ⟨hne, hM, ?_, ?_⟩
  · rw [speciesDissipation_eq_frozenInformation A hLip b F]
    unfold frozenEntropy
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    calc 2 * frozenLSRateInf A *
          (ENNReal.ofReal (F.weight s) * relativeEntropy
            (densityMeasure (F.density s) : Measure (Torus d)) (frozenGibbs A ν).measure)
        = ENNReal.ofReal (F.weight s) * (2 * frozenLSRateInf A *
            relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
              (frozenGibbs A ν).measure) := by ring
      _ ≤ ENNReal.ofReal (F.weight s) * (2 * ordinaryLSRate (frozenGibbs A ν) *
            relativeEntropy (densityMeasure (F.density s) : Measure (Torus d))
              (frozenGibbs A ν).measure) := by
          gcongr
          exact frozenLSRateInf_le A ν
      _ ≤ _ := by
          gcongr
          exact budget_lsi_fisher _ _ (hfin s)
  · gcongr
    calc ENNReal.ofReal ((speciesGap A F : ℝ) - totalOscillation A)
        ≤ ENNReal.ofReal (frozenEntropy A F).toReal :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ = frozenEntropy A F := ENNReal.ofReal_toReal hne

end DGPS.Structural
