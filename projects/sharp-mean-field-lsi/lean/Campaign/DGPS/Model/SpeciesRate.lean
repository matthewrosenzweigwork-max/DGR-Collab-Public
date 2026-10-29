import DGPS.Foundations.SobolevEntropy
import DGPS.Model.Barycenter
import DGPS.Model.Drift
import DGPS.Model.FreeEnergy
import DGPS.Model.SpeciesFamily

/-!
# Finite-species gap, dissipation and rate (DEF013)

INTERFACES/common_lemmas.md DEF013. For interaction data `A`, a weak-drift provider `b`, and a
finite species family `F` (species roots `u_s`, weights `θ_s`, barycenter `ρ̄ = ∑ θ_s u_s²`):

* `DGPS.speciesGap A F : ℝ≥0` is
  `G_θ = ∑ θ_s H(ρ_s | m) + ∫ V ρ̄ + (1/2) ∬ W ρ̄² - F_*`
  (`speciesRawGap`, a real number: every entropy is finite by DEF006 and `F_*` is finite by
  DEF008). It is nonnegative (`speciesRawGap_nonneg`) by the exact splitting
  `G_θ = [F(ρ̄) - F_*] + [∑ θ_s H(ρ_s) - H(ρ̄)]`: the first bracket is `≥ 0` by minimality of
  `F_*` (DEF008) and the second by the finite weighted Jensen inequality for `t ↦ t log t`
  integrated against Haar measure. The route does not use the later relative-entropy
  decomposition (LIP003/DEF014).
* `DGPS.speciesDissipation A b F : ℝ≥0∞` is
  `D_θ = ∑ θ_s ∫⁻ |2 ∇u_s + u_s b(ρ̄)|²`; the force `b.force (barycenter F)` depends only on the
  barycenter, not on the individual species.
* `DGPS.speciesRate A b : ℝ≥0∞` is `r_ms = inf_{G_θ > 0} D_θ / (2 G_θ)` over all species
  families with positive gap; the infimum over the empty set is `⊤`, and an infinite `D_θ`
  stays in the competitor class.
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS

variable {d : ℕ}

/-- When the relative entropy is finite, the free energy is the embedding of the real sum. -/
theorem freeEnergy_eq_real (A : InteractionData d) (ν : ProbabilityMeasure (Torus d))
    (h : relativeEntropy (ν : Measure (Torus d)) (haar d) ≠ ⊤) :
    freeEnergy A ν =
      (((relativeEntropy (ν : Measure (Torus d)) (haar d)).toReal + potentialEnergy A ν +
        (1 / 2 : ℝ) * interactionEnergy A ν : ℝ) : EReal) := by
  unfold freeEnergy
  rw [← EReal.coe_ennreal_toReal h, EReal.coe_add, EReal.coe_add]

/-- Minimality of `F_*` in real form, for a probability of finite entropy. -/
theorem freeEnergyMinimumReal_le (A : InteractionData d) (ν : ProbabilityMeasure (Torus d))
    (h : relativeEntropy (ν : Measure (Torus d)) (haar d) ≠ ⊤) :
    freeEnergyMinimumReal A ≤
      (relativeEntropy (ν : Measure (Torus d)) (haar d)).toReal + potentialEnergy A ν +
        (1 / 2 : ℝ) * interactionEnergy A ν := by
  have h1 : freeEnergyMinimum A ≤ freeEnergy A ν := iInf_le _ ν
  rw [← coe_freeEnergyMinimumReal, freeEnergy_eq_real A ν h, EReal.coe_le_coe_iff] at h1
  exact h1

/-! ### Jensen for `t log t` -/

/-- Finite weighted Jensen for `j(t) = t log t` on `[0, ∞)`, `j(0) = 0` (pointwise). -/
theorem mul_log_sum_le {ι : Type*} (s : Finset ι) (w a : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) (ha : ∀ i ∈ s, 0 ≤ a i) :
    (∑ i ∈ s, w i * a i) * Real.log (∑ i ∈ s, w i * a i) ≤
      ∑ i ∈ s, w i * (a i * Real.log (a i)) := by
  have := Real.convexOn_mul_log.map_sum_le hw hw1 (fun i hi => Set.mem_Ici.2 (ha i hi))
  simpa only [smul_eq_mul] using this

/-- Entropy of the barycenter is at most the weighted sum of the species entropies. -/
theorem barycenter_entropy_le (F : SpeciesFamily d) :
    (relativeEntropy (densityMeasure (barycenter F)) (haar d)).toReal ≤
      ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar d)).toReal := by
  obtain ⟨-, hsum⟩ := absoluteDensity_entropy_sum_finite (Finset.univ : Finset (Fin F.count))
    F.density
  obtain ⟨hI, hE⟩ := hsum F.weight
  rw [hE, (absoluteDensity_entropy_finite (barycenter F)).2.2.2]
  refine integral_mono (barycenter F).integrable_density_mul_log hI fun x => ?_
  have hb : (barycenter F).density x = ∑ s, F.weight s * (F.density s).density x :=
    F.barycenter_density_apply x
  rw [hb]
  exact mul_log_sum_le _ _ _ (fun s _ => F.weight_nonneg s) F.weight_sum
    (fun s _ => (F.density s).density_nonneg x)

/-! ### Gap -/

/-- The finite real species gap
`∑ θ_s H(ρ_s | m) + ∫ V ρ̄ + (1/2) ∬ W ρ̄² - F_*`. -/
noncomputable def speciesRawGap (A : InteractionData d) (F : SpeciesFamily d) : ℝ :=
  ∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar d)).toReal +
    potentialEnergy A (densityMeasure (barycenter F)) +
    (1 / 2 : ℝ) * interactionEnergy A (densityMeasure (barycenter F)) -
    freeEnergyMinimumReal A

/-- The raw gap splits as `[F(ρ̄) - F_*] + [∑ θ_s H(ρ_s) - H(ρ̄)]`. -/
theorem speciesRawGap_eq (A : InteractionData d) (F : SpeciesFamily d) :
    speciesRawGap A F =
      ((relativeEntropy (densityMeasure (barycenter F)) (haar d)).toReal +
          potentialEnergy A (densityMeasure (barycenter F)) +
          (1 / 2 : ℝ) * interactionEnergy A (densityMeasure (barycenter F)) -
        freeEnergyMinimumReal A) +
      (∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar d)).toReal -
        (relativeEntropy (densityMeasure (barycenter F)) (haar d)).toReal) := by
  unfold speciesRawGap; ring

/-- DEF013: the raw species gap is nonnegative. -/
theorem speciesRawGap_nonneg (A : InteractionData d) (F : SpeciesFamily d) :
    0 ≤ speciesRawGap A F := by
  rw [speciesRawGap_eq]
  have h1 := freeEnergyMinimumReal_le A (densityMeasure (barycenter F))
    (absoluteDensity_entropy_finite (barycenter F)).2.2.1
  have h2 := barycenter_entropy_le F
  linarith

/-- The species gap `G_θ ∈ ℝ≥0` (DEF013). -/
noncomputable def speciesGap (A : InteractionData d) (F : SpeciesFamily d) : ℝ≥0 :=
  ⟨speciesRawGap A F, speciesRawGap_nonneg A F⟩

@[simp] theorem coe_speciesGap (A : InteractionData d) (F : SpeciesFamily d) :
    (speciesGap A F : ℝ) = speciesRawGap A F := rfl

/-- The species gap is the exact decomposition into the barycenter free-energy gap and the
Jensen defect (both nonnegative). -/
theorem speciesGap_eq (A : InteractionData d) (F : SpeciesFamily d) :
    (speciesGap A F : ℝ) =
      ((relativeEntropy (densityMeasure (barycenter F)) (haar d)).toReal +
          potentialEnergy A (densityMeasure (barycenter F)) +
          (1 / 2 : ℝ) * interactionEnergy A (densityMeasure (barycenter F)) -
        freeEnergyMinimumReal A) +
      (∑ s, F.weight s * (relativeEntropy (densityMeasure (F.density s)) (haar d)).toReal -
        (relativeEntropy (densityMeasure (barycenter F)) (haar d)).toReal) :=
  speciesRawGap_eq A F

/-! ### Dissipation -/

/-- The species dissipation
`D_θ = ∑ θ_s ∫⁻ |2 ∇u_s + u_s b(ρ̄)|²` in `ℝ≥0∞`; the force is that of the barycenter only. -/
noncomputable def speciesDissipation (A : InteractionData d) (b : AbsoluteDrift A)
    (F : SpeciesFamily d) : ℝ≥0∞ :=
  ∑ s, ENNReal.ofReal (F.weight s) *
    ∫⁻ x, ENNReal.ofReal
      (‖(2 : ℝ) • F.sqrtGradient s x + (F.density s).sqrt x • b.force (barycenter F) x‖ ^ 2)
      ∂haar d

/-! ### Rate -/

/-- The quotient `D_θ / (2 G_θ)` in `ℝ≥0∞`. -/
noncomputable def speciesQuotient (A : InteractionData d) (b : AbsoluteDrift A)
    (F : SpeciesFamily d) : ℝ≥0∞ :=
  speciesDissipation A b F / (2 * (speciesGap A F : ℝ≥0∞))

/-- The multi-species rate `r_ms = inf_{G_θ > 0} D_θ / (2 G_θ)` over all species families with
positive gap; the empty infimum is `⊤`. -/
noncomputable def speciesRate (A : InteractionData d) (b : AbsoluteDrift A) : ℝ≥0∞ :=
  ⨅ F : {F : SpeciesFamily d // 0 < speciesGap A F}, speciesQuotient A b F.1

theorem speciesRate_le (A : InteractionData d) (b : AbsoluteDrift A) (F : SpeciesFamily d)
    (hG : 0 < speciesGap A F) : speciesRate A b ≤ speciesQuotient A b F :=
  iInf_le (fun F : {F : SpeciesFamily d // 0 < speciesGap A F} => speciesQuotient A b F.1)
    ⟨F, hG⟩

/-- Empty competitor class gives `⊤`. -/
theorem speciesRate_eq_top (A : InteractionData d) (b : AbsoluteDrift A)
    (h : ∀ F : SpeciesFamily d, speciesGap A F = 0) : speciesRate A b = ⊤ := by
  refine iInf_eq_top.2 fun F => ?_
  exact absurd F.2 (by rw [h F.1]; exact lt_irrefl _)

end DGPS
