import DGPS.Model.ScalarRate
import DGPS.Model.SpeciesRate

/-!
# One-species inclusion and finite species-count rates (DEF030)

The one-species family `SpeciesFamily.single ρ` (weight one) has barycenter density `ρ`, so
`G_θ = G` and `D_θ = D`; hence `r_ms ≤ r_*`. The at-most-`k` rate `r_k` is the infimum over
families with `1 ≤ q ≤ k` species and positive gap; `r_1 = r_*` and `r_ms ≤ r_2 ≤ r_*`.
The exact-`k` form is not treated here (it agrees with at-most-`k` only after the
identical-species splitting equivalence).
-/

open MeasureTheory
open scoped ENNReal NNReal

namespace DGPS

variable {d : ℕ}

theorem sum_single_count {M : Type*} [AddCommMonoid M] (ρ : AbsoluteDensity d)
    (f : Fin (SpeciesFamily.single ρ).count → M) :
    ∑ s, f s = f ⟨0, by simp [SpeciesFamily.single]⟩ :=
  Fin.sum_univ_one f

/-- The barycenter of a one-species family has the same density function as the species. -/
theorem barycenter_single_density (ρ : AbsoluteDensity d) (x : Torus d) :
    (barycenter (SpeciesFamily.single ρ)).density x = ρ.density x := by
  rw [SpeciesFamily.barycenter_density_apply]
  rw [sum_single_count]
  simp [SpeciesFamily.single, AbsoluteDensity.density]

theorem densityMeasure_barycenter_single (ρ : AbsoluteDensity d) :
    densityMeasure (barycenter (SpeciesFamily.single ρ)) = densityMeasure ρ := by
  apply Subtype.ext
  show Measure.withDensity _ _ = Measure.withDensity _ _
  congr 1
  funext x
  exact congrArg ENNReal.ofReal (barycenter_single_density ρ x)

theorem interactionPotential_barycenter_single (A : InteractionData d) (ρ : AbsoluteDensity d) :
    interactionPotential A (barycenter (SpeciesFamily.single ρ)) =
      interactionPotential A ρ := by
  unfold interactionPotential
  rw [densityMeasure_barycenter_single]

theorem force_barycenter_single (A : InteractionData d) (b : AbsoluteDrift A)
    (ρ : AbsoluteDensity d) :
    b.force (barycenter (SpeciesFamily.single ρ)) =ᵐ[haar d] b.force ρ :=
  b.ae_eq_of_isWeakGradient _ (by
    rw [interactionPotential_barycenter_single]
    exact b.weak_gradient ρ)

theorem speciesGap_single (A : InteractionData d) (ρ : AbsoluteDensity d) :
    speciesGap A (SpeciesFamily.single ρ) = scalarGap A ρ := by
  apply NNReal.eq
  rw [coe_speciesGap, coe_scalarGap, speciesRawGap, densityMeasure_barycenter_single]
  have hfin := (absoluteDensity_entropy_finite ρ).2.2.1
  have h1 : ((densityFreeEnergy A ρ : ℝ) : EReal) =
      (((relativeEntropy (densityMeasure ρ : Measure (Torus d)) (haar d)).toReal +
        potentialEnergy A (densityMeasure ρ) +
        (1 / 2 : ℝ) * interactionEnergy A (densityMeasure ρ) : ℝ) : EReal) := by
    rw [coe_densityFreeEnergy]
    exact freeEnergy_eq_real A _ hfin
  have h2 := EReal.coe_injective h1
  rw [h2]
  rw [sum_single_count]
  simp [SpeciesFamily.single]

theorem speciesDissipation_single (A : InteractionData d) (b : AbsoluteDrift A)
    (ρ : AbsoluteDensity d) :
    speciesDissipation A b (SpeciesFamily.single ρ) = scalarDissipation A b ρ := by
  unfold speciesDissipation scalarDissipation scalarScore
  rw [sum_single_count]
  have hw : ENNReal.ofReal ((SpeciesFamily.single ρ).weight ⟨0, by simp [SpeciesFamily.single]⟩) = 1 := by
    rw [SpeciesFamily.single_weight, ENNReal.ofReal_one]
  rw [hw, one_mul]
  refine lintegral_congr_ae ?_
  filter_upwards [force_barycenter_single A b ρ] with x hx
  rw [hx]
  rfl

theorem speciesQuotient_single (A : InteractionData d) (b : AbsoluteDrift A)
    (ρ : AbsoluteDensity d) :
    speciesQuotient A b (SpeciesFamily.single ρ) = scalarQuotient A b ρ := by
  unfold speciesQuotient scalarQuotient
  rw [speciesGap_single, speciesDissipation_single]

/-- DEF030: the multi-species rate is at most the scalar rate, `r_ms ≤ r_*`. -/
theorem speciesRate_le_scalarRate (A : InteractionData d) (b : AbsoluteDrift A) :
    speciesRate A b ≤ scalarRate A b := by
  refine le_iInf fun ρ => ?_
  have hG : 0 < speciesGap A (SpeciesFamily.single ρ.1) := by
    rw [speciesGap_single]; exact ρ.2
  calc speciesRate A b ≤ speciesQuotient A b (SpeciesFamily.single ρ.1) := speciesRate_le A b _ hG
    _ = scalarQuotient A b ρ.1 := speciesQuotient_single A b ρ.1

/-- DEF030: `r_k = inf { D_θ / (2 G_θ) : 1 ≤ q ≤ k, G_θ > 0 }` (at-most-`k` species; `ℕ+` count
gives `1 ≤ q`). The empty infimum is `⊤`. -/
noncomputable def speciesRateAtMost (A : InteractionData d) (b : AbsoluteDrift A) (k : ℕ) :
    ℝ≥0∞ :=
  ⨅ F : {F : SpeciesFamily d // (F.count : ℕ) ≤ k ∧ 0 < speciesGap A F},
    speciesQuotient A b F.1

theorem speciesRateAtMost_le (A : InteractionData d) (b : AbsoluteDrift A) (k : ℕ)
    (F : SpeciesFamily d) (hk : (F.count : ℕ) ≤ k) (hG : 0 < speciesGap A F) :
    speciesRateAtMost A b k ≤ speciesQuotient A b F :=
  iInf_le (fun F : {F : SpeciesFamily d // (F.count : ℕ) ≤ k ∧ 0 < speciesGap A F} =>
    speciesQuotient A b F.1) ⟨F, hk, hG⟩

/-- `r_ms ≤ r_k`: the at-most-`k` competitor class sits inside all families. -/
theorem speciesRate_le_speciesRateAtMost (A : InteractionData d) (b : AbsoluteDrift A) (k : ℕ) :
    speciesRate A b ≤ speciesRateAtMost A b k :=
  le_iInf fun F => speciesRate_le A b F.1 F.2.2

/-- `r_k` is antitone in `k`. -/
theorem speciesRateAtMost_anti (A : InteractionData d) (b : AbsoluteDrift A) {k l : ℕ}
    (h : k ≤ l) : speciesRateAtMost A b l ≤ speciesRateAtMost A b k :=
  le_iInf fun F => speciesRateAtMost_le A b l F.1 (F.2.1.trans h) F.2.2

/-- A one-species family is `single` of its density. -/
theorem SpeciesFamily.exists_eq_single_of_count_eq_one (F : SpeciesFamily d)
    (h : F.count = 1) : ∃ ρ : AbsoluteDensity d, F = SpeciesFamily.single ρ := by
  obtain ⟨c, w, wp, ws, dn⟩ := F
  change c = 1 at h
  subst h
  have hsub : ∀ s t : Fin ((1 : ℕ+) : ℕ), s = t := fun s t =>
    Fin.ext (by have h1 := s.2; have h2 := t.2; change _ < 1 at h1 h2; omega)
  have h0 : (0 : ℕ) < ((1 : ℕ+) : ℕ) := by simp
  have hw : w = fun _ => 1 := by
    funext s
    have h1 : w ⟨0, h0⟩ = 1 := by
      have := ws
      rwa [show ∑ s, w s = w ⟨0, h0⟩ from Fin.sum_univ_one w] at this
    rwa [hsub s ⟨0, h0⟩]
  refine ⟨dn ⟨0, h0⟩, ?_⟩
  subst hw
  have hd : dn = fun _ => dn ⟨0, h0⟩ := by
    funext s; exact congrArg dn (hsub _ _)
  simp only [SpeciesFamily.single]
  congr

/-- DEF030: `r_1 = r_*`. -/
theorem speciesRateAtMost_one (A : InteractionData d) (b : AbsoluteDrift A) :
    speciesRateAtMost A b 1 = scalarRate A b := by
  apply le_antisymm
  · refine le_iInf fun ρ => ?_
    have hG : 0 < speciesGap A (SpeciesFamily.single ρ.1) := by
      rw [speciesGap_single]; exact ρ.2
    calc speciesRateAtMost A b 1 ≤ speciesQuotient A b (SpeciesFamily.single ρ.1) :=
          speciesRateAtMost_le A b 1 _ (by simp [SpeciesFamily.single]) hG
      _ = scalarQuotient A b ρ.1 := speciesQuotient_single A b ρ.1
  · refine le_iInf fun F => ?_
    have hc : F.1.count = 1 := PNat.eq (le_antisymm F.2.1 F.1.count.pos)
    obtain ⟨ρ, hρ⟩ := SpeciesFamily.exists_eq_single_of_count_eq_one F.1 hc
    have hF := F.2.2
    rw [hρ, speciesGap_single] at hF
    calc scalarRate A b ≤ scalarQuotient A b ρ := scalarRate_le_quotient A b ρ hF
      _ = speciesQuotient A b F.1 := by rw [hρ, speciesQuotient_single]

/-- DEF030: `r_ms ≤ r_2 ≤ r_*`. -/
theorem speciesRate_le_speciesRateAtMost_two_le_scalarRate (A : InteractionData d)
    (b : AbsoluteDrift A) :
    speciesRate A b ≤ speciesRateAtMost A b 2 ∧ speciesRateAtMost A b 2 ≤ scalarRate A b :=
  ⟨speciesRate_le_speciesRateAtMost A b 2,
    speciesRateAtMost_one A b ▸ speciesRateAtMost_anti A b (by norm_num)⟩

end DGPS
