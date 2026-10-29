import Mathlib

/-!
# One-coordinate invariance of a finite product measure

For a probability `ρ` and `Q = ρ^{⊗N}`, the map `(ω, s) ↦ update ω i s` sends `Q ⊗ ρ` to `Q`.
Hence `∫ H dQ = ∫ ∫ H (update ω i s) dρ(s) dQ(ω)` (resample coordinate `i`).
-/

open MeasureTheory

namespace SharpLSI.FL

private lemma measurePreserving_pi_update {N : ℕ} {S : Type*} [MeasurableSpace S]
    (ρ : Measure S) [IsProbabilityMeasure ρ] (i : Fin N) :
    MeasurePreserving (fun p : (Fin N → S) × S => Function.update p.1 i p.2)
      ((Measure.pi fun _ : Fin N => ρ).prod ρ) (Measure.pi fun _ : Fin N => ρ) := by
  refine ⟨measurable_update', ?_⟩
  symm
  refine Measure.pi_eq (μ := fun _ : Fin N => ρ) (fun A hA => ?_)
  rw [Measure.map_apply measurable_update' (MeasurableSet.univ_pi hA)]
  have hpre : (fun p : (Fin N → S) × S => Function.update p.1 i p.2) ⁻¹' (Set.univ.pi A) =
      (Set.univ.pi (Function.update A i Set.univ)) ×ˢ A i := by
    ext ⟨ω, s⟩
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_prod]
    constructor
    · intro h
      refine ⟨fun l => ?_, ?_⟩
      · by_cases hl : l = i
        · subst hl; simp
        · have := h l
          simpa [Function.update_of_ne hl] using this
      · have := h i
        simpa using this
    · rintro ⟨h1, h2⟩ l
      by_cases hl : l = i
      · subst hl; simpa using h2
      · have := h1 l
        simpa [Function.update_of_ne hl] using this
  rw [hpre, Measure.prod_prod, Measure.pi_pi]
  rw [← Finset.mul_prod_erase Finset.univ (fun l => ρ (A l)) (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun l => ρ (Function.update A i Set.univ l))
      (Finset.mem_univ i)]
  have : ∏ l ∈ Finset.univ.erase i, ρ (Function.update A i Set.univ l) =
      ∏ l ∈ Finset.univ.erase i, ρ (A l) := by
    refine Finset.prod_congr rfl (fun l hl => ?_)
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hl)]
  rw [this]
  simp [mul_comm]

/-- Resampling one coordinate of a product measure does not change integrals. -/
theorem integral_pi_update {N : ℕ} {S : Type*} [MeasurableSpace S] (ρ : Measure S)
    [IsProbabilityMeasure ρ] (i : Fin N) {H : (Fin N → S) → ℝ}
    (hH : Integrable H (Measure.pi fun _ : Fin N => ρ)) :
    ∫ ω, H ω ∂Measure.pi (fun _ : Fin N => ρ) =
      ∫ ω, ∫ s, H (Function.update ω i s) ∂ρ ∂Measure.pi (fun _ : Fin N => ρ) := by
  have hT := measurePreserving_pi_update ρ i
  have hint := hT.integrable_comp_of_integrable hH
  have h1 : ∫ ω, H ω ∂Measure.pi (fun _ : Fin N => ρ) =
      ∫ p, H (Function.update p.1 i p.2) ∂((Measure.pi fun _ : Fin N => ρ).prod ρ) := by
    have hm : AEStronglyMeasurable H
        (Measure.map (fun p : (Fin N → S) × S => Function.update p.1 i p.2)
          ((Measure.pi fun _ : Fin N => ρ).prod ρ)) := by
      rw [hT.map_eq]; exact hH.aestronglyMeasurable
    have := integral_map hT.measurable.aemeasurable hm
    rw [hT.map_eq] at this
    exact this
  rw [h1]
  exact integral_prod _ hint

end SharpLSI.FL
