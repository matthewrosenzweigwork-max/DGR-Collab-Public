import DGPS.Lipschitz.T01SmallEntropyCoercivity
import DGPS.Lipschitz.T01HessianContinuousForm

/-!
# Global entropy coercivity from the current equilibrium inputs

This completes the small/intermediate/large entropy argument on the absolute mean-field
objects. The explicit form hypothesis is a centered Hessian lower bound, not an entropy
estimate; its provider from `IsCoerciveDensityHessian` is kept separate.
-/

open MeasureTheory InformationTheory Filter Topology
open scoped ENNReal

namespace DGPS.Lipschitz

variable {d : ℕ}

/-- Exact real free-energy splitting, with finiteness derived from finite entropy to the
minimizing Gibbs reference rather than assumed as an extra competitor restriction. -/
theorem t01_freeEnergy_eq_entropy_correction (A : InteractionData d)
    {μ : ProbabilityMeasure (Torus d)} (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (ν : ProbabilityMeasure (Torus d))
    (hν : klDiv (ν : Measure (Torus d)) (μ : Measure (Torus d)) ≠ ⊤) :
    freeEnergy A ν =
      (((klDiv (ν : Measure (Torus d)) (μ : Measure (Torus d))).toReal +
        t01CenteredCorrection A μ ν + freeEnergyMinimumReal A : ℝ) : EReal) := by
  have hgib := minimizer_eq_gibbs A μ (DGPS.Structural.minimizer_le A hμ)
  have hνh : relativeEntropy (ν : Measure (Torus d)) (haar d) ≠ ⊤ := by
    rw [Analysis.relativeEntropy_eq_klDiv,
      ← klDiv_gibbs_ne_top_iff A (μ : Measure (Torus d)) (ν : Measure (Torus d)), ← hgib]
    exact hν
  obtain ⟨Fr, hFr⟩ := (finiteFreeEnergy_iff A ν).mpr hνh
  have hsub := free_energy_sub_eq A μ hgib ν hνh
  rw [hFr, hμ, ← coe_freeEnergyMinimumReal, Analysis.relativeEntropy_eq_klDiv,
    ← EReal.coe_ennreal_toReal hν, ← EReal.coe_sub, ← EReal.coe_add] at hsub
  change ((Fr - freeEnergyMinimumReal A : ℝ) : EReal) =
    (((klDiv (ν : Measure (Torus d)) (μ : Measure (Torus d))).toReal +
      t01CenteredCorrection A μ ν : ℝ) : EReal) at hsub
  have hreal := EReal.coe_injective hsub
  rw [hFr]
  congr 1
  linarith

/-- Global coercivity of entropy plus the centered correction. All Borel probabilities of
finite entropy to the reference are included; the constant is uniform over those probabilities. -/
theorem t01_global_entropy_coercivity_of_form (A : InteractionData d)
    {μ : ProbabilityMeasure (Torus d)} (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (huniq : ∀ ν, freeEnergy A ν = freeEnergyMinimum A → ν = μ)
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ ≤ 1)
    (hσ : ∀ w : C(Torus d, ℝ), (∫ x, w x ∂(μ : Measure (Torus d))) = 0 →
      σ * (∫ x, w x ^ 2 ∂(μ : Measure (Torus d))) ≤
        (∫ x, w x ^ 2 ∂(μ : Measure (Torus d))) +
          SharpLSI.quadF (centeredKernel A (μ : Measure (Torus d))) μ w) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ ν : ProbabilityMeasure (Torus d),
      klDiv (ν : Measure (Torus d)) (μ : Measure (Torus d)) ≠ ⊤ →
        c * (klDiv (ν : Measure (Torus d)) (μ : Measure (Torus d))).toReal ≤
          (klDiv (ν : Measure (Torus d)) (μ : Measure (Torus d))).toReal +
            t01CenteredCorrection A μ ν := by
  obtain ⟨δ, hδ0, hsmall⟩ := t01_small_entropy_coercive_of_form A hμ hσ0 hσ1 hσ
  obtain ⟨B, hB0, hB⟩ := t01CenteredCorrection_bounded A μ
  obtain ⟨n, hn⟩ := t01_small_gap_forces_small_centeredCorrection A hμ huniq hδ0
  set η := min (1 / ((n : ℝ) + 1)) (δ / 2) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by linarith)
  set M := 2 * (B + 1) with hM
  have hM0 : 0 < M := by positivity
  set c := min (min (σ / 2) (1 / 2)) (η / M) with hc
  have hc0 : 0 < c := lt_min (lt_min (by positivity) (by norm_num)) (by positivity)
  have hc1 : c ≤ 1 := (min_le_left _ _).trans ((min_le_right _ _).trans (by norm_num))
  refine ⟨c, hc0, hc1, fun ρ hKρ => ?_⟩
  have hF := t01_freeEnergy_eq_entropy_correction A hμ ρ hKρ
  set H := (klDiv (ρ : Measure (Torus d)) (μ : Measure (Torus d))).toReal with hH
  set J := t01CenteredCorrection A μ ρ with hJ
  have hH0 : 0 ≤ H := ENNReal.toReal_nonneg
  have hJB : |J| ≤ B := hB ρ
  rcases le_or_gt H δ with hHδ | hHδ
  · -- small entropy
    have h := hsmall ρ hKρ hHδ
    have : c ≤ σ / 2 := (min_le_left _ _).trans (min_le_left _ _)
    nlinarith
  rcases le_or_gt M H with hHM | hHM
  · -- large entropy
    have : c ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
    have hJ' := neg_abs_le J
    nlinarith
  · -- intermediate entropy
    have hGη : η ≤ H + J := by
      by_contra hlt
      push_neg at hlt
      have hle : freeEnergy A ρ ≤ ((freeEnergyMinimumReal A + 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
        rw [hF, EReal.coe_le_coe_iff]
        have : η ≤ 1 / ((n : ℝ) + 1) := min_le_left _ _
        linarith
      have h1 := hn ρ hle
      have h2 := neg_abs_le J
      have h3 : η ≤ δ / 2 := min_le_right _ _
      linarith
    have : c ≤ η / M := min_le_right _ _
    have h1 : c * H ≤ η / M * H := mul_le_mul_of_nonneg_right this hH0
    have h2 : η / M * H ≤ η := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hM0]
      exact mul_le_mul_of_nonneg_left hHM.le hη0.le
    linarith


/-- Actual current Hessian coercivity supplies the finite-rank form input internally. -/
theorem t01_entropy_correction_coercive_of_unique_hessian (A : InteractionData d)
    {μ : ProbabilityMeasure (Torus d)} (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (huniq : ∀ ν, freeEnergy A ν = freeEnergyMinimum A → ν = μ)
    (hH : IsCoerciveDensityHessian A μ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ ν : ProbabilityMeasure (Torus d),
      klDiv (ν : Measure (Torus d)) (μ : Measure (Torus d)) ≠ ⊤ →
        c * (klDiv (ν : Measure (Torus d)) (μ : Measure (Torus d))).toReal ≤
          (klDiv (ν : Measure (Torus d)) (μ : Measure (Torus d))).toReal +
            t01CenteredCorrection A μ ν := by
  obtain ⟨σ, hσ0, hσ1, hform⟩ := t01_continuous_hessian_form A μ hH
  exact t01_global_entropy_coercivity_of_form A hμ huniq hσ0 hσ1 hform

/-- The global entropy coercivity estimate on the original finite-free-energy domain. -/
theorem t01_freeEnergy_entropy_coercive_of_unique_hessian (A : InteractionData d)
    {μ : ProbabilityMeasure (Torus d)} (hμ : freeEnergy A μ = freeEnergyMinimum A)
    (huniq : ∀ ν, freeEnergy A ν = freeEnergyMinimum A → ν = μ)
    (hH : IsCoerciveDensityHessian A μ) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ ν : ProbabilityMeasure (Torus d),
      relativeEntropy (ν : Measure (Torus d)) (haar d) ≠ ⊤ →
        (c : EReal) * (relativeEntropy (ν : Measure (Torus d))
          (μ : Measure (Torus d)) : EReal) ≤ freeEnergy A ν - freeEnergyMinimum A := by
  obtain ⟨c, hc0, hc1, hco⟩ := t01_entropy_correction_coercive_of_unique_hessian A hμ huniq hH
  refine ⟨c, hc0, hc1, fun ν hν => ?_⟩
  have hgib := minimizer_eq_gibbs A μ (DGPS.Structural.minimizer_le A hμ)
  have hνk : klDiv (ν : Measure (Torus d)) (haar d) ≠ ⊤ := by
    simpa only [Analysis.relativeEntropy_eq_klDiv] using hν
  have hfin := (klDiv_gibbs_ne_top_iff A (μ : Measure (Torus d))
    (ν : Measure (Torus d))).mpr hνk
  rw [← hgib] at hfin
  have hreal := hco ν hfin
  have hF := t01_freeEnergy_eq_entropy_correction A hμ ν hfin
  rw [Analysis.relativeEntropy_eq_klDiv, ← EReal.coe_ennreal_toReal hfin,
    ← EReal.coe_mul, hF, ← coe_freeEnergyMinimumReal, ← EReal.coe_sub,
    EReal.coe_le_coe_iff]
  linarith

end DGPS.Lipschitz
