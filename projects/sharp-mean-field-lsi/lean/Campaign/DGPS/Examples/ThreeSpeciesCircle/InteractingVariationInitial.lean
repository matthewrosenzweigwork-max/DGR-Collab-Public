import DGPS.Examples.ThreeSpeciesCircle.InteractingCorrectionVariation
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarCompactness

/-! Exact initial-law and functional identification for normalized original H1
variations. Stored roots may differ on null sets; no pointwise sign convention
is imposed on them. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

theorem absoluteRootVariation_density_zero (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) (x : Torus 1) :
    (absoluteRootVariation ρ hφ 0).density x = ρ.density x := by
  have hn0 : 0 < ∫ x, (ρ.sqrt x + (0 : ℝ) * φ x) ^ 2 ∂haar 1 := by
    simpa only [zero_mul, add_zero, ρ.mass_one] using (one_pos : (0 : ℝ) < 1)
  unfold absoluteRootVariation
  rw [dif_pos hn0]
  dsimp only [normAbs, AbsoluteDensity.density]
  rw [div_pow, sq_abs, Real.sq_sqrt hn0.le]
  simp only [zero_mul, add_zero, ρ.mass_one, div_one]

theorem absoluteRootVariation_measure_zero (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    densityMeasure (absoluteRootVariation ρ hφ 0) = densityMeasure ρ := by
  apply Subtype.ext
  change (haar 1).withDensity (fun x => ENNReal.ofReal ((absoluteRootVariation ρ hφ 0).density x)) =
    (haar 1).withDensity (fun x => ENNReal.ofReal (ρ.density x))
  apply congrArg ((haar 1).withDensity)
  funext x
  rw [absoluteRootVariation_density_zero]

theorem absoluteRootVariation_fisher_zero (h : ℝ) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    ordinaryFisher h (absoluteRootVariation ρ hφ 0) = ordinaryFisher h ρ := by
  have hn0 : 0 < ∫ x, (ρ.sqrt x + (0 : ℝ) * φ x) ^ 2 ∂haar 1 := by
    simpa only [zero_mul, add_zero, ρ.mass_one] using (one_pos : (0 : ℝ) < 1)
  have hv := (isWeakGradient_weakGradient ρ.sqrt_mem).add (hφ.smul 0)
  have hnorm := normAbs_fisher h hv hn0
  unfold absoluteRootVariation
  rw [dif_pos hn0]
  calc
    _ = ENNReal.ofReal
        ((∫ x, (2 * (weakGradient ρ.sqrt ρ.sqrt_mem x + (0 : ℝ) • G x) 0 -
          (ρ.sqrt x + 0 * φ x) * logScore h x) ^ 2 ∂haar 1) /
          ∫ x, (ρ.sqrt x + (0 : ℝ) * φ x) ^ 2 ∂haar 1) := hnorm
    _ = ordinaryFisher h ρ := by
      rw [ordinaryFisher_eq]
      simp only [zero_smul, add_zero, zero_mul, ρ.mass_one, div_one]

/-- The free-energy gap depends on the actual initial law, not a chosen root
representative. Its exact zero-time identification holds for every interaction. -/
theorem absoluteRootVariation_gap_zero (A : InteractionData 1) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    scalarGap A (absoluteRootVariation ρ hφ 0) = scalarGap A ρ := by
  have hμ := absoluteRootVariation_measure_zero ρ hφ
  have hF1 : densityFreeEnergy A (absoluteRootVariation ρ hφ 0) ≤ densityFreeEnergy A ρ := by
    apply EReal.coe_le_coe_iff.mp
    rw [coe_densityFreeEnergy, coe_densityFreeEnergy, hμ]
  have hF2 : densityFreeEnergy A ρ ≤ densityFreeEnergy A (absoluteRootVariation ρ hφ 0) := by
    apply EReal.coe_le_coe_iff.mp
    rw [coe_densityFreeEnergy, coe_densityFreeEnergy, hμ]
  apply Subtype.ext
  change densityFreeEnergy A (absoluteRootVariation ρ hφ 0) - freeEnergyMinimumReal A =
    densityFreeEnergy A ρ - freeEnergyMinimumReal A
  exact congrArg (fun z : ℝ => z - freeEnergyMinimumReal A) (le_antisymm hF1 hF2)

/-- The actual nonlinear dissipation at zero equals the original dissipation.
Fisher and all changing-force moments are identified using actual model formulas. -/
theorem absoluteRootVariation_dissipation_zero (h ε : ℝ)
    (b : AbsoluteDrift (modelData h ε)) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    scalarDissipation (modelData h ε) b (absoluteRootVariation ρ hφ 0) =
      scalarDissipation (modelData h ε) b ρ := by
  have hμ := absoluteRootVariation_measure_zero ρ hφ
  have hC : elementaryC h 0 (absoluteRootVariation ρ hφ 0) = elementaryC h 0 ρ := by
    unfold elementaryC
    simp_rw [absoluteRootVariation_density_zero, hμ]
  have hJ : elementaryJ h (absoluteRootVariation ρ hφ 0) = elementaryJ h ρ := by
    unfold elementaryJ
    simp_rw [absoluteRootVariation_density_zero, hμ]
  obtain ⟨hfin, he⟩ := elementaryModel_scalarDissipation_real h ε b (absoluteRootVariation ρ hφ 0)
  obtain ⟨hfin0, he0⟩ := elementaryModel_scalarDissipation_real h ε b ρ
  have hr : (scalarDissipation (modelData h ε) b (absoluteRootVariation ρ hφ 0)).toReal =
      (scalarDissipation (modelData h ε) b ρ).toReal := by
    rw [he, he0, absoluteRootVariation_fisher_zero, hC, hJ]
  calc
    _ = ENNReal.ofReal (scalarDissipation (modelData h ε) b (absoluteRootVariation ρ hφ 0)).toReal :=
      (ENNReal.ofReal_toReal hfin).symm
    _ = ENNReal.ofReal (scalarDissipation (modelData h ε) b ρ).toReal := congrArg ENNReal.ofReal hr
    _ = _ := ENNReal.ofReal_toReal hfin0

end DGPS.Examples.ThreeSpeciesCircle
