import DGPS.Examples.ThreeSpeciesCircle.InteractingRootVariations

/-! Actual entropy differentiation along normalized absolute H1 paths. The
entropy integrand derivative is the one already proved at zero, so no positive
stored-root or smooth-competitor restriction is imposed. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The normalization term is retained in the entropy derivative on the full
original H1 carrier. Positive entropy is only used to remove the `ofReal`
clipping in a neighborhood of the initial density. -/
theorem absoluteRootVariation_entropy_hasDerivAt (h : ℝ) (ρ : AbsoluteDensity 1)
    (hpos : 0 < ordinaryEntropy h ρ) {φ : Torus 1 → ℝ}
    {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    HasDerivAt
      (fun t : ℝ => (ordinaryEntropy h (absoluteRootVariation ρ hφ t)).toReal)
      ((∫ x, eulF' (ρ.sqrt x) * φ x ∂haar 1) -
        2 * (∫ x, ρ.sqrt x * φ x * Real.log (referenceDensity h x) ∂haar 1) -
        (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) * ((ordinaryEntropy h ρ).toReal + 1)) 0 := by
  let n := fun t : ℝ => ∫ x, (ρ.sqrt x + t * φ x) ^ 2 ∂haar 1
  let Φ := fun t : ℝ => ∫ x, eulF (ρ.sqrt x + t * φ x) ∂haar 1
  let R := fun t : ℝ => ∫ x, (ρ.sqrt x + t * φ x) ^ 2 *
    Real.log (referenceDensity h x) ∂haar 1
  let E := fun t : ℝ => Φ t / n t - Real.log (n t) - R t / n t
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  have hn0 : n 0 = 1 := by simpa only [n, zero_mul, add_zero] using ρ.mass_one
  have hn : HasDerivAt n (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) 0 := by
    have hh := hasDerivAt_integral_quad
      (c := fun _ : Torus 1 => (1 : ℝ)) (C := 1) aestronglyMeasurable_const
      (fun x => by norm_num) ρ.memLp_sqrt hφ.memLp
    simpa only [n, mul_one] using hh
  have hΦ : HasDerivAt Φ (∫ x, eulF' (ρ.sqrt x) * φ x ∂haar 1) 0 :=
    hasDerivAt_integral_eulF hw hφ
  have hLc : Continuous (fun x : Torus 1 => Real.log (referenceDensity h x)) :=
    (continuous_referenceDensity h).log (fun x => (referenceDensity_pos (h := h) x).ne')
  have hR : HasDerivAt R
      (2 * ∫ x, ρ.sqrt x * φ x * Real.log (referenceDensity h x) ∂haar 1) 0 :=
    hasDerivAt_integral_quad hLc.aestronglyMeasurable
      (abs_log_referenceDensity_le h) ρ.memLp_sqrt hφ.memLp
  have hEntropy0 : ordinaryEntropy h ρ = ENNReal.ofReal (Φ 0 - R 0) := by
    rw [ordinaryEntropy_eq, circleEntropy_eq]
    simp only [Φ, R, zero_mul, add_zero, eulF, AbsoluteDensity.density]
  have hE0pos : 0 < Φ 0 - R 0 := by
    rw [hEntropy0] at hpos
    exact ENNReal.ofReal_pos.mp hpos
  have hHreal : (ordinaryEntropy h ρ).toReal = Φ 0 - R 0 := by
    rw [hEntropy0, ENNReal.toReal_ofReal hE0pos.le]
  have hEn : HasDerivAt E
      (((∫ x, eulF' (ρ.sqrt x) * φ x ∂haar 1) * n 0 -
          Φ 0 * (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1)) / n 0 ^ 2 -
        (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) / n 0 -
        ((2 * ∫ x, ρ.sqrt x * φ x * Real.log (referenceDensity h x) ∂haar 1) * n 0 -
          R 0 * (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1)) / n 0 ^ 2) 0 :=
    ((hΦ.div hn (by rw [hn0]; exact one_ne_zero)).sub
      (hn.log (by rw [hn0]; exact one_ne_zero))).sub
        (hR.div hn (by rw [hn0]; exact one_ne_zero))
  have hE : HasDerivAt E
      ((∫ x, eulF' (ρ.sqrt x) * φ x ∂haar 1) -
        2 * (∫ x, ρ.sqrt x * φ x * Real.log (referenceDensity h x) ∂haar 1) -
        (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) * ((ordinaryEntropy h ρ).toReal + 1)) 0 := by
    convert hEn using 1
    rw [hn0, hHreal]
    ring
  have hnpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < n t :=
    hn.continuousAt.eventually (lt_mem_nhds (by rw [hn0]; norm_num))
  have hepos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < E t :=
    hE.continuousAt.eventually (lt_mem_nhds (by
      simpa only [E, hn0, div_one, Real.log_one, sub_zero] using hE0pos))
  apply hE.congr_of_eventuallyEq
  filter_upwards [hnpos, hepos] with t hnt het
  have he : ordinaryEntropy h (absoluteRootVariation ρ hφ t) = ENNReal.ofReal (E t) := by
    have hvm : MemH1 (fun x => ρ.sqrt x + t * φ x) := ⟨_, hw.add (hφ.smul t)⟩
    have hnorm : ordinaryEntropy h
        (normAbs (fun x => ρ.sqrt x + t * φ x) hvm hnt) = ENNReal.ofReal (E t) :=
      normAbs_entropy h hvm hnt
    unfold absoluteRootVariation
    rw [dif_pos hnt]
    exact hnorm
  rw [he, ENNReal.toReal_ofReal het.le]

end DGPS.Examples.ThreeSpeciesCircle
