import DGPS.Examples.ThreeSpeciesCircle.InteractingEntropyAllVariation
import DGPS.Examples.ThreeSpeciesCircle.InteractingScalarWeakEuler

/-! Fixed-field first variation on the full original absolute H1 carrier.
The varied density and the density producing the common field are independent.
Global minimality and the native common value are factual inputs here; no
individual scalar minimizer premise is substituted for a family species. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- A global minimum of the actual fixed native field functional, at its
actual common multiplier, satisfies the physical weak equation in EVERY H1
direction, including at zero ordinary entropy. -/
theorem elementaryFixedField_globalMin_weakEuler
    (h ε r : ℝ) (τ ρ : AbsoluteDensity 1)
    (hmin : ∀ σ : AbsoluteDensity 1,
      (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal +
          (∫ x, elementaryEulerCorrection h ε r τ x ∂(densityMeasure ρ : Measure (Torus 1))) ≤
        (ordinaryFisher h σ).toReal - 2 * r * (ordinaryEntropy h σ).toReal +
          (∫ x, elementaryEulerCorrection h ε r τ x ∂(densityMeasure σ : Measure (Torus 1))))
    (hvalue : (ordinaryFisher h ρ).toReal - 2 * r * (ordinaryEntropy h ρ).toReal +
      (∫ x, elementaryEulerCorrection h ε r τ x ∂(densityMeasure ρ : Measure (Torus 1))) =
        elementaryEulerMultiplier h ε r τ)
    (φ : Torus 1 → ℝ) (G : Torus 1 → Tangent 1) (hφ : IsWeakGradient φ G) :
    (∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * logScore h x) *
        (2 * G x 0 - φ x * logScore h x) ∂haar 1) +
      (∫ x, ρ.sqrt x * φ x * elementaryEulerCorrection h ε r τ x ∂haar 1) =
        2 * r * (∫ x, ρ.sqrt x * φ x *
          (Real.log (ρ.sqrt x ^ 2) - Real.log (referenceDensity h x)) ∂haar 1) +
        elementaryEulerMultiplier h ε r τ * (∫ x, ρ.sqrt x * φ x ∂haar 1) := by
  let Ξ := elementaryEulerCorrection h ε r τ
  let m := ∫ x, ρ.sqrt x * φ x ∂haar 1
  let I := (ordinaryFisher h ρ).toReal
  let H := (ordinaryEntropy h ρ).toReal
  let M := ∫ x, Ξ x ∂(densityMeasure ρ : Measure (Torus 1))
  let P := ∫ x, ρ.sqrt x * φ x * Ξ x ∂haar 1
  let A := ∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * logScore h x) *
    (2 * G x 0 - φ x * logScore h x) ∂haar 1
  let R := ∫ x, ρ.sqrt x * φ x *
    (Real.log (ρ.sqrt x ^ 2) - Real.log (referenceDensity h x)) ∂haar 1
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  have hiLog := integrable_mul_mul_log hw hφ
  have hLc : Continuous (fun x : Torus 1 => Real.log (referenceDensity h x)) :=
    (continuous_referenceDensity h).log (fun x => (referenceDensity_pos (h := h) x).ne')
  have hiQ := integrable_mul_bdd_two hLc.aestronglyMeasurable
    (abs_log_referenceDensity_le h) ρ.memLp_sqrt hφ.memLp
  have hiM : Integrable (fun x => ρ.sqrt x * φ x) (haar 1) :=
    ρ.memLp_sqrt.integrable_mul hφ.memLp
  have hEF : (∫ x, eulF' (ρ.sqrt x) * φ x ∂haar 1) =
      2 * (∫ x, ρ.sqrt x * φ x * Real.log (ρ.sqrt x ^ 2) ∂haar 1) + 2 * m := by
    have he : (fun x => eulF' (ρ.sqrt x) * φ x) = fun x =>
        2 * (ρ.sqrt x * φ x * Real.log (ρ.sqrt x ^ 2)) + 2 * (ρ.sqrt x * φ x) := by
      funext x
      unfold eulF'
      ring
    rw [he, integral_add (hiLog.const_mul 2) (hiM.const_mul 2),
      integral_const_mul, integral_const_mul]
  have hR : R = (∫ x, ρ.sqrt x * φ x * Real.log (ρ.sqrt x ^ 2) ∂haar 1) -
      ∫ x, ρ.sqrt x * φ x * Real.log (referenceDensity h x) ∂haar 1 := by
    dsimp only [R]
    rw [← integral_sub hiLog hiQ]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by ring
  have hI := absoluteRootVariation_fisher_hasDerivAt h ρ hφ
  change HasDerivAt (fun t : ℝ => (ordinaryFisher h (absoluteRootVariation ρ hφ t)).toReal)
    (2 * A - 2 * m * I) 0 at hI
  have hHraw := absoluteRootVariation_entropy_all_hasDerivAt h ρ hφ
  have hH : HasDerivAt (fun t : ℝ => (ordinaryEntropy h (absoluteRootVariation ρ hφ t)).toReal)
      (2 * R - 2 * m * H) 0 := by
    convert hHraw using 1
    rw [hEF, hR]
    dsimp only [m, H]
    ring
  have hΞ := (isSmooth_elementaryEulerCorrection h ε r τ).continuous_torus
  have hM := absoluteRootVariation_moment_hasDerivAt ρ hφ Ξ hΞ
  change HasDerivAt
    (fun t : ℝ => ∫ x, Ξ x ∂(densityMeasure (absoluteRootVariation ρ hφ t) : Measure (Torus 1)))
    (2 * P - 2 * m * M) 0 at hM
  let f := fun t : ℝ => (ordinaryFisher h (absoluteRootVariation ρ hφ t)).toReal -
    2 * r * (ordinaryEntropy h (absoluteRootVariation ρ hφ t)).toReal +
      ∫ x, Ξ x ∂(densityMeasure (absoluteRootVariation ρ hφ t) : Measure (Torus 1))
  have hf : HasDerivAt f
      ((2 * A - 2 * m * I) - 2 * r * (2 * R - 2 * m * H) + (2 * P - 2 * m * M)) 0 :=
    (hI.sub (hH.const_mul (2 * r))).add hM
  have hEntropy0 : ordinaryEntropy h (absoluteRootVariation ρ hφ 0) = ordinaryEntropy h ρ := by
    change relativeEntropy (densityMeasure (absoluteRootVariation ρ hφ 0)) (threefoldReference h) = _
    rw [absoluteRootVariation_measure_zero]
    rfl
  have hf0 : f 0 = I - 2 * r * H + M := by
    dsimp only [f, I, H, M]
    rw [absoluteRootVariation_fisher_zero, hEntropy0, absoluteRootVariation_moment_zero]
  have hloc : IsLocalMin f 0 := by
    apply Eventually.of_forall
    intro t
    rw [hf0]
    exact hmin (absoluteRootVariation ρ hφ t)
  have hd := hloc.hasDerivAt_eq_zero hf
  change I - 2 * r * H + M = elementaryEulerMultiplier h ε r τ at hvalue
  change A + P = 2 * r * R + elementaryEulerMultiplier h ε r τ * m
  nlinarith [congrArg (fun z : ℝ => m * z) hvalue]

end DGPS.Examples.ThreeSpeciesCircle
