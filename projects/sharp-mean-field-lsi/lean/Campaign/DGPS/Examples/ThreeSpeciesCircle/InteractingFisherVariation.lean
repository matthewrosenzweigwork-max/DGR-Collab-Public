import DGPS.Examples.ThreeSpeciesCircle.InteractingRootVariations

/-! Genuine ordinary relative Fisher differentiation along the actual normalized
absolute H1 path. Absolute values at zeros are handled by the accepted
`normAbs_fisher` identity, not differentiated as if the root were positive. -/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The exact original-H1 Fisher variation, including mass normalization. -/
theorem absoluteRootVariation_fisher_hasDerivAt (h : ℝ) (ρ : AbsoluteDensity 1)
    {φ : Torus 1 → ℝ} {G : Torus 1 → Tangent 1} (hφ : IsWeakGradient φ G) :
    HasDerivAt
      (fun t : ℝ => (ordinaryFisher h (absoluteRootVariation ρ hφ t)).toReal)
      (2 * (∫ x, (2 * weakGradient ρ.sqrt ρ.sqrt_mem x 0 - ρ.sqrt x * logScore h x) *
          (2 * G x 0 - φ x * logScore h x) ∂haar 1) -
        (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) * (ordinaryFisher h ρ).toReal) 0 := by
  let W := weakGradient ρ.sqrt ρ.sqrt_mem
  let S := fun x => 2 * W x 0 - ρ.sqrt x * logScore h x
  let T := fun x => 2 * G x 0 - φ x * logScore h x
  let n := fun t : ℝ => ∫ x, (ρ.sqrt x + t * φ x) ^ 2 ∂haar 1
  let A := fun t : ℝ => ∫ x, (S x + t * T x) ^ 2 ∂haar 1
  have hw := isWeakGradient_weakGradient ρ.sqrt_mem
  have hS : MemLp S 2 (haar 1) :=
    ((memLp_coord hw.memLp_grad 0).const_mul 2).sub (memLp_mul_logScore h hw.memLp)
  have hT : MemLp T 2 (haar 1) :=
    ((memLp_coord hφ.memLp_grad 0).const_mul 2).sub (memLp_mul_logScore h hφ.memLp)
  have hn0 : n 0 = 1 := by simpa only [n, zero_mul, add_zero] using ρ.mass_one
  have hn : HasDerivAt n (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) 0 := by
    have ht := hasDerivAt_integral_quad
      (c := fun _ : Torus 1 => (1 : ℝ)) (C := 1) aestronglyMeasurable_const
      (fun x => by norm_num) ρ.memLp_sqrt hφ.memLp
    simpa only [n, mul_one] using ht
  have hA : HasDerivAt A (2 * ∫ x, S x * T x ∂haar 1) 0 := by
    have ht := hasDerivAt_integral_quad
      (c := fun _ : Torus 1 => (1 : ℝ)) (C := 1) aestronglyMeasurable_const
      (fun x => by norm_num) hS hT
    simpa only [A, mul_one] using ht
  have hA0 : A 0 = (ordinaryFisher h ρ).toReal := by
    rw [ordinaryFisher_eq, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
    simp only [A, S, W, zero_mul, add_zero]
  have hquot := hA.div hn (by rw [hn0]; exact one_ne_zero)
  have hder : HasDerivAt (fun t => A t / n t)
      (2 * (∫ x, S x * T x ∂haar 1) -
        (2 * ∫ x, ρ.sqrt x * φ x ∂haar 1) * (ordinaryFisher h ρ).toReal) 0 := by
    convert hquot using 1
    rw [hn0, hA0]
    ring
  have hnpos : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < n t :=
    hn.continuousAt.eventually (lt_mem_nhds (by rw [hn0]; norm_num))
  apply hder.congr_of_eventuallyEq
  filter_upwards [hnpos] with t hnt
  unfold absoluteRootVariation
  rw [dif_pos hnt]
  have hv := hw.add (hφ.smul t)
  rw [normAbs_fisher h hv hnt,
    ENNReal.toReal_ofReal (div_nonneg (integral_nonneg fun _ => sq_nonneg _) hnt.le)]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    dsimp only [S, T, W]
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    ring

end DGPS.Examples.ThreeSpeciesCircle
