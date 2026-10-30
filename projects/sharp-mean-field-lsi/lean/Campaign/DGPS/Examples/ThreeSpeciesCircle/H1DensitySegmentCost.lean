import DGPS.Examples.ThreeSpeciesCircle.H1DensitySegmentCalculus
import DGPS.Structural.HarmonicRateComparison

/-! The all-real scalar density-coordinate functional and its identification
with the actual original-H1 law on the closed segment. No spatial smoothness,
parameter differentiability, Poincare or convexity premise is imposed. -/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

/-- The density-coordinate cost is defined for every real parameter; its
positive extension is established separately before parameter differentiation. -/
def h1DensitySegmentPhi (h r : ℝ) (ρ σ : AbsoluteDensity 1)
    (u v : Torus 1 → ℝ) (t : ℝ) : ℝ :=
  ∫ x, let T := h1DensitySegmentValue u v t x
       let G := h1DensitySegmentGradient ρ σ u v t x 0
       (G - T * logScore h x) ^ 2 / T -
         2 * r * (T * Real.log T - T * Real.log (referenceDensity h x)) ∂haar 1

section Segment
variable (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
  (hu : Continuous u) (hv : Continuous v) (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
  (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
  (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)

/-- Exact physical Fisher integrand at the genuine segment law, with its
original chosen weak gradients and a finite integral proved internally. -/
theorem h1DensitySegment_fisher_identity (h : ℝ) :
    Integrable (fun x =>
      (h1DensitySegmentGradient ρ σ u v t x 0 - h1DensitySegmentValue u v t x * logScore h x) ^ 2 /
        h1DensitySegmentValue u v t x) (haar 1) ∧
      (ordinaryFisher h (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht)).toReal =
        ∫ x, (h1DensitySegmentGradient ρ σ u v t x 0 -
          h1DensitySegmentValue u v t x * logScore h x) ^ 2 /
            h1DensitySegmentValue u v t x ∂haar 1 := by
  let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht
  let T := h1DensitySegmentValue u v t
  let P := h1DensitySegmentGradient ρ σ u v t
  have hp : ∀ x, 0 < T x := h1DensitySegmentValue_positive u v hup hvp t ht
  have hc : Continuous T := h1DensitySegmentValue_continuous u v hu hv t
  have hTw : IsWeakGradient T P := h1DensitySegmentValue_weak ρ σ u v hρ hσ t
  have hRw := continuousH1_sqrt_gradient hTw hc hp
  have hgrad := (isWeakGradient_weakGradient τ.sqrt_mem).ae_eq hRw
  let S := fun x => 2 * weakGradient τ.sqrt τ.sqrt_mem x 0 - τ.sqrt x * logScore h x
  have hSm : MemLp S 2 (haar 1) :=
    ((memLp_coord (isWeakGradient_weakGradient τ.sqrt_mem).memLp_grad 0).const_mul 2).sub
      (memLp_mul_logScore h τ.memLp_sqrt)
  have hpoint : (fun x => S x ^ 2) =ᵐ[haar 1]
      (fun x => (P x 0 - T x * logScore h x) ^ 2 / T x) := by
    filter_upwards [hgrad] with x hx
    have hx0 := congrArg (fun z : Tangent 1 => z 0) hx
    simp only [PiLp.smul_apply, smul_eq_mul] at hx0
    have hspos : 0 < Real.sqrt (T x) := Real.sqrt_pos.2 (hp x)
    have hsq : Real.sqrt (T x) ^ 2 = T x := Real.sq_sqrt (hp x).le
    have hscore : S x * Real.sqrt (T x) = P x 0 - T x * logScore h x := by
      dsimp only [S]
      rw [hx0]
      change (2 * ((2 * Real.sqrt (T x))⁻¹ * P x 0) -
        Real.sqrt (T x) * logScore h x) * Real.sqrt (T x) = _
      field_simp [hspos.ne']
      rw [hsq]
      ring
    apply (eq_div_iff (hp x).ne').2
    calc S x ^ 2 * T x = (S x * Real.sqrt (T x)) ^ 2 := by rw [mul_pow, hsq]
      _ = (P x 0 - T x * logScore h x) ^ 2 := congrArg (fun z : ℝ => z ^ 2) hscore
  have hi : Integrable (fun x => (P x 0 - T x * logScore h x) ^ 2 / T x) (haar 1) :=
    hSm.integrable_sq.congr hpoint
  refine ⟨hi, ?_⟩
  rw [ordinaryFisher_eq, ENNReal.toReal_ofReal (integral_nonneg fun _ => sq_nonneg _)]
  exact integral_congr_ae hpoint

/-- Exact relative entropy integrand at the genuine segment law. The real
identity is obtained from actual finite KL, so no ofReal clipping is discarded. -/
theorem h1DensitySegment_entropy_identity (h : ℝ) :
    Integrable (fun x => h1DensitySegmentValue u v t x * Real.log (h1DensitySegmentValue u v t x) -
      h1DensitySegmentValue u v t x * Real.log (referenceDensity h x)) (haar 1) ∧
      (ordinaryEntropy h (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht)).toReal =
        ∫ x, h1DensitySegmentValue u v t x * Real.log (h1DensitySegmentValue u v t x) -
          h1DensitySegmentValue u v t x * Real.log (referenceDensity h x) ∂haar 1 := by
  let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht
  let T := h1DensitySegmentValue u v t
  have hp : ∀ x, 0 < T x := h1DensitySegmentValue_positive u v hup hvp t ht
  have hc : Continuous T := h1DensitySegmentValue_continuous u v hu hv t
  have hd : τ.density = T := funext fun x => h1DensitySegment_density ρ σ u v hu hv hup hvp hρ hσ t ht x
  have hi1 : Integrable (fun x => T x * Real.log (T x)) (haar 1) :=
    (hc.mul (hc.log fun x => (hp x).ne')).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hi2 : Integrable (fun x => T x * Real.log (referenceDensity h x)) (haar 1) :=
    (hc.mul ((continuous_referenceDensity h).log fun x =>
      (referenceDensity_pos (h := h) x).ne')).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have he := (Structural.relativeEntropy_reference (ordinaryReference h) τ).2
  rw [← circleEntropy_eq_relativeEntropy] at he
  have hreal : (ordinaryEntropy h τ).toReal = DGPS.Analysis.circleEntropy τ -
      ∫ x, τ.density x * Real.log (referenceDensity h x) ∂haar 1 := he
  refine ⟨hi1.sub hi2, ?_⟩
  rw [hreal, circleEntropy_eq, hd, integral_sub hi1 hi2]

/-- Actual law identification is on the original closed segment; Phi itself
is an all-real scalar function for the separate extension/differentiation proof. -/
theorem h1DensitySegmentPhi_eq (h r : ℝ) :
    h1DensitySegmentPhi h r ρ σ u v t =
      (ordinaryFisher h (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht)).toReal -
        2 * r * (ordinaryEntropy h (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht)).toReal := by
  obtain ⟨hiF, hF⟩ := h1DensitySegment_fisher_identity ρ σ u v hu hv hup hvp hρ hσ t ht h
  obtain ⟨hiH, hH⟩ := h1DensitySegment_entropy_identity ρ σ u v hu hv hup hvp hρ hσ t ht h
  change (∫ x, (h1DensitySegmentGradient ρ σ u v t x 0 -
      h1DensitySegmentValue u v t x * logScore h x) ^ 2 / h1DensitySegmentValue u v t x -
        2 * r * (h1DensitySegmentValue u v t x * Real.log (h1DensitySegmentValue u v t x) -
          h1DensitySegmentValue u v t x * Real.log (referenceDensity h x)) ∂haar 1) = _
  rw [integral_sub hiF (hiH.const_mul (2 * r)), integral_const_mul, ← hF, ← hH]

end Segment
end DGPS.Examples.ThreeSpeciesCircle
