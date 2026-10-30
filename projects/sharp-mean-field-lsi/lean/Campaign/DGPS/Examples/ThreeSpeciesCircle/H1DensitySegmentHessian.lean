import DGPS.Examples.ThreeSpeciesCircle.H1DensitySegmentDifferentiation
import DGPS.Examples.ThreeSpeciesCircle.H1DensitySegmentCost

/-! Actual density-path Fisher-minus-entropy Hessians and their native ratio
interpretation. All chosen endpoint gradients and physical normalizations are retained. -/

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace DGPS.Examples.ThreeSpeciesCircle

def h1DensityEndpointGradient (ρ : AbsoluteDensity 1) (u : Torus 1 → ℝ) (x : Torus 1) : ℝ :=
  2 * u x * weakGradient ρ.sqrt ρ.sqrt_mem x 0

theorem h1DensityEndpointGradient_memLp (ρ : AbsoluteDensity 1) (u : Torus 1 → ℝ)
    (hu : Continuous u) : MemLp (h1DensityEndpointGradient ρ u) 2 (haar 1) := by
  have hm : MemLp (fun x => u x * weakGradient ρ.sqrt ρ.sqrt_mem x 0) 2 (haar 1) :=
    (memLp_top_of_continuous' hu).mul
      (memLp_coord (isWeakGradient_weakGradient ρ.sqrt_mem).memLp_grad 0)
  convert hm.const_mul 2 using 1
  funext x
  simp only [h1DensityEndpointGradient, Pi.mul_apply]
  ring

theorem h1DensitySegmentGradient_coord (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ)
    (t : ℝ) (x : Torus 1) :
    h1DensitySegmentGradient ρ σ u v t x 0 = h1DensityEndpointGradient ρ u x +
      t * (h1DensityEndpointGradient σ v x - h1DensityEndpointGradient ρ u x) := by
  simp only [h1DensitySegmentGradient, h1DensityEndpointGradient,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

private def segmentReferenceTerm (h r : ℝ) (c a : Torus 1 → ℝ) (x : Torus 1) : ℝ :=
  -2 * a x * logScore h x +
    c x * (logScore h x ^ 2 + 2 * r * Real.log (referenceDensity h x))

/-- The chosen reference weak score is controlled only a.e., through its
actual L2 multiplier theorem. No pointwise continuous score is substituted. -/
private theorem segmentReferenceTerm_integrable (h r : ℝ) (c a : Torus 1 → ℝ)
    (hc : Continuous c) (ha : MemLp a 2 (haar 1)) :
    Integrable (segmentReferenceTerm h r c a) (haar 1) := by
  have hi1 := (memLp_mul_logScore h ha).integrable one_le_two
  have hi2 := (memLp_mul_logScore h (memLp_mul_logScore h (memLp_two_of_continuous hc))).integrable one_le_two
  have hi3 : Integrable (fun x => c x * Real.log (referenceDensity h x)) (haar 1) :=
    (hc.mul ((continuous_referenceDensity h).log fun x =>
      (referenceDensity_pos (h := h) x).ne')).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  refine (((hi1.const_mul (-2)).add hi2).add (hi3.const_mul (2 * r))).congr ?_
  exact Eventually.of_forall fun x => by
    dsimp only [segmentReferenceTerm]
    simp only [Pi.add_apply, Pi.mul_apply]
    ring

private theorem segmentNonlinearIntegrand_integrable (r : ℝ) (u v a b : Torus 1 → ℝ)
    (hu : Continuous u) (hv : Continuous v) (ha : MemLp a 2 (haar 1)) (hb : MemLp b 2 (haar 1))
    (t : ℝ) (hp : ∀ x, 0 < u x ^ 2 + t * (v x ^ 2 - u x ^ 2)) :
    Integrable (fun x => h1SegmentCostIntegrand r (u x ^ 2) (v x ^ 2 - u x ^ 2)
      (a x) (b x) t) (haar 1) := by
  let P := fun x => u x ^ 2 + t * (v x ^ 2 - u x ^ 2)
  have hc : Continuous P := by dsimp only [P]; fun_prop
  have hci : Continuous (fun x => (P x)⁻¹) := by
    convert ((continuous_const : Continuous (fun _ : Torus 1 => (1 : ℝ))).div hc
      (fun x => (hp x).ne')) using 1
    funext x
    simp only [Pi.div_apply, one_div]
  obtain ⟨K, hK⟩ := isCompact_univ.exists_bound_of_continuousOn hci.continuousOn
  have hA := (ha.add (hb.const_mul t)).integrable_sq
  have hI := hA.mul_bdd hci.aestronglyMeasurable (Eventually.of_forall fun x => hK x (mem_univ x))
  have hH : Integrable (fun x => P x * Real.log (P x)) (haar 1) :=
    (hc.mul (hc.log fun x => (hp x).ne')).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  convert hI.sub (hH.const_mul (2 * r)) using 1
  funext x
  simp only [h1SegmentCostIntegrand, P, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.pow_apply, div_eq_mul_inv]

private def segmentReferenceConstant (h r : ℝ) (ρ : AbsoluteDensity 1) (u : Torus 1 → ℝ) : ℝ :=
  ∫ x, segmentReferenceTerm h r (fun x => u x ^ 2) (h1DensityEndpointGradient ρ u) x ∂haar 1

private def segmentReferenceSlope (h r : ℝ) (ρ σ : AbsoluteDensity 1) (u v : Torus 1 → ℝ) : ℝ :=
  ∫ x, segmentReferenceTerm h r (fun x => v x ^ 2 - u x ^ 2)
    (fun x => h1DensityEndpointGradient σ v x - h1DensityEndpointGradient ρ u x) x ∂haar 1

/-- Reference terms are affine in the actual density and its weak derivative.
This identity holds throughout the genuine positive extension, not just at
parameters where the closed-segment law constructor has been invoked. -/
private theorem segmentPhi_decomposition (h r : ℝ) (ρ σ : AbsoluteDensity 1)
    (u v : Torus 1 → ℝ) (hu : Continuous u) (hv : Continuous v) (t : ℝ)
    (hp : ∀ x, 0 < h1DensitySegmentValue u v t x) :
    h1DensitySegmentPhi h r ρ σ u v t =
      h1SegmentNonlinearCost r u v (h1DensityEndpointGradient ρ u)
        (fun x => h1DensityEndpointGradient σ v x - h1DensityEndpointGradient ρ u x) t +
      segmentReferenceConstant h r ρ u + t * segmentReferenceSlope h r ρ σ u v := by
  let a := h1DensityEndpointGradient ρ u
  let b := fun x => h1DensityEndpointGradient σ v x - h1DensityEndpointGradient ρ u x
  have ha := h1DensityEndpointGradient_memLp ρ u hu
  have hb := (h1DensityEndpointGradient_memLp σ v hv).sub ha
  have hshape (x : Torus 1) : u x ^ 2 + t * (v x ^ 2 - u x ^ 2) =
      h1DensitySegmentValue u v t x := by unfold h1DensitySegmentValue; ring
  have hN := segmentNonlinearIntegrand_integrable r u v a b hu hv ha hb t
    (fun x => by rw [hshape]; exact hp x)
  have hC0 := segmentReferenceTerm_integrable h r (fun x => u x ^ 2) a (hu.pow 2) ha
  have hC1 := segmentReferenceTerm_integrable h r (fun x => v x ^ 2 - u x ^ 2) b
    ((hv.pow 2).sub (hu.pow 2)) hb
  have he (x : Torus 1) :
      (h1DensitySegmentGradient ρ σ u v t x 0 - h1DensitySegmentValue u v t x * logScore h x) ^ 2 /
          h1DensitySegmentValue u v t x -
        2 * r * (h1DensitySegmentValue u v t x * Real.log (h1DensitySegmentValue u v t x) -
          h1DensitySegmentValue u v t x * Real.log (referenceDensity h x)) =
      h1SegmentCostIntegrand r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t +
        segmentReferenceTerm h r (fun x => u x ^ 2) a x +
          t * segmentReferenceTerm h r (fun x => v x ^ 2 - u x ^ 2) b x := by
    rw [h1DensitySegmentGradient_coord, ← hshape]
    change ((a x + t * b x) - (u x ^ 2 + t * (v x ^ 2 - u x ^ 2)) * logScore h x) ^ 2 /
        (u x ^ 2 + t * (v x ^ 2 - u x ^ 2)) - _ = _
    have hn : u x ^ 2 + t * (v x ^ 2 - u x ^ 2) ≠ 0 := by rw [hshape]; exact (hp x).ne'
    dsimp only [h1SegmentCostIntegrand, segmentReferenceTerm]
    field_simp [hn]
    <;> ring
  unfold h1DensitySegmentPhi
  simp_rw [he]
  change (∫ x, (h1SegmentCostIntegrand r (u x ^ 2) (v x ^ 2 - u x ^ 2)
    (a x) (b x) t + segmentReferenceTerm h r (fun x => u x ^ 2) a x) +
    (t * segmentReferenceTerm h r (fun x => v x ^ 2 - u x ^ 2) b x) ∂haar 1) = _
  have hs := integral_add (hN.add hC0) (hC1.const_mul t)
  simp only [Pi.add_apply, Pi.mul_apply] at hs
  rw [hs, integral_add hN hC0, integral_const_mul]
  rfl

/-- The all-real explicit first-derivative function. Its equality with the
derivative of the actual law cost is established below on the closed segment. -/
def h1DensitySegmentPhiDerivative (h r : ℝ) (ρ σ : AbsoluteDensity 1)
    (u v : Torus 1 → ℝ) (t : ℝ) : ℝ :=
  (∫ x, h1SegmentCostDerivative r (u x ^ 2) (v x ^ 2 - u x ^ 2)
    (h1DensityEndpointGradient ρ u x)
    (h1DensityEndpointGradient σ v x - h1DensityEndpointGradient ρ u x) t ∂haar 1) +
      segmentReferenceSlope h r ρ σ u v

/-- Honest first derivative of the actual density-coordinate cost; endpoint
parameters are justified by the real positive extension and L1 domination. -/
theorem h1DensitySegmentPhi_hasDerivAt (h r : ℝ) (ρ σ : AbsoluteDensity 1)
    (u v : Torus 1 → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (t0 : ℝ) (ht0 : t0 ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (h1DensitySegmentPhi h r ρ σ u v)
      (h1DensitySegmentPhiDerivative h r ρ σ u v t0) t0 := by
  let a := h1DensityEndpointGradient ρ u
  let b := fun x => h1DensityEndpointGradient σ v x - h1DensityEndpointGradient ρ u x
  have ha := h1DensityEndpointGradient_memLp ρ u hu
  have hb := (h1DensityEndpointGradient_memLp σ v hv).sub ha
  have hcore := h1SegmentNonlinearCost_hasDerivAt r u v a b hu hv hup hvp ha hb t0 ht0
  have hd := (hcore.add_const (segmentReferenceConstant h r ρ u)).add
    ((hasDerivAt_id t0).mul_const (segmentReferenceSlope h r ρ σ u v))
  obtain ⟨η, m, K, hη, hm, _, hbounds⟩ := h1DensitySegment_uniform_positive_extension u v hu hv hup hvp
  have heq : (fun t => h1SegmentNonlinearCost r u v a b t + segmentReferenceConstant h r ρ u +
      t * segmentReferenceSlope h r ρ σ u v) =ᶠ[𝓝 t0] h1DensitySegmentPhi h r ρ σ u v := by
    filter_upwards [Ioo_mem_nhds (by linarith [ht0.1] : -η < t0)
      (by linarith [ht0.2] : t0 < 1 + η)] with t ht
    exact (segmentPhi_decomposition h r ρ σ u v hu hv t
      (fun x => hm.trans_le (hbounds t ⟨ht.1.le, ht.2.le⟩ x).1)).symm
  have hΦ : HasDerivAt (h1DensitySegmentPhi h r ρ σ u v)
      ((∫ x, h1SegmentCostDerivative r (u x ^ 2) (v x ^ 2 - u x ^ 2) (a x) (b x) t0 ∂haar 1) +
        segmentReferenceSlope h r ρ σ u v) t0 := by
    simpa only [one_mul] using (hd.congr_of_eventuallyEq heq.symm)
  exact hΦ

/-- Actual integrated second derivative, before rewriting it as native ratio
Dirichlet energy and variance. No Poincare or Hessian estimate is assumed. -/
theorem h1DensitySegmentPhiDerivative_hasDerivAt (h r : ℝ) (ρ σ : AbsoluteDensity 1)
    (u v : Torus 1 → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (t0 : ℝ) (ht0 : t0 ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (h1DensitySegmentPhiDerivative h r ρ σ u v)
      (∫ x, 2 * ((h1DensityEndpointGradient σ v x - h1DensityEndpointGradient ρ u x) *
          h1DensitySegmentValue u v t0 x - (v x ^ 2 - u x ^ 2) *
            h1DensitySegmentGradient ρ σ u v t0 x 0) ^ 2 / h1DensitySegmentValue u v t0 x ^ 3 -
        2 * r * (v x ^ 2 - u x ^ 2) ^ 2 / h1DensitySegmentValue u v t0 x ∂haar 1) t0 := by
  let a := h1DensityEndpointGradient ρ u
  let b := fun x => h1DensityEndpointGradient σ v x - h1DensityEndpointGradient ρ u x
  have ha := h1DensityEndpointGradient_memLp ρ u hu
  have hb := (h1DensityEndpointGradient_memLp σ v hv).sub ha
  have hd := (h1SegmentNonlinearCostDerivative_hasDerivAt r u v a b hu hv hup hvp ha hb t0 ht0).add_const
    (segmentReferenceSlope h r ρ σ u v)
  convert hd using 1
  · rfl
  · apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      have hshape : u x ^ 2 + t0 * (v x ^ 2 - u x ^ 2) = h1DensitySegmentValue u v t0 x := by
        unfold h1DensitySegmentValue
        ring
      change _ = _
      simp only [Pi.add_apply, Pi.mul_apply]
      rw [← hshape, h1DensitySegmentGradient_coord]

/-- The genuine full-native-domain density-path Hessian. The ratio and its
centering/domain are constructed internally; no Hessian or Poincare inequality
is assumed, and arbitrary null-set values of the original roots are retained. -/
theorem h1DensitySegmentPhiDerivative_native_hasDerivAt (h r : ℝ) (ρ σ : AbsoluteDensity 1)
    (u v : Torus 1 → ℝ) (hu : Continuous u) (hv : Continuous v)
    (hup : ∀ x, 0 < u x) (hvp : ∀ x, 0 < v x)
    (hρ : ρ.sqrt =ᵐ[haar 1] u) (hσ : σ.sqrt =ᵐ[haar 1] v)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht
    let f := h1DensitySegmentRatio ρ σ u v hu hv hup hvp hρ hσ t ht
    HasDerivAt (h1DensitySegmentPhiDerivative h r ρ σ u v)
      (2 * (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure τ : Measure (Torus 1))) -
        2 * r * weightedVariance (densityMeasure τ) f.fn) t := by
  let τ := h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht
  let f := h1DensitySegmentRatio ρ σ u v hu hv hup hvp hρ hσ t ht
  let P := h1DensitySegmentValue u v t
  let W := fun x => (h1DensityEndpointGradient σ v x - h1DensityEndpointGradient ρ u x) * P x -
    (v x ^ 2 - u x ^ 2) * h1DensitySegmentGradient ρ σ u v t x 0
  have hp : ∀ x, 0 < P x := h1DensitySegmentValue_positive u v hup hvp t ht
  have hPc : Continuous P := h1DensitySegmentValue_continuous u v hu hv t
  have hRW := h1DensitySegment_ratio_weak ρ σ u v hu hv hup hvp hρ hσ t ht
  have hn (z : Tangent 1) : ‖z‖ ^ 2 = (z 0) ^ 2 := by
    simp [EuclideanSpace.norm_sq_eq]
  have hGp (x : Torus 1) : P x * ‖f.grad x‖ ^ 2 = W x ^ 2 / P x ^ 3 := by
    rw [hn]
    simp only [f, h1DensitySegmentRatio, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
    dsimp only [W, h1DensityEndpointGradient, P]
    field_simp [(hp x).ne']
    <;> ring
  have hFp (x : Torus 1) : P x * f.fn x ^ 2 = (v x ^ 2 - u x ^ 2) ^ 2 / P x := by
    dsimp only [f, h1DensitySegmentRatio]
    change P x * ((v x ^ 2 - u x ^ 2) / P x) ^ 2 = _
    field_simp [(hp x).ne']
    <;> ring
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hPc.continuousOn
  have hGI : Integrable (fun x => P x * ‖f.grad x‖ ^ 2) (haar 1) :=
    hRW.memLp_grad.norm.integrable_sq.bdd_mul hPc.aestronglyMeasurable
      (Eventually.of_forall fun x => hB x (mem_univ x))
  have hFI : Integrable (fun x => P x * f.fn x ^ 2) (haar 1) :=
    hRW.memLp.integrable_sq.bdd_mul hPc.aestronglyMeasurable
      (Eventually.of_forall fun x => hB x (mem_univ x))
  have hEn : (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure τ : Measure (Torus 1))) =
      ∫ x, P x * ‖f.grad x‖ ^ 2 ∂haar 1 := by
    rw [Structural.budget_integral_densityMeasure]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change τ.density x * _ = P x * _
      change (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht).density x * _ = _
      rw [h1DensitySegment_density]
  have hFn : (∫ x, f.fn x ^ 2 ∂(densityMeasure τ : Measure (Torus 1))) =
      ∫ x, P x * f.fn x ^ 2 ∂haar 1 := by
    rw [Structural.budget_integral_densityMeasure]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change τ.density x * _ = P x * _
      change (h1DensitySegment ρ σ u v hu hv hup hvp hρ hσ t ht).density x * _ = _
      rw [h1DensitySegment_density]
  have hV : weightedVariance (densityMeasure τ) f.fn =
      ∫ x, f.fn x ^ 2 ∂(densityMeasure τ : Measure (Torus 1)) := by
    unfold weightedVariance
    rw [h1DensitySegmentRatio_mean ρ σ u v hu hv hup hvp hρ hσ t ht]
    simp only [sub_zero]
  have hcoeff : 2 * (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure τ : Measure (Torus 1))) -
      2 * r * weightedVariance (densityMeasure τ) f.fn =
        ∫ x, 2 * W x ^ 2 / P x ^ 3 - 2 * r * (v x ^ 2 - u x ^ 2) ^ 2 / P x ∂haar 1 := by
    rw [hV, hEn, hFn]
    rw [← integral_const_mul, ← integral_const_mul, ← integral_sub (hGI.const_mul 2) (hFI.const_mul (2 * r))]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      change 2 * (P x * ‖f.grad x‖ ^ 2) - 2 * r * (P x * f.fn x ^ 2) = _
      rw [hGp, hFp]
      ring
  change HasDerivAt (h1DensitySegmentPhiDerivative h r ρ σ u v)
    (2 * (∫ x, ‖f.grad x‖ ^ 2 ∂(densityMeasure τ : Measure (Torus 1))) -
      2 * r * weightedVariance (densityMeasure τ) f.fn) t
  rw [hcoeff]
  exact h1DensitySegmentPhiDerivative_hasDerivAt h r ρ σ u v hu hv hup hvp t ht

end DGPS.Examples.ThreeSpeciesCircle
