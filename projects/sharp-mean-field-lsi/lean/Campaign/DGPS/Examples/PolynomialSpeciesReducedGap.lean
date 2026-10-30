import DGPS.Examples.PolynomialSpeciesRangeGap
import DGPS.Frontier.STR029.T56

/-! The actual interacting reduced gap uses the existing STR029 segment Taylor
formula. The graph hypotheses here are exactly conclusions of the actual common
graph producer; no amplitude-factor or Hessian conclusion is a hypothesis. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

/-- The actual independent-parameter amplitude slice. -/
def polynomialGapSlice (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ) : PolynomialRangeParameters :=
  (x.1, x.2, θ.1, θ.2)

/-- The same graph correction is inserted in the normalized C2 chart. -/
def polynomialGapLift (ψ : PolynomialRangeParameters → E_STR02969)
    (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ) : PeriodicC2_STR02969 :=
  x.1 • cosC2_STR02915 + x.2 • sinC2_STR02915 +
    (ψ (polynomialGapSlice θ x) : PeriodicC2_STR02969)

/-- Reduced gap of the actual independent reference, with no change of graph witness. -/
def polynomialReducedGap (ψ : PolynomialRangeParameters → E_STR02969)
    (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ) : ℝ :=
  polynomialRangeGap θ.1 (polynomialGapLift ψ θ x)

private theorem slice_smooth (θ : (ℝ × ℝ) × ℝ) : ContDiff ℝ ∞ (polynomialGapSlice θ) := by
  exact contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const.prodMk contDiff_const))

private theorem lift_smooth {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hψ : ContDiffOn ℝ ∞ ψ U)
    (θ : (ℝ × ℝ) × ℝ) :
    ContDiffOn ℝ ∞ (polynomialGapLift ψ θ) (polynomialGapSlice θ ⁻¹' U) := by
  have hΦ : ContDiffOn ℝ ∞ (fun x => ψ (polynomialGapSlice θ x))
      (polynomialGapSlice θ ⁻¹' U) :=
    hψ.comp (slice_smooth θ).contDiffOn (fun _ hx => hx)
  have hE := E_STR02969.subtypeL.contDiff.comp_contDiffOn hΦ
  have hlin : ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
      x.1 • cosC2_STR02915 + x.2 • sinC2_STR02915) :=
    (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)
  exact hlin.contDiffOn.add hE

private theorem curry_smooth (F : (ℝ × ℝ) × PeriodicC2_STR02969 → ℝ)
    (hF : ContDiff ℝ ∞ F) (p : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 => F (p, u)) := by
  exact hF.comp (contDiff_const.prodMk contDiff_id)

private theorem compose_smooth (F : PeriodicC2_STR02969 → ℝ) (hF : ContDiff ℝ ∞ F)
    (L : (ℝ × ℝ) → PeriodicC2_STR02969) (W : Set (ℝ × ℝ)) (hL : ContDiffOn ℝ ∞ L W) :
    ContDiffOn ℝ ∞ (fun x => F (L x)) W := hF.comp_contDiffOn hL

private theorem composition_critical (F : PeriodicC2_STR02969 → ℝ)
    (L : (ℝ × ℝ) → PeriodicC2_STR02969) (hF : DifferentiableAt ℝ F (L 0))
    (hL : DifferentiableAt ℝ L 0) (hL0 : L 0 = 0) (hDF : fderiv ℝ F 0 = 0) :
    fderiv ℝ (F ∘ L) 0 = 0 := by
  rw [fderiv_comp 0 hF hL, hL0, hDF]
  exact ContinuousLinearMap.zero_comp _

/-- Smoothness is established in the independent parameters before root selection. -/
theorem polynomialReducedGap_smooth {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hψ : ContDiffOn ℝ ∞ ψ U)
    (θ : (ℝ × ℝ) × ℝ) :
    ContDiffOn ℝ ∞ (polynomialReducedGap ψ θ) (polynomialGapSlice θ ⁻¹' U) := by
  have hG := curry_smooth (fun x => polynomialRangeGap x.1 x.2) polynomialRangeGap_smooth θ.1
  exact compose_smooth (polynomialRangeGap θ.1) hG (polynomialGapLift ψ θ) _ (lift_smooth hψ θ)

/-- Exact quadratic amplitude factor for the genuine reduced gap. This invokes the
existing Taylor theorem; no new Taylor or implicit-function theorem is introduced. -/
theorem polynomialReducedGap_quadratic_factor {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ ∞ ψ U)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, polynomialGapSlice θ (t • x) ∈ U) :
    polynomialReducedGap ψ θ 0 = 0 ∧
      fderiv ℝ (polynomialReducedGap ψ θ) 0 = 0 ∧
      polynomialReducedGap ψ θ x = ∫ t in (0 : ℝ)..1,
        (1 - t) * fderiv ℝ (fderiv ℝ (polynomialReducedGap ψ θ)) (t • x) x x := by
  let W := polynomialGapSlice θ ⁻¹' U
  have hW : IsOpen W := hU.preimage (slice_smooth θ).continuous
  have h0W : (0 : ℝ × ℝ) ∈ W := by
    have h := hseg 0 ⟨le_rfl, zero_le_one⟩
    change polynomialGapSlice θ 0 ∈ U
    simpa only [zero_smul] using h
  have hψ0 : ψ (polynomialGapSlice θ 0) = 0 :=
    hzero θ.1.1 θ.1.2 θ.2 h0W
  have hL0 : polynomialGapLift ψ θ 0 = 0 := by
    change (0 : ℝ) • cosC2_STR02915 + (0 : ℝ) • sinC2_STR02915 +
      (ψ (polynomialGapSlice θ 0) : PeriodicC2_STR02969) = 0
    rw [hψ0]
    simp
  have hz : polynomialReducedGap ψ θ 0 = 0 := by
    rw [polynomialReducedGap, hL0, polynomialRangeGap_zero]
  have hLd : DifferentiableAt ℝ (polynomialGapLift ψ θ) 0 :=
    ((lift_smooth hψ θ).contDiffAt (hW.mem_nhds h0W)).differentiableAt (by simp)
  have hG := curry_smooth (fun x => polynomialRangeGap x.1 x.2) polynomialRangeGap_smooth θ.1
  have hd : fderiv ℝ (polynomialReducedGap ψ θ) 0 = 0 :=
    composition_critical (polynomialRangeGap θ.1) (polynomialGapLift ψ θ)
      (hG.differentiable (by simp) _) hLd hL0 (polynomialRangeGap_fderiv_zero θ.1)
  refine ⟨hz, hd, ?_⟩
  exact taylor_quad_STR02956 (polynomialReducedGap ψ θ) W hW
    (polynomialReducedGap_smooth hψ θ) x hseg hz hd

/-- The reduced gap on the selected-root slice is the original absolute-density gap. -/
theorem polynomialReducedGap_actual (ψ : PolynomialRangeParameters → E_STR02969)
    (h γ : ℝ) (x : ℝ × ℝ) (b : AbsoluteDrift (canonical_elementary_polynomial_model h)) :
    polynomialReducedGap ψ ((h, root_EX054 h), γ) x =
      (scalarGap (canonical_elementary_polynomial_model h)
        (polynomialChartAbsolute h (polynomialGapLift ψ ((h, root_EX054 h), γ) x)) : ℝ) := by
  exact (polynomialChartAbsolute_gap_eq_rangeGap h b _).symm

end DGPS.Examples.PolynomialSpecies
