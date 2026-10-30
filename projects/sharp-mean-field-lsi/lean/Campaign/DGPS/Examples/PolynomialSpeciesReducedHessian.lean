import DGPS.Examples.PolynomialSpeciesReducedGap
import DGPS.Examples.PolynomialSpeciesRangeQuadratic

/-! Transport of the actual origin gap Hessian through the SAME interacting
range graph. Its correction has zero amplitude derivative, proved by the actual
range equation; the chain rule retains and then kills the graph second derivative
using the genuine criticality of the full gap. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

private theorem critical_gap_chain (G : PeriodicC2_STR02969 → ℝ)
    (hG : ContDiff ℝ ∞ G) (hDG : fderiv ℝ G 0 = 0)
    (L : ℝ × ℝ → PeriodicC2_STR02969)
    (W : Set (ℝ × ℝ)) (hW : IsOpen W) (h0W : (0 : ℝ × ℝ) ∈ W)
    (hL : ContDiffOn ℝ ∞ L W) (hL0 : L 0 = 0) (x : ℝ × ℝ) :
    fderiv ℝ (fderiv ℝ (G ∘ L)) 0 x x =
      fderiv ℝ (fderiv ℝ G) 0
        (fderiv ℝ L 0 x) (fderiv ℝ L 0 x) := by
  have hLd := (hL.contDiffAt (hW.mem_nhds h0W)).differentiableAt (by simp)
  have hDFG : DifferentiableAt ℝ (fderiv ℝ G) (L 0) :=
    ((hG.fderiv_right (m := 1) (by simp)).differentiable (by simp)) _
  have hDL : DifferentiableAt ℝ (fderiv ℝ L) 0 :=
    (((hL.fderiv_of_isOpen hW (m := 1) (by simp)).contDiffAt
      (hW.mem_nhds h0W)).differentiableAt (by simp))
  have he : fderiv ℝ (G ∘ L) =ᶠ[𝓝 0]
      (fun y => (fderiv ℝ G (L y)).comp (fderiv ℝ L y)) := by
    filter_upwards [hW.mem_nhds h0W] with y hy
    exact fderiv_comp y (hG.differentiable (by simp) _)
      ((hL.contDiffAt (hW.mem_nhds hy)).differentiableAt (by simp))
  have hc := hDFG.hasFDerivAt.comp 0 hLd.hasFDerivAt
  have hd := hc.clm_comp hDL.hasFDerivAt
  change HasFDerivAt (fun y => (fderiv ℝ G (L y)).comp (fderiv ℝ L y)) _ 0 at hd
  rw [he.fderiv_eq, hd.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, Function.comp_apply, hL0,
    hDG,
    ContinuousLinearMap.zero_apply, zero_add]

private def originLift (ψ : PolynomialRangeParameters → E_STR02969) :
    (ℝ × ℝ) → PeriodicC2_STR02969 := polynomialGapLift ψ ((0, 0), 0)

private def amplitudeLinear : (ℝ × ℝ) →L[ℝ] PeriodicC2_STR02969 :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight cosC2_STR02915 +
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight sinC2_STR02915

private theorem originLift_data {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    : let W := (polynomialGapSlice ((0, 0), 0)) ⁻¹' U
      IsOpen W ∧ (0 : ℝ × ℝ) ∈ W ∧ ContDiffOn ℝ ∞ (originLift ψ) W ∧
        originLift ψ 0 = 0 ∧ fderiv ℝ (originLift ψ) 0 = amplitudeLinear := by
  let θ : (ℝ × ℝ) × ℝ := ((0, 0), 0)
  let q := polynomialGapSlice θ
  let W := q ⁻¹' U
  let L := originLift ψ
  have hq : ContDiff ℝ ∞ q := by
    exact contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const.prodMk contDiff_const))
  have hq0 : q 0 = 0 := by ext <;> rfl
  have hW : IsOpen W := hU.preimage hq.continuous
  have h0W : (0 : ℝ × ℝ) ∈ W := by change q 0 ∈ U; rw [hq0]; exact h0U
  have hΦ : ContDiffOn ℝ ∞ (fun x => ψ (q x)) W :=
    hψ.comp hq.contDiffOn (fun _ hx => hx)
  have hE := E_STR02969.subtypeL.contDiff.comp_contDiffOn hΦ
  have hlin : ContDiff ℝ ∞ (fun x : ℝ × ℝ =>
      x.1 • cosC2_STR02915 + x.2 • sinC2_STR02915) :=
    (contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)
  have hL : ContDiffOn ℝ ∞ L W := hlin.contDiffOn.add hE
  have hL0 : L 0 = 0 := by
    change (0 : ℝ) • cosC2_STR02915 + (0 : ℝ) • sinC2_STR02915 +
      (ψ (q 0) : PeriodicC2_STR02969) = 0
    rw [hq0, hψ0]
    simp
  let A := amplitudeLinear
  have hA : HasFDerivAt (fun x : ℝ × ℝ =>
      x.1 • cosC2_STR02915 + x.2 • sinC2_STR02915) A 0 := A.hasFDerivAt
  have hχ : fderiv ℝ (fun x => ψ (q x)) 0 = 0 := hamp
  have hχd := (hΦ.contDiffAt (hW.mem_nhds h0W)).differentiableAt (by simp)
  have hEc := E_STR02969.subtypeL.hasFDerivAt.comp 0 hχd.hasFDerivAt
  rw [hχ] at hEc
  have hDL : fderiv ℝ L 0 = A := by
    have hd : HasFDerivAt L A 0 := by
      have hh := hA.add hEc
      simp only [ContinuousLinearMap.comp_zero, add_zero] at hh
      convert hh using 1 <;> rfl
    exact hd.fderiv
  exact ⟨hW, h0W, hL, hL0, hDL⟩

private def originGap : PeriodicC2_STR02969 → ℝ := polynomialRangeGap (0, 0)

private theorem curry_smooth (F : (ℝ × ℝ) × PeriodicC2_STR02969 → ℝ)
    (hF : ContDiff ℝ ∞ F) (p : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 => F (p, u)) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

private theorem originGap_smooth : ContDiff ℝ ∞ originGap :=
  curry_smooth (fun x => polynomialRangeGap x.1 x.2) polynomialRangeGap_smooth (0, 0)

/-- The actual reduced gap has the true first-harmonic Hessian. The hypotheses on
this SAME graph are conclusions of `exists_polynomial_common_range_graph`; no
reduced Hessian, quadratic coefficient or amplitude estimate is a premise. -/
theorem polynomialReducedGap_hessian_origin {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (h0U : (0 : PolynomialRangeParameters) ∈ U) (hψ : ContDiffOn ℝ ∞ ψ U)
    (hψ0 : ψ (0 : PolynomialRangeParameters) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (a b : ℝ) :
    fderiv ℝ (fderiv ℝ (polynomialReducedGap ψ ((0, 0), 0))) 0 (a, b) (a, b) =
      (a ^ 2 + b ^ 2) / 2 := by
  obtain ⟨hW, h0W, hL, hL0, hDL⟩ := originLift_data hU h0U hψ hψ0 hamp
  change fderiv ℝ (fderiv ℝ (originGap ∘ originLift ψ)) 0 (a, b) (a, b) = _
  rw [critical_gap_chain originGap originGap_smooth
    (polynomialRangeGap_fderiv_zero (0, 0)) (originLift ψ) _ hW h0W hL hL0, hDL]
  exact polynomialRangeGap_first_amplitude_hessian a b

end DGPS.Examples.PolynomialSpecies
