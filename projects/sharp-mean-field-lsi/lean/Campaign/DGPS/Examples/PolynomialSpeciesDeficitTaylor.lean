import DGPS.Examples.PolynomialSpeciesReducedGap
import DGPS.Examples.PolynomialSpeciesRangeStationarity
import DGPS.Examples.PolynomialSpeciesHalfTurnGraph
import DGPS.Frontier.STR029.T56

/-! The ACTUAL reduced interacting value has a quadratic amplitude factor for
all small independent reference and rate parameters. This reuses the existing
segment Taylor theorem, with genuine actual-value stationarity proved upstream. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029

namespace DGPS.Examples.PolynomialSpecies

/-- Joint smoothness of the actual same-graph value, before selected-root entry. -/
theorem polynomialReducedDeficit_smooth {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hψ : ContDiffOn ℝ ∞ ψ U) :
    ContDiffOn ℝ ∞ (polynomialReducedDeficit ψ) U := by
  have hE := E_STR02969.subtypeL.contDiff.comp_contDiffOn hψ
  have hlin : ContDiff ℝ ∞ (fun p : PolynomialRangeParameters =>
      p.1 • cosC2_STR02915 + p.2.1 • sinC2_STR02915) := by fun_prop
  have hL : ContDiffOn ℝ ∞ (fun p : PolynomialRangeParameters =>
      p.1 • cosC2_STR02915 + p.2.1 • sinC2_STR02915 + (ψ p : PeriodicC2_STR02969)) U :=
    hlin.contDiffOn.add hE
  have hp : ContDiff ℝ ∞ (fun p : PolynomialRangeParameters => p.2.2.1) := by fun_prop
  have hr : ContDiff ℝ ∞ (fun p : PolynomialRangeParameters =>
      DGPS.Circle.AngularNormalization.a0 * (1 + p.2.2.2)) := by fun_prop
  let V : PolynomialEulerInput → ℝ := fun q => polynomialRangeDeficit q.1 q.2.1 q.2.2
  let Q : PolynomialRangeParameters → PolynomialEulerInput := fun p =>
    (p.2.2.1, DGPS.Circle.AngularNormalization.a0 * (1 + p.2.2.2),
      p.1 • cosC2_STR02915 + p.2.1 • sinC2_STR02915 + (ψ p : PeriodicC2_STR02969))
  have hV : ContDiff ℝ ∞ V := polynomialRangeDeficit_smooth
  have hQ : ContDiffOn ℝ ∞ Q U := hp.contDiffOn.prodMk (hr.contDiffOn.prodMk hL)
  change ContDiffOn ℝ ∞ (V ∘ Q) U
  exact hV.comp_contDiffOn hQ

private theorem fixed_smooth (F : PolynomialEulerInput → ℝ) (hF : ContDiff ℝ ∞ F)
    (p : ℝ × ℝ) (r : ℝ) : ContDiff ℝ ∞ (fun u : PeriodicC2_STR02969 => F (p, r, u)) := by
  exact hF.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))

private theorem critical_composition (F : PeriodicC2_STR02969 → ℝ)
    (L : (ℝ × ℝ) → PeriodicC2_STR02969) (hF : DifferentiableAt ℝ F (L 0))
    (hL : DifferentiableAt ℝ L 0) (hL0 : L 0 = 0) (hD : fderiv ℝ F 0 = 0) :
    fderiv ℝ (F ∘ L) 0 = 0 := by
  rw [fderiv_comp 0 hF hL, hL0, hD]
  exact ContinuousLinearMap.zero_comp _

/-- Exact actual-value amplitude factor on a segment in the actual graph domain.
There is no amplitude-factor, sharp-remainder or optimizer premise. -/
theorem polynomialReducedDeficit_quadratic_factor {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ ∞ ψ U)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (θ : (ℝ × ℝ) × ℝ) (x : ℝ × ℝ)
    (hseg : ∀ t ∈ Set.Icc (0 : ℝ) 1, polynomialGapSlice θ (t • x) ∈ U) :
    let F := fun y : ℝ × ℝ => polynomialReducedDeficit ψ (polynomialGapSlice θ y)
    F 0 = 0 ∧ fderiv ℝ F 0 = 0 ∧
      F x = ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ F) (t • x) x x := by
  let q := polynomialGapSlice θ
  let W := q ⁻¹' U
  let L := polynomialGapLift ψ θ
  let r := DGPS.Circle.AngularNormalization.a0 * (1 + θ.2)
  let G := polynomialRangeDeficit θ.1 r
  let F := fun y : ℝ × ℝ => polynomialReducedDeficit ψ (q y)
  have hq : ContDiff ℝ ∞ q :=
    contDiff_fst.prodMk (contDiff_snd.prodMk (contDiff_const.prodMk contDiff_const))
  have hW : IsOpen W := hU.preimage hq.continuous
  have h0W : (0 : ℝ × ℝ) ∈ W := by
    change q 0 ∈ U
    simpa only [zero_smul] using hseg 0 ⟨le_rfl, zero_le_one⟩
  have hψ0 : ψ (q 0) = 0 := hzero θ.1.1 θ.1.2 θ.2 h0W
  have hL0 : L 0 = 0 := by
    change (0 : ℝ) • cosC2_STR02915 + (0 : ℝ) • sinC2_STR02915 +
      (ψ (q 0) : PeriodicC2_STR02969) = 0
    rw [hψ0]
    simp
  have he : F = G ∘ L := rfl
  have hFs : ContDiffOn ℝ ∞ F W :=
    (polynomialReducedDeficit_smooth hψ).comp hq.contDiffOn (fun _ hy => hy)
  have hΦ : ContDiffOn ℝ ∞ (fun y => ψ (q y)) W :=
    hψ.comp hq.contDiffOn (fun _ hy => hy)
  have hlin : ContDiff ℝ ∞ (fun y : ℝ × ℝ =>
      y.1 • cosC2_STR02915 + y.2 • sinC2_STR02915) := by fun_prop
  have hLs : ContDiffOn ℝ ∞ L W :=
    hlin.contDiffOn.add (E_STR02969.subtypeL.contDiff.comp_contDiffOn hΦ)
  have hG := fixed_smooth (fun z => polynomialRangeDeficit z.1 z.2.1 z.2.2)
    polynomialRangeDeficit_smooth θ.1 r
  have hz : F 0 = 0 := by rw [he, Function.comp_apply, hL0]; exact polynomialRangeDeficit_zero θ.1 r
  have hd : fderiv ℝ F 0 = 0 := by
    rw [he]
    exact critical_composition G L (hG.differentiable (by simp) _)
      ((hLs.contDiffAt (hW.mem_nhds h0W)).differentiableAt (by simp)) hL0
      (polynomialRangeDeficit_fderiv_zero θ.1 r)
  exact ⟨hz, hd, taylor_quad_STR02956 F W hW hFs x hseg hz hd⟩

end DGPS.Examples.PolynomialSpecies
