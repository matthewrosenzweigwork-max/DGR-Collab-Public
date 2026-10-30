import DGPS.Examples.PolynomialSpeciesRadialEnvelope
import DGPS.Examples.PolynomialSpeciesGapRadial
import DGPS.Examples.PolynomialSpeciesReducedRadial
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Sign-sensitive rate control of the actual selected-reference radial deficit.
Every rate segment stays in one fixed joint ball. Only the production envelope
on the selected root slice is used; that root is never differentiated. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium
open DGPS.Circle.AngularNormalization

namespace DGPS.Examples.PolynomialSpecies

private def rateSelectedInput (h : ℝ) (z : (ℝ × ℝ) × ℝ) : PolynomialRangeParameters :=
  (z.1.1, z.1.2, (h, root_EX054 h), z.2)
private def rateSelectedF (ψ : PolynomialRangeParameters → E_STR02969) (h : ℝ)
    (z : (ℝ × ℝ) × ℝ) : ℝ :=
  polynomialRangeDeficit (h, root_EX054 h) (a0 * (1 + z.2))
    (polynomialGapLift ψ ((h, root_EX054 h), z.2) z.1)
private def rateSelectedG (ψ : PolynomialRangeParameters → E_STR02969) (h : ℝ)
    (z : (ℝ × ℝ) × ℝ) : ℝ :=
  polynomialReducedGap ψ ((h, root_EX054 h), z.2) z.1

private theorem selected_smooth {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hU : IsOpen U)
    (hψ : ContDiffOn ℝ ∞ ψ U) (h : ℝ) :
    IsOpen (rateSelectedInput h ⁻¹' U) ∧
      ContDiffOn ℝ ∞ (rateSelectedF ψ h) (rateSelectedInput h ⁻¹' U) ∧
      ContDiffOn ℝ ∞ (rateSelectedG ψ h) (rateSelectedInput h ⁻¹' U) := by
  have hs : ContDiff ℝ ∞ (rateSelectedInput h) := by unfold rateSelectedInput; fun_prop
  let W := rateSelectedInput h ⁻¹' U
  let L := fun z : (ℝ × ℝ) × ℝ => polynomialGapLift ψ ((h, root_EX054 h), z.2) z.1
  have hΦ : ContDiffOn ℝ ∞ (fun z => ψ (rateSelectedInput h z)) W :=
    hψ.comp hs.contDiffOn (fun _ hz => hz)
  have hlin : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
      z.1.1 • cosC2_STR02915 + z.1.2 • sinC2_STR02915) :=
    ((contDiff_fst.comp contDiff_fst).smul contDiff_const).add
      ((contDiff_snd.comp contDiff_fst).smul contDiff_const)
  have hL : ContDiffOn ℝ ∞ L W := by
    change ContDiffOn ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
      z.1.1 • cosC2_STR02915 + z.1.2 • sinC2_STR02915 +
        (E_STR02969.subtypeL (ψ (rateSelectedInput h z)))) W
    exact hlin.contDiffOn.add (E_STR02969.subtypeL.contDiff.comp_contDiffOn hΦ)
  have hr : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ => a0 * (1 + z.2)) :=
    contDiff_const.mul (contDiff_const.add contDiff_snd)
  have hI : ContDiffOn ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
      ((h, root_EX054 h), a0 * (1 + z.2), L z)) W :=
    contDiffOn_const.prodMk (hr.contDiffOn.prodMk hL)
  refine ⟨hU.preimage hs.continuous, ?_, ?_⟩
  · let V : PolynomialEulerInput → ℝ := fun q => polynomialRangeDeficit q.1 q.2.1 q.2.2
    let I : (ℝ × ℝ) × ℝ → PolynomialEulerInput := fun z =>
      ((h, root_EX054 h), a0 * (1 + z.2), L z)
    have hV : ContDiff ℝ ∞ V := polynomialRangeDeficit_smooth
    have he : rateSelectedF ψ h = V ∘ I := rfl
    rw [he]
    exact hV.comp_contDiffOn hI
  · let V : (ℝ × ℝ) × PeriodicC2_STR02969 → ℝ := fun q => polynomialRangeGap q.1 q.2
    let I : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × PeriodicC2_STR02969 := fun z =>
      ((h, root_EX054 h), L z)
    have hV : ContDiff ℝ ∞ V := polynomialRangeGap_smooth
    have hGI : ContDiffOn ℝ ∞ I W := contDiffOn_const.prodMk hL
    have he : rateSelectedG ψ h = V ∘ I := rfl
    rw [he]
    exact hV.comp_contDiffOn hGI

private theorem amplitude_derivative (F : (ℝ × ℝ) × ℝ → ℝ) (x : ℝ × ℝ) (γ : ℝ)
    (hF : DifferentiableAt ℝ F (x, γ)) :
    fderiv ℝ (fun y : ℝ × ℝ => F (y, γ)) x x = fderiv ℝ F (x, γ) (x, 0) := by
  have hi : HasFDerivAt (fun y : ℝ × ℝ => (y, γ))
      ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod (0 : (ℝ × ℝ) →L[ℝ] ℝ)) x :=
    (hasFDerivAt_id x).prodMk (hasFDerivAt_const γ x)
  have hd := hF.hasFDerivAt.comp x hi
  change (fderiv ℝ (F ∘ (fun y : ℝ × ℝ => (y, γ))) x) x = _
  rw [hd.fderiv]
  simp

private theorem signed_derivative_bound (f d : ℝ → ℝ) (A B γ : ℝ)
    (hd : ∀ t ∈ Set.uIcc (0 : ℝ) γ, HasDerivAt f (d t) t)
    (hbound : ∀ t ∈ Set.uIcc (0 : ℝ) γ, -A ≤ d t ∧ d t ≤ -B) :
    f 0 - A * max γ 0 + B * max (-γ) 0 ≤ f γ := by
  have hc : ContinuousOn f (Set.uIcc (0 : ℝ) γ) :=
    fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hf : DifferentiableOn ℝ f (interior (Set.uIcc (0 : ℝ) γ)) :=
    fun t ht => (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt
  rcases le_total (0 : ℝ) γ with hγ | hγ
  · have hb : ∀ t ∈ interior (Set.uIcc (0 : ℝ) γ), -A ≤ deriv f t := by
      intro t ht
      rw [(hd t (interior_subset ht)).deriv]
      exact (hbound t (interior_subset ht)).1
    have he := (convex_uIcc (0 : ℝ) γ).mul_sub_le_image_sub_of_le_deriv hc hf hb
      0 (Set.left_mem_uIcc) γ (Set.right_mem_uIcc) hγ
    rw [max_eq_left hγ, max_eq_right (neg_nonpos.mpr hγ), mul_zero, add_zero]
    linarith
  · have hb : ∀ t ∈ interior (Set.uIcc (0 : ℝ) γ), deriv f t ≤ -B := by
      intro t ht
      rw [(hd t (interior_subset ht)).deriv]
      exact (hbound t (interior_subset ht)).2
    have he := (convex_uIcc (0 : ℝ) γ).image_sub_le_mul_sub_of_deriv_le hc hf hb
      γ (Set.right_mem_uIcc) 0 (Set.left_mem_uIcc) hγ
    rw [max_eq_right hγ, max_eq_left (neg_nonneg.mpr hγ), mul_zero, sub_zero]
    linarith

private theorem rate_segment_norm (h γ t : ℝ) (x : ℝ × ℝ)
    (ht : t ∈ Set.uIcc (0 : ℝ) γ) :
    ‖(((h, root_EX054 h), t), x)‖ ≤ ‖(((h, root_EX054 h), γ), x)‖ := by
  have hat : |t| ≤ |γ| := by
    rcases le_total (0 : ℝ) γ with hγ | hγ
    · rw [Set.uIcc_of_le hγ] at ht
      rw [abs_of_nonneg ht.1, abs_of_nonneg hγ]
      exact ht.2
    · rw [Set.uIcc_of_ge hγ] at ht
      rw [abs_of_nonpos ht.2, abs_of_nonpos hγ]
      linarith [ht.1]
  simp only [Prod.norm_def, Real.norm_eq_abs]
  exact max_le_max (max_le_max le_rfl hat) le_rfl

/-- One common joint ball controls the ENTIRE rate segment at every fixed actual
selected reference. The envelope premise is precisely the factual Common
output. A negative rate shift strengthens the radial lower bound. -/
theorem polynomialSelectedDeficit_radial_rate_control
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (h0U : (0 : PolynomialRangeParameters) ∈ U)
    (hψ : ContDiffOn ℝ ∞ ψ U)
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (hamp : fderiv ℝ (fun x : ℝ × ℝ => ψ (x.1, x.2, (0, 0), 0)) 0 = 0)
    (henv : ∀ a b h γ : ℝ,
      ((a, b, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U →
      HasDerivAt (fun τ : ℝ => polynomialChartDeficit h (a0 * (1 + τ))
        (a • cosC2_STR02915 + b • sinC2_STR02915 +
          (ψ (a, b, (h, root_EX054 h), τ) : PeriodicC2_STR02969)))
        (-2 * a0 * polynomialChartGap h
          (a • cosC2_STR02915 + b • sinC2_STR02915 +
            (ψ (a, b, (h, root_EX054 h), γ) : PeriodicC2_STR02969))) γ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (h γ : ℝ) (x : ℝ × ℝ),
      ‖(((h, root_EX054 h), γ), x)‖ < δ →
      polynomialReducedDeficitRadial ψ ((h, root_EX054 h), 0) x -
          (3 * a0 / 2) * max γ 0 * (x.1 ^ 2 + x.2 ^ 2) +
          (a0 / 2) * max (-γ) 0 * (x.1 ^ 2 + x.2 ^ 2) ≤
        polynomialReducedDeficitRadial ψ ((h, root_EX054 h), γ) x := by
  obtain ⟨δ, hδ, hgap⟩ := polynomialReducedGap_radial_comparison hU h0U hψ hzero hamp
  refine ⟨δ, hδ, fun h γ x hx => ?_⟩
  let W := rateSelectedInput h ⁻¹' U
  obtain ⟨hW, hFs, hGs⟩ := selected_smooth hU hψ h
  let e := fun t : ℝ => polynomialReducedDeficitRadial ψ ((h, root_EX054 h), t) x
  let d := fun t : ℝ => -2 * a0 * fderiv ℝ (polynomialReducedGap ψ ((h, root_EX054 h), t)) x x
  have hall (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) γ) :
      ((x.1, x.2, (h, root_EX054 h), t) : PolynomialRangeParameters) ∈ U ∧
      (x.1 ^ 2 + x.2 ^ 2) / 4 ≤ fderiv ℝ (polynomialReducedGap ψ ((h, root_EX054 h), t)) x x ∧
      fderiv ℝ (polynomialReducedGap ψ ((h, root_EX054 h), t)) x x ≤ 3 * (x.1 ^ 2 + x.2 ^ 2) / 4 :=
    hgap _ x ((rate_segment_norm h γ t x ht).trans_lt hx)
  have hd : ∀ t ∈ Set.uIcc (0 : ℝ) γ, HasDerivAt e (d t) t := by
    intro t ht
    have hp := (hall t ht).1
    have hd0 := polynomialSelectedDeficit_radial_rate_envelope hU hψ h
      (fun a b τ => henv a b h τ) x t hp
    change HasDerivAt (fun τ : ℝ => fderiv ℝ (rateSelectedF ψ h) (x, τ) (x, 0))
      (-2 * a0 * fderiv ℝ (rateSelectedG ψ h) (x, t) (x, 0)) t at hd0
    have hpW : (x,t) ∈ rateSelectedInput h ⁻¹' U := hp
    have hGd := (hGs.contDiffAt (hW.mem_nhds hpW)).differentiableAt (by simp)
    have hGeq := amplitude_derivative (rateSelectedG ψ h) x t hGd
    change fderiv ℝ (polynomialReducedGap ψ ((h, root_EX054 h), t)) x x =
      fderiv ℝ (rateSelectedG ψ h) (x, t) (x, 0) at hGeq
    rw [← hGeq] at hd0
    have heq : e =ᶠ[𝓝 t] (fun τ : ℝ => fderiv ℝ (rateSelectedF ψ h) (x, τ) (x, 0)) := by
      have hc : Continuous (fun τ : ℝ => rateSelectedInput h (x, τ)) := by unfold rateSelectedInput; fun_prop
      filter_upwards [(hc.tendsto t).eventually (hU.mem_nhds hp)] with τ hτ
      exact amplitude_derivative (rateSelectedF ψ h) x τ
        ((hFs.contDiffAt (hW.mem_nhds (show (x,τ) ∈ rateSelectedInput h ⁻¹' U from hτ))).differentiableAt (by simp))
    exact hd0.congr_of_eventuallyEq heq
  have hb : ∀ t ∈ Set.uIcc (0 : ℝ) γ,
      -((3 * a0 / 2) * (x.1 ^ 2 + x.2 ^ 2)) ≤ d t ∧
        d t ≤ -((a0 / 2) * (x.1 ^ 2 + x.2 ^ 2)) := by
    intro t ht
    obtain ⟨_, hl, hu⟩ := hall t ht
    have ha := a0_pos
    have hl' := mul_le_mul_of_nonneg_left hl
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha.le)
    have hu' := mul_le_mul_of_nonneg_left hu
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha.le)
    dsimp only [d]
    constructor <;> nlinarith only [hl', hu']
  have he := signed_derivative_bound e d ((3 * a0 / 2) * (x.1 ^ 2 + x.2 ^ 2))
    ((a0 / 2) * (x.1 ^ 2 + x.2 ^ 2)) γ hd hb
  dsimp only [e] at he
  nlinarith only [he]

/-- A genuine positive-gap chart on the retained graph has nonzero amplitude.
This proves the denominator needed by the scale bootstrap; it does not assume
any amplitude lower bound, optimizer classification or stationarity. -/
theorem polynomialSelectedGap_positive_amplitude
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hzero : ∀ h s γ : ℝ, ((0, 0, (h, s), γ) : PolynomialRangeParameters) ∈ U →
      ψ (0, 0, (h, s), γ) = 0)
    (h γ : ℝ) (x : ℝ × ℝ) (b : AbsoluteDrift (canonical_elementary_polynomial_model h))
    (hp : ((x.1, x.2, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U)
    (hG : 0 < scalarGap (canonical_elementary_polynomial_model h)
      (polynomialChartAbsolute h (polynomialGapLift ψ ((h, root_EX054 h), γ) x))) :
    0 < x.1 ^ 2 + x.2 ^ 2 := by
  by_contra hn
  have hr : x.1 ^ 2 + x.2 ^ 2 ≤ 0 := le_of_not_gt hn
  have hx1 : x.1 = 0 := by
    apply sq_eq_zero_iff.mp
    exact le_antisymm (by linarith [sq_nonneg x.2]) (sq_nonneg x.1)
  have hx2 : x.2 = 0 := by
    apply sq_eq_zero_iff.mp
    exact le_antisymm (by linarith [sq_nonneg x.1]) (sq_nonneg x.2)
  have hx : x = 0 := Prod.ext hx1 hx2
  have hψ0 := hzero h (root_EX054 h) γ (by simpa only [hx, Prod.fst_zero, Prod.snd_zero] using hp)
  have hL : polynomialGapLift ψ ((h, root_EX054 h), γ) x = 0 := by
    rw [hx]
    simp only [polynomialGapLift, polynomialGapSlice, Prod.fst_zero, Prod.snd_zero,
      zero_smul, zero_add, hψ0, Submodule.coe_zero]
  have hg := polynomialReducedGap_actual ψ h γ x b
  have hz : polynomialReducedGap ψ ((h, root_EX054 h), γ) x = 0 := by
    unfold polynomialReducedGap
    rw [hL, polynomialRangeGap_zero]
  rw [hz] at hg
  have hpG : 0 < (scalarGap (canonical_elementary_polynomial_model h)
      (polynomialChartAbsolute h (polynomialGapLift ψ ((h, root_EX054 h), γ) x)) : ℝ) := hG
  linarith only [hg, hpG]

end DGPS.Examples.PolynomialSpecies
