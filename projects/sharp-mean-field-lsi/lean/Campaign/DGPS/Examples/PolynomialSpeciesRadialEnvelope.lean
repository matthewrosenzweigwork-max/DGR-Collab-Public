import DGPS.Examples.PolynomialSpeciesRangeCommon
import DGPS.Examples.PolynomialSpeciesRangeDeficit
import DGPS.Examples.PolynomialSpeciesReducedGap
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-! The actual rate envelope can be differentiated in amplitude on each fixed
selected-reference slice. The moving graph is retained, and the physical a0
factor is not removed. No derivative of the selected reference root is used. -/

noncomputable section
open Filter Topology NormedSpace
open scoped ContDiff
open DGPS.Frontier.STR029 DGPS.Examples.PolynomialEquilibrium

namespace DGPS.Examples.PolynomialSpecies

private theorem mixed_partial_eq
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F G : X → ℝ) (W : Set X) (hW : IsOpen W)
    (hF : ContDiffOn ℝ ∞ F W) (hG : ContDiffOn ℝ ∞ G W)
    (c : ℝ) (e v z : X) (hz : z ∈ W)
    (henv : ∀ y ∈ W, fderiv ℝ F y e = c * G y) :
    fderiv ℝ (fderiv ℝ F) z e v = c * fderiv ℝ G z v := by
  have hFc : ContDiffAt ℝ ∞ F z := hF.contDiffAt (hW.mem_nhds hz)
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) z :=
    ((hF.fderiv_of_isOpen hW (m := 1) (by simp)).contDiffAt
      (hW.mem_nhds hz)).differentiableAt (by simp)
  have hGd : DifferentiableAt ℝ G z :=
    (hG.contDiffAt (hW.mem_nhds hz)).differentiableAt (by simp)
  have he : (fun y => fderiv ℝ F y e) =ᶠ[𝓝 z] (fun y => c * G y) := by
    filter_upwards [hW.mem_nhds hz] with y hy
    exact henv y hy
  have hleft : HasFDerivAt (fun y => fderiv ℝ F y e)
      ((fderiv ℝ (fderiv ℝ F) z).flip e) z := by
    have hd := hDF.hasFDerivAt.clm_apply (hasFDerivAt_const e z)
    simpa only [ContinuousLinearMap.comp_zero, zero_add] using hd
  have hright : HasFDerivAt (fun y => c * G y) (c • fderiv ℝ G z) z :=
    hGd.hasFDerivAt.const_mul c
  have heq : fderiv ℝ (fun y => fderiv ℝ F y e) z =
      fderiv ℝ (fun y => c * G y) z := he.fderiv_eq
  rw [hleft.fderiv, hright.fderiv] at heq
  have hm := congrArg (fun L : X →L[ℝ] ℝ => L v) heq
  have hsym : IsSymmSndFDerivAt ℝ F z := hFc.isSymmSndFDerivAt (by simp)
  calc
    fderiv ℝ (fderiv ℝ F) z e v = fderiv ℝ (fderiv ℝ F) z v e := hsym.eq e v
    _ = c * fderiv ℝ G z v := by
      simpa only [ContinuousLinearMap.flip_apply, smul_apply, smul_eq_mul] using hm

private theorem envelope_path_derivative
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (F G : X → ℝ) (W : Set X) (hW : IsOpen W)
    (hF : ContDiffOn ℝ ∞ F W) (hG : ContDiffOn ℝ ∞ G W)
    (c : ℝ) (e v z : X) (hz : z ∈ W)
    (henv : ∀ y ∈ W, fderiv ℝ F y e = c * G y)
    (p : ℝ → X) (t : ℝ) (hp : HasDerivAt p e t) (hpz : z = p t) :
    HasDerivAt (fun s : ℝ => fderiv ℝ F (p s) v) (c * fderiv ℝ G z v) t := by
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) z :=
    ((hF.fderiv_of_isOpen hW (m := 1) (by simp)).contDiffAt
      (hW.mem_nhds hz)).differentiableAt (by simp)
  have hd : HasDerivAt (fun s : ℝ => fderiv ℝ F (p s) v)
      (fderiv ℝ (fderiv ℝ F) z e v) t := by
    have hh := (hDF.hasFDerivAt.comp_hasDerivAt_of_eq t hp hpz).clm_apply
      (hasDerivAt_const t v)
    simpa only [Function.comp_apply, map_zero, add_zero] using hh
  exact hd.congr_deriv (mixed_partial_eq F G W hW hF hG c e v z hz henv)

private theorem mixed_radial_derivative
    (F G : (ℝ × ℝ) × ℝ → ℝ) (W : Set ((ℝ × ℝ) × ℝ))
    (hW : IsOpen W) (hF : ContDiffOn ℝ ∞ F W) (hG : ContDiffOn ℝ ∞ G W)
    (c : ℝ) (henv : ∀ z ∈ W, fderiv ℝ F z (0, 1) = c * G z)
    (z : (ℝ × ℝ) × ℝ) (hz : z ∈ W) :
    HasDerivAt (fun t : ℝ => fderiv ℝ F (z.1, t) (z.1, 0))
      (c * fderiv ℝ G z (z.1, 0)) z.2 := by
  have hs : HasDerivAt (fun t : ℝ => (z.1, t)) (0, 1) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  exact envelope_path_derivative F G W hW hF hG c (0, 1) (z.1, 0) z hz henv
    (fun t : ℝ => (z.1, t)) z.2 hs rfl

private def rateSlice (h : ℝ) (z : (ℝ × ℝ) × ℝ) : PolynomialRangeParameters :=
  (z.1.1, z.1.2, (h, root_EX054 h), z.2)

private theorem rateSlice_smooth (h : ℝ) : ContDiff ℝ ∞ (rateSlice h) := by
  unfold rateSlice
  fun_prop

private def selectedLift (ψ : PolynomialRangeParameters → E_STR02969)
    (h : ℝ) (z : (ℝ × ℝ) × ℝ) : PeriodicC2_STR02969 :=
  polynomialGapLift ψ ((h, root_EX054 h), z.2) z.1

private theorem selectedLift_smooth {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hψ : ContDiffOn ℝ ∞ ψ U) (h : ℝ) :
    ContDiffOn ℝ ∞ (selectedLift ψ h) (rateSlice h ⁻¹' U) := by
  have hΦ : ContDiffOn ℝ ∞ (fun z => ψ (rateSlice h z)) (rateSlice h ⁻¹' U) :=
    hψ.comp (rateSlice_smooth h).contDiffOn (fun _ hz => hz)
  have hlin : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
      z.1.1 • cosC2_STR02915 + z.1.2 • sinC2_STR02915) := by fun_prop
  exact hlin.contDiffOn.add (E_STR02969.subtypeL.contDiff.comp_contDiffOn hΦ)

private def selectedInput (ψ : PolynomialRangeParameters → E_STR02969)
    (h : ℝ) (z : (ℝ × ℝ) × ℝ) : PolynomialEulerInput :=
  ((h, root_EX054 h), DGPS.Circle.AngularNormalization.a0 * (1 + z.2), selectedLift ψ h z)

private theorem selectedInput_smooth {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hψ : ContDiffOn ℝ ∞ ψ U) (h : ℝ) :
    ContDiffOn ℝ ∞ (selectedInput ψ h) (rateSlice h ⁻¹' U) := by
  have hr : ContDiff ℝ ∞ (fun z : (ℝ × ℝ) × ℝ =>
      DGPS.Circle.AngularNormalization.a0 * (1 + z.2)) := by fun_prop
  exact contDiffOn_const.prodMk (hr.contDiffOn.prodMk (selectedLift_smooth hψ h))

private def selectedValue (ψ : PolynomialRangeParameters → E_STR02969)
    (h : ℝ) (z : (ℝ × ℝ) × ℝ) : ℝ :=
  polynomialRangeDeficit (h, root_EX054 h)
    (DGPS.Circle.AngularNormalization.a0 * (1 + z.2)) (selectedLift ψ h z)

private theorem selectedValue_smooth {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hψ : ContDiffOn ℝ ∞ ψ U) (h : ℝ) :
    ContDiffOn ℝ ∞ (selectedValue ψ h) (rateSlice h ⁻¹' U) := by
  let V : PolynomialEulerInput → ℝ := fun q => polynomialRangeDeficit q.1 q.2.1 q.2.2
  have hV : ContDiff ℝ ∞ V := polynomialRangeDeficit_smooth
  have he : selectedValue ψ h = V ∘ selectedInput ψ h := rfl
  rw [he]
  exact hV.comp_contDiffOn (selectedInput_smooth hψ h)

private def selectedGap (ψ : PolynomialRangeParameters → E_STR02969)
    (h : ℝ) (z : (ℝ × ℝ) × ℝ) : ℝ :=
  polynomialRangeGap (h, root_EX054 h) (selectedLift ψ h z)

private theorem selectedGap_smooth {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969} (hψ : ContDiffOn ℝ ∞ ψ U) (h : ℝ) :
    ContDiffOn ℝ ∞ (selectedGap ψ h) (rateSlice h ⁻¹' U) := by
  let V : (ℝ × ℝ) × PeriodicC2_STR02969 → ℝ := fun q => polynomialRangeGap q.1 q.2
  let q : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × PeriodicC2_STR02969 :=
    fun z => ((h, root_EX054 h), selectedLift ψ h z)
  have hV : ContDiff ℝ ∞ V := polynomialRangeGap_smooth
  have hq : ContDiffOn ℝ ∞ q (rateSlice h ⁻¹' U) :=
    contDiffOn_const.prodMk (selectedLift_smooth hψ h)
  have he : selectedGap ψ h = V ∘ q := rfl
  rw [he]
  exact hV.comp_contDiffOn hq

private theorem selectedValue_partial {U : Set PolynomialRangeParameters}
    {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U) (h : ℝ)
    (henv : ∀ z ∈ rateSlice h ⁻¹' U,
      HasDerivAt (fun τ : ℝ => polynomialChartDeficit h
        (DGPS.Circle.AngularNormalization.a0 * (1 + τ)) (selectedLift ψ h (z.1, τ)))
        (-2 * DGPS.Circle.AngularNormalization.a0 * polynomialChartGap h (selectedLift ψ h z)) z.2) :
    ∀ z ∈ rateSlice h ⁻¹' U, fderiv ℝ (selectedValue ψ h) z (0, 1) =
      (-2 * DGPS.Circle.AngularNormalization.a0) * selectedGap ψ h z := by
  intro z hz
  have hW := hU.preimage (rateSlice_smooth h).continuous
  have hFd := ((selectedValue_smooth hψ h).contDiffAt
    (hW.mem_nhds hz)).differentiableAt (by simp)
  have hs : HasDerivAt (fun τ : ℝ => (z.1, τ)) (0, 1) z.2 :=
    (hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2)
  have hd := hFd.hasFDerivAt.comp_hasDerivAt z.2 hs
  have hv : (fun τ : ℝ => selectedValue ψ h (z.1, τ)) =
      (fun τ : ℝ => polynomialChartDeficit h
        (DGPS.Circle.AngularNormalization.a0 * (1 + τ)) (selectedLift ψ h (z.1, τ))) := by
    funext τ
    exact polynomialRangeDeficit_actual h _ _
  change HasDerivAt (fun τ : ℝ => selectedValue ψ h (z.1, τ)) _ z.2 at hd
  rw [hv] at hd
  have hr := hd.unique (henv z hz)
  change fderiv ℝ (selectedValue ψ h) z (0, 1) = _ at hr
  rw [← polynomialRangeGap_actual h (selectedLift ψ h z)] at hr
  exact hr

/-- Actual radial rate derivative on the SAME graph as the production envelope.
The envelope hypothesis is exactly the corresponding output of Common, on a
full open amplitude/rate slice. No independent-reference envelope or desired
radial derivative is assumed. The radial vector has rate coordinate zero. -/
theorem polynomialSelectedDeficit_radial_rate_envelope
    {U : Set PolynomialRangeParameters} {ψ : PolynomialRangeParameters → E_STR02969}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ ∞ ψ U) (h : ℝ)
    (henv : ∀ a b γ : ℝ,
      ((a, b, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U →
      HasDerivAt (fun τ : ℝ => polynomialChartDeficit h
        (DGPS.Circle.AngularNormalization.a0 * (1 + τ))
        (a • cosC2_STR02915 + b • sinC2_STR02915 +
          (ψ (a, b, (h, root_EX054 h), τ) : PeriodicC2_STR02969)))
        (-2 * DGPS.Circle.AngularNormalization.a0 * polynomialChartGap h
          (a • cosC2_STR02915 + b • sinC2_STR02915 +
            (ψ (a, b, (h, root_EX054 h), γ) : PeriodicC2_STR02969))) γ)
    (x : ℝ × ℝ) (γ : ℝ)
    (hp : ((x.1, x.2, (h, root_EX054 h), γ) : PolynomialRangeParameters) ∈ U) :
    let F := fun z : (ℝ × ℝ) × ℝ => polynomialRangeDeficit (h, root_EX054 h)
      (DGPS.Circle.AngularNormalization.a0 * (1 + z.2))
      (polynomialGapLift ψ ((h, root_EX054 h), z.2) z.1)
    let G := fun z : (ℝ × ℝ) × ℝ =>
      polynomialReducedGap ψ ((h, root_EX054 h), z.2) z.1
    HasDerivAt (fun τ : ℝ => fderiv ℝ F (x, τ) (x, 0))
      (-2 * DGPS.Circle.AngularNormalization.a0 * fderiv ℝ G (x, γ) (x, 0)) γ := by
  let W := rateSlice h ⁻¹' U
  have hW : IsOpen W := hU.preimage (rateSlice_smooth h).continuous
  have he := selectedValue_partial hU hψ h (fun z hz => henv z.1.1 z.1.2 z.2 hz)
  exact mixed_radial_derivative (selectedValue ψ h) (selectedGap ψ h) W hW
    (selectedValue_smooth hψ h) (selectedGap_smooth hψ h)
    (-2 * DGPS.Circle.AngularNormalization.a0) he (x, γ) hp

end DGPS.Examples.PolynomialSpecies
