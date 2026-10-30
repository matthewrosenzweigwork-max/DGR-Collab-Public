import DGPS.Examples.ThreeSpeciesCircle.OrdinaryGroundStateRoots
import DGPS.Structural.AmplitudeComparison
import DGPS.Frontier.STR029.T05
import DGPS.Frontier.STR029.T26s2

/-!
# The strict ordinary reference Poincare gap

The full native weighted weak-H1 domain is transported to T05. The canonical ordinary
rate expansion then gives a strict gap and a positive uniform lower rate for small h.
-/

open MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open DGPS.Circle.AngularNormalization DGPS.Frontier.STR029

namespace DGPS.Examples.ThreeSpeciesCircle

private theorem reference_integral_angular (h : ℝ) (f : Torus 1 → ℝ) :
    (∫ x, f x ∂threefoldReference h) = normInt_STR02933
      (fun t => qT_STR02904 h t * f (angEquiv.symm (t : AngCircle))) := by
  rw [integral_threefoldReference]
  have he : (fun x => referenceDensity h x * f x) =
      fun x => (fun θ : AngCircle => qT_STR02904 h (angSec θ) *
        f (angEquiv.symm θ)) (angEquiv x) := by
    funext x
    have hq := qAng_eq_qT_STR02962 h (angEquiv x)
    change referenceDensity h (angEquiv.symm (angEquiv x)) =
      qT_STR02904 h (angSec (angEquiv x)) at hq
    simp only [angEquiv.symm_apply_apply] at hq ⊢
    rw [hq]
  rw [he, integral_comp_angEquiv (fun θ : AngCircle =>
    qT_STR02904 h (angSec θ) * f (angEquiv.symm θ))]
  have hs : (fun θ : AngCircle => qT_STR02904 h (angSec θ) * f (angEquiv.symm θ)) =
      fun θ => (fun t : ℝ => qT_STR02904 h t * f (angEquiv.symm (t : AngCircle))) (angSec θ) := by
    funext θ
    change qT_STR02904 h (angSec θ) * f (angEquiv.symm θ) =
      qT_STR02904 h (angSec θ) * f (angEquiv.symm ((angSec θ : ℝ) : AngCircle))
    rw [coe_angSec_STR02962]
  rw [hs, integral_angSec_STR02962 (fun t => qT_STR02904 h t * f (angEquiv.symm (t : AngCircle)))]
  exact (normInt_eq_meanT_STR02962 _).symm

private theorem haar_integral_angular (f : Torus 1 → ℝ) :
    (∫ x, f x ∂haar 1) = normInt_STR02933 (fun t => f (angEquiv.symm (t : AngCircle))) := by
  calc
    _ = ∫ θ, f (angEquiv.symm θ) ∂angHaar := by
      simpa only [angEquiv.symm_apply_apply] using
        integral_comp_angEquiv (fun θ : AngCircle => f (angEquiv.symm θ))
    _ = _ := by
      have he : (fun θ : AngCircle => f (angEquiv.symm θ)) =
          fun θ => (fun t : ℝ => f (angEquiv.symm (t : AngCircle))) (angSec θ) := by
        funext θ
        change f (angEquiv.symm θ) = f (angEquiv.symm ((angSec θ : ℝ) : AngCircle))
        rw [coe_angSec_STR02962]
      rw [he, integral_angSec_STR02962 (fun t => f (angEquiv.symm (t : AngCircle)))]
      exact (normInt_eq_meanT_STR02962 _).symm

private theorem variance_shift (μ : ProbabilityMeasure (Torus 1)) (f : WeakH1Test μ) (c : ℝ) :
    weightedVariance μ (Structural.shiftTest μ f c).fn = weightedVariance μ f.fn := by
  have hm : (∫ x, (f.fn x - c) ∂(μ : Measure (Torus 1))) =
      (∫ x, f.fn x ∂(μ : Measure (Torus 1))) - c := by
    rw [integral_sub (f.isWeak.memLp.integrable (by norm_num)) (integrable_const c)]
    simp
  unfold weightedVariance
  change (∫ x, (f.fn x - c - ∫ y, (f.fn y - c) ∂(μ : Measure (Torus 1))) ^ 2
    ∂(μ : Measure (Torus 1))) = _
  rw [hm]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

/-- T05 on the entire native weighted form domain, in physical units. -/
theorem threefold_reference_poincare_lower (h : ℝ) (hh : |h| ≤ 1 / 1000) :
    ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 * (1 - h ^ 2)) ≤ poincareRate (str025_prob h) := by
  have ha0 : 0 < DGPS.Circle.AngularNormalization.a0 := by unfold DGPS.Circle.AngularNormalization.a0; positivity
  have hh1 : 0 ≤ 1 - h ^ 2 := by
    have hsq := (sq_le_sq₀ (abs_nonneg h) (by norm_num : (0 : ℝ) ≤ 1 / 1000)).2 hh
    rw [sq_abs] at hsq
    nlinarith
  apply (le_poincareRate_iff_forall _ _).2
  intro f hf
  let c := ∫ x, f.fn x ∂haar 1
  let fc := Structural.shiftTest (str025_prob h) f c
  let F : AngCircle → ℝ := fun θ => fc.fn (angEquiv.symm θ)
  let G : AngCircle → ℝ := fun θ => (2 * Real.pi)⁻¹ * fc.grad (angEquiv.symm θ) 0
  have hHaar : IsWeakGradient fc.fn fc.grad :=
    (isWeightedWeakGradient_iff (ordinaryReference h)).mp
      ((isMeasureWeakGradient_iff (ordinaryReference h)).mp fc.isWeak)
  have hFG : IsWeakGradient (F ∘ angEquiv) (physGrad G) := by
    refine hHaar.congr_ae (Eventually.of_forall fun x => ?_)
      (Eventually.of_forall fun x => ?_)
    · simp only [Function.comp_apply, F, angEquiv.symm_apply_apply]
    · ext i
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      subst i
      rw [physGrad_apply]
      dsimp only [G]
      rw [angEquiv.symm_apply_apply]
      field_simp [Real.two_pi_pos.ne']
  have hweak := angularWD_to_periodicWD_STR02926 ((isWeakGradient_comp_iff F G).mpr hFG)
  have hmean : normInt_STR02933 (fun t : ℝ => F (t : AngCircle)) = 0 := by
    rw [← haar_integral_angular fc.fn]
    change (∫ x, (f.fn x - c) ∂haar 1) = 0
    rw [integral_sub f.isWeak.integrable (integrable_const c)]
    simp [c]
  have hp := str029_05_poincare_bound_sufficient_attainment h hh
    (fun t : ℝ => F (t : AngCircle)) (fun t : ℝ => G (t : AngCircle)) hweak
  simp only [hmean, sub_zero] at hp
  have hv : weightedVariance (str025_prob h) fc.fn =
      varQ_STR02935 h (fun t : ℝ => F (t : AngCircle)) := by
    have hv := ProbabilityTheory.variance_eq_sub fc.isWeak.memLp
    have hv0 := ProbabilityTheory.variance_eq_integral
      fc.isWeak.memLp.aestronglyMeasurable.aemeasurable
    rw [hv0] at hv
    change weightedVariance (str025_prob h) fc.fn = _ at hv
    rw [hv]
    change (∫ x, fc.fn x ^ 2 ∂threefoldReference h) -
      (∫ x, fc.fn x ∂threefoldReference h) ^ 2 = _
    rw [reference_integral_angular h (fun x => fc.fn x ^ 2), reference_integral_angular h fc.fn]
    unfold varQ_STR02935
    simp only [F, mul_comm]
  have hgi : Integrable (fun x => ‖fc.grad x‖ ^ 2) (threefoldReference h) :=
    fc.isWeak.memLp_grad.norm.integrable_sq
  have hn : ∀ z : Tangent 1, ‖z‖ ^ 2 = (z 0) ^ 2 := by
    intro z
    simp [EuclideanSpace.norm_sq_eq]
  have heBase : dirichletEnergy (str025_prob h) fc =
      ENNReal.ofReal (∫ x, ‖fc.grad x‖ ^ 2 ∂threefoldReference h) := by
    unfold dirichletEnergy
    rw [ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall fun _ => sq_nonneg _)]
    apply lintegral_congr
    intro x
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  have he : dirichletEnergy (str025_prob h) fc = ENNReal.ofReal
      (DGPS.Circle.AngularNormalization.a0 * normInt_STR02933 (fun t : ℝ => G (t : AngCircle) ^ 2 * qT_STR02904 h t)) := by
    rw [heBase]
    congr 1
    simp_rw [hn]
    rw [reference_integral_angular h (fun x => (fc.grad x 0) ^ 2), ← normInt_mul_const_STR02933]
    apply congrArg normInt_STR02933
    funext t
    dsimp only [G]
    unfold DGPS.Circle.AngularNormalization.a0
    field_simp [Real.two_pi_pos.ne']
    ring
  have hineq : (1 - h ^ 2) * weightedVariance (str025_prob h) f.fn ≤
      normInt_STR02933 (fun t : ℝ => G (t : AngCircle) ^ 2 * qT_STR02904 h t) := by
    rw [← variance_shift (str025_prob h) f c, hv]
    exact hp
  have he0 : dirichletEnergy (str025_prob h) fc = dirichletEnergy (str025_prob h) f := rfl
  rw [he0] at he
  rw [he, ← ENNReal.ofReal_mul (mul_nonneg ha0.le hh1)]
  apply ENNReal.ofReal_le_ofReal
  nlinarith [mul_le_mul_of_nonneg_left hineq ha0.le]

/-- The actual canonical ordinary rate stays positive and is strictly below the native
reference Poincare rate on a common small positive-h interval. -/
theorem threefold_reference_rate_and_strictPoincareGap :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ordinaryLSRate (ordinaryReference h) ≠ ⊤ ∧
      ENNReal.ofReal (DGPS.Circle.AngularNormalization.a0 / 2) ≤ ordinaryLSRate (ordinaryReference h) ∧
      ordinaryLSRate (ordinaryReference h) < poincareRate (str025_prob h) := by
  obtain ⟨ψ, Z, δB, C, hδB, hC, _, _, _, hmain, _⟩ := threefold_ordinaryRate_expansion
  have ha0 : 0 < DGPS.Circle.AngularNormalization.a0 := by unfold DGPS.Circle.AngularNormalization.a0; positivity
  let ε := Real.sqrt (DGPS.Circle.AngularNormalization.a0 / (30 * (C + 1)))
  have hε : 0 < ε := by dsimp [ε]; positivity
  let δ := min δB (min (1 / 1000) (min (1 / 4) ε))
  have hδ : 0 < δ := lt_min hδB (lt_min (by norm_num) (lt_min (by norm_num) hε))
  refine ⟨δ, hδ, fun h hh hhd => ?_⟩
  have hhB : h < δB := hhd.trans_le (min_le_left _ _)
  have hh1000 : h < 1 / 1000 := hhd.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hh4 : h < 1 / 4 := hhd.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hhε : h < ε := hhd.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨hfin, hexp, _⟩ := hmain h hh hhB
  have hs : h ^ 2 < DGPS.Circle.AngularNormalization.a0 / (30 * (C + 1)) := by
    have hs := (sq_lt_sq₀ hh.le hε.le).2 hhε
    dsimp only [ε] at hs
    rwa [Real.sq_sqrt (by positivity)] at hs
  have hC2 : C * h ^ 2 ≤ DGPS.Circle.AngularNormalization.a0 / 30 := by
    have hm := (lt_div_iff₀ (by positivity : (0 : ℝ) < 30 * (C + 1))).mp hs
    nlinarith [sq_nonneg h]
  have hC4 : C * h ^ 4 ≤ DGPS.Circle.AngularNormalization.a0 / 30 * h ^ 2 := by
    have hm := mul_le_mul_of_nonneg_right hC2 (sq_nonneg h)
    nlinarith
  have hsq4 : h ^ 2 < (1 / 16 : ℝ) := by nlinarith
  have hlow : DGPS.Circle.AngularNormalization.a0 / 2 ≤ (ordinaryLSRate (ordinaryReference h)).toReal := by
    have hlo := (abs_le.mp hexp).1
    nlinarith [mul_pos ha0 (show 0 < (1 / 16 : ℝ) - h ^ 2 by linarith)]
  have hupper : (ordinaryLSRate (ordinaryReference h)).toReal < DGPS.Circle.AngularNormalization.a0 * (1 - h ^ 2) := by
    have hhi := (abs_le.mp hexp).2
    nlinarith [mul_pos ha0 (sq_pos_of_pos hh)]
  refine ⟨hfin, ?_, ?_⟩
  · rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal hlow
  · have hr := threefold_reference_poincare_lower h (by rw [abs_of_pos hh]; exact hh1000.le)
    apply lt_of_lt_of_le _ hr
    rw [← ENNReal.ofReal_toReal hfin]
    apply (ENNReal.ofReal_lt_ofReal_iff (mul_pos ha0 (by linarith))).2
    exact hupper

/-- Strict reference gap with no supplied analytic premise. -/
theorem threefold_reference_strictPoincareGap :
    ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, 0 < h → h < δ →
      ordinaryLSRate (ordinaryReference h) < poincareRate (str025_prob h) := by
  obtain ⟨δ, hδ, hmain⟩ := threefold_reference_rate_and_strictPoincareGap
  exact ⟨δ, hδ, fun h hh hhd => (hmain h hh hhd).2.2⟩

end DGPS.Examples.ThreeSpeciesCircle
